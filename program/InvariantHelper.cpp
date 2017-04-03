/*
 * InvariantHelper.cpp
 *      Location: Vienna
 */

#include "InvariantHelper.hpp"

#include "Forwards.hpp"

#include "Debug/Tracer.hpp"

#include "Kernel/FormulaUnit.hpp"
#include "Kernel/InferenceStore.hpp"
#include "Kernel/MainLoop.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Event.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Timer.hpp"

#include "Lib/Sys/Multiprocessing.hpp"

#include "Parse/TPTP.hpp"

#include "Saturation/ProvingHelper.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Saturation/SymElOutput.hpp"

#include "Shell/CNF.hpp"
#include "Shell/Options.hpp"
#include "Shell/Preprocess.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UIHelper.hpp"

using Lib::env;
using namespace Kernel;

namespace Program {

  void InvariantHelper::setSEIOptions()
  {
    CALL("InvariantHelper::setSEIOptions");

    //env.options->set("splitting", "on");
    env.options->set("show_symbol_elimination", "on");
    //env.options->set("unused_predicate_definition_removal", "off");
    // env.options->set("propositional_to_bdd","off");
        
    env.options->setNaming(32000);
  }

  void InvariantHelper::run()
  {
    CALL("InvariantHelper::run");

    setSEIOptions();

    Shell::Options::InvariantFiltering filter = env.options->invariantFiltering();
    
    if (filter == Shell::Options::InvariantFiltering::OFF || UnitList::isEmpty(_goal)) {
      generateAll();
    } else if (filter == Shell::Options::InvariantFiltering::ON) {
      generateAndProveConjecture();
    } else if (filter == Shell::Options::InvariantFiltering::DIRECT_PROOF) {
      generateWithNegatedConjecture();
    }
  }

  void InvariantHelper::generateAll()
  {
    CALL("InvariantHelper::generateAll");

    if (_verbose)
      displayUnits(_properties);

    Problem gen(_properties);
    Shell::Preprocess p(*env.options);
    p.preprocess(gen);

    Saturation::ProvingHelper::runVampireSaturation(gen, *env.options);
    env.beginOutput();
    UIHelper::outputResult(env.out());
    env.endOutput();
  }

  void InvariantHelper::generateWithNegatedConjecture()
  {
    CALL("InvariantHelper::generateWithNegatedConjecture");

    UnitList* l = _properties->append(_goal);
    if (_verbose)
      displayUnits(l);
    
    Problem gen(l);
    Shell::Preprocess p(*env.options);
    p.preprocess(gen);

    Saturation::ProvingHelper::runVampireSaturation(gen, *env.options);
    env.beginOutput();
    UIHelper::outputResult(env.out());
    env.endOutput();
  }

  void InvariantHelper::generateAndProveConjecture()
  {
    CALL("InvariantHelper::generateAndProveConjecture");

    if (_verbose) {
      env.beginOutput();
      env.out() << "------- Generation --------" << std::endl;
      displayUnits(_properties);
      env.out() << "--- Postcondition proof ---" << std::endl;
      displayUnits(_goal);
      env.endOutput();
    }
    
    pid_t child = Lib::Multiprocessing::instance()->fork();
    ASS_NEQ(child,-1);
    
    if(child) {
      //we're in parent
      UnitList* res = runDynamicRefutation();
      Multiprocessing::instance()->kill(child, SIGINT);
      env.beginOutput();
      env.out() << "-------Relevant invariants-------" << endl;
      displayUnits(res);
      env.out() << "---------------------------------" << endl;
      env.endOutput();
    } else {
      // silence output
      env.beginOutput();
      env.out().setstate(std::ios_base::failbit);
      env.endOutput();
      runClauseGeneration();
    }
  }

  void InvariantHelper::runClauseGeneration()
  {
    CALL("InvariantHelper::runClauseGeneration");

    // TODO enforce time limit
    Problem pb(_properties);
    Shell::Preprocess pp(*env.options);
    pp.preprocess(pb);
    Saturation::SaturationAlgorithm *salg = Saturation::SaturationAlgorithm::createFromOptions(pb, *env.options);
    // every time a new clause is output by symbol elimination, print it on sync pipe
    _syncPipe.neverRead();
    _syncPipe.acquireWrite();
    _printer.setTargetStream(&_syncPipe.out());

    printStartingProblem();
    
    salg->getSymbolEliminationOutput()->symElEvent.subscribe(this, &InvariantHelper::onSymElEvent);
    salg->initAlgorithmRun();
    for (;;) {
      _newInv = false;
      salg->doOneAlgorithmStep();
      if (_newInv) {
        // print an empty line as delimiter
        _syncPipe.out() << std::endl;
        _newInv = false;
      }
    }
    
    _syncPipe.releaseWrite();
  }

  // callback function, writes clause on pipe
  void InvariantHelper::onSymElEvent(Clause *c)
  {
    CALL("InvariantHelper::onSymElEvent");

    _printer.print(c);
    _newInv = true;
  }

  void InvariantHelper::printStartingProblem()
  {
    CALL("InvariantHelper::printStartingProblem");

    UnitList::Iterator it(_goal);
    
    while (it.hasNext()) {
      _printer.print(it.next());
    }
    
    // blank line as delimiter
    _syncPipe.out() << std::endl;
  }

  UnitList* InvariantHelper::runDynamicRefutation()
  {
    CALL("InvariantHelper::runDynamicRefutation");

    env.options->setTimeLimitInDeciseconds(10);
    // with time limit enforced, the system terminates immediately
    // upon reached the time limit
    env.timer->setTimeLimitEnforcement(false);
    Lib::vstring str = "", line;
    Saturation::SaturationAlgorithm *salg;
    Shell::Preprocess pp(*env.options);
    Problem *pb;
    
    _syncPipe.neverWrite();
    
    for (;;) {     
      env.timer->reset();
      env.timer->start();
      _syncPipe.acquireRead();

      while (getline(_syncPipe.in(), line) && (line != "")) {
        //read lines, up to the first blank line, store all in str
        str += line;
        str += "\n";
      }

      _syncPipe.releaseRead();

      if (str == "") {
        // nothing received yet (first iterations only), busy wait
        continue;
      }
      
      // rebuild and restart the problem
      
      vistringstream vis(str);
      
      delete env.signature;
      env.signature = new Signature();
      
      pb = new Problem(Parse::TPTP::parse(vis));


      pp.preprocess(*pb);

      salg = Saturation::SaturationAlgorithm::createFromOptions(*pb, *env.options);
      MainLoopResult res = salg->run();
      switch (res.terminationReason) {
      case Statistics::REFUTATION:
        return selectRelevantInvariants(res.refutation);
      case Statistics::TIME_LIMIT:
        // increase time limit
        env.options->setTimeLimitInDeciseconds(env.options->timeLimitInDeciseconds() + 10);
        break;
      case Statistics::SATISFIABLE:
      case Statistics::SAT_UNSATISFIABLE:
      case Statistics::SAT_SATISFIABLE:
      case Statistics::REFUTATION_NOT_FOUND:
      case Statistics::UNKNOWN:
      case Statistics::MEMORY_LIMIT:
        break;
      }
      
      delete salg;
    }
    return UnitList::empty();
  }

  void InvariantHelper::displayUnits(Lib::List<Unit*>* l)
  {
    CALL("InvariantHelper::displayUnits");

    env.beginOutput();
    UnitList::Iterator it(l);
    while (it.hasNext())
      env.out() << *it.next() << std::endl;
    env.endOutput();
  }

  UnitList* InvariantHelper::selectRelevantInvariants(Unit *refutation) {
    CALL("InvariantHelper::selectRelevantInvariants");
    
    Inference::Rule rule;
    UnitIterator it = InferenceStore::instance()->getParents(refutation, rule);
    if (rule == Inference::INPUT && refutation->inputType() == Unit::ASSUMPTION) {
      return UnitList::empty()->cons(refutation);
    } else {
      UnitList*l = UnitList::empty();
      
      while (it.hasNext()) {
        l = l->append(selectRelevantInvariants(it.next()));
      }

      return l;
    }
  }

}
