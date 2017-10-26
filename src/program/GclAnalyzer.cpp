#include "GclAnalyzer.hpp"

#include <fstream>
#include <ostream>

#include "program/Properties.hpp"
#include "util/Output.hpp"

namespace program {

  bool GclAnalyzer::_errorFlag = false;

  int GclAnalyzer::parse(const std::string& f)
  {
    // test readbility, easier than catching exception thrown by parser
    std::ifstream istr(f);
    if (!istr) {
      std::cerr << "Unable to read file " << f << std::endl;
      return 0;
    }
    
    file = f;
    scan_begin();
    parser::GclParser parser(*this);
    parser.set_debug_level(false); // no traces
    int res = parser.parse();
    scan_end();
    
    return res;
  }

  bool GclAnalyzer::available(const std::string& name) {
    return _variables.find(name) == _variables.end();
  }

  PVariable* GclAnalyzer::declareVariable(const std::string& name)
  {
    PVariable *v = new PVariable(name, _typeDeclCtx);
    _variables[name] = v;
    return v;
  }

  QVariable* GclAnalyzer::openLocalScope(const std::string& name, Type t)
  {
    // TODO prevent variable capture (disallow same name)
    QVariable *v = new QVariable(name, t);
    _localScopes.push_front(v);
    return v;
  }

  void GclAnalyzer::closeLocalScope()
  {
    _localScopes.pop_front();
  }

  Variable* GclAnalyzer::getVariable(const std::string& name)
  {
    for (auto it1 = _localScopes.begin(); it1 != _localScopes.end(); ++it1) {
      if ((*it1)->name() == name)
        return *it1;
    }
    auto it2 = _variables.find(name);
    if (it2 != _variables.end()) {
      return (*it2).second;
    } else {
      return nullptr;
    }
  }

  void GclAnalyzer::densityAndStrictness(GuardedCommandCollection &c)
  {
    for (auto it = _variables.begin(); it != _variables.end(); ++it) {
      densityAndStrictness(c, (*it).second);
    }
  }

  void GclAnalyzer::densityAndStrictness(GuardedCommandCollection &c, PVariable *v) {
    if (!v->isMonotonic())
      return;

    bool strict = true, dense = true;
    int incr;
    for (auto it = c.commands().begin(); it != c.commands().end(); ++it) {
      if (isIncremented(*it, v, incr))
        dense &= (incr == 1 || incr == -1);
      else
        strict = false;
    }
    
    if (strict)
      v->setStrict();
    if (dense)
      v->setDense();
  }

  /** helper function, return true iff v is incremented by a constant
      in the guard gc. The constant is then stored in incr */
  bool GclAnalyzer::isIncremented(GuardedCommand *gc, PVariable *v, int &incr)
  {
    for (auto it = gc->assignments().begin(); it != gc->assignments().end(); ++it) {
      if ((*it)->hasLhs(*v))
        return ((*it)->isScalarIncrement(incr) && incr != 0);
    }
    return false;
  }

  void GclAnalyzer::buildProperties(GuardedCommandCollection &c) {
    
    
    // final bit of light-weight analysis on monotonic scalars
    c.finalizeGuards();
    densityAndStrictness(c);
    printInfo(c);

    // creating units
    Properties props(c, _variables);

    //add precondition and post conditions
    for (auto it = std::begin(_preconditions); it != std::end(_preconditions); ++it) {
      props.addPrecondition(*it);
    }

    for (auto it = std::begin(_postconditions); it != std::end(_postconditions); ++it) {
      props.addPostcondition(*it);
    }
    
    props.analyze();
    props.outputTPTP();
  }

  void GclAnalyzer::printInfo(GuardedCommandCollection &c) {
    std::ostream& ostr = util::Output::stream();

    ostr << util::Output::comment
         << "--- Parsed loop ---\n\n"
         << c
         << "\n\n--- Table of symbols ---\n\n";
    for (auto it = _variables.begin(); it != _variables.end(); ++it) {
      ostr << util::Output::comment << *(*it).second << "\n";
    }
    ostr << util::Output::nocomment;
    ostr << std::endl;
  }

  /* The following are declared in Parse/GclParser.ll
   *
   * void program::GclAnalyzer::scan_begin()
   *
   * void program::GclAnalyzer::scan_end()
   */

}
