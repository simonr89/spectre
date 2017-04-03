/*
 * InvariantHelper.hpp
 *      Location: Vienna
 */

#ifndef __InvariantHelper__
#define __InvariantHelper__

#include "Lib/List.hpp"

#include "Lib/Sys/SyncPipe.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Sorts.hpp"

#include "Shell/TPTPPrinter.hpp"

/*
 * Helper class in order to generate invariants for a while loop
 *
 */
namespace Program
{

class InvariantHelper {
public:
  // The goal should typically be the conjunction of negated
  // postcondition and negated loop condition(s) (i.e. the goal is
  // expected to be already negated). If this is never set, vampire
  // will simply output as many invariants as possible given the time
  // limit. If a goal is set, generated invariants will be used to try
  // to prove the goal.
  InvariantHelper(Kernel::UnitList *properties,
                  Kernel::UnitList *goal = 0) :
    _verbose(true),
    _properties(properties),
    _goal(goal),
    _syncPipe(),
    _printer()
  {}
  
  ~InvariantHelper() {}

  void run();

private:
  bool _verbose;
  Kernel::UnitList *_properties;
  Kernel::UnitList *_goal;

  Lib::Sys::SyncPipe _syncPipe;
  Shell::TPTPPrinter _printer;

  bool _newInv; // flag used for the filtering mode
  
  void setSEIOptions();

  void generateAll();
  void generateWithNegatedConjecture();
  void generateAndProveConjecture();

  void runClauseGeneration();
  Kernel::UnitList* runDynamicRefutation();

  void onSymElEvent(Kernel::Clause *c);

  void displayUnits(Kernel::UnitList *l);

  void printStartingProblem();

  Kernel::UnitList* selectRelevantInvariants(Kernel::Unit *refutation);
};

}

#endif /* __InvariantHelper__ */
