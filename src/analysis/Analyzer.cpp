#include "Analyzer.hpp"

#include <fstream>
#include <ostream>

#include "Properties.hpp"
#include "Output.hpp"

namespace program {

  void Analyzer::densityAndStrictness(GuardedCommandCollection &c)
  {
    for (auto it = _variables.begin(); it != _variables.end(); ++it) {
      densityAndStrictness(c, (*it).second);
    }
  }

  void Analyzer::densityAndStrictness(GuardedCommandCollection &c, PVariable *v) {
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
  bool Analyzer::isIncremented(GuardedCommand *gc, PVariable *v, int &incr)
  {
    for (auto it = gc->assignments().begin(); it != gc->assignments().end(); ++it) {
      if ((*it)->hasLhs(*v))
        return ((*it)->isScalarIncrement(incr) && incr != 0);
    }
    return false;
  }

    void Analyzer::buildProperties(GuardedCommandCollection &c)
    {
        
        
        // final bit of light-weight analysis on monotonic scalars
        c.finalizeGuards();
        densityAndStrictness(c);
        
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
}
