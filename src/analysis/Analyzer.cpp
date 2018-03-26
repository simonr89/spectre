#include "Analyzer.hpp"

#include <fstream>
#include <ostream>

#include "Properties.hpp"
#include "Output.hpp"

namespace program {

  void Analyzer::densityAndStrictness()
  {
    for (auto it = variables.begin(); it != variables.end(); ++it) {
      densityAndStrictness((*it).second);
    }
  }

  void Analyzer::densityAndStrictness(PVariable *v) {
    if (!v->isMonotonic())
      return;

    bool strict = true, dense = true;
    int incr;
    for (auto it = loop.commands().begin(); it != loop.commands().end(); ++it) {
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

    void Analyzer::buildProperties()
    {
        // final bit of light-weight analysis on monotonic scalars
        densityAndStrictness();
        
        // creating units
        Properties props(loop, variables, preconditions);
        
        for (auto it = std::begin(postconditions); it != std::end(postconditions); ++it) {
            props.addPostcondition(*it);
        }
        
        props.analyze();
        props.outputTPTP();
    }
}
