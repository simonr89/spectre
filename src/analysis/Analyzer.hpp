
#ifndef __Analyzer__
#define __Analyzer__

#include <string>
#include <list>
#include <vector>
#include <map>
#include "Expression.hpp"
#include "GuardedCommandCollection.hpp"
#include "Variable.hpp"

namespace program {

  class Analyzer
  {
  public:

      Analyzer(const GuardedCommandCollection& loop,
               const std::vector<FExpression*>& preconditions,
               const std::vector<FExpression*>& postconditions,
               const std::map<std::string, PVariable*>& variables
               ) : loop(loop), preconditions(preconditions), postconditions(postconditions), variables(variables) {}
      
      const GuardedCommandCollection& loop;
      const std::vector<FExpression*> preconditions;
      const std::vector<FExpression*> postconditions;
      const std::map<std::string, PVariable*> variables; /* symbol table */
      
      void buildProperties();

  protected:
    /** Set density and strictness flags for all variables, according to
        the loop description */
    void densityAndStrictness();
    void densityAndStrictness(PVariable *v);
    bool isIncremented(GuardedCommand *gc, PVariable *v, int &incr);
  };

}
#endif
