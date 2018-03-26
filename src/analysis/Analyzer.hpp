
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

    Analyzer() :
      _preconditions(),
      _postconditions()
    {}
  
    ~Analyzer() {}

    void buildProperties(GuardedCommandCollection &c);

    void addPrecondition(FExpression *e) { _preconditions.push_back(e); }
    void addPostcondition(FExpression *e) { _postconditions.push_back(e); }
      void setVariables(std::map<std::string, PVariable*>& variables) {_variables = variables;}

  protected:
    /** symbol table */
    std::map<std::string, PVariable*> _variables;

    std::vector<FExpression*> _preconditions;
    std::vector<FExpression*> _postconditions;

    /** Set density and strictness flags for all variables, according to
        the loop description */
    void densityAndStrictness(GuardedCommandCollection &c);
    void densityAndStrictness(GuardedCommandCollection &c, PVariable *v);
    bool isIncremented(GuardedCommand *gc, PVariable *v, int &incr);
  };

}
#endif