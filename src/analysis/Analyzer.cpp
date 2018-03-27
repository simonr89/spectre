#include "Analyzer.hpp"

#include <fstream>
#include <ostream>

#include "Properties.hpp"
#include "Output.hpp"

namespace program {

  void Analyzer::densityAndStrictness()
  {
    for (auto it = _variables.begin(); it != _variables.end(); ++it) {
      densityAndStrictness((*it));
    }
  }

  void Analyzer::densityAndStrictness(const PVariable *v) {
      if (_monotonic.at(v) == Monotonicity::OTHER)
      return;

    bool strict = true, dense = true;
    int incr;
    for (auto it = _loop.commands.begin(); it != _loop.commands.end(); ++it) {
      if (isIncremented(*it, v, incr))
        dense &= (incr == 1 || incr == -1);
      else
        strict = false;
    }
    
    if (strict)
        _strict[v] = true;
    if (dense)
        _dense[v] = true;
  }

  /** helper function, return true iff v is incremented by a constant
      in the guard gc. The constant is then stored in incr */
  bool Analyzer::isIncremented(const GuardedCommand *gc, const PVariable *v, int &incr)
  {
    for (auto it = gc->assignments.begin(); it != gc->assignments.end(); ++it) {
      if ((*it)->hasLhs(*v))
        return (isScalarIncrement(*it,incr) && incr != 0);
    }
    return false;
  }

    bool Analyzer::isScalarIncrement(Assignment* a, int &incr)
    {
        if (a->lhs->varInfo()->vtype() != Type::TY_INTEGER)
            return false;
        
        incr = 0;
        return a->rhs->equivToVPlusX(a->lhs->varInfo(), incr);
    }
    
    void Analyzer::recordLhsInfo(Assignment* a)
    {
        PVariable *v = a->lhs->varInfo();
        int incr;
        if (isScalarIncrement(a,incr))
            recordScalarIncrement(v, incr);
        else
        {
            _monotonic.at(v) = Monotonicity::OTHER;
        }
        // setUpdated must be called after recordScalarIncrement
        _updated.at(v) = true;
    }
    
    void Analyzer::recordScalarIncrement(PVariable *v, int n)
    {
        if (n > 0)
        {
            if (!_updated.at(v))
                _monotonic.at(v) = Monotonicity::INC;
            else if (_monotonic.at(v) == Monotonicity::DEC)
                _monotonic.at(v) = Monotonicity::OTHER;
        }
        else if (n < 0)
        {
            if (!_updated.at(v))
                _monotonic.at(v) = Monotonicity::DEC;
            else if (_monotonic.at(v) == Monotonicity::INC)
                _monotonic.at(v) = Monotonicity::OTHER;
        }
    }
    
    AnalyzerResult Analyzer::computeVariableProperties()
    {
        // compute updated and monotonicity
        for (const auto& guardedCommandPtr : _loop.commands)
        {
            for (const auto& a : guardedCommandPtr->assignments)
            {
                recordLhsInfo(a);
            }
        }
        
        // compute density and strictness
        densityAndStrictness();
        
        return AnalyzerResult(std::move(_updated), std::move(_monotonic), std::move(_strict), std::move(_dense));
    }
}
