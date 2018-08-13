#include "Analyzer.hpp"

#include <fstream>
#include <ostream>

#include "Properties.hpp"
#include "Output.hpp"

namespace program {

    void Analyzer::densityAndStrictness(const Program& p)
    {
        for (auto v : p.loop->variables)
        {
            densityAndStrictness(p, v);
        }
    }

    void Analyzer::densityAndStrictness(const Program& p, PVariable *v) {
        if (v->monotonicity() == Monotonicity::OTHER)
        {
            return;
        }

        bool strict = true, dense = true;
        int incr;
        for (auto c : p.loop->commands)
        {
            if (isIncremented(c, v, incr))
                dense &= (incr == 1 || incr == -1);
            else
                strict = false;
        }
    
        if (strict)
        {
            v->markStrictMonotonic();
        }
        if (dense)
        {
            v->markDense();
        }
    }

    /** helper function, return true iff v is incremented by a constant
        in the guard gc. The constant is then stored in incr */
    bool Analyzer::isIncremented(const GuardedCommand *gc, const PVariable *v, int &incr)
    {
        for (auto asg : gc->assignments)
        {
            if (asg->hasLhs(*v))
            {
                return (isScalarIncrement(asg,incr) && incr != 0);
            }
        }
        return false;
    }

    bool Analyzer::isScalarIncrement(Assignment* a, int &incr)
    {
        if (a->lhs->varInfo()->type != Type::TY_INTEGER)
        {
            return false;
        }
        
        incr = 0;
        return a->rhs->equivToVPlusX(a->lhs->varInfo(), incr);
    }
    
    void Analyzer::recordLhsInfo(Assignment* a)
    {
        PVariable *v = a->lhs->varInfo();
        int incr;
        if (isScalarIncrement(a,incr))
        {
            recordScalarIncrement(v, incr);
        }
        else
        {
            v->setMonotonicity(Monotonicity::OTHER);
        }
        // setUpdated must be called after recordScalarIncrement
        v->markUpdated();
    }
    
    void Analyzer::recordScalarIncrement(PVariable *v, int n)
    {
        if (n > 0)
        {
            if (!v->isUpdated())
            {
                v->setMonotonicity(Monotonicity::INC);
            }
            else if (v->monotonicity() == Monotonicity::DEC)
            {
                v->setMonotonicity(Monotonicity::OTHER);
            }
        }
        else if (n < 0)
        {
            if (!v->isUpdated())
            {
                v->setMonotonicity(Monotonicity::DEC);
            }
            else if (v->monotonicity() == Monotonicity::INC)
            {
                v->setMonotonicity(Monotonicity::OTHER);
            }
        }
    }
    
    void Analyzer::computeVariableProperties(const Program& p)
    {
        // compute updated and monotonicity
        for (const auto& guardedCommandPtr : p.loop->commands)
        {
            for (const auto& a : guardedCommandPtr->assignments)
            {
                recordLhsInfo(a);
            }
        }
        
        // compute density and strictness
        densityAndStrictness(p);
    }
}
