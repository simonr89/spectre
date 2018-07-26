#ifndef __Assignment__
#define __Assignment__

#include "Expression.hpp"
#include "Formula.hpp"

namespace program
{
    class Assignment {
    public:
        
        Assignment(LocationExpression* lhs, Expression* rhs) : lhs(lhs), rhs(rhs){}
        
        const LocationExpression* lhs;
        const Expression* rhs;
       
        bool hasLhs(const PVariable &v) const { return lhs->varInfo() == &v; }
                
        logic::FormulaPtr weakestPrecondition(logic::FormulaPtr f) const;
    };
}



#endif
