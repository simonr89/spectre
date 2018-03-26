#ifndef __Assignment__
#define __Assignment__

#include "Expression.hpp"

namespace program
{
    class Assignment {
    public:
        
        Assignment(LocationExpression* lhs, Expression* rhs) : lhs(lhs), rhs(rhs){}
        
        bool hasLhs(const PVariable &v) { return lhs->varInfo() == &v; }
                
        friend std::ostream& operator<<(std::ostream&, const Assignment&);
        
        const LocationExpression* lhs;
        const Expression* rhs;
    };
}



#endif
