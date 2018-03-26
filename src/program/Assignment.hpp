#ifndef __Assignment__
#define __Assignment__

#include "Expression.hpp"

namespace program
{
    class Assignment {
    public:
        
        Assignment(LocationExpression* lhs, Expression* rhs) : lhs(lhs), rhs(rhs)
        {
            recordLhsInfo();
        }
 
        /** Modifies the information associated with the lhs
         variable*/
        void recordLhsInfo();
        
        bool hasLhs(const PVariable &v) { return lhs->varInfo() == &v; }
        
        /**
         * True iff the assignment has the form x = x + c, where x is an
         * integer variable and c an integer constant, c is then copied to
         * incr
         */
        bool isScalarIncrement(int &incr);
        
        friend std::ostream& operator<<(std::ostream&, const Assignment&);
        
        const LocationExpression* lhs;
        const Expression* rhs;
    };
}



#endif
