#ifndef __Assignment__
#define __Assignment__

#include "Expression.hpp"

namespace program
{
    class Assignment {
    public:
        
        Assignment(LocationExpression *lhs, Expression *rhs) :
        _lhs(lhs),
        _rhs(rhs)
        {}
        ~Assignment() {}
        
        LocationExpression *lhs() { return _lhs; }
        Expression *rhs() { return _rhs; }
        
        bool hasLhs(const PVariable &v) { return _lhs->varInfo() == &v; }
        
        /**
         * True iff the assignment has the form x = x + c, where x is an
         * integer variable and c an integer constant, c is then copied to
         * incr
         */
        bool isScalarIncrement(int &incr);
        
        /** Modifies the information associated with the lhs
         variable. Should be executed immediately after the
         constructor */
        void recordLhsInfo();
        
        friend std::ostream& operator<<(std::ostream&, const Assignment&);
        
    protected:
        LocationExpression *_lhs;
        Expression *_rhs;
        
        bool isScalarIncrement(Expression *e, PVariable *v, int &incr);
    };
}



#endif
