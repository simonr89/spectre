#include "Assignment.hpp"

namespace program
{
    bool Assignment::isScalarIncrement(int &incr)
    {
        if (lhs->varInfo()->vtype() != Type::TY_INTEGER)
            return false;
        
        incr = 0;
        return rhs->equivToVPlusX(lhs->varInfo(), incr);
    }
    
    void Assignment::recordLhsInfo() {
        PVariable *v = lhs->varInfo();
        int incr;
        if (isScalarIncrement(incr))
            v->recordScalarIncrement(incr);
        else
            v->setMonotonic(false);
        // setUpdated must be called after recordScalarIncrement
        v->setUpdated();
    }
}


