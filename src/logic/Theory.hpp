#ifndef __Theory__
#define __Theory__

#include <string>
#include "Term.hpp"

namespace logic {
    
    enum class InterpretedSymbol {
        INT_PLUS,
        INT_MINUS,
        INT_MULTIPLY,
        INT_QUOTIENT_E,
        INT_UNARY_MINUS,
        
        INT_GREATER,
        INT_GREATER_EQUAL,
        INT_LESS,
        INT_LESS_EQUAL,
        
        ARRAY_SELECT,
        ARRAY_STORE,
        
        TIME_ZERO,  // timepoint 0
        TIME_SUCC,  // successor of timepoint
        TIME_PRE,  // predecessor of timepoint
        TIME_SUB   // subterm relation between timepoints
    };
    
    class Theory {
    public:
        
        static Symbol* getSymbol(InterpretedSymbol s);
        
        static FuncTerm* integerConstant(int i);
        
        static PredTerm* booleanConstant(bool b);
        
        static FuncTerm* timeZero();
        static FuncTerm* timeSucc(Term* term);
        static FuncTerm* timePre(Term* term);
        static PredTerm* timeSub(Term* t1, Term* t2);
    };
    
}

#endif

