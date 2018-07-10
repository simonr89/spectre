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
        
        static std::shared_ptr<const FuncTerm> integerConstant(int i);
        static std::shared_ptr<const PredTerm> booleanConstant(bool b);
        
        static std::shared_ptr<const FuncTerm> timeZero();
        static std::shared_ptr<const FuncTerm> timeSucc(std::shared_ptr<const Term>);
        static std::shared_ptr<const FuncTerm> timePre(std::shared_ptr<const Term>);
        static std::shared_ptr<const PredTerm> timeSub(std::shared_ptr<const Term>, std::shared_ptr<const Term>);
    };
    
}

#endif

