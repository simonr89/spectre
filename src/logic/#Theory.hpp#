#ifndef __Theory__
#define __Theory__

#include <string>
#include "Formula.hpp"
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
        
        static FuncTermPtr integerConstant(int i);
        static PredTermPtr booleanConstant(bool b);

        // these function might deal with integers or natural number
        // (term algebra) depending on the chosen representation of
        // timepoints
        static FuncTermPtr timeZero();
        static FuncTermPtr timeSucc(TermPtr t);
        static FuncTermPtr timePred(TermPtr t);
        static PredTermPtr timeLt(TermPtr t1, TermPtr t2);

        static FormulaPtr timeSubAxiom1();
        static FormulaPtr timeSubAxiom2();
        static FormulaPtr selectOverStoreAxiom1();
        static FormulaPtr selectOverStoreAxiom2();
    };
    
}

#endif

