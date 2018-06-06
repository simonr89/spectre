#include "Theory.hpp"

#include <cassert>

namespace logic {
    
    Symbol* Theory::getSymbol(InterpretedSymbol s) {
        switch (s) {
            case InterpretedSymbol::INT_PLUS:
                static Symbol plus("int_plus", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
                return &plus;
            case InterpretedSymbol::INT_MINUS:
                static Symbol minus("int_minus", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
                return &minus;
            case InterpretedSymbol::INT_MULTIPLY:
                static Symbol times("int_multiply", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
                return &times;
            case InterpretedSymbol::INT_QUOTIENT_E:
                static Symbol divide("int_quotient_e", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
                return &divide;
            case InterpretedSymbol::INT_UNARY_MINUS:
                static Symbol uminus("int_unary_minus", { Sorts::intSort() } , Sorts::intSort(), true);
                return &uminus;
            case InterpretedSymbol::INT_GREATER:
                static Symbol greater("int_greater", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
                return &greater;
            case InterpretedSymbol::INT_GREATER_EQUAL:
                static Symbol greatereq("int_greater_eq", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
                return &greatereq;
            case InterpretedSymbol::INT_LESS:
                static Symbol less("int_less", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
                return &less;
            case InterpretedSymbol::INT_LESS_EQUAL:
                static Symbol lesseq("int_less_eq", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
                return &lesseq;
            case InterpretedSymbol::ARRAY_SELECT:
                static Symbol select("array_select", { Sorts::intArraySort(), Sorts::intSort() }, Sorts::intSort(), true);
                return &select;
            case InterpretedSymbol::ARRAY_STORE:
                static Symbol store("array_store", { Sorts::intArraySort(), Sorts::intSort(), Sorts::intSort() }, Sorts::intArraySort(), true);
                return &store;
            case InterpretedSymbol::TIME_ZERO:
                static Symbol zero("time_zero", Sorts::timeSort(), true, true);
                return &zero;
            case InterpretedSymbol::TIME_SUCC:
                static Symbol succ("time_succ", {Sorts::timeSort()}, Sorts::timeSort(), true, true);
                return &succ;
            case InterpretedSymbol::TIME_PRE:
                static Symbol pred("time_pre", {Sorts::timeSort()}, Sorts::timeSort(), true, true);
                return &pred;
            case InterpretedSymbol::TIME_SUB:
                static Symbol sub("time_sub", {Sorts::timeSort(), Sorts::timeSort()}, Sorts::boolSort(), true, true);
                return &sub;
            default:
                assert(0); //unreachable
                return nullptr;
        }
    }
    
    FuncTerm* Theory::integerConstant(int i) {
        Symbol *s = new Symbol(std::to_string(i), Sorts::intSort(), true);
        return new FuncTerm(s, {});
    }
    
    PredTerm* Theory::booleanConstant(bool b) {
        static Symbol t("bool_true", Sorts::boolSort(), true);
        static Symbol f("bool_false", Sorts::boolSort(), true);
        return b ? new PredTerm(&t, {}) : new PredTerm(&f, {});
    }
    
    FuncTerm* Theory::timeZero()
    {
        Symbol* zero = getSymbol(InterpretedSymbol::TIME_ZERO);
        return new FuncTerm(zero, {});
    }
    
    FuncTerm* Theory::timeSucc(Term* term)
    {
        Symbol* succ = getSymbol(InterpretedSymbol::TIME_SUCC);
        return new FuncTerm(succ, {term});
    }
    
    FuncTerm* Theory::timePre(Term* term)
    {
        Symbol* pre = getSymbol(InterpretedSymbol::TIME_SUCC);
        return new FuncTerm(pre, {term});
    }
    
    PredTerm* Theory::timeSub(Term* t1, Term* t2)
    {
        Symbol* sub = getSymbol(InterpretedSymbol::TIME_SUB);
        return new PredTerm(sub, {t1,t2});
    }
    
}

