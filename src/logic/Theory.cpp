#include "Theory.hpp"

#include <cassert>

namespace logic {
    
    Symbol* Theory::getSymbol(InterpretedSymbol s) {
        switch (s) {
            case InterpretedSymbol::INT_PLUS:
                return Signature::fetchOrDeclare("int_plus", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
            case InterpretedSymbol::INT_MINUS:
                return Signature::fetchOrDeclare("int_minus", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
            case InterpretedSymbol::INT_MULTIPLY:
                return Signature::fetchOrDeclare("int_multiply", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
            case InterpretedSymbol::INT_QUOTIENT_E:
                return Signature::fetchOrDeclare("int_quotient_e", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
            case InterpretedSymbol::INT_UNARY_MINUS:
                return Signature::fetchOrDeclare("int_unary_minus", { Sorts::intSort() } , Sorts::intSort(), true);
            case InterpretedSymbol::INT_GREATER:
                return Signature::fetchOrDeclare("int_greater", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
            case InterpretedSymbol::INT_GREATER_EQUAL:
                return Signature::fetchOrDeclare("int_greater_eq", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
            case InterpretedSymbol::INT_LESS:
                return Signature::fetchOrDeclare("int_less", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
            case InterpretedSymbol::INT_LESS_EQUAL:
                return Signature::fetchOrDeclare("int_less_eq", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
            case InterpretedSymbol::ARRAY_SELECT:
                return Signature::fetchOrDeclare("array_select", { Sorts::intArraySort(), Sorts::intSort() }, Sorts::intSort(), true);
            case InterpretedSymbol::ARRAY_STORE:
                return Signature::fetchOrDeclare("array_store", { Sorts::intArraySort(), Sorts::intSort(), Sorts::intSort() }, Sorts::intArraySort(), true);
            case InterpretedSymbol::TIME_ZERO:
                return Signature::fetchOrDeclare("time_zero", Sorts::timeSort(), true, true);
            case InterpretedSymbol::TIME_SUCC:
                return Signature::fetchOrDeclare("time_succ", {Sorts::timeSort()}, Sorts::timeSort(), true, true);
            case InterpretedSymbol::TIME_PRE:
                return Signature::fetchOrDeclare("time_pre", {Sorts::timeSort()}, Sorts::timeSort(), true, true);
            case InterpretedSymbol::TIME_SUB:
                return Signature::fetchOrDeclare("time_sub", {Sorts::timeSort(), Sorts::timeSort()}, Sorts::boolSort(), true, true);
            default:
                assert(0); //unreachable
                return nullptr;
        }
    }
    
    std::shared_ptr<const FuncTerm> Theory::integerConstant(int i)
    {
        Symbol *s = Signature::fetchOrDeclare(std::to_string(i), Sorts::intSort(), true);
        return Terms::funcTerm(s, {});
    }
    
    std::shared_ptr<const PredTerm> Theory::booleanConstant(bool b)
    {
        Symbol *t = Signature::fetchOrDeclare("bool_true", Sorts::boolSort(), true);
        Symbol *f = Signature::fetchOrDeclare("bool_false", Sorts::boolSort(), true);

        return b ? Terms::predTerm(t, {}) : Terms::predTerm(f, {});
    }
    
    std::shared_ptr<const FuncTerm> Theory::timeZero()
    {
        Symbol* zero = getSymbol(InterpretedSymbol::TIME_ZERO);
        return Terms::funcTerm(zero, {});
    }
    
    std::shared_ptr<const FuncTerm> Theory::timeSucc(std::shared_ptr<const Term> term)
    {
        Symbol* succ = getSymbol(InterpretedSymbol::TIME_SUCC);
        return Terms::funcTerm(succ, {term});
    }
    
    std::shared_ptr<const FuncTerm> Theory::timePre(std::shared_ptr<const Term> term)
    {
        Symbol* pre = getSymbol(InterpretedSymbol::TIME_PRE);
        return Terms::funcTerm(pre, {term});
    }
    
    std::shared_ptr<const PredTerm> Theory::timeSub(std::shared_ptr<const Term> t1, std::shared_ptr<const Term> t2)
    {
        Symbol* sub = getSymbol(InterpretedSymbol::TIME_SUB);
        return Terms::predTerm(sub, {t1,t2});
    }
    
}

