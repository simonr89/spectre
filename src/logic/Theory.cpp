#include "Theory.hpp"

#include <cassert>

#include "Options.hpp"

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
    
    FuncTermPtr Theory::integerConstant(int i)
    {
        Symbol *s = Signature::fetchOrDeclare(std::to_string(i), Sorts::intSort(), true);
        return Terms::funcTerm(s, {});
    }
    
    PredTermPtr Theory::booleanConstant(bool b)
    {
        Symbol *t = Signature::fetchOrDeclare("bool_true", Sorts::boolSort(), true);
        Symbol *f = Signature::fetchOrDeclare("bool_false", Sorts::boolSort(), true);

        return b ? Terms::predTerm(t, {}) : Terms::predTerm(f, {});
    }
    
    FuncTermPtr Theory::timeZero()
    {
        if (util::Configuration::instance().timepoints().getValue())
        {
            Symbol* zero = getSymbol(InterpretedSymbol::TIME_ZERO);
            return Terms::funcTerm(zero, {});
        } else {
            return integerConstant(0);
        }
        
    }
    
    FuncTermPtr Theory::timeSucc(TermPtr t)
    {
        if (util::Configuration::instance().timepoints().getValue())
        {
            return Terms::funcTerm(getSymbol(InterpretedSymbol::TIME_SUCC),
                                   {t});
        } else {
            return Terms::funcTerm(getSymbol(InterpretedSymbol::INT_PLUS),
                                   {t, Theory::integerConstant(1)});
        }
    }
    
    FuncTermPtr Theory::timePred(TermPtr t)
    {
        if (util::Configuration::instance().timepoints().getValue())
        {
            return Terms::funcTerm(getSymbol(InterpretedSymbol::TIME_PRE),
                                   {t});
        } else {
            return Terms::funcTerm(getSymbol(InterpretedSymbol::INT_MINUS),
                                   {t, Theory::integerConstant(1)});
        }
    }
    
    PredTermPtr Theory::timeLt(TermPtr t1, TermPtr t2)
    {
        Symbol* lt = (util::Configuration::instance().timepoints().getValue()
                      ? getSymbol(InterpretedSymbol::TIME_SUB)
                      : getSymbol(InterpretedSymbol::INT_LESS));
        return Terms::predTerm(lt, {t1,t2});
    }
    
}

