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
                return Signature::fetchOrDeclare("$array_select", { Sorts::intArraySort(), Sorts::intSort() }, Sorts::intSort(), false);
            case InterpretedSymbol::ARRAY_STORE:
                return Signature::fetchOrDeclare("$array_store", { Sorts::intArraySort(), Sorts::intSort(), Sorts::intSort() }, Sorts::intArraySort(), false);
            case InterpretedSymbol::TIME_ZERO:
                return Signature::fetchOrDeclare("time_zero", Sorts::timeSort(), true);
            case InterpretedSymbol::TIME_SUCC:
                return Signature::fetchOrDeclare("time_succ", {Sorts::timeSort()}, Sorts::timeSort(), true);
            case InterpretedSymbol::TIME_PRE:
                return Signature::fetchOrDeclare("time_pre", {Sorts::timeSort()}, Sorts::timeSort(), true);
            case InterpretedSymbol::TIME_SUB:
                return Signature::fetchOrDeclare("time_sub", {Sorts::timeSort(), Sorts::timeSort()}, Sorts::boolSort(), false);
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

    // forall i, sub(i, s(i))
    FormulaPtr Theory::timeSubAxiom1()
    {
        assert(util::Configuration::instance().timepoints().getValue());
        
        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It");
        
        return Formulas::universalFormula({i}, Formulas::predicateFormula(timeLt(i, timeSucc(i))));
    }

    // forall i j, sub(i, j) -> sub(i, s(j))
    FormulaPtr Theory::timeSubAxiom2()
    {
        assert(util::Configuration::instance().timepoints().getValue());
        
        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It1");
        LVariablePtr j = Terms::lVariable(Sorts::timeSort(), "It2");
        
        return Formulas::universalFormula({i, j},
                                          Formulas::implicationFormula(Formulas::predicateFormula(timeLt(i, j)),
                                                                       Formulas::predicateFormula(timeLt(i, timeSucc(j)))));
    }

    // forall a, p, v, select(store(a,p,v), p) = v
    FormulaPtr Theory::selectOverStoreAxiom1()
    {
        LVariablePtr a = Terms::lVariable(Sorts::intArraySort(), "A");
        LVariablePtr p = Terms::lVariable(Sorts::intSort(), "P");
        LVariablePtr v = Terms::lVariable(Sorts::intSort(), "V");
        
        FuncTermPtr s = Terms::funcTerm(getSymbol(InterpretedSymbol::ARRAY_STORE),
                                        {a, p, v});
        FuncTermPtr t = Terms::funcTerm(getSymbol(InterpretedSymbol::ARRAY_SELECT),
                                        {s, p});
        
        return Formulas::universalFormula({a, p, v},
                                          Formulas::equalityFormula(true, t, v));
    }

    // forall a, p1, p2 v, p1 != p2 -> select(store(a,p2,v), p1) = select(a, p1)
    FormulaPtr Theory::selectOverStoreAxiom2()
    {
        LVariablePtr a = Terms::lVariable(Sorts::intArraySort(), "A");
        LVariablePtr p1 = Terms::lVariable(Sorts::intSort(), "P1");
        LVariablePtr p2 = Terms::lVariable(Sorts::intSort(), "P2");
        LVariablePtr v = Terms::lVariable(Sorts::intSort(), "V");
        
        FuncTermPtr s = Terms::funcTerm(getSymbol(InterpretedSymbol::ARRAY_STORE),
                                        {a, p2, v});
        FuncTermPtr t = Terms::funcTerm(getSymbol(InterpretedSymbol::ARRAY_SELECT),
                                        {s, p1});
        FuncTermPtr u = Terms::funcTerm(getSymbol(InterpretedSymbol::ARRAY_SELECT),
                                        {a, p1});
        
        return Formulas::universalFormula({a, p1, p2, v},
                                          Formulas::implicationFormula(Formulas::equalityFormula(false, p1, p2),
                                                                       Formulas::equalityFormula(true, t, u)));
    }
}

