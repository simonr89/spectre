#include "Expression.hpp"

#include <cassert>
#include "Sort.hpp"
#include "Theory.hpp"
#include "Options.hpp"

namespace program {
    
    Expression::~Expression() {
        delete _children;
    }
    
    Expression * Expression::child(unsigned n) const
    {
        return (n < _arity ? _children[n] : nullptr);
    }
    
    bool ArithmeticExpression::evalToCstInt(int &value)
    {
        int a, b;
        switch (_kind) {
            case ArithExprKind::EXP_CST_INTEGER:
                value = _constInfo;
                return true;
            case ArithExprKind::EXP_ADD:
                if (_children[0]->evalToCstInt(a) && _children[1]->evalToCstInt(b)) {
                    value = a + b;
                    return true;
                }
                return false;
            case ArithExprKind::EXP_SUB:
                if (_children[0]->evalToCstInt(a) && _children[1]->evalToCstInt(b)) {
                    value = a - b;
                    return true;
                }
                return false;
            case ArithExprKind::EXP_MUL:
                if (_children[0]->evalToCstInt(a) && _children[1]->evalToCstInt(b)) {
                    value = a * b;
                    return true;
                }
                return false;
            case ArithExprKind::EXP_DIV:
                if (_children[0]->evalToCstInt(a) && _children[1]->evalToCstInt(b)) {
                    value = a / b;
                    return true;
                }
                return false;
            case ArithExprKind::EXP_MINUS:
                if (_children[0]->evalToCstInt(a)) {
                    value = -a;
                    return true;
                }
                return false;
        }
        return false;
    }
    
    bool ArithmeticExpression::equivToVPlusX(const PVariable *v, int &incr) const
    {
        Expression *e1, *e2;
        int a, b;
        switch (_kind) {
            case ArithExprKind::EXP_ADD:
                e1 = _children[0];
                e2 = _children[1];
                if (e1->equivToVPlusX(v, a) && e2->evalToCstInt(b)) {
                    incr = a + b;
                    return true;
                } else if (e1->evalToCstInt(a) && e2->equivToVPlusX(v, b)) {
                    incr = a + b;
                    return true;
                }
                return false;
            case ArithExprKind::EXP_SUB:
                e1 = _children[0];
                e2 = _children[1];
                if (e1->equivToVPlusX(v, a) && e2->evalToCstInt(b)) {
                    incr = a - b;
                    return true;
                }
                return false;
            default:
                return false;
        }
    }
    
    bool LocationExpression::equivToVPlusX(const PVariable *v, int &incr) const
    {
        if (_kind == LocationExprKind::EXP_VAR_LOC && _var == v) {
            incr = 0;
            return true;
        }
        return false;
    }
    
    /**
     * Translate program expressions into Vampire terms (termlists)
     *
     * The index parameter is the index in extended expressions. If it
     * is empty, then the expression is in the non extended language (as
     * understood by the user)
     */
    std::shared_ptr<const logic::Term> ArithmeticExpression::toTerm(std::shared_ptr<const logic::Term> index) const
    {
        using namespace logic;
        
        logic::InterpretedSymbol interp;
        
        switch (_kind) {
            case ArithExprKind::EXP_CST_INTEGER:
                return Theory::integerConstant(_constInfo);
            case ArithExprKind::EXP_ADD:
                interp = InterpretedSymbol::INT_PLUS;
                break;
            case ArithExprKind::EXP_SUB:
                interp = InterpretedSymbol::INT_MINUS;
                break;
            case ArithExprKind::EXP_MUL:
                interp = InterpretedSymbol::INT_MULTIPLY;
                break;
            case ArithExprKind::EXP_DIV:
                interp = InterpretedSymbol::INT_QUOTIENT_E;
                break;
            case ArithExprKind::EXP_MINUS:
                interp = InterpretedSymbol::INT_UNARY_MINUS;
                break;
        }
        
        switch (_arity) {
            case 1: {
                return logic::Terms::funcTerm(Theory::getSymbol(interp), { _children[0]->toTerm(index) });
            }
            case 2: {
                return logic::Terms::funcTerm(Theory::getSymbol(interp), { _children[0]->toTerm(index), _children[1]->toTerm(index) });
            }
            default:
                assert(0); // unreachable
                return nullptr;
        }
    }
    
    std::shared_ptr<const logic::Term> LocationExpression::toTerm(std::shared_ptr<const logic::Term> index) const
    {
        switch (_kind) {
            case LocationExprKind::EXP_VAR_LOC:
                return _var->toTerm(index);
            case LocationExprKind::EXP_ARRAY_LOC:
                return _var->toTerm(index, _children[0]->toTerm(index));
            case LocationExprKind::EXP_FIELD_LOC:
                assert(false); // TODO: not supported yet
                break;
        }
        
        assert(0); // unreachable
        return nullptr;
    }
    
    std::shared_ptr<const logic::Term> VariableExpression::toTerm(std::shared_ptr<const logic::Term> index) const
    {
        return _var->toTerm(index);
    }
    
    std::shared_ptr<const logic::Term> BooleanExpression::toTerm(std::shared_ptr<const logic::Term> index) const
    {
        //TODO check original implementation
        //return toFormula(index);
        assert(0);
        return nullptr;
    }
    
    std::shared_ptr<const logic::Term> QuantifiedExpression::toTerm(std::shared_ptr<const logic::Term> index) const
    {
        assert(0);
        return nullptr;
    }
    
    std::shared_ptr<const logic::Formula> LocationExpression::toFormula(std::shared_ptr<const logic::Term> index) const
    {
        switch (_kind) {
            case LocationExprKind::EXP_VAR_LOC:
                return std::make_shared<logic::PredicateFormula>(logic::PredicateFormula(std::dynamic_pointer_cast<const logic::PredTerm>(_var->toTerm(index))));
            case LocationExprKind::EXP_ARRAY_LOC:
                return std::make_shared<logic::PredicateFormula>(logic::PredicateFormula(std::dynamic_pointer_cast<const logic::PredTerm>(_var->toTerm(index, _children[0]->toTerm(index)))));
            case LocationExprKind::EXP_FIELD_LOC:
                assert(false); // TODO: not supported yet
                break;
        }
        
        assert(0); // unreachable
        return nullptr;
    }
    
    std::shared_ptr<const logic::Formula> BooleanExpression::toFormula(std::shared_ptr<const logic::Term> index) const
    {
        using namespace logic;
        
        InterpretedSymbol interp;
        
        switch (_kind) {
            case BooleanExprKind::EXP_CST_BOOLEAN:
                return std::make_shared<PredicateFormula>(Theory::booleanConstant(_constInfo));
            case BooleanExprKind::EXP_NEG:
                return std::make_shared<NegationFormula>(dynamic_cast<FExpression*>(_children[0])->toFormula(index));
            case BooleanExprKind::EXP_AND:
            {
                auto conjuncts = {dynamic_cast<FExpression*>(_children[0])->toFormula(index),
                    dynamic_cast<FExpression*>(_children[1])->toFormula(index)};
                return std::make_shared<ConjunctionFormula>(conjuncts);
            }
            case BooleanExprKind::EXP_OR:
            {
                auto disjuncts = {dynamic_cast<FExpression*>(_children[0])->toFormula(index),
                    dynamic_cast<FExpression*>(_children[1])->toFormula(index)};
                return std::make_shared<DisjunctionFormula>(disjuncts);
            }
            case BooleanExprKind::EXP_EQ:
            {
                return std::make_shared<EqualityFormula>(true,
                                           _children[0]->toTerm(index),
                                           _children[1]->toTerm(index));
            }
            case BooleanExprKind::EXP_LT:
                interp = InterpretedSymbol::INT_LESS;
                break;
            case BooleanExprKind::EXP_LE:
                interp = InterpretedSymbol::INT_LESS_EQUAL;
                break;
            case BooleanExprKind::EXP_GT:
                interp = InterpretedSymbol::INT_GREATER;
                break;
            case BooleanExprKind::EXP_GE:
                interp = InterpretedSymbol::INT_GREATER_EQUAL;
                break;
        }
        if (_arity == 2)
        {
            return std::make_shared<PredicateFormula>(Terms::predTerm(Theory::getSymbol(interp),
                                                     { _children[0]->toTerm(index),
                                                         _children[1]->toTerm(index) }));
        }
        assert(0); // unreachable
        return nullptr;
    }
    
    std::shared_ptr<const logic::Formula> VariableExpression::toFormula(std::shared_ptr<const logic::Term> index) const
    {
        return std::make_shared<const logic::PredicateFormula>(std::dynamic_pointer_cast<const logic::PredTerm>(_var->toTerm(index)));
    }
    
    std::shared_ptr<const logic::Formula> QuantifiedExpression::toFormula(std::shared_ptr<const logic::Term> index) const
    {
        std::shared_ptr<const logic::Formula> f = dynamic_cast<FExpression*>(_children[0])->toFormula(index);
        auto vars = {_var->toVar()};

        assert(_kind == QuantifiedExprKind::EXP_FORALL || _kind == QuantifiedExprKind::EXP_EXISTS);
        if (_kind == QuantifiedExprKind::EXP_FORALL)
        {
            return std::make_shared<const logic::UniversalFormula>(vars, f);
        }
        else
        {
            return std::make_shared<const logic::ExistentialFormula>(vars, f);
        }
    }
    
    Type LocationExpression::etype() const {
        switch (_kind) {
            case LocationExprKind::EXP_ARRAY_LOC:
                return returnType(_var->type);
            case LocationExprKind::EXP_VAR_LOC:
                return _var->type;
            default:
                assert(0); // unreachable
                return Type::TY_INTEGER;
        }
    }
    
    /* initializers */
    ArithmeticExpression* ArithmeticExpression::mkConstantInteger(int v)
    {
        ArithmeticExpression* r = new ArithmeticExpression(ArithExprKind::EXP_CST_INTEGER);
        r->_constInfo = v;
        return r;
    }
    
    ArithmeticExpression* ArithmeticExpression::mkAdd(Expression *e1, Expression *e2)
    {
        if (e1->etype() != Type::TY_INTEGER || e2->etype() != Type::TY_INTEGER)
            return nullptr;
        ArithmeticExpression *r = new ArithmeticExpression(ArithExprKind::EXP_ADD, 2);
        r->_children[0] = e1;
        r->_children[1] = e2;
        return r;
    }
    
    ArithmeticExpression* ArithmeticExpression::mkSub(Expression *e1, Expression *e2)
    {
        if (e1->etype() != Type::TY_INTEGER || e2->etype() != Type::TY_INTEGER)
            return nullptr;
        ArithmeticExpression *r = new ArithmeticExpression(ArithExprKind::EXP_SUB, 2);
        r->_children[0] = e1;
        r->_children[1] = e2;
        return r;
        
    }
    
    ArithmeticExpression* ArithmeticExpression::mkMul(Expression* e1, Expression* e2)
    {
        if (e1->etype() != Type::TY_INTEGER || e2->etype() != Type::TY_INTEGER)
            return nullptr;
        ArithmeticExpression* r = new ArithmeticExpression(ArithExprKind::EXP_MUL, 2);
        r->_children[0] = e1;
        r->_children[1] = e2;
        return r;
    }
    
    ArithmeticExpression* ArithmeticExpression::mkDiv(Expression* e1, Expression* e2)
    {
        if (e1->etype() != Type::TY_INTEGER || e2->etype() != Type::TY_INTEGER)
            return nullptr;
        ArithmeticExpression* r = new ArithmeticExpression(ArithExprKind::EXP_DIV, 2);
        r->_children[0] = e1;
        r->_children[1] = e2;
        return r;
    }
    
    ArithmeticExpression* ArithmeticExpression::mkMinus(Expression* e)
    {
        if (e->etype() != Type::TY_INTEGER)
            return nullptr;
        ArithmeticExpression *r = new ArithmeticExpression(ArithExprKind::EXP_MINUS, 1);
        r->_children[0] = e;
        return r;
    }
    
    BooleanExpression* BooleanExpression::mkConstantBoolean(bool v)
    {
        BooleanExpression* r = new BooleanExpression(BooleanExprKind::EXP_CST_BOOLEAN);
        r->_constInfo = v;
        return r;
    }
    
    BooleanExpression* BooleanExpression::mkNegation(Expression* e)
    {
        if (e->etype() != Type::TY_BOOLEAN)
            return nullptr;
        BooleanExpression* r = new BooleanExpression(BooleanExprKind::EXP_NEG, 1);
        r->_children[0] = e;
        return r;
    }
    
    BooleanExpression* BooleanExpression::mkOr(Expression* e1, Expression* e2)
    {
        if (e1->etype() != Type::TY_BOOLEAN || e2->etype() != Type::TY_BOOLEAN)
            return nullptr;
        BooleanExpression *r = new BooleanExpression(BooleanExprKind::EXP_OR, 2);
        r->_children[0] = e1;
        r->_children[1] = e2;
        return r;
    }
    
    BooleanExpression* BooleanExpression::mkAnd(Expression* e1, Expression* e2)
    {
        if (e1->etype() != Type::TY_BOOLEAN || e2->etype() != Type::TY_BOOLEAN)
            return nullptr;
        
        if (e1->isTrue())
        {
            return dynamic_cast<BooleanExpression*>(e2);
        }
        if (e2->isTrue())
        {
            return dynamic_cast<BooleanExpression*>(e1);
        }
        if(e1->isFalse())
        {
            return dynamic_cast<BooleanExpression*>(e1);
        }
        if(e2->isFalse())
        {
            return dynamic_cast<BooleanExpression*>(e2);
        }
        BooleanExpression* r = new BooleanExpression(BooleanExprKind::EXP_AND, 2);
        r->_children[0] = e1;
        r->_children[1] = e2;
        return r;
    }
    
    BooleanExpression* BooleanExpression::mkGe(Expression* e1, Expression* e2)
    {
        if (e1->etype() != Type::TY_INTEGER || e2->etype() != Type::TY_INTEGER)
            return nullptr;
        BooleanExpression* r = new BooleanExpression(BooleanExprKind::EXP_GE, 2);
        r->_children[0] = e1;
        r->_children[1] = e2;
        return r;
    }
    
    BooleanExpression* BooleanExpression::mkGt(Expression *e1, Expression *e2)
    {
        if (e1->etype() != Type::TY_INTEGER || e2->etype() != Type::TY_INTEGER)
            return nullptr;
        BooleanExpression *r = new BooleanExpression(BooleanExprKind::EXP_GT, 2);
        r->_children[0] = e1;
        r->_children[1] = e2;
        return r;
    }
    
    BooleanExpression* BooleanExpression::mkLe(Expression* e1, Expression* e2)
    {
        if (e1->etype() != Type::TY_INTEGER || e2->etype() != Type::TY_INTEGER)
            return nullptr;
        BooleanExpression* r = new BooleanExpression(BooleanExprKind::EXP_LE, 2);
        r->_children[0] = e1;
        r->_children[1] = e2;
        return r;
    }
    
    BooleanExpression* BooleanExpression::mkLt(Expression* e1, Expression* e2)
    {
        if (e1->etype() != Type::TY_INTEGER || e2->etype() != Type::TY_INTEGER)
            return nullptr;
        BooleanExpression* r = new BooleanExpression(BooleanExprKind::EXP_LT, 2);
        r->_children[0] = e1;
        r->_children[1] = e2;
        return r;
    }
    
    BooleanExpression* BooleanExpression::mkEq(Expression* e1, Expression* e2)
    {
        if (e1->etype() != Type::TY_INTEGER || e2->etype() != Type::TY_INTEGER)
            return nullptr;
        BooleanExpression* r = new BooleanExpression(BooleanExprKind::EXP_EQ, 2);
        r->_children[0] = e1;
        r->_children[1] = e2;
        return r;
    }
    
    BooleanExpression* BooleanExpression::mkNeq(Expression* e1, Expression* e2)
    {
        BooleanExpression *e = mkEq(e1, e2);
        if (!e)
            return nullptr;
        return mkNegation(e);
    }
    
    BooleanExpression* BooleanExpression::mkImplication(Expression* e1, Expression* e2)
    {
        BooleanExpression* ne1 = mkNegation(e1);
        if (!ne1 || e2->etype() != Type::TY_BOOLEAN)
            return nullptr;
        return mkOr(ne1, e2);
    }
    
    LocationExpression* LocationExpression::mkArrayApp(PVariable* v, Expression* e)
    {
        if (!isArrayType(v->type) || e->etype() != Type::TY_INTEGER)
            return nullptr;
        LocationExpression* r = new LocationExpression(LocationExprKind::EXP_ARRAY_LOC, v, 1);
        r->_children[0] = e;
        return r;
    }
    
    LocationExpression* LocationExpression::mkProgramVariable(PVariable* v)
    {
        return new LocationExpression(LocationExprKind::EXP_VAR_LOC, v);
    }
    
    VariableExpression* VariableExpression::mkQuantifiedVariable(QVariable* v)
    {
        return new VariableExpression(v);
    }
    
    QuantifiedExpression* QuantifiedExpression::mkForall(QVariable *v, Expression *e)
    {
        if (e->etype() != Type::TY_BOOLEAN && e->etype() != Type::TY_FORMULA)
            return nullptr;
        QuantifiedExpression* r = new QuantifiedExpression(QuantifiedExprKind::EXP_FORALL);
        r->_var = v;
        r->_children[0] = e;
        return r;
    }
    
    QuantifiedExpression* QuantifiedExpression::mkExists(QVariable* v, Expression* e)
    {
        if (e->etype() != Type::TY_BOOLEAN && e->etype() != Type::TY_FORMULA)
            return nullptr;
        QuantifiedExpression* r = new QuantifiedExpression(QuantifiedExprKind::EXP_EXISTS);
        r->_var = v;
        r->_children[0] = e;
        return r;
    }
    
    // pretty printer
    std::ostream& ArithmeticExpression::toStream(std::ostream& ostr) const
    {
        switch (_kind) {
            case ArithExprKind::EXP_CST_INTEGER:
                ostr << _constInfo;
                break;
            case ArithExprKind::EXP_ADD:
                ostr << "(" << *_children[0] << " + " << *_children[1] << ")";
                break;
            case ArithExprKind::EXP_SUB:
                ostr << "(" << *_children[0] << " - " << *_children[1] << ")";
                break;
            case ArithExprKind::EXP_MUL:
                ostr << "(" << *_children[0] << " * " << *_children[1] << ")";
                break;
            case ArithExprKind::EXP_DIV:
                ostr << "(" << *_children[0] << " / " << *_children[1] << ")";
                break;
            case ArithExprKind::EXP_MINUS:
                ostr << "-(" << *_children[0] << ")";
                break;
        }
        return ostr;
    }
    
    std::ostream& BooleanExpression::toStream(std::ostream& ostr) const
    {
        switch (_kind) {
            case BooleanExprKind::EXP_CST_BOOLEAN:
                ostr << std::boolalpha << _constInfo;
                break;
            case BooleanExprKind::EXP_NEG:
                ostr << "!" << *_children[0] ;
                break;
            case BooleanExprKind::EXP_OR:
                ostr << "(" << *_children[0] << " | " << *_children[1] << ")";
                break;
            case BooleanExprKind::EXP_AND:
                ostr << "(" << *_children[0] << " & " << *_children[1] << ")";
                break;
            case BooleanExprKind::EXP_GE:
                ostr << "(" << *_children[0] << " >= " << *_children[1] << ")";
                break;
            case BooleanExprKind::EXP_GT:
                ostr << "(" << *_children[0] << " > " << *_children[1] << ")";
                break;
            case BooleanExprKind::EXP_LE:
                ostr << "(" << *_children[0] << " <= " << *_children[1] << ")";
                break;
            case BooleanExprKind::EXP_LT:
                ostr << "(" << *_children[0] << " < " << *_children[1] << ")";
                break;
            case BooleanExprKind::EXP_EQ:
                ostr << "(" << *_children[0] << " == " << *_children[1] << ")";
                break;
        }
        return ostr;
    }
    
    std::ostream& LocationExpression::toStream(std::ostream& ostr) const
    {
        switch (_kind) {
            case LocationExprKind::EXP_ARRAY_LOC:
                ostr << _var->name << "[" << *_children[0] << "]";
                break;
            case LocationExprKind::EXP_VAR_LOC:
                ostr << _var->name;
                break;
            case LocationExprKind::EXP_FIELD_LOC:
                assert(false); // TODO: not supported yet
                break;
        }
        return ostr;
    }
    
    std::ostream& VariableExpression::toStream(std::ostream& ostr) const
    {
        ostr << _var->name;
        return ostr;
    }
    
    std::ostream& QuantifiedExpression::toStream(std::ostream& ostr) const
    {
        switch (_kind) {
            case QuantifiedExprKind::EXP_FORALL:
                ostr << "forall ";
                break;
            case QuantifiedExprKind::EXP_EXISTS:
                ostr << "exists ";
                break;
        }
        ostr << _var->type << " " << _var->name << ", " << *_children[0];
        return ostr;
    }
}

