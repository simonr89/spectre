#include "PropertiesTime.hpp"

#include <cassert>
#include <iostream>

#include "Signature.hpp"
#include "Theory.hpp"
#include "Options.hpp"
#include "Output.hpp"

using namespace logic;

namespace program {
    
#pragma mark - High level methods
    
    void PropertiesTime::analyze()
    {
        assert(!util::Configuration::instance().arrayTheory().getValue()); // not supported yet
        
        constnessProps();
        monotonicityProps();
        translateAssignments();
        updatePredicatesOfArrays();
        loopConditionHypothesis();
        // if in the verification mode, add loop exit property to properties
        if (util::Configuration::instance().mainMode().getValue() == "verification")
        {
            std::shared_ptr<const Formula> f = _loop.loopCondition->toFormula(loopCounterSymbol());
            addProperty("loop_exit", Formulas::negationFormula(f));
        }
        
        if (util::Configuration::instance().mainMode().getValue() == "generation") {
            symbolEliminationAxioms();
        }
    }
    
    void PropertiesTime::output()
    {
        assert(util::Configuration::instance().outputFormat().getValue() == "smtlib"); // since we need features which are not provided by TPTP
        
        std::ostream& ostr = util::Output::stream();
        
        // output sort declarations
        for(const auto& pair : Sorts::nameToSort())
        {
                ostr << declareSortSMTLIB(*pair.second);
        }
        
        // output symbol definitions
        for (const auto& symbol : Signature::signature())
        {
            ostr << symbol->declareSymbolSMTLIB();
        }
        
        // if in generation-mode, also output symbol colors
        if (util::Configuration::instance().mainMode().getValue() == "generation")
        {
            for (const auto& symbol : Signature::signature())
            {
                if (symbol->colored)
                {
                    ostr << symbol->declareSymbolColorSMTLIB();
                }
            }
        }
        
        // output preconditions (at loop iteration 0)
        int i=0;
        for (const auto& precondition : _preconditions)
        {
            ostr << precondition->toFormula(Theory::timeZero())->declareSMTLIB("precondition_" + std::to_string(i++)) << std::endl;
        }
        
        // output all properties
        for (auto it = _properties.begin(); it != _properties.end(); ++it)
        {
            Property p = *it;
            ostr << p.second->declareSMTLIB(p.first) << std::endl;
        }
        
        // if in verification mode,
        if (util::Configuration::instance().mainMode().getValue() == "verification")
        {
            // conjoin post-conditions to conjecture
            std::vector<std::shared_ptr<const Formula>>conjuncts;
            for (const auto& postcondition : _postconditions)
            {
                conjuncts.push_back(postcondition->toFormula(loopCounterSymbol()));
            }
            auto conjecture = Formulas::conjunctionFormula(conjuncts);
            
            // output conjecture
            ostr << conjecture->declareSMTLIB("post_conditions", true) << std::endl;
        }
    }
    
    
#pragma mark - General Properties
    
    void PropertiesTime::constnessProps()
    {
        for (const auto& var : _vars)
        {
            if (!_updated.at(var))
            {
                auto it = Terms::lVariable(Sorts::timeSort(), "It");
                
                std::shared_ptr<const Formula> eq;
                // eq(it) := x(it) = x(0)
                if (!isArrayType(var->type))
                {
                    Symbol* var0Symbol = Signature::fetchOrDeclare(var->name+"0", toSort(var->type));
                    auto var0 = Terms::funcTerm(var0Symbol, {});
                    
                    eq = Formulas::equalityFormula(true,
                                             var->toTerm(it),
                                             var0);
                }
                // eq(i) := forall p. x(i,p) = x(0,p)
                else
                {
                    // suppport for other options not implemented yet
                    assert(!util::Configuration::instance().arrayTheory().getValue());
                    
                    auto p = Terms::lVariable(Sorts::intSort(), "P");
                    
                    Symbol* var0Symbol = Signature::fetchOrDeclare(var->name+"0", { Sorts::intSort() }, toSort(var->type));
                    auto var0 = Terms::funcTerm(var0Symbol, {p});
                    
                    auto eqWithoutQuantifiers = Formulas::equalityFormula(true,
                                                                        var->toTerm(it, p),
                                                                        var0);
                    eq = Formulas::universalFormula({p}, eqWithoutQuantifiers);
                }
                
                // forall i. eq(i)
                auto f = Formulas::universalFormula({it}, eq);
                
                // add property
                addProperty("not_updated_" + var->name, f);
            }
        }
    }
    
    std::shared_ptr<const FuncTerm> PropertiesTime::loopCounterSymbol()
    {
        // initialization note that the syntax of the guarded command
        // language does not allow special characters such as $
        Symbol* s = Signature::fetchOrDeclare("$n", Sorts::timeSort(), false, true);
        return Terms::funcTerm(s, {});
    }
    
    // iter(i) := i < n
    // we use i < n instead of 0 <= i < n, since for our term algebra, 0 <= i for any i.
    std::shared_ptr<const Formula> PropertiesTime::iter(std::shared_ptr<const Term> i)
    {
        return Formulas::predicateFormula(Theory::timeSub(i, loopCounterSymbol()));
    }
    
#pragma mark - Monotonicity Properties
    
    /*
     * Monotonicity propreties
     */
    void PropertiesTime::monotonicityProps()
    {
        for (auto it = _vars.begin(); it != _vars.end(); ++it)
        {
            const PVariable *v = (*it);
            if(_monotonic.at(v) == Monotonicity::OTHER)
                continue;
            
            addProperty("update_" + v->name, updatePropertyOfVar(v));

            if (_strict.at(v))
            {
                addProperty("injectivity_" + v->name, injectivityProp(v));
                addProperty("strict_" + v->name, strictProp(v));
            }
            else
            {
                addProperty("non_strict_" + v->name, nonStrictProp(v));
            }
        }
    }
    
    /** forall i j. (i != j => v(i) != v(j) ) */
    std::shared_ptr<const logic::Formula> PropertiesTime::injectivityProp(const PVariable *v)
    {
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(_updated.at(v));
        assert(_strict.at(v));
        
        auto i = Terms::lVariable(Sorts::timeSort(), "It1");
        auto j = Terms::lVariable(Sorts::timeSort(), "It2");
        
        auto imp = Formulas::implicationFormula(Formulas::equalityFormula(false, i, j),
                               Formulas::equalityFormula(false, v->toTerm(i), v->toTerm(j)));
        return Formulas::universalFormula({i,j}, imp);
    }
    
    /** forall i j. (i < j => v(i) < v(j)) [v(j) < v(i) if v is decreasing] */
    std::shared_ptr<const logic::Formula> PropertiesTime::strictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(_strict.at(v));
        
        auto i = Terms::lVariable(Sorts::timeSort(), "It1");
        auto j = Terms::lVariable(Sorts::timeSort(), "It2");
        
        if (_monotonic.at(v) == Monotonicity::INC)
        {

            auto imp = Formulas::implicationFormula(Formulas::predicateFormula(Theory::timeSub(i, j)),
                                                    Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_LESS),{ v->toTerm(i), v->toTerm(j) })));
            return Formulas::universalFormula({i,j}, imp);
        }
        else
        {
            auto imp = Formulas::implicationFormula(Formulas::predicateFormula(Theory::timeSub(i, j)),
                                                    Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_LESS),{ v->toTerm(j), v->toTerm(i) })));
            return Formulas::universalFormula({i,j}, imp);
        }
    }
    
    /** forall i j. (i<j => v(i)<=v(j)) [v(j)<=v(i) if v is decreasing] */
    std::shared_ptr<const logic::Formula> PropertiesTime::nonStrictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(!_strict.at(v));
        
        auto i = Terms::lVariable(Sorts::timeSort(), "It1");
        auto j = Terms::lVariable(Sorts::timeSort(), "It2");
        
        if (_monotonic.at(v) == Monotonicity::INC)
        {
            auto imp = Formulas::implicationFormula(Formulas::predicateFormula(Theory::timeSub(i, j)),
                                                    Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_LESS_EQUAL),{ v->toTerm(i), v->toTerm(j) })));
            return Formulas::universalFormula({i,j}, imp);
        }
        else
        {
            auto imp = Formulas::implicationFormula(Formulas::predicateFormula(Theory::timeSub(i, j)),
                                                    Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_LESS_EQUAL),{ v->toTerm(j), v->toTerm(i) })));
            return Formulas::universalFormula({i,j}, imp);
        }
    }
    
    /*
     * Update properties of guarded assignments
     */
    
    /** This property indicates that if a monotonic variable has been
     *  modified, then there exists a program point at which conditions
     *  for this change have been enabled.
     *
     *  forall x, (x >= v(0) & v(n) > x => exists i, DISJ(u) (G_u(i) & pred))
     *  where if v is dense pred <=> v(i) = x
     *  and otherwise       pred <=> x >= v(i) & v(s(i)) > x [resp. <=, < if decreasing]
     */
    std::shared_ptr<const logic::Formula> PropertiesTime::updatePropertyOfVar(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        
        auto x = Terms::lVariable(Sorts::intSort(), "X");
        auto i = Terms::lVariable(Sorts::timeSort(), "It");
        auto succOfI = Theory::timeSucc(i);
        
        InterpretedSymbol geOrLe = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER_EQUAL
                                    : InterpretedSymbol::INT_LESS_EQUAL);
        InterpretedSymbol gtOrLt = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER
                                    : InterpretedSymbol::INT_LESS);
        
        // build the disjunction
        std::vector<std::shared_ptr<const Formula>> disj;
        for (const auto& command : _loop.commands)
        {
            // only take into account commands that do affect v
            if (!command->findAssignment(*v))
                continue;
            
            std::vector<std::shared_ptr<const Formula>> conj { command->guard->toFormula(i) } ;
            if (_dense.at(v))
            {
                conj.push_back(Formulas::equalityFormula(true, v->toTerm(i), x));
            }
            else
            {
                conj.push_back(Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(geOrLe),
                                                                 { x, v->toTerm(i) })));
                conj.push_back(Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(gtOrLt),
                                                                 { v->toTerm(succOfI), x })));
            }
            disj.push_back(Formulas::conjunctionFormula(conj));
        }
        
        // since v is monotonic, there should be at least one guard that updates it
        assert(disj.size() > 0);
        
        auto f = Formulas::conjunctionFormula( { iter(i), Formulas::disjunctionFormula(disj) } );
        
        auto p1 = Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                    { x, v->toTerm(Theory::timeZero()) });
        auto p2 = Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER),
                                    { v->toTerm(loopCounterSymbol()), x });
        std::vector<std::shared_ptr<const Formula>> conds { Formulas::predicateFormula(p1), Formulas::predicateFormula(p2) };
        
        return Formulas::universalFormula( { x },Formulas::implicationFormula(Formulas::conjunctionFormula(conds),
                                                                              Formulas::existentialFormula( { i } , f)));
    }
    
#pragma mark - Translation of Assignments
    
    /*
     * Translation of guarded assignments
     */
    
    void PropertiesTime::translateAssignments()
    {
        static unsigned i = 0;
        for (auto it = _loop.commands.begin(); it != _loop.commands.end(); ++it) {
            addProperty("assignment_" + std::to_string(i++), commandToFormula(*it));
        }
    }
    
    std::shared_ptr<const logic::Formula> PropertiesTime::commandToFormula(const GuardedCommand *c)
    {
        Assignment *a;
        std::vector<std::shared_ptr<const Formula>> conj {};
        
        auto i = Terms::lVariable(Sorts::timeSort(), "It1");
        auto succOfI = Theory::timeSucc(i);

        for (const auto& v : _vars)
        {
            // constant variables are constant symbols in formulas, nothing
            // to do then
            if (!_updated.at(v))
                continue;
            
            if (isArrayType(v->type))
            {
                assert(!util::Configuration::instance().arrayTheory().getValue());

                for (const auto& a : c->assignments)
                {
                    if (a->hasLhs(*v))
                    {
                        conj.push_back(arrayAssignment(a, i, succOfI));
                    }
                }
                conj.push_back(arrayNonAssignment(v, c, i, succOfI));
            }
            else
            {
                // only one assignment to a given scalar variable is possible
                // in a command (unlike array variables)
                a = c->findAssignment(*v);
                if (a)
                {
                    conj.push_back(assignment(a, i, succOfI));
                }
                else
                {
                    // no assignment to v in this command
                    conj.push_back(nonAssignment(v, i, succOfI));
                }
            }
        }
        
        assert(conj.size() > 0);
        auto guardAtI = c->guard->toFormula(i);
        auto f2 = Formulas::conjunctionFormula(conj);
        
        return Formulas::universalFormula( { i }, Formulas::implicationFormula(guardAtI, f2));
    }
    
    /** Given a scalar assignment v = e, return the formula v(s(i)) = e(i) */
    std::shared_ptr<const logic::Formula> PropertiesTime::assignment(const Assignment *a,
                                    std::shared_ptr<const Term> i,
                                    std::shared_ptr<const Term> succOfI)
    {
        PVariable * lhsVar = a->lhs->varInfo();
        assert(_updated.at(lhsVar));
        
        return Formulas::equalityFormula(true,
                                   lhsVar->toTerm(succOfI),
                                   a->rhs->toTerm(i));
    }
    
    /** Given an array assignment v[x] = e, return the formula v(s(i), x(i)) = e(i) */
    std::shared_ptr<const logic::Formula> PropertiesTime::arrayAssignment(const Assignment *a,
                                         std::shared_ptr<const Term> i,
                                         std::shared_ptr<const Term> succOfI)
    {
        PVariable * lhsVar = a->lhs->varInfo();
        assert(_updated.at(lhsVar));
        
        return Formulas::equalityFormula(true,
                                   lhsVar->toTerm(succOfI,
                                                  a->lhs->child(0)->toTerm(i)),
                                   a->rhs->toTerm(i));
    }
    
    /** Given a scalar variable v, return the formula v(s(i)) = v(i) */
    std::shared_ptr<const logic::Formula> PropertiesTime::nonAssignment(const PVariable *v,
                                       std::shared_ptr<const Term> i,
                                       std::shared_ptr<const Term> succOfI)
    {
        assert(_updated.at(v));
        
        return Formulas::equalityFormula(true,
                                   v->toTerm(succOfI),
                                   v->toTerm(i));
    }
    
    /** Given an array variable v, return the formula forall j, cond => v(s(i), j) = v(i, j) */
    std::shared_ptr<const logic::Formula> PropertiesTime::arrayNonAssignment(const PVariable *v,
                                            const GuardedCommand *gc,
                                            std::shared_ptr<const Term> i,
                                            std::shared_ptr<const Term> succOfI)
    {
        assert(_updated.at(v));
        assert(isArrayType(v->type));
        
        auto j = Terms::lVariable(Sorts::intSort(), "It2");
        std::vector<std::shared_ptr<const logic::Formula>> conj {};
        for(const auto& assignment : gc->assignments)
        {
            if (assignment->hasLhs(*v))
            {
                conj.push_back(Formulas::equalityFormula(false, j, assignment->lhs->child(0)->toTerm(i)));
            }
        }
        
        auto eq = Formulas::equalityFormula(true,
                                          v->toTerm(succOfI, j),
                                          v->toTerm(i, j));
        
        auto f = Formulas::implicationFormula(Formulas::conjunctionFormula(conj), eq);
        
        return Formulas::universalFormula({ j }, f);
    }
    
#pragma mark - Update predicates of arrays
    
    /*
     * Update predicates of arrays
     */
    void PropertiesTime::updatePredicatesOfArrays()
    {
        for (const auto& v : _vars)
        {
            // only check updates array variables
            if (!isArrayType(v->type) || !_updated.at(v))
                continue;
            
            if (util::Configuration::instance().existentialAxioms().getValue()) {
                // these axioms introduce skolem symbols
                addProperty("stability_" + v->name, stabilityAxiom(v));
                addProperty("unique_update_" + v->name, uniqueUpdateAxiom(v));
            }
        }
    }
    
    /** forall p, (forall i, iter(i) => !update_a(i, p)) => a(n, p) = a(0, p) */
    std::shared_ptr<const logic::Formula> PropertiesTime::stabilityAxiom(const PVariable *a)
    {
        assert(isArrayType(a->type));
        assert(_updated.at(a));
        
        auto p = Terms::lVariable(Sorts::intSort(), "P");
        auto i = Terms::lVariable(Sorts::timeSort(), "It");

        auto fa = Formulas::implicationFormula(iter(i),
                                               Formulas::negationFormula(arrayUpdatePredicate(a, i, p, nullptr)));
        
        auto fb = Formulas::universalFormula( {i}, fa);
        auto fc = Formulas::equalityFormula(true,
                                          a->toTerm(Theory::timeZero(), p),
                                          a->toTerm(loopCounterSymbol(), p));
        
        return Formulas::universalFormula( {p}, Formulas::implicationFormula(fb, fc));
    }
    
    /** forall i p v, (iter(i) & update_a(i, p, v) & (forall j, iter(j) & j != i => !update_a(j, p))) => a(n, p) = v */
    /* this property is only useful if the array is written at most once by the loop! */
    std::shared_ptr<const logic::Formula> PropertiesTime::uniqueUpdateAxiom(const PVariable *a)
    {
        assert(isArrayType(a->type));
        assert(_updated.at(a));
        
        auto i = Terms::lVariable(Sorts::timeSort(), "It1");
        auto j = Terms::lVariable(Sorts::timeSort(), "It2");
        auto p = Terms::lVariable(Sorts::intSort(), "P");
        auto v = Terms::lVariable(toSort(a->type), "V");
        
        auto fa = Formulas::implicationFormula(Formulas::conjunctionFormula({ Formulas::equalityFormula(false, i,j), iter(j) }),
                                             Formulas::negationFormula(arrayUpdatePredicate(a, j, p, nullptr)));
        auto fb = Formulas::conjunctionFormula(
                                               { Formulas::universalFormula({j}, fa),
                                                 arrayUpdatePredicate(a, i, p, v),
                                                 iter(i) }
                                             );
        
        auto fc = Formulas::equalityFormula(true,
                                          v,
                                          a->toTerm(loopCounterSymbol(), p));
        
        auto imp = Formulas::implicationFormula(fb, fc);
        return Formulas::universalFormula({i, p, v}, imp);
    }
    
    // if v is nullptr, updatePredicate with 2 args
    std::shared_ptr<const logic::Formula> PropertiesTime::arrayUpdatePredicate(const PVariable *a,
                                              std::shared_ptr<const logic::Term> i,
                                              std::shared_ptr<const logic::Term> p,
                                              std::shared_ptr<const logic::Term> v)
    {
        std::vector<std::shared_ptr<const logic::Formula>> disj {};
        
        for(const auto& command : _loop.commands)
        {
            for (const auto& assignment : command->assignments)
            {
                if (assignment->hasLhs(*a))
                {
                    disj.push_back(arrayAssignmentConditions(assignment, command->guard, i, p, v));
                }
            }
        }
        
        // a is updated, this shouldn't be empty
        assert(!disj.empty());
        
        return Formulas::disjunctionFormula(disj);
    }
    
    std::shared_ptr<const logic::Formula> PropertiesTime::arrayAssignmentConditions(const Assignment *asg,
                                                   const FExpression *guard,
                                                   std::shared_ptr<const logic::Term> i,
                                                   std::shared_ptr<const logic::Term> p,
                                                   std::shared_ptr<const logic::Term> v)
    {
        std::vector<std::shared_ptr<const logic::Formula>> conj;
        conj.push_back(guard->toFormula(i));
        conj.push_back(Formulas::equalityFormula(true,
                                           p,
                                           asg->lhs->child(0)->toTerm(i)));
        if (v)
            conj.push_back(Formulas::equalityFormula(true,
                                               v,
                                               asg->rhs->toTerm(i)));
        
        return Formulas::conjunctionFormula(conj);
    }
    
#pragma mark - loop condition properties
    
    // forall i, iter(i) => cond(i)
    void PropertiesTime::loopConditionHypothesis()
    {
        auto i = Terms::lVariable(Sorts::timeSort(), "It");
        
        addProperty("loop_condition", Formulas::universalFormula({i},
                                                                 Formulas::implicationFormula(iter(i),
                                                                                  _loop.loopCondition->toFormula(i))));
    }
    
#pragma mark - Symbol elimination properties
    
    void PropertiesTime::symbolEliminationAxioms()
    {
        for (const auto& v : _vars)
        {
            if (_updated.at(v))
            {
                addSymbolEliminationAxioms(v);
            }
        }
    }
    
    void PropertiesTime::addSymbolEliminationAxioms(const PVariable *v)
    {
        if (!_updated.at(v))
            return; // v's symbol won't be eliminated, no need for axiom
        
        std::shared_ptr<const Term> empty = nullptr;
        unsigned arity = isArrayType(v->type) ? 1 : 0;
        
        std::shared_ptr<const Term> lhsCounter;
        std::shared_ptr<const Term> rhsCounter;
        std::shared_ptr<const Term> lhsInit;
        std::shared_ptr<const Term> rhsInit;
        std::vector<std::shared_ptr<const LVariable>> vars;
        
        if (isArrayType(v->type))
        {
            auto p = Terms::lVariable(Sorts::intSort(), "P");
            vars.push_back(p);
            
            assert (arity == 1);
            rhsCounter = v->toTerm(empty, p);
            lhsCounter = v->toTerm(loopCounterSymbol(), p);
            Symbol* s = Signature::fetchOrDeclare(v->name + "$init", { Sorts::intSort() }, toSort(v->type));
            lhsInit = v->toTerm(Theory::integerConstant(0), p);
            rhsInit = Terms::funcTerm(s, {p});
        }
        else
        {
            rhsCounter = v->toTerm(empty);
            lhsCounter = v->toTerm(loopCounterSymbol());
            Symbol* s = Signature::fetchOrDeclare(v->name + "$init", toSort(v->type));
            lhsInit = v->toTerm(Theory::integerConstant(0));
            rhsInit = Terms::funcTerm(s, {});
        }
        
        addProperty("final_value_" + v->name, Formulas::universalFormula(vars, Formulas::equalityFormula(true, lhsCounter, rhsCounter)));
        addProperty("initial_value_" + v->name, Formulas::universalFormula(vars, Formulas::equalityFormula(true, lhsInit, rhsInit)));
    }
}


