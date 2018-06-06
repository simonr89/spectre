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
            Formula *f = _loop.loopCondition->toFormula(loopCounterSymbol());
            addProperty("loop_exit", new NegationFormula(f));
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
        for (const auto& pair : Symbol::signature())
        {
            const auto symbol = pair.second;
            ostr << symbol->declareSymbolSMTLIB();
        }
        
        // if in generation-mode, also output symbol colors
        if (util::Configuration::instance().mainMode().getValue() == "generation")
        {
            for (const auto& pair : Symbol::signature())
            {
                const auto symbol = pair.second;
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
            std::vector<Formula*>conjuncts;
            for (const auto& postcondition : _postconditions)
            {
                conjuncts.push_back(postcondition->toFormula(loopCounterSymbol()));
            }
            Formula* conjecture = new ConjunctionFormula(conjuncts);
            
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
                LVariable* it = new LVariable(Sorts::timeSort(), "It");
                
                Formula* eq;
                // eq(it) := x(it) = x(0)
                if (!isArrayType(var->vtype()))
                {
                    Symbol* var0Symbol = new Symbol(var->name()+"0", toSort(var->vtype()));
                    Term* var0 = new FuncTerm(var0Symbol, {});
                    
                    eq = new EqualityFormula(true,
                                             var->toTerm(it),
                                             var0);
                }
                // eq(i) := forall p. x(i,p) = x(0,p)
                else
                {
                    // suppport for other options not implemented yet
                    assert(!util::Configuration::instance().arrayTheory().getValue());
                    
                    LVariable* p = new LVariable(Sorts::intSort(), "P");
                    
                    Symbol* var0Symbol = new Symbol(var->name()+"0", { Sorts::intSort() }, toSort(var->vtype()));
                    Term* var0 = new FuncTerm(var0Symbol, {p});
                    
                    Formula* eqWithoutQuantifiers = new EqualityFormula(true,
                                                                        var->toTerm(it, p),
                                                                        var0);
                    eq = new UniversalFormula({p}, eqWithoutQuantifiers);
                }
                
                // forall i. eq(i)
                Formula* f = new UniversalFormula({it}, eq);
                
                // add property
                addProperty("not_updated_" + var->name(), f);
            }
        }
    }
    
    FuncTerm* PropertiesTime::loopCounterSymbol()
    {
        // initialization note that the syntax of the guarded command
        // language does not allow special characters such as $
        static Symbol* s = new Symbol("$n", Sorts::timeSort(), false, true);
        return new FuncTerm(s, {});
    }
    
    // iter(i) := i < n
    // we use i < n instead of 0 <= i < n, since for our term algebra, 0 <= i for any i.
    Formula* PropertiesTime::iter(Term* i)
    {
        return new PredicateFormula(Theory::timeSub(i, loopCounterSymbol()));
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
            
            addProperty("update_" + v->name(), updatePropertyOfVar(v));

            if (_strict.at(v))
            {
                addProperty("strict_" + v->name(), strictProp(v));
            }
            else
            {
                addProperty("non_strict_" + v->name(), nonStrictProp(v));
            }
        }
    }
    
    /** forall i j. (i < j => v(i) < v(j)) [v(j) < v(i) if v is decreasing] */
    Formula *PropertiesTime::strictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(_strict.at(v));
        
        LVariable* i = new LVariable(Sorts::timeSort(), "It1");
        LVariable* j = new LVariable(Sorts::timeSort(), "It2");
        
        if (_monotonic.at(v) == Monotonicity::INC)
        {

            ImplicationFormula imp(new PredicateFormula(Theory::timeSub(i, j)),
                                   new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_LESS),{ v->toTerm(i), v->toTerm(j) })));
            return imp.quantify();
        }
        else
        {
            ImplicationFormula imp(new PredicateFormula(Theory::timeSub(i, j)),
                                   new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_LESS),{ v->toTerm(j), v->toTerm(i) })));
            return imp.quantify();
        }
    }
    
    /** forall i j. (i<j => v(i)<=v(j)) [v(j)<=v(i) if v is decreasing] */
    Formula *PropertiesTime::nonStrictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(!_strict.at(v));
        
        LVariable* i = new LVariable(Sorts::timeSort(), "It1");
        LVariable* j = new LVariable(Sorts::timeSort(), "It2");
        
        if (_monotonic.at(v) == Monotonicity::INC)
        {
            ImplicationFormula imp(new PredicateFormula(Theory::timeSub(i, j)),
                                   new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_LESS_EQUAL),{ v->toTerm(i), v->toTerm(j) })));
            return imp.quantify();
        }
        else
        {
            ImplicationFormula imp(new PredicateFormula(Theory::timeSub(i, j)),
                                   new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_LESS_EQUAL),{ v->toTerm(j), v->toTerm(i) })));
            return imp.quantify();
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
    Formula *PropertiesTime::updatePropertyOfVar(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        
        LVariable* x = new LVariable(Sorts::intSort(), "X");
        LVariable* i = new LVariable(Sorts::timeSort(), "It");
        FuncTerm* succOfI = Theory::timeSucc(i);
        
        InterpretedSymbol geOrLe = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER_EQUAL
                                    : InterpretedSymbol::INT_LESS_EQUAL);
        InterpretedSymbol gtOrLt = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER
                                    : InterpretedSymbol::INT_LESS);
        
        // build the disjunction
        std::vector<Formula*> disj {};
        for (auto it = _loop.commands.begin(); it != _loop.commands.end(); ++it)
        {
            // only take into account commands that do affect v
            if (!(*it)->findAssignment(*v))
                continue;
            
            std::vector<Formula*> conj { (*it)->guard->toFormula(i) } ;
            if (_dense.at(v))
            {
                conj.push_back(new EqualityFormula(true, v->toTerm(i), x));
            }
            else
            {
                conj.push_back(new PredicateFormula(new PredTerm(Theory::getSymbol(geOrLe),
                                                                 { x, v->toTerm(i) })));
                conj.push_back(new PredicateFormula(new PredTerm(Theory::getSymbol(gtOrLt),
                                                                 { v->toTerm(succOfI), x })));
            }
            disj.push_back(new ConjunctionFormula(conj));
        }
        
        // since v is monotonic, there should be at least one guard that updates it
        assert(disj.size() > 0);
        
        Formula *f = new ConjunctionFormula( { iter(i), new DisjunctionFormula(disj) } );
        
        PredTerm *p1 = new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                    { x, v->toTerm(Theory::timeZero()) });
        PredTerm *p2 = new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER),
                                    { v->toTerm(loopCounterSymbol()), x });
        std::vector<Formula*> conds { new PredicateFormula(p1), new PredicateFormula(p2) };
        
        return new UniversalFormula( { x }, new ImplicationFormula(new ConjunctionFormula(conds),
                                                                   new ExistentialFormula( { i } , f)));
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
    
    Formula *PropertiesTime::commandToFormula(const GuardedCommand *c)
    {
        Assignment *a;
        std::vector<Formula*> conj {};
        
        LVariable* i = new LVariable(Sorts::timeSort(), "It1");
        FuncTerm* succOfI = Theory::timeSucc(i);

        for (const auto& v : _vars)
        {
            // constant variables are constant symbols in formulas, nothing
            // to do then
            if (!_updated.at(v))
                continue;
            
            if (isArrayType(v->vtype()))
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
        Formula *f1 = new ConjunctionFormula( { c->guard->toFormula(i), iter(i) } );
        Formula *f2 = new ConjunctionFormula(conj);
        
        return new UniversalFormula( { i }, new ImplicationFormula(f1, f2));
    }
    
    /** Given a scalar assignment v = e, return the formula v(s(i)) = e(i) */
    Formula* PropertiesTime::assignment(const Assignment *a,
                                    const Term* i,
                                    const Term* succOfI)
    {
        PVariable * lhsVar = a->lhs->varInfo();
        assert(_updated.at(lhsVar));
        
        return new EqualityFormula(true,
                                   lhsVar->toTerm(succOfI),
                                   a->rhs->toTerm(i));
    }
    
    /** Given an array assignment v[x] = e, return the formula v(s(i), x(i)) = e(i) */
    Formula* PropertiesTime::arrayAssignment(const Assignment *a,
                                         const Term* i,
                                         const Term* succOfI)
    {
        PVariable * lhsVar = a->lhs->varInfo();
        assert(_updated.at(lhsVar));
        
        return new EqualityFormula(true,
                                   lhsVar->toTerm(succOfI,
                                                  a->lhs->child(0)->toTerm(i)),
                                   a->rhs->toTerm(i));
    }
    
    /** Given a scalar variable v, return the formula v(s(i)) = v(i) */
    Formula* PropertiesTime::nonAssignment(const PVariable *v,
                                       const Term* i,
                                       const Term* succOfI)
    {
        assert(_updated.at(v));
        
        return new EqualityFormula(true,
                                   v->toTerm(succOfI),
                                   v->toTerm(i));
    }
    
    /** Given an array variable v, return the formula forall j, cond => v(s(i), j) = v(i, j) */
    Formula* PropertiesTime::arrayNonAssignment(const PVariable *v,
                                            const GuardedCommand *gc,
                                            const Term* i,
                                            const Term* succOfI)
    {
        assert(_updated.at(v));
        assert(isArrayType(v->vtype()));
        
        LVariable* j = new LVariable(Sorts::intSort(), "It2");
        std::vector<Formula*> conj {};
        for(const auto& assignment : gc->assignments)
        {
            if (assignment->hasLhs(*v))
            {
                conj.push_back(new EqualityFormula(false, j, assignment->lhs->child(0)->toTerm(i)));
            }
        }
        
        Formula *eq = new EqualityFormula(true,
                                          v->toTerm(succOfI, j),
                                          v->toTerm(i, j));
        
        Formula *f = conj.empty() ? eq : new ImplicationFormula(new ConjunctionFormula(conj), eq);
        
        return new UniversalFormula({ j }, f);
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
            if (!isArrayType(v->vtype()) || !_updated.at(v))
                continue;
            
            if (util::Configuration::instance().existentialAxioms().getValue()) {
                // these axioms introduce skolem symbols
                addProperty("stability_" + v->name(), stabilityAxiom(v));
                addProperty("unique_update_" + v->name(), uniqueUpdateAxiom(v));
            }
        }
    }
    
    /** forall p, (forall i, iter(i) => !update_a(i, p)) => a(n, p) = a(0, p) */
    Formula* PropertiesTime::stabilityAxiom(const PVariable *a)
    {
        assert(isArrayType(a->vtype()));
        assert(_updated.at(a));
        
        LVariable* p = new LVariable(Sorts::intSort(), "P");
        LVariable* i = new LVariable(Sorts::timeSort(), "It");

        Formula *fa = new ImplicationFormula(iter(i),
                                             new NegationFormula(arrayUpdatePredicate(a, i, p, nullptr)));
        
        Formula *fb = new UniversalFormula( {i}, fa);
        Formula *fc = new EqualityFormula(true,
                                          a->toTerm(Theory::timeZero(), p),
                                          a->toTerm(loopCounterSymbol(), p));
        
        return new UniversalFormula( {p}, new ImplicationFormula(fb, fc));
        
    }
    
    /** forall i p v, (iter(i) & update_a(i, p, v) & (forall j, iter(j) & j != i => !update_a(j, p))) => a(n, p) = v */
    /* this property is only useful if the array is written at most once by the loop! */
    Formula* PropertiesTime::uniqueUpdateAxiom(const PVariable *a)
    {
        assert(isArrayType(a->vtype()));
        assert(_updated.at(a));
        
        LVariable* i = new LVariable(Sorts::timeSort(), "It1");
        LVariable* j = new LVariable(Sorts::timeSort(), "It2");
        LVariable* p = new LVariable(Sorts::intSort(), "P");
        LVariable* v = new LVariable(toSort(a->vtype()), "V");
        
        Formula *fa = new ImplicationFormula(new ConjunctionFormula({ new EqualityFormula(false, i,j), iter(j) }),
                                             new NegationFormula(arrayUpdatePredicate(a, j, p, nullptr)));
        Formula *fb = new ConjunctionFormula(
                                             { new UniversalFormula({j}, fa),
                                                 arrayUpdatePredicate(a, i, p, v),
                                                 iter(i) }
                                             );
        
        Formula *fc = new EqualityFormula(true,
                                          v,
                                          a->toTerm(loopCounterSymbol(), p));
        
        return ImplicationFormula(fb, fc).quantify();
    }
    
    // if v is nullptr, updatePredicate with 2 args
    Formula* PropertiesTime::arrayUpdatePredicate(const PVariable *a,
                                              const Term* i,
                                              const Term* p,
                                              const Term* v)
    {
        std::vector<Formula*> disj {};
        
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
        
        return new DisjunctionFormula(disj);
    }
    
    Formula* PropertiesTime::arrayAssignmentConditions(const Assignment *asg,
                                                   const FExpression *guard,
                                                   const Term* i,
                                                   const Term* p,
                                                   const Term* v)
    {
        std::vector<Formula*> conj;
        conj.push_back(guard->toFormula(i));
        conj.push_back(new EqualityFormula(true,
                                           p,
                                           asg->lhs->child(0)->toTerm(i)));
        if (v)
            conj.push_back(new EqualityFormula(true,
                                               v,
                                               asg->rhs->toTerm(i)));
        
        return new ConjunctionFormula(conj);
    }
    
#pragma mark - loop condition properties
    
    // forall i, iter(i) => cond(i)
    void PropertiesTime::loopConditionHypothesis()
    {
        LVariable* i = new LVariable(Sorts::timeSort(), "It");
        
        addProperty("loop_condition", new UniversalFormula({i},
                                                           new ImplicationFormula(iter(i),
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
        
        Term* empty = nullptr;
        unsigned arity = isArrayType(v->vtype()) ? 1 : 0;
        
        Term* lhsCounter;
        Term* rhsCounter;
        Term* lhsInit;
        Term* rhsInit;
        
        if (isArrayType(v->vtype()))
        {
            LVariable* p = new LVariable(Sorts::intSort(), "P");
            
            assert (arity == 1);
            rhsCounter = v->toTerm(empty, p);
            lhsCounter = v->toTerm(loopCounterSymbol(), p);
            Symbol* s = new Symbol(v->name() + "$init", { Sorts::intSort() }, toSort(v->vtype()));
            lhsInit = v->toTerm(Theory::integerConstant(0), p);
            rhsInit = new FuncTerm(s, {p});
        }
        else
        {
            rhsCounter = v->toTerm(empty);
            lhsCounter = v->toTerm(loopCounterSymbol());
            Symbol* s = new Symbol(v->name() + "$init", toSort(v->vtype()));
            lhsInit = v->toTerm(Theory::integerConstant(0));
            rhsInit = new FuncTerm(s, {});
        }
        
        addProperty("final_value_" + v->name(), EqualityFormula(true, lhsCounter, rhsCounter).quantify());
        addProperty("initial_value_" + v->name(), EqualityFormula(true, lhsInit, rhsInit).quantify());
    }
}


