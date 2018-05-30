#include "Properties.hpp"

#include <cassert>
#include <iostream>

#include "Signature.hpp"
#include "Theory.hpp"
#include "Options.hpp"
#include "Output.hpp"

using namespace logic;

namespace program {
    
#pragma mark - High level methods

    void Properties::analyze()
    {
        monotonicityProps();
        translateAssignments();
        updatePredicatesOfArrays();
        loopCounterHypothesis();
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
        
        constnessProps();
    }
    
    void Properties::constnessProps()
    {
        for (const auto& var : _vars)
        {
            if (!_updated.at(var))
            {
                LVariable* it = new LVariable(Sorts::intSort(), "It");
                
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

    
    void Properties::output()
    {
        assert(util::Configuration::instance().outputFormat().getValue() == "tptp" ||
               util::Configuration::instance().outputFormat().getValue() == "smtlib");

        std::ostream& ostr = util::Output::stream();
        
        // output sort declarations
        for(const auto& pair : Sorts::nameToSort())
        {
            if (util::Configuration::instance().outputFormat().getValue() == "tptp")
            {
                ostr << declareSortTPTP(*pair.second);
            }
            else
            {
                ostr << declareSortSMTLIB(*pair.second);
            }
        }
        
        // output symbol definitions
        for (const auto& pair : Symbol::signature())
        {
            const auto symbol = pair.second;
            if (util::Configuration::instance().outputFormat().getValue() == "tptp")
            {
                ostr << symbol->declareSymbolTPTP();
            }
            else
            {
                ostr << symbol->declareSymbolSMTLIB();
            }
        }
        
        // if in generation-mode, also output symbol colors
        if (util::Configuration::instance().mainMode().getValue() == "generation")
        {
            for (const auto& pair : Symbol::signature())
            {
                const auto symbol = pair.second;
                if (symbol->colored)
                {
                    if (util::Configuration::instance().outputFormat().getValue() == "tptp")
                    {
                        ostr << symbol->declareSymbolColorTPTP();
                    }
                    else
                    {
                        ostr << symbol->declareSymbolColorSMTLIB();
                    }
                }
            }
        }
        
        // output preconditions (at loop iteration 0)
        int i=0;
        for (const auto& precondition : _preconditions)
        {
            if (util::Configuration::instance().outputFormat().getValue() == "tptp")
            {
                ostr << precondition->toFormula(Theory::integerConstant(0))->declareTPTP("precondition_" + std::to_string(i++)) << std::endl;
            }
            else
            {
                ostr << precondition->toFormula(Theory::integerConstant(0))->declareSMTLIB("precondition_" + std::to_string(i++)) << std::endl;
            }
        }
        
        // output all properties
        for (auto it = _properties.begin(); it != _properties.end(); ++it)
        {
            Property p = *it;
            if (util::Configuration::instance().outputFormat().getValue() == "tptp")
            {
                ostr << p.second->declareTPTP(p.first) << std::endl;
            }
            else
            {
                ostr << p.second->declareSMTLIB(p.first) << std::endl;
            }
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
            if (util::Configuration::instance().outputFormat().getValue() == "tptp")
            {
                ostr << conjecture->declareTPTP("post_conditions", true) << std::endl;
            }
            else
            {
                ostr << conjecture->declareSMTLIB("post_conditions", true) << std::endl;
            }
        }
    }


#pragma mark - General Properties

    
    FuncTerm* Properties::loopCounterSymbol()
    {
        // initialization note that the syntax of the guarded command
        // language does not allow special characters such as $
        static Symbol* s = new Symbol("$n", Sorts::intSort(), false, true);
        
        return new FuncTerm(s, {});
    }
    
    
    // 0 <= i < n
    Formula* Properties::iter(Term* i)
    {
        return new ConjunctionFormula( {
            new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                              { i, Theory::integerConstant(0) } )),
            new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER),
                                              { loopCounterSymbol(), i })) } );
    }
    
#pragma mark - Monotonicity Properties
    
    /*
     * Monotonicity propreties
     */
    
    void Properties::monotonicityProps()
    {
        for (auto it = _vars.begin(); it != _vars.end(); ++it) {
            const PVariable *v = (*it);
            if(_monotonic.at(v) == Monotonicity::OTHER)
                continue;
            
            if (_dense.at(v))
            {
                if (_strict.at(v))
                {
                    // don't add updatePropertyOfVar here since dense prop is
                    // stronger and does not have an existential quantifier
                    //addProperty("update_" + v->name, updatePropertyOfVar(v));
                    addProperty("dense_strict_" + v->name(), denseStrictProp(v)); // also implies strictProp
                } else {
                    addProperty("update_" + v->name(), updatePropertyOfVar(v));
                    addProperty("non_strict_" + v->name(), nonStrictProp(v));
                    addProperty("dense_non_strict" + v->name(), denseNonStrictProp(v));
                }
            } else {
                addProperty("update_" + v->name(), updatePropertyOfVar(v));
                if (_strict.at(v)) {
                    addProperty("strict_" + v->name(), strictProp(v));
                } else {
                    addProperty("non_strict_" + v->name(), nonStrictProp(v));
                }
            }
        }
    }
    
    /** forall i, v(i) = v(0) + i [v(0) - i if v is decreasing] */
    Formula* Properties::denseStrictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(_dense.at(v));
        assert(_strict.at(v));
        
        LVariable* i = new LVariable(Sorts::intSort(), "It");
        
        InterpretedSymbol interp = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_PLUS
                                    : InterpretedSymbol::INT_MINUS);
        Term* v0 = v->toTerm(Theory::integerConstant(0));
        Term* lhsTerm = v->toTerm(i);
        FuncTerm* rhsTerm = new FuncTerm(Theory::getSymbol(interp), {v0, i});
        return EqualityFormula(true, lhsTerm, rhsTerm).quantify();
    }
    
    /** forall i j, j > i => v(j) > v(i) [v(j) < v(i) if v is
     decreasing] */
    Formula *Properties::strictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(_dense.at(v));
        assert(_strict.at(v));
        
        LVariable* i = new LVariable(Sorts::intSort(), "It1");
        LVariable* j = new LVariable(Sorts::intSort(), "It2");
        
        InterpretedSymbol interp = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER
                                    : InterpretedSymbol::INT_LESS);
        ImplicationFormula imp(new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER),
                                                                 {j, i})),
                               new PredicateFormula(new PredTerm(Theory::getSymbol(interp),
                                                                 { v->toTerm(j), v->toTerm(i) })));
        return imp.quantify();
    }
    
    /** forall i j, j >= i => v(i) + j >= v(j) + i [v(j) + j >= v(i) + i
     if v is decreasing] */
    Formula* Properties::denseNonStrictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(_dense.at(v));
        assert(!_strict.at(v));
        
        LVariable* i = new LVariable(Sorts::intSort(), "It1");
        LVariable* j = new LVariable(Sorts::intSort(), "It2");
        
        bool incr = (_monotonic.at(v) == Monotonicity::INC);
        FuncTerm* lhs = new FuncTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                     { incr ? v->toTerm(i) : v->toTerm(j), j });
        FuncTerm* rhs = new FuncTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                     { incr ? v->toTerm(j) : v->toTerm(i), i });
        ImplicationFormula imp(new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                                 { j, i })),
                               new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                                 { lhs, rhs })));
        return imp.quantify();
    }
    
    /** forall i j, j >= i => v(j) >= v(i) [v(j) <= v(i) if v is
     decreasing] */
    Formula *Properties::nonStrictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(!_strict.at(v));
        
        LVariable* i = new LVariable(Sorts::intSort(), "It1");
        LVariable* j = new LVariable(Sorts::intSort(), "It2");
        
        InterpretedSymbol interp = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER_EQUAL
                                    : InterpretedSymbol::INT_LESS_EQUAL);
        ImplicationFormula imp(new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                                 { i, j })),
                               new PredicateFormula(new PredTerm(Theory::getSymbol(interp),
                                                                 { v->toTerm(i), v->toTerm(j) })));
        return imp.quantify();
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
     *  and otherwise       pred <=> x >= v(i) & v(i+1) > x [resp. <=, < if decreasing]
     */
    Formula *Properties::updatePropertyOfVar(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        
        LVariable* x = new LVariable(Sorts::intSort(), "X");
        LVariable* i = new LVariable(Sorts::intSort(), "It");
        FuncTerm* iPlusOne = new FuncTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                          {i, Theory::integerConstant(1)});
        
        InterpretedSymbol geOrLe = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER_EQUAL
                                    : InterpretedSymbol::INT_LESS_EQUAL);
        InterpretedSymbol gtOrLt = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER
                                    : InterpretedSymbol::INT_LESS);
        
        // build the disjunction
        std::vector<Formula*> disj {};
        for (auto it = _loop.commands.begin(); it != _loop.commands.end(); ++it) {
            // only take into account commands that do affect v
            if (!(*it)->findAssignment(*v))
                continue;
            
            std::vector<Formula*> conj { (*it)->guard->toFormula(i) } ;
            if (_dense.at(v)) {
                conj.push_back(new EqualityFormula(true, v->toTerm(i), x));
            } else {
                conj.push_back(new PredicateFormula(new PredTerm(Theory::getSymbol(geOrLe),
                                                                 { x, v->toTerm(i) })));
                conj.push_back(new PredicateFormula(new PredTerm(Theory::getSymbol(gtOrLt),
                                                                 { v->toTerm(iPlusOne), x })));
            }
            disj.push_back(new ConjunctionFormula(conj));
        }
        
        // since v is monotonic, there should be at least one guard that updates it
        assert(disj.size() > 0);
        
        Formula *f = new ConjunctionFormula( { iter(i), new DisjunctionFormula(disj) } );
        
        PredTerm *p1 = new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                    { x, v->toTerm(Theory::integerConstant(0)) });
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
    
    void Properties::translateAssignments()
    {
        static unsigned i = 0;
        for (auto it = _loop.commands.begin(); it != _loop.commands.end(); ++it) {
            addProperty("assignment_" + std::to_string(i++), commandToFormula(*it));
        }
    }
    
    Formula *Properties::commandToFormula(const GuardedCommand *c)
    {
        Assignment *a;
        std::vector<Formula*> conj {};
        
        LVariable* i = new LVariable(Sorts::intSort(), "It1");
        Term* iPlusOne = new FuncTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                      { i, Theory::integerConstant(1) } );
        
        for (auto it = _vars.begin(); it != _vars.end(); ++it) {
            const PVariable* v = (*it);
            // constant variables are constant symbols in formulas, nothing
            // to do then
            if (!_updated.at(v))
                continue;
            
            if (isArrayType(v->vtype())) {
                if (util::Configuration::instance().arrayTheory().getValue()) {
                    // representation using array axiomatization
                    Term *store = v->toTerm(i);
                    for (auto itAsg = c->assignments.begin();
                         itAsg != c->assignments.end();
                         ++itAsg) {
                        a = *itAsg;
                        if (a->hasLhs(*v))
                            store = new FuncTerm(Theory::getSymbol(InterpretedSymbol::ARRAY_STORE),
                                                 { store, a->lhs->child(0)->toTerm(i), a->rhs->toTerm(i) });
                    }
                    conj.push_back(new EqualityFormula(true,
                                                       v->toTerm(iPlusOne),
                                                       store));
                } else {
                    // representation of arrays as functions
                    for (auto itAsg = c->assignments.begin();
                         itAsg != c->assignments.end();
                         ++itAsg) {
                        a = *itAsg;
                        if (a->hasLhs(*v))
                            conj.push_back(arrayAssignment(a, i, iPlusOne));
                    }
                    conj.push_back(arrayNonAssignment(v, c, i, iPlusOne));
                }
            } else {
                // only one assignment to a given scalar variable is possible
                // in a command (unlike array variables)
                a = c->findAssignment(*v);
                if (a) {
                    conj.push_back(assignment(a, i, iPlusOne));
                } else {
                    // no assignment to v in this command
                    conj.push_back(nonAssignment(v, i, iPlusOne));
                }
            }
        }
        
        assert(conj.size() > 0);
        Formula *f1 = new ConjunctionFormula( { c->guard->toFormula(i), iter(i) } );
        Formula *f2 = new ConjunctionFormula(conj);
        
        return new UniversalFormula( { i }, new ImplicationFormula(f1, f2));
        
    }
    
    /** Given a scalar assignment v = e, return the formula v(i+1) = e(i) */
    Formula* Properties::assignment(const Assignment *a,
                                    const Term* index,
                                    const Term* indexPlusOne)
    {
        PVariable * lhsVar = a->lhs->varInfo();
        assert(_updated.at(lhsVar));
        
        return new EqualityFormula(true,
                                   lhsVar->toTerm(indexPlusOne),
                                   a->rhs->toTerm(index));
    }
    
    /** Given an array assignment v[x] = e, return the formula v(i+1, x(i)) = e(i) */
    Formula* Properties::arrayAssignment(const Assignment *a,
                                         const Term* index,
                                         const Term* indexPlusOne)
    {
        PVariable * lhsVar = a->lhs->varInfo();
        assert(_updated.at(lhsVar));
        
        return new EqualityFormula(true,
                                   lhsVar->toTerm(indexPlusOne,
                                                  a->lhs->child(0)->toTerm(index)),
                                   a->rhs->toTerm(index));
    }
    
    /** Given a scalar variable v, return the formula v(i+1) = v(i) */
    Formula* Properties::nonAssignment(const PVariable *v,
                                       const Term* index,
                                       const Term* indexPlusOne)
    {
        assert(_updated.at(v));
        
        return new EqualityFormula(true,
                                   v->toTerm(indexPlusOne),
                                   v->toTerm(index));
    }
    
    /** Given an array variable v, return the formula forall j, cond => v(i+1, j) = v(i, j) */
    Formula* Properties::arrayNonAssignment(const PVariable *v,
                                            const GuardedCommand *gc,
                                            const Term* index,
                                            const Term* indexPlusOne)
    {
        assert(_updated.at(v));
        assert(isArrayType(v->vtype()));
        
        LVariable* j = new LVariable(Sorts::intSort(), "It2");
        std::vector<Formula*> conj {};
        for (auto it = gc->assignments.begin();
             it != gc->assignments.end();
             ++it) {
            if ((*it)->hasLhs(*v))
                conj.push_back(new EqualityFormula(false,
                                                   j,
                                                   (*it)->lhs->child(0)->toTerm(index)));
        }
        
        Formula *eq = new EqualityFormula(true,
                                          v->toTerm(indexPlusOne, j),
                                          v->toTerm(index, j));
        
        Formula *f = conj.empty() ? eq : new ImplicationFormula(new ConjunctionFormula(conj), eq);
        
        return new UniversalFormula({ j }, f);
    }
    
#pragma mark - Update predicates of arrays

    /*
     * Update predicates of arrays
     */
    void Properties::updatePredicatesOfArrays()
    {
        for (auto it = _vars.begin(); it != _vars.end(); ++it) {
            const PVariable *v = (*it);
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
    Formula* Properties::stabilityAxiom(const PVariable *a)
    {
        assert(isArrayType(a->vtype()));
        assert(_updated.at(a));
        
        LVariable* i = new LVariable(Sorts::intSort(), "It");
        LVariable* p = new LVariable(Sorts::intSort(), "P");
        
        Formula *fa = new ImplicationFormula(iter(i),
                                             new NegationFormula(arrayUpdatePredicate(a, i, p, nullptr)));
        
        Formula *fb = new UniversalFormula( {i}, fa);
        Formula *fc = new EqualityFormula(true,
                                          a->toTerm(Theory::integerConstant(0), p),
                                          a->toTerm(loopCounterSymbol(), p));
        
        return new UniversalFormula( {p}, new ImplicationFormula(fb, fc));
        
    }
    
    /** forall i p v, (iter(i) & update_a(i, p, v) & (forall j, iter(j) & j != i => !update_a(j, p))) => a(n, p) = v */
    /* this is true only if the array is written at most once by the loop! */
    Formula* Properties::uniqueUpdateAxiom(const PVariable *a)
    {
        assert(isArrayType(a->vtype()));
        assert(_updated.at(a));
        
        LVariable* i = new LVariable(Sorts::intSort(), "It1");
        LVariable* j = new LVariable(Sorts::intSort(), "It2");
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
    
    /** forall i p v, (iter(i) & update_a(i, p, v) & (forall j, iter(j) & j > i => !update_a(j, p))) => a(n, p) = v */
    Formula* Properties::lastUpdateAxiom(const PVariable *a)
    {
        assert(isArrayType(a->vtype()));
        assert(_updated.at(a));
        
        LVariable* i = new LVariable(Sorts::intSort(), "It1");
        LVariable* j = new LVariable(Sorts::intSort(), "It2");
        LVariable* p = new LVariable(Sorts::intSort(), "P");
        LVariable* v = new LVariable(toSort(a->vtype()), "V");
        
        PredTerm* gt = new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER), {j, i});
        Formula *fa = new ImplicationFormula(new ConjunctionFormula({ new PredicateFormula(gt), iter(j) }),
                                             new NegationFormula(arrayUpdatePredicate(a, j, p, nullptr)));
        Formula *fb = new ConjunctionFormula(
                                             { new UniversalFormula({j}, fa),
                                                 arrayUpdatePredicate(a, i, p, v),
                                                 iter(i) }
                                             );
        
        Formula *fc = new EqualityFormula(true,
                                          v,
                                          a->toTerm(loopCounterSymbol(), p));
        
        return new UniversalFormula({i, p, v} , new ImplicationFormula(fb, fc));
    }
    
    // if v is nullptr, updatePredicate with 2 args
    Formula* Properties::arrayUpdatePredicate(const PVariable *a,
                                              const Term* i,
                                              const Term* p,
                                              const Term* v)
    {
        std::vector<Formula*> disj {};
        
        for (auto itCmd = _loop.commands.begin(); itCmd != _loop.commands.end(); ++itCmd) {
            GuardedCommand *gc = *itCmd;
            
            for (auto itAsg = gc->assignments.begin(); itAsg != gc->assignments.end(); ++itAsg) {
                Assignment *asg = *itAsg;
                
                if (asg->hasLhs(*a))
                    disj.push_back(arrayAssignmentConditions(asg, gc->guard, i, p, v));
            }
        }
        
        // a is updated, this shouldn't be empty
        assert(!disj.empty());
        
        return new DisjunctionFormula(disj);
    }
    
    Formula* Properties::arrayAssignmentConditions(const Assignment *asg,
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

#pragma mark - loop counter properties

    // counter >= 0
    void Properties::loopCounterHypothesis()
    {
        addProperty("loop_counter", new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                                      { loopCounterSymbol(), Theory::integerConstant(0) })));
    }
    
#pragma mark - loop condition properties

    // forall i, iter(i) => cond(i)
    void Properties::loopConditionHypothesis()
    {
        LVariable* i = new LVariable(Sorts::intSort(), "It");
        
        addProperty("loop_condition", new UniversalFormula({i},
                                                           new ImplicationFormula(iter(i),
                                                                                  _loop.loopCondition->toFormula(i))));
    }
    
#pragma mark - Symbol elimination properties
    
    void Properties::symbolEliminationAxioms()
    {
        for (auto it = _vars.begin(); it != _vars.end(); ++it) {
            const PVariable *v = (*it);
            if (_updated.at(v))
                addSymbolEliminationAxioms(v);
        }
    }
    
    void Properties::addSymbolEliminationAxioms(const PVariable *v)
    {
        if (!_updated.at(v))
            return; // v's symbol won't be eliminated, no need for axiom
        
        LVariable* i = new LVariable(Sorts::intSort());
        Term* empty = nullptr;
        unsigned arity = isArrayType(v->vtype()) ? 1 : 0;
        
        Term* lhsCounter;
        Term* rhsCounter;
        Term* lhsInit;
        Term* rhsInit;
        Symbol* s;
        
        if (isArrayType(v->vtype())) {
            // array symbol
            assert (arity == 1);
            rhsCounter = v->toTerm(empty, i);
            lhsCounter = v->toTerm(loopCounterSymbol(), i);
            s = new Symbol(v->name() + "$init", { Sorts::intSort() }, toSort(v->vtype()));
            lhsInit = v->toTerm(Theory::integerConstant(0), i);
            rhsInit = new FuncTerm(s, {i});
        } else {
            rhsCounter = v->toTerm(empty);
            lhsCounter = v->toTerm(loopCounterSymbol());
            s = new Symbol(v->name() + "$init", toSort(v->vtype()));
            lhsInit = v->toTerm(Theory::integerConstant(0));
            rhsInit = new FuncTerm(s, {});
        }
        
        addProperty("final_value_" + v->name(), EqualityFormula(true, lhsCounter, rhsCounter).quantify());
        addProperty("initial_value_" + v->name(), EqualityFormula(true, lhsInit, rhsInit).quantify());
    }
}

