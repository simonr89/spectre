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
        // main axiom
        stepAxiom();

        // trace lemmas to complement the axiom
        constnessProps();
        monotonicityProps();
        translateAssignments();
        updatePredicatesOfArrays();

        // theory axioms
        theoryAxioms();

        // goal
        if (util::Configuration::instance().mainMode().getValue() == "verification")
        {
            // negation of the formula forall n, P(0) & (forall m, m < n -> C(m)) & ~C(n) -> Q(n) 
            preconditionsSatisfied();
            loopCounterNonNegative();
            loopCondition();
            loopExit();
            verificationGoal();
        } else if (util::Configuration::instance().mainMode().getValue() == "generation") {
            preconditionsSatisfied();
            loopCounterNonNegative();
            loopCondition();
            symbolEliminationAxioms();
        } else if (util::Configuration::instance().mainMode().getValue() == "termination") {
            // negation of the formula P(0) => exists n, ~C(n)
            preconditionsSatisfied();
            terminationGoal();
        }
    }
    
    void Properties::outputTPTP()
    {
        std::ostream& ostr = util::Output::stream();
        
        // output sort declarations
        for(const auto& pair : Sorts::nameToSort())
        {
            ostr << declareSortTPTP(*pair.second);
        }
        
        // output symbol definitions
        for (const auto& symbol : Signature::signature())
        {
            ostr << symbol->declareSymbolTPTP();
        }
        
        // if in generation-mode, also output symbol colors
        if (util::Configuration::instance().mainMode().getValue() == "generation")
        {
            for (const auto& symbol : Signature::signature())
            {
                if (symbol->colored)
                {
                    ostr << symbol->declareSymbolColorTPTP();
                }
            }
        }
        
        // output all properties
        for (auto it = properties.begin(); it != properties.end(); ++it)
        {
            Property p = *it;
            ostr << p.second->declareTPTP(p.first) << std::endl;
        }
    }

    void Properties::outputSMTLIB()
    {
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
        
        // output all properties
        for (auto it = properties.begin(); it != properties.end(); ++it)
        {
            Property p = *it;
            ostr << p.second->declareSMTLIB(p.first) << std::endl;
        }
    }
    
#pragma mark - Main axiom

    void Properties::stepAxiom()
    {
        //TODO
    }

    void Properties::theoryAxioms()
    {
        if (util::Configuration::instance().arrayTheory().getValue())
        {
            addProperty("select_over_store_1", Theory::selectOverStoreAxiom1());
            addProperty("select_over_store_2", Theory::selectOverStoreAxiom2());
        }
        if (util::Configuration::instance().timepoints().getValue())
        {
            addProperty("timesub_1", Theory::timeSubAxiom1());
            addProperty("timesub_2", Theory::timeSubAxiom2());
        }
    }

#pragma mark - General Properties

    FormulaPtr Properties::timepointQuantified(std::vector<LVariablePtr> vars, FormulaPtr f)
    {
        if (util::Configuration::instance().timepoints().getValue())
        {
            return Formulas::universalFormula(vars, f);
        }
        else
        {
            std::vector<FormulaPtr> conjuncts;
            for (const auto& var : vars)
            {
                conjuncts.push_back(Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                                               { var, Theory::integerConstant(0) } )));
            }
            return Formulas::universalFormula(vars, Formulas::implicationFormula(Formulas::conjunctionFormula(conjuncts), f));
        }
    }

    void Properties::constnessProps()
    {
        for (const auto& var : vars)
        {
            if (!updated.at(var))
            {
                LVariablePtr it = Terms::lVariable(Sorts::timeSort(), "It");
                
                FormulaPtr eq;
                if (isArrayType(var->type)
                    && !util::Configuration::instance().arrayTheory().getValue())
                {
                    // eq(i) := forall p. x(i,p) = x(0,p)
                    LVariablePtr p = Terms::lVariable(Sorts::intSort(), "P");
                    
                    //Symbol* var0Symbol = Signature::fetchOrDeclare(var->name+"0", { Sorts::intSort() }, toSort(var->type));
                    //TermPtr var0 = Terms::funcTerm(var0Symbol, {p});
                    
                    FormulaPtr eqWithoutQuantifiers = Formulas::equalityFormula(true,
                                                                                var->toTerm(it, p),
                                                                                var->toTerm(Theory::timeZero(), p));
                    eq = Formulas::universalFormula({p}, eqWithoutQuantifiers);
                }
                else
                {
                    // eq(it) := x(it) = x(0)
                    //Symbol* var0Symbol = Signature::fetchOrDeclare(var->name + "0", toSort(var->type));
                    //TermPtr var0 = Terms::funcTerm(var0Symbol, {});
                    
                    eq = Formulas::equalityFormula(true,
                                                   var->toTerm(it),
                                                   var->toTerm(Theory::timeZero()));
                }
                
                FormulaPtr f = timepointQuantified({it}, eq);
                
                // add property
                addProperty("constant_" + var->name, f);
            }
        }
    }
    
#pragma mark - Monotonicity Properties
    
    /*
     * Monotonicity propreties
     */
    
    void Properties::monotonicityProps()
    {
        for (auto it = vars.begin(); it != vars.end(); ++it) {
            const PVariable *v = (*it);
            if(monotonic.at(v) == Monotonicity::OTHER)
                continue;

            if (util::Configuration::instance().timepoints().getValue())
            {
                // term algebra representation of iteration requires
                // different monotonicity props
                addProperty("update_" + v->name, updatePropertyOfVar(v));

                if (strict.at(v))
                {
                    addProperty("injectivity_" + v->name, injectivityProp(v));
                    addProperty("strict_" + v->name, strictProp(v));
                }
                else
                {
                    addProperty("nonstrict_" + v->name, nonStrictProp(v));
                }
            } else {
                if (dense.at(v))
                {
                    if (strict.at(v))
                    {
                        // don't add updatePropertyOfVar here since dense prop is
                        // stronger and does not have an existential quantifier
                        //addProperty("update_" + v->name, updatePropertyOfVar(v));
                        addProperty("densestrict_" + v->name, denseStrictProp(v)); // also implies strictProp
                    } else {
                        addProperty("update_" + v->name, updatePropertyOfVar(v));
                        addProperty("nonstrict_" + v->name, nonStrictProp(v));
                        addProperty("dense_nonstrict" + v->name, denseNonStrictProp(v));
                    }
                } else {
                    addProperty("update_" + v->name, updatePropertyOfVar(v));
                    if (strict.at(v)) {
                        addProperty("strict_" + v->name, strictProp(v));
                    } else {
                        addProperty("nonstrict_" + v->name, nonStrictProp(v));
                    }
                }
            }
        }
    }
    
    /** forall i, v(i) = v(0) + i [v(0) - i if v is decreasing] */
    FormulaPtr Properties::denseStrictProp(const PVariable *v)
    {
        assert(updated.at(v));
        assert(monotonic.at(v) != Monotonicity::OTHER);
        assert(dense.at(v));
        assert(strict.at(v));
        assert(!util::Configuration::instance().timepoints().getValue());
        
        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It");
        
        InterpretedSymbol interp = (monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_PLUS
                                    : InterpretedSymbol::INT_MINUS);
        TermPtr v0 = v->toTerm(Theory::integerConstant(0));
        TermPtr lhsTerm = v->toTerm(i);
        TermPtr rhsTerm = Terms::funcTerm(Theory::getSymbol(interp), {v0, i});
        FormulaPtr eq = Formulas::equalityFormula(true, lhsTerm, rhsTerm);
        return timepointQuantified({i}, eq);
    }
    
    /** forall i j, i < j => v(i) < v(j) [v(j) < v(i) if v is
        decreasing] */
    FormulaPtr Properties::strictProp(const PVariable *v)
    {
        assert(updated.at(v));
        assert(monotonic.at(v) != Monotonicity::OTHER);
        assert(strict.at(v));

        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It1");
        LVariablePtr j = Terms::lVariable(Sorts::timeSort(), "It2");

        FormulaPtr f1 = Formulas::predicateFormula(Theory::timeLt(i, j));

        InterpretedSymbol interp = (monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_LESS
                                    : InterpretedSymbol::INT_GREATER);
        FormulaPtr f2 = Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(interp),
                                                                   { v->toTerm(i), v->toTerm(j) }));
        return timepointQuantified({i, j}, Formulas::implicationFormula(f1, f2));
    }

    /** forall i j, i < j => v(i) <= v(j) [v(j) <= v(i) if v is
        decreasing] */
    FormulaPtr Properties::nonStrictProp(const PVariable *v)
    {
        assert(updated.at(v));
        assert(monotonic.at(v) != Monotonicity::OTHER);
        assert(!strict.at(v));

        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It1");
        LVariablePtr j = Terms::lVariable(Sorts::timeSort(), "It2");

        FormulaPtr f1 = Formulas::predicateFormula(Theory::timeLt(i, j));

        InterpretedSymbol interp = (monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_LESS_EQUAL
                                    : InterpretedSymbol::INT_GREATER_EQUAL);
        FormulaPtr f2 = Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(interp),
                                                                   { v->toTerm(i), v->toTerm(j) }));
        return timepointQuantified({i,j}, Formulas::implicationFormula(f1, f2));
    }
    
    /** forall i j, i < j => v(j) + i < v(i) + j [v(i) + i < v(j) + j
        if v is decreasing] */
    FormulaPtr Properties::denseNonStrictProp(const PVariable *v)
    {
        assert(updated.at(v));
        assert(monotonic.at(v) != Monotonicity::OTHER);
        assert(dense.at(v));
        assert(!strict.at(v));
        assert(!util::Configuration::instance().timepoints().getValue());
        
        LVariablePtr i = Terms::lVariable(Sorts::intSort(), "It1");
        LVariablePtr j = Terms::lVariable(Sorts::intSort(), "It2");
        
        FormulaPtr f1 = Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_LESS),
                                                                   { i, j }));
        bool incr = (monotonic.at(v) == Monotonicity::INC);
        TermPtr t1 = Terms::funcTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                     { incr ? v->toTerm(j) : v->toTerm(i) , i });
        TermPtr t2 = Terms::funcTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                     { incr ? v->toTerm(i) : v->toTerm(j), j });
        FormulaPtr f2 = Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_LESS),
                                                                   { t1, t2 }));
        return timepointQuantified({i,j}, Formulas::implicationFormula(f1, f2));
    }

    /** forall i j. (v(i) = v(j) => i = j ) */
    FormulaPtr Properties::injectivityProp(const PVariable *v)
    {
        assert(monotonic.at(v) != Monotonicity::OTHER);
        assert(updated.at(v));
        assert(strict.at(v));
        
        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It1");
        LVariablePtr j = Terms::lVariable(Sorts::timeSort(), "It2");
        
        FormulaPtr imp = Formulas::implicationFormula(Formulas::equalityFormula(true, v->toTerm(i), v->toTerm(j)),
                                                      Formulas::equalityFormula(true, i, j));
        return timepointQuantified({i,j}, imp);
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
    FormulaPtr Properties::updatePropertyOfVar(const PVariable *v)
    {
        assert(updated.at(v));
        assert(monotonic.at(v) != Monotonicity::OTHER);
        
        LVariablePtr x = Terms::lVariable(Sorts::intSort(), "X");
        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It");
        TermPtr iPlusOne = Theory::timeSucc(i);
        
        InterpretedSymbol geOrLe = (monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER_EQUAL
                                    : InterpretedSymbol::INT_LESS_EQUAL);
        InterpretedSymbol gtOrLt = (monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER
                                    : InterpretedSymbol::INT_LESS);
        
        // build the disjunction
        std::vector<FormulaPtr> disj {};
        for (const auto& command : loop.commands)
        {
            // only take into account commands that do affect v
            if (!(command)->findAssignment(*v))
                continue;
            
            std::vector<FormulaPtr> conj { (command)->guard->toFormula(i) } ;
            if (dense.at(v))
            {
                conj.push_back(Formulas::equalityFormula(true, v->toTerm(i), x));
            }
            else
            {
                conj.push_back(Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(geOrLe),
                                                                 { x, v->toTerm(i) })));
                conj.push_back(Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(gtOrLt),
                                                                 { v->toTerm(iPlusOne), x })));
            }
            disj.push_back(Formulas::conjunctionFormula(conj));
        }
        
        // since v is monotonic, there should be at least one guard that updates it
        assert(disj.size() > 0);
        
        FormulaPtr f = Formulas::disjunctionFormula(disj);
        
        PredTermPtr p1 = Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                         { x, v->toTerm(Theory::timeZero()) });
        PredTermPtr p2 = Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER),
                                         { v->toTerm(loopCounterSymbol()), x });
        std::vector<FormulaPtr> conds { Formulas::predicateFormula(p1), Formulas::predicateFormula(p2) };
        
        return Formulas::universalFormula( { x }, Formulas::implicationFormula(Formulas::conjunctionFormula(conds),
                                                                               Formulas::existentialFormula( { i } , f)));
    }
    
#pragma mark - Translation of Assignments

    /*
     * Translation of guarded assignments
     */
    
    void Properties::translateAssignments()
    {
        static unsigned i = 0;
        for (auto it = loop.commands.begin(); it != loop.commands.end(); ++it) {
            addProperty("assignment_" + std::to_string(i++), commandToFormula(*it));
        }
    }

    // TODO this will probably be replaced by stepAxiom
    FormulaPtr Properties::commandToFormula(const GuardedCommand *c)
    {
        Assignment *a;
        std::vector<FormulaPtr> conj;

        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It1");
        TermPtr iPlusOne = Theory::timeSucc(i);
        
        for (auto it = vars.begin(); it != vars.end(); ++it)
        {
            const PVariable* v = (*it);
            // constant variables are constant symbols in formulas, nothing
            // to do then
            if (!updated.at(v))
                continue;
            
            if (isArrayType(v->type)) {
                if (util::Configuration::instance().arrayTheory().getValue()) {
                    // representation using array axiomatization
                    TermPtr store = v->toTerm(i);
                    for (auto itAsg = c->assignments.begin();
                         itAsg != c->assignments.end();
                         ++itAsg) {
                        a = *itAsg;
                        if (a->hasLhs(*v))
                            store = Terms::funcTerm(Theory::getSymbol(InterpretedSymbol::ARRAY_STORE),
                                                    { store, a->lhs->child(0)->toTerm(i), a->rhs->toTerm(i) });
                    }
                    conj.push_back(Formulas::equalityFormula(true,
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

        FormulaPtr f1;
        if (util::Configuration::instance().timepoints().getValue())
        {
            f1 = Formulas::conjunctionFormula({ c->guard->toFormula(i) });
        }
        else
        {
            FormulaPtr ige0 = Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                                         { i, Theory::integerConstant(0) } ));
            f1 = Formulas::conjunctionFormula({ c->guard->toFormula(i), ige0 });
        }
        FormulaPtr f2 = Formulas::conjunctionFormula(conj);
        
        return timepointQuantified({i}, Formulas::implicationFormula(f1, f2));
    }
    
    /** Given a scalar assignment v = e, return the formula v(i+1) = e(i) */
    FormulaPtr Properties::assignment(const Assignment *a,
                                    TermPtr index,
                                    TermPtr indexPlusOne)
    {
        PVariable * lhsVar = a->lhs->varInfo();
        assert(updated.at(lhsVar));
        
        return Formulas::equalityFormula(true,
                                   lhsVar->toTerm(indexPlusOne),
                                   a->rhs->toTerm(index));
    }
    
    /** Given an array assignment v[x] = e, return the formula v(i+1, x(i)) = e(i) */
    FormulaPtr Properties::arrayAssignment(const Assignment *a,
                                         TermPtr index,
                                         TermPtr indexPlusOne)
    {
        PVariable * lhsVar = a->lhs->varInfo();
        assert(updated.at(lhsVar));
        
        return Formulas::equalityFormula(true,
                                   lhsVar->toTerm(indexPlusOne,
                                                  a->lhs->child(0)->toTerm(index)),
                                   a->rhs->toTerm(index));
    }
    
    /** Given a scalar variable v, return the formula v(i+1) = v(i) */
    FormulaPtr Properties::nonAssignment(const PVariable *v,
                                       TermPtr index,
                                       TermPtr indexPlusOne)
    {
        assert(updated.at(v));
        
        return Formulas::equalityFormula(true,
                                   v->toTerm(indexPlusOne),
                                   v->toTerm(index));
    }
    
    /** Given an array variable v, return the formula forall p, cond => v(i+1, p) = v(i, p) */
    FormulaPtr Properties::arrayNonAssignment(const PVariable *v,
                                            const GuardedCommand *gc,
                                            TermPtr index,
                                            TermPtr indexPlusOne)
    {
        assert(updated.at(v));
        assert(isArrayType(v->type));
        
        LVariablePtr p = Terms::lVariable(Sorts::intSort(), "P");
        std::vector<FormulaPtr> conj;
        for (const auto& assignment : gc->assignments)
        {
            if (assignment->hasLhs(*v))
            {
                conj.push_back(Formulas::equalityFormula(false, p, assignment->lhs->child(0)->toTerm(index)));
            }
        }
        
        FormulaPtr eq = Formulas::equalityFormula(true,
                                                  v->toTerm(indexPlusOne, p),
                                                  v->toTerm(index, p));
        
        FormulaPtr f = Formulas::implicationFormula(Formulas::conjunctionFormula(conj), eq);
        
        return Formulas::universalFormula({p}, f);
    }
    
#pragma mark - Update predicates of arrays

    /*
     * Update predicates of arrays
     */
    void Properties::updatePredicatesOfArrays()
    {
        for (auto it = vars.begin(); it != vars.end(); ++it) {
            const PVariable *v = (*it);
            // only check updates array variables
            if (!isArrayType(v->type) || !updated.at(v))
                continue;
            
            if (util::Configuration::instance().existentialAxioms().getValue())
            {
                // these axioms introduce skolem symbols
                addProperty("stability_" + v->name, stabilityAxiom(v));
                addProperty("unique_update_" + v->name, uniqueUpdateAxiom(v));
            }
        }
    }
    
    /** forall i p, (forall j, !update_a(j, p)) => a(i, p) = a(0, p) */
    FormulaPtr Properties::stabilityAxiom(const PVariable *a)
    {
        assert(isArrayType(a->type));
        assert(updated.at(a));

        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It1");
        LVariablePtr j = Terms::lVariable(Sorts::timeSort(), "It2");
        LVariablePtr p = Terms::lVariable(Sorts::intSort(), "P");
        
        FormulaPtr f1 = timepointQuantified({j}, Formulas::negationFormula(arrayUpdatePredicate(a, j, p, nullptr)));
        
        FormulaPtr f2 = Formulas::equalityFormula(true,
                                                  a->toTerm(Theory::timeZero(), p),
                                                  a->toTerm(i, p));
        
        return timepointQuantified({i}, Formulas::universalFormula({p}, Formulas::implicationFormula(f1, f2)));
        
    }
    
    /** forall i k p v, (update_a(i, p, v) & (forall j, & j != i => !update_a(j, p)) & i < k) => a(k, p) = v */
    /* this is true only if the array is written at most once by the loop! */
    FormulaPtr Properties::uniqueUpdateAxiom(const PVariable *a)
    {
        assert(isArrayType(a->type));
        assert(updated.at(a));
        
        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It1");
        LVariablePtr j = Terms::lVariable(Sorts::timeSort(), "It2");
        LVariablePtr k = Terms::lVariable(Sorts::timeSort(), "It3");
        LVariablePtr p = Terms::lVariable(Sorts::intSort(), "P");
        LVariablePtr v = Terms::lVariable(toSort(a->type), "V");
        
        FormulaPtr f1 = Formulas::implicationFormula(Formulas::equalityFormula(false, i,j),
                                                     Formulas::negationFormula(arrayUpdatePredicate(a, j, p, nullptr)));
        FormulaPtr f2 = Formulas::conjunctionFormula(
            { Formulas::universalFormula({j}, f1),
              arrayUpdatePredicate(a, i, p, v),
              Formulas::predicateFormula(Theory::timeLt(i, k)) }
            );
        
        FormulaPtr f3 = Formulas::equalityFormula(true,
                                                  v,
                                                  a->toTerm(k, p));
        
        return timepointQuantified({i, k}, Formulas::universalFormula({p, v}, Formulas::implicationFormula(f2, f3)));
    }
    
    
    /** forall i k p v, (update_a(i, p, v) & (forall j, i < j => !update_a(j, p)) & i < k) =>
        a(k, p) = v
     * Not used currently! (instead the weaker but more efficient uniqueUpdateAxiom)
     */
    FormulaPtr Properties::lastUpdateAxiom(const PVariable *a)
    {
        assert(isArrayType(a->type));
        assert(updated.at(a));
        
        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It1");
        LVariablePtr j = Terms::lVariable(Sorts::timeSort(), "It2");
        LVariablePtr k = Terms::lVariable(Sorts::timeSort(), "It3");
        LVariablePtr p = Terms::lVariable(Sorts::intSort(), "P");
        LVariablePtr v = Terms::lVariable(toSort(a->type), "V");
        
        FormulaPtr f1 = Formulas::implicationFormula(Formulas::predicateFormula(Theory::timeLt(i, j)),
                                                     Formulas::negationFormula(arrayUpdatePredicate(a, j, p, nullptr)));
        FormulaPtr f2 = Formulas::conjunctionFormula(
            { Formulas::universalFormula({j}, f1),
              arrayUpdatePredicate(a, i, p, v),
              Formulas::predicateFormula(Theory::timeLt(i, k)) }
            );
        
        FormulaPtr f3 = Formulas::equalityFormula(true,
                                                  v,
                                                  a->toTerm(k, p));
        
        return timepointQuantified({i, k}, Formulas::universalFormula({p, v}, Formulas::implicationFormula(f2, f3)));
    }
    
    // if v is nullptr, updatePredicate with 2 args
    FormulaPtr Properties::arrayUpdatePredicate(const PVariable *a,
                                                TermPtr i,
                                                TermPtr p,
                                                TermPtr v)
    {
        std::vector<FormulaPtr> disj {};
        
        for(const auto& command : loop.commands)
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
    
    FormulaPtr Properties::arrayAssignmentConditions(const Assignment *asg,
                                                     const FExpression *guard,
                                                     TermPtr i,
                                                     TermPtr p,
                                                     TermPtr v)
    {
        std::vector<FormulaPtr> conj;
        conj.push_back(guard->toFormula(i));
        conj.push_back(Formulas::equalityFormula(true,
                                           p,
                                           asg->lhs->child(0)->toTerm(i)));
        if (v)
        {
            conj.push_back(Formulas::equalityFormula(true,
                                               v,
                                               asg->rhs->toTerm(i)));
        }
        
        return Formulas::conjunctionFormula(conj);
    }

    void Properties::preconditionsSatisfied()
    {
        int i=0;
        for (const auto& precondition : preconditions)
        {
            addProperty("precondition_" + std::to_string(i++),
                        precondition->toFormula(Theory::timeZero()));
        }
    }

#pragma mark - loop counter properties

    FuncTermPtr Properties::loopCounterSymbol()
    {
        // initialization note that the syntax of the guarded command
        // language does not allow special characters such as $
        Symbol* s = Signature::fetchOrDeclare("$n", Sorts::timeSort(), false, true);
        
        return Terms::funcTerm(s, {});
    }

    // $counter >= 0
    void Properties::loopCounterNonNegative()
    {
        if (!util::Configuration::instance().timepoints().getValue())
        {
            addProperty("loop_counter", Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                                                   { loopCounterSymbol(), Theory::integerConstant(0) })));
        }
    }

    // forall m, m < $counter => cond(m)
    void Properties::loopCondition()
    {
        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It");

        FormulaPtr f = Formulas::implicationFormula(Formulas::predicateFormula(Theory::timeLt(i, loopCounterSymbol())),
                                                    loop.loopCondition->toFormula(i));
        addProperty("loop_condition", timepointQuantified({i}, f));
    }

    // ~cond($counter)
    void Properties::loopExit()
    {
        FormulaPtr f = Formulas::negationFormula(loop.loopCondition->toFormula(loopCounterSymbol()));
        addProperty("loop_exit", f);
    }
    
#pragma mark - Symbol elimination properties
    
    void Properties::symbolEliminationAxioms()
    {
        for (auto it = vars.begin(); it != vars.end(); ++it) {
            const PVariable *v = (*it);
            if (updated.at(v))
                addSymbolEliminationAxioms(v);
        }
    }
    
    void Properties::addSymbolEliminationAxioms(const PVariable* v)
    {
        if (!updated.at(v))
            return; // v's symbol won't be eliminated, no need for axiom
        
        TermPtr empty = nullptr;
        unsigned arity = isArrayType(v->type) ? 1 : 0;
        std::vector<LVariablePtr> vars;
        
        TermPtr lhsCounter;
        TermPtr  rhsCounter;
        Symbol* s;
        TermPtr  lhsInit;
        TermPtr  rhsInit;
        
        if (isArrayType(v->type)
            && util::Configuration::instance().arrayTheory().getValue())
        {
            LVariablePtr p = Terms::lVariable(Sorts::intSort(), "P");
            vars.push_back(p);
            // array symbol
            assert (arity == 1);
            rhsCounter = v->toTerm(nullptr, p);
            lhsCounter = v->toTerm(loopCounterSymbol(), p);
            s = Signature::fetchOrDeclare(v->name + "$init", { Sorts::intSort() }, toSort(v->type));
            lhsInit = v->toTerm(Theory::integerConstant(0), p);
            rhsInit = Terms::funcTerm(s, {p});            
        } else {
            rhsCounter = v->toTerm(empty);
            lhsCounter = v->toTerm(loopCounterSymbol());
            s = Signature::fetchOrDeclare(v->name + "$init", toSort(v->type));
            lhsInit = v->toTerm(Theory::integerConstant(0));
            rhsInit = Terms::funcTerm(s, {});
        }
        
        addProperty("final_value_" + v->name, Formulas::universalFormula(vars, Formulas::equalityFormula(true, lhsCounter, rhsCounter)));
        addProperty("initial_value_" + v->name, Formulas::universalFormula(vars, Formulas::equalityFormula(true, lhsInit, rhsInit)));
    }

    void Properties::verificationGoal()
    {
        std::vector<FormulaPtr> conjuncts;
        for (const auto& postcondition : postconditions)
        {
            conjuncts.push_back(postcondition->toFormula(loopCounterSymbol()));
        }
        FormulaPtr goal = Formulas::negationFormula(Formulas::conjunctionFormula(conjuncts));

        // TODO mark this as negated conjecture in TPTP output
        addProperty("post_condition", goal);
    }

    void Properties::terminationGoal()
    {
        LVariablePtr i = Terms::lVariable(Sorts::timeSort(), "It");
        FormulaPtr goal = timepointQuantified({i}, loop.loopCondition->toFormula(i));

        // TODO mark this as negated conjecture
        addProperty("loop_termination", goal);
    }
}

