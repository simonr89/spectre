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
        constnessProps();
        monotonicityProps();
        translateAssignments();
        updatePredicatesOfArrays();
        loopCounterHypothesis();
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
        for (const auto& symbol : Signature::signature())
        {
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
            for (const auto& symbol : Signature::signature())
            {
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
            std::vector<std::shared_ptr<const Formula>> conjuncts;
            for (const auto& postcondition : _postconditions)
            {
                conjuncts.push_back(postcondition->toFormula(loopCounterSymbol()));
            }
            auto conjecture = Formulas::conjunctionFormula(conjuncts);
            
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

    void Properties::constnessProps()
    {
        for (const auto& var : _vars)
        {
            if (!_updated.at(var))
            {
                auto it = Terms::lVariable(Sorts::intSort(), "It");
                
                std::shared_ptr<const Formula> eq;
                // eq(it) := x(it) = x(0)
                if (!isArrayType(var->type))
                {
                    
                    Symbol* var0Symbol = Signature::fetchOrDeclare(var->name + "0", toSort(var->type));
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

    std::shared_ptr<const FuncTerm> Properties::loopCounterSymbol()
    {
        // initialization note that the syntax of the guarded command
        // language does not allow special characters such as $
        Symbol* s = Signature::fetchOrDeclare("$n", Sorts::intSort(), false, true);
        
        return Terms::funcTerm(s, {});
    }
    
    
    // 0 <= i < n
    std::shared_ptr<const Formula> Properties::iter(std::shared_ptr<const Term> i)
    {
        return Formulas::conjunctionFormula( {
            Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                              { i, Theory::integerConstant(0) } )),
            Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER),
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
                    addProperty("dense_strict_" + v->name, denseStrictProp(v)); // also implies strictProp
                } else {
                    addProperty("update_" + v->name, updatePropertyOfVar(v));
                    addProperty("non_strict_" + v->name, nonStrictProp(v));
                    addProperty("dense_non_strict" + v->name, denseNonStrictProp(v));
                }
            } else {
                addProperty("update_" + v->name, updatePropertyOfVar(v));
                if (_strict.at(v)) {
                    addProperty("strict_" + v->name, strictProp(v));
                } else {
                    addProperty("non_strict_" + v->name, nonStrictProp(v));
                }
            }
        }
    }
    
    /** forall i, v(i) = v(0) + i [v(0) - i if v is decreasing] */
    std::shared_ptr<const logic::Formula> Properties::denseStrictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(_dense.at(v));
        assert(_strict.at(v));
        
        auto i = Terms::lVariable(Sorts::intSort(), "It");
        
        InterpretedSymbol interp = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_PLUS
                                    : InterpretedSymbol::INT_MINUS);
        auto v0 = v->toTerm(Theory::integerConstant(0));
        auto lhsTerm = v->toTerm(i);
        auto rhsTerm = Terms::funcTerm(Theory::getSymbol(interp), {v0, i});
        auto eq = Formulas::equalityFormula(true, lhsTerm, rhsTerm);
        return Formulas::universalFormula({i}, eq);
    }
    
    /** forall i j, j > i => v(j) > v(i) [v(j) < v(i) if v is
     decreasing] */
    std::shared_ptr<const logic::Formula> Properties::strictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(_dense.at(v));
        assert(_strict.at(v));
        
        auto i = Terms::lVariable(Sorts::intSort(), "It1");
        auto j = Terms::lVariable(Sorts::intSort(), "It2");
        
        InterpretedSymbol interp = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER
                                    : InterpretedSymbol::INT_LESS);
        auto imp = (Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER),
                                                                 {j, i})),
                    Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(interp),
                                                                 { v->toTerm(j), v->toTerm(i) })));
        return Formulas::universalFormula({i,j}, imp);
    }
    
    /** forall i j, j >= i => v(i) + j >= v(j) + i [v(j) + j >= v(i) + i
     if v is decreasing] */
    std::shared_ptr<const logic::Formula> Properties::denseNonStrictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(_dense.at(v));
        assert(!_strict.at(v));
        
        auto i = Terms::lVariable(Sorts::intSort(), "It1");
        auto j = Terms::lVariable(Sorts::intSort(), "It2");
        
        bool incr = (_monotonic.at(v) == Monotonicity::INC);
        auto lhs = Terms::funcTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                     { incr ? v->toTerm(i) : v->toTerm(j), j });
        auto rhs = Terms::funcTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                     { incr ? v->toTerm(j) : v->toTerm(i), i });
        auto imp = Formulas::implicationFormula(Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                                 { j, i })),
                                                 Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                                 { lhs, rhs })));
        return Formulas::universalFormula({i,j}, imp);
    }
    
    /** forall i j, j >= i => v(j) >= v(i) [v(j) <= v(i) if v is
     decreasing] */
    std::shared_ptr<const logic::Formula> Properties::nonStrictProp(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        assert(!_strict.at(v));
        
        auto i = Terms::lVariable(Sorts::intSort(), "It1");
        auto j = Terms::lVariable(Sorts::intSort(), "It2");
        
        InterpretedSymbol interp = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER_EQUAL
                                    : InterpretedSymbol::INT_LESS_EQUAL);
        auto imp = Formulas::implicationFormula(Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                                 { i, j })),
                    Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(interp),
                                                                 { v->toTerm(i), v->toTerm(j) })));
        return Formulas::universalFormula({i,j}, imp);
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
    std::shared_ptr<const logic::Formula> Properties::updatePropertyOfVar(const PVariable *v)
    {
        assert(_updated.at(v));
        assert(_monotonic.at(v) != Monotonicity::OTHER);
        
        auto x = Terms::lVariable(Sorts::intSort(), "X");
        auto i = Terms::lVariable(Sorts::intSort(), "It");
        auto iPlusOne = Terms::funcTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                          {i, Theory::integerConstant(1)});
        
        InterpretedSymbol geOrLe = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER_EQUAL
                                    : InterpretedSymbol::INT_LESS_EQUAL);
        InterpretedSymbol gtOrLt = (_monotonic.at(v) == Monotonicity::INC
                                    ? InterpretedSymbol::INT_GREATER
                                    : InterpretedSymbol::INT_LESS);
        
        // build the disjunction
        std::vector<std::shared_ptr<const Formula>> disj {};
        for (const auto& command : _loop.commands)
        {
            // only take into account commands that do affect v
            if (!(command)->findAssignment(*v))
                continue;
            
            std::vector<std::shared_ptr<const Formula>> conj { (command)->guard->toFormula(i) } ;
            if (_dense.at(v))
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
        
        auto f = Formulas::conjunctionFormula( { iter(i), Formulas::disjunctionFormula(disj) } );
        
        auto p1 = Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                    { x, v->toTerm(Theory::integerConstant(0)) });
        auto p2 = Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER),
                                    { v->toTerm(loopCounterSymbol()), x });
        std::vector<std::shared_ptr<const Formula>> conds { Formulas::predicateFormula(p1), Formulas::predicateFormula(p2) };
        
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
        for (auto it = _loop.commands.begin(); it != _loop.commands.end(); ++it) {
            addProperty("assignment_" + std::to_string(i++), commandToFormula(*it));
        }
    }
    
    std::shared_ptr<const logic::Formula> Properties::commandToFormula(const GuardedCommand *c)
    {
        Assignment *a;
        std::vector<std::shared_ptr<const Formula>> conj;
        
        auto i = Terms::lVariable(Sorts::intSort(), "It1");
        auto iPlusOne = Terms::funcTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                      { i, Theory::integerConstant(1) } );
        
        for (auto it = _vars.begin(); it != _vars.end(); ++it)
        {
            const PVariable* v = (*it);
            // constant variables are constant symbols in formulas, nothing
            // to do then
            if (!_updated.at(v))
                continue;
            
            if (isArrayType(v->type)) {
                if (util::Configuration::instance().arrayTheory().getValue()) {
                    // representation using array axiomatization
                    auto store = v->toTerm(i);
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
        auto iGreaterEqual0 = Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                           { i, Theory::integerConstant(0) } ));
        auto f1 = Formulas::conjunctionFormula({ c->guard->toFormula(i), iGreaterEqual0});
        auto f2 = Formulas::conjunctionFormula(conj);
        
        return Formulas::universalFormula( { i }, Formulas::implicationFormula(f1, f2));
    }
    
    /** Given a scalar assignment v = e, return the formula v(i+1) = e(i) */
    std::shared_ptr<const logic::Formula> Properties::assignment(const Assignment *a,
                                    std::shared_ptr<const logic::Term> index,
                                    std::shared_ptr<const logic::Term> indexPlusOne)
    {
        PVariable * lhsVar = a->lhs->varInfo();
        assert(_updated.at(lhsVar));
        
        return Formulas::equalityFormula(true,
                                   lhsVar->toTerm(indexPlusOne),
                                   a->rhs->toTerm(index));
    }
    
    /** Given an array assignment v[x] = e, return the formula v(i+1, x(i)) = e(i) */
    std::shared_ptr<const logic::Formula> Properties::arrayAssignment(const Assignment *a,
                                         std::shared_ptr<const logic::Term> index,
                                         std::shared_ptr<const logic::Term> indexPlusOne)
    {
        PVariable * lhsVar = a->lhs->varInfo();
        assert(_updated.at(lhsVar));
        
        return Formulas::equalityFormula(true,
                                   lhsVar->toTerm(indexPlusOne,
                                                  a->lhs->child(0)->toTerm(index)),
                                   a->rhs->toTerm(index));
    }
    
    /** Given a scalar variable v, return the formula v(i+1) = v(i) */
    std::shared_ptr<const logic::Formula> Properties::nonAssignment(const PVariable *v,
                                       std::shared_ptr<const logic::Term> index,
                                       std::shared_ptr<const logic::Term> indexPlusOne)
    {
        assert(_updated.at(v));
        
        return Formulas::equalityFormula(true,
                                   v->toTerm(indexPlusOne),
                                   v->toTerm(index));
    }
    
    /** Given an array variable v, return the formula forall j, cond => v(i+1, j) = v(i, j) */
    std::shared_ptr<const logic::Formula> Properties::arrayNonAssignment(const PVariable *v,
                                            const GuardedCommand *gc,
                                            std::shared_ptr<const logic::Term> index,
                                            std::shared_ptr<const logic::Term> indexPlusOne)
    {
        assert(_updated.at(v));
        assert(isArrayType(v->type));
        
        auto j = Terms::lVariable(Sorts::intSort(), "It2");
        std::vector<std::shared_ptr<const logic::Formula>> conj;
        for (const auto& assignment : gc->assignments)
        {
            if (assignment->hasLhs(*v))
            {
                conj.push_back(Formulas::equalityFormula(false, j, assignment->lhs->child(0)->toTerm(index)));
            }
        }
        
        auto eq = Formulas::equalityFormula(true,
                                          v->toTerm(indexPlusOne, j),
                                          v->toTerm(index, j));
        
        std::shared_ptr<const Formula> f = Formulas::implicationFormula(Formulas::conjunctionFormula(conj), eq);
        
        return Formulas::universalFormula({ j }, f);
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
            if (!isArrayType(v->type) || !_updated.at(v))
                continue;
            
            if (util::Configuration::instance().existentialAxioms().getValue())
            {
                // these axioms introduce skolem symbols
                addProperty("stability_" + v->name, stabilityAxiom(v));
                addProperty("unique_update_" + v->name, uniqueUpdateAxiom(v));
            }
        }
    }
    
    /** forall p, (forall i, iter(i) => !update_a(i, p)) => a(n, p) = a(0, p) */
    std::shared_ptr<const logic::Formula> Properties::stabilityAxiom(const PVariable *a)
    {
        assert(isArrayType(a->type));
        assert(_updated.at(a));
        
        auto i = Terms::lVariable(Sorts::intSort(), "It");
        auto p = Terms::lVariable(Sorts::intSort(), "P");
        
        auto fa = Formulas::implicationFormula(iter(i), Formulas::negationFormula(arrayUpdatePredicate(a, i, p, nullptr)));
        
        auto fb = Formulas::universalFormula( {i}, fa);
        auto fc = Formulas::equalityFormula(true,
                                          a->toTerm(Theory::integerConstant(0), p),
                                          a->toTerm(loopCounterSymbol(), p));
        
        return Formulas::universalFormula( {p}, Formulas::implicationFormula(fb, fc));
        
    }
    
    /** forall i p v, (iter(i) & update_a(i, p, v) & (forall j, iter(j) & j != i => !update_a(j, p))) => a(n, p) = v */
    /* this is true only if the array is written at most once by the loop! */
    std::shared_ptr<const logic::Formula> Properties::uniqueUpdateAxiom(const PVariable *a)
    {
        assert(isArrayType(a->type));
        assert(_updated.at(a));
        
        auto i = Terms::lVariable(Sorts::intSort(), "It1");
        auto j = Terms::lVariable(Sorts::intSort(), "It2");
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
        return Formulas::universalFormula({i, p, v}, Formulas::implicationFormula(fb, fc));
    }
    
    
    /** forall i p v, (iter(i) & update_a(i, p, v) & (forall j, iter(j) & j > i => !update_a(j, p))) => a(n, p) = v
     * Not used currently! (instead the weaker but more efficient uniqueUpdateAxiom)
     */
    std::shared_ptr<const logic::Formula> Properties::lastUpdateAxiom(const PVariable *a)
    {
        assert(isArrayType(a->type));
        assert(_updated.at(a));
        
        auto i = Terms::lVariable(Sorts::intSort(), "It1");
        auto j = Terms::lVariable(Sorts::intSort(), "It2");
        auto p = Terms::lVariable(Sorts::intSort(), "P");
        auto v = Terms::lVariable(toSort(a->type), "V");
        
        auto gt = Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER), {j, i});
        auto fa = Formulas::implicationFormula(Formulas::conjunctionFormula({ Formulas::predicateFormula(gt), iter(j) }),
                                             Formulas::negationFormula(arrayUpdatePredicate(a, j, p, nullptr)));
        auto fb = Formulas::conjunctionFormula(
                                             { Formulas::universalFormula({j}, fa),
                                                 arrayUpdatePredicate(a, i, p, v),
                                                 iter(i) }
                                             );
        
        auto fc = Formulas::equalityFormula(true,
                                          v,
                                          a->toTerm(loopCounterSymbol(), p));
        
        return Formulas::universalFormula({i, p, v}, Formulas::implicationFormula(fb, fc));
    }
    
    // if v is nullptr, updatePredicate with 2 args
    std::shared_ptr<const logic::Formula> Properties::arrayUpdatePredicate(const PVariable *a,
                                              std::shared_ptr<const logic::Term> i,
                                              std::shared_ptr<const logic::Term> p,
                                              std::shared_ptr<const logic::Term> v)
    {
        std::vector<std::shared_ptr<const Formula>> disj {};
        
        for(const auto& command : _loop.commands)
        {
            for (const auto& assignment : command->assignments)
            {
                if (assignment->hasLhs(*a))
                    disj.push_back(arrayAssignmentConditions(assignment, command->guard, i, p, v));
            }
        }
        
        // a is updated, this shouldn't be empty
        assert(!disj.empty());
        
        return Formulas::disjunctionFormula(disj);
    }
    
    std::shared_ptr<const logic::Formula> Properties::arrayAssignmentConditions(const Assignment *asg,
                                                   const FExpression *guard,
                                                   std::shared_ptr<const Term> i,
                                                   std::shared_ptr<const Term> p,
                                                   std::shared_ptr<const Term> v)
    {
        std::vector<std::shared_ptr<const Formula>> conj;
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

#pragma mark - loop counter properties

    // counter >= 0
    void Properties::loopCounterHypothesis()
    {
        addProperty("loop_counter", Formulas::predicateFormula(Terms::predTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                                      { loopCounterSymbol(), Theory::integerConstant(0) })));
    }
    
#pragma mark - loop condition properties

    // forall i, iter(i) => cond(i)
    void Properties::loopConditionHypothesis()
    {
        auto i = Terms::lVariable(Sorts::intSort(), "It");
        
        addProperty("loop_condition", Formulas::universalFormula({i},
                                                                 Formulas::implicationFormula(iter(i),
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
    
    void Properties::addSymbolEliminationAxioms(const PVariable* v)
    {
        if (!_updated.at(v))
            return; // v's symbol won't be eliminated, no need for axiom
        
        std::shared_ptr<const LVariable> i = Terms::lVariable(Sorts::intSort());
        std::shared_ptr<const Term> empty = nullptr;
        unsigned arity = isArrayType(v->type) ? 1 : 0;
        
        std::shared_ptr<const Term> lhsCounter;
        std::shared_ptr<const Term>  rhsCounter;
        Symbol* s;
        std::shared_ptr<const Term>  lhsInit;
        std::shared_ptr<const Term>  rhsInit;
        
        std::vector<std::shared_ptr<const LVariable>> vars;
        
        if (isArrayType(v->type))
        {
            // array symbol
            assert (arity == 1);
            rhsCounter = v->toTerm(empty, i);
            lhsCounter = v->toTerm(loopCounterSymbol(), i);
            s = Signature::fetchOrDeclare(v->name + "$init", { Sorts::intSort() }, toSort(v->type));
            lhsInit = v->toTerm(Theory::integerConstant(0), i);
            rhsInit = Terms::funcTerm(s, {i});
            vars.push_back(i);
        }
        else
        {
            rhsCounter = v->toTerm(empty);
            lhsCounter = v->toTerm(loopCounterSymbol());
            s = Signature::fetchOrDeclare(v->name + "$init", toSort(v->type));
            lhsInit = v->toTerm(Theory::integerConstant(0));
            rhsInit = Terms::funcTerm(s, {});
        }
        
        addProperty("final_value_" + v->name, Formulas::universalFormula(vars, Formulas::equalityFormula(true, lhsCounter, rhsCounter)));
        addProperty("initial_value_" + v->name, Formulas::universalFormula(vars, Formulas::equalityFormula(true, lhsInit, rhsInit)));
    }
}

