#include "Properties.hpp"

#include <cassert>
#include <iostream>

#include "logic/Signature.hpp"
#include "logic/Theory.hpp"

using namespace logic;

namespace program {

  void Properties::addPrecondition(FExpression *e)
  {
    addProperty(e->toFormula(Theory::integerConstant(0)));
  }

  void Properties::addPostcondition(FExpression *e)
  {
    // empty term list as index so that e->toFormula(i) evaluates to an
    // expression in the non-extended language)
    Term* i = nullptr;
    
    _postconditions.push_front(e->toFormula(i));
  }

  FuncTerm* Properties::loopCounterSymbol()
  {
    // initialization note that the syntax of the guarded command
    // language does not allow special characters such as $
    static Symbol* s = new Symbol("$counter", Sort::intSort());
    s->makeColored();

    return new FuncTerm(s, {});
  }

  void Properties::analyze()
  {
    monotonicityProps();
    translateAssignments();
    updatePredicatesOfArrays();
    symbolEliminationAxioms();
    loopCounterHypothesis();
    loopConditionHypothesis();
  }

  void Properties::outputTPTP(std::ostream& ostr)
  {
    std::list<Formula*> goalUnits {};
    if (! _postconditions.empty()) {
      // add negated loop condition to assumptions + negated goal (in non extended language)
      Term* i = nullptr;
      Formula *f = _loop.loopCondition()->toFormula(i);
      // this is an axiom only so that it is not output as invariant by the filtering mechanism
      goalUnits.push_front(new NegationFormula(f));
      
      f = new ConjunctionFormula(_postconditions);
      goalUnits.push_front(new NegationFormula(f));
    }

    unsigned i = 0;
    for (auto it = Sort::sortsBegin(); it != Sort::sortsEnd(); ++it) {
      if ((*it).isUserDefined())
        ostr << (*it).declareTPTP("decl" + std::to_string(i++)) << std::endl;
    }
    
    for (auto it = Symbol::sigBegin(); it != Symbol::sigEnd(); ++it) {
      if ((*it).isUserDefined())
        ostr << (*it).declareTPTP("decl" + std::to_string(i++)) << std::endl;
    }

    for (auto it = _properties.begin(); it != _properties.end(); ++it) {
      ostr << (*it)->declareTPTP("decl" + std::to_string(i++)) << std::endl;
    }

    for (auto it = goalUnits.begin(); it != goalUnits.end(); ++it) {
      ostr << (*it)->declareTPTP("decl" + std::to_string(i++)) << std::endl;
    }
  }

  /*
   * Monotonicity propreties
   */

  void Properties::monotonicityProps()
  {    
    for (auto it = _vars.begin(); it != _vars.end(); ++it) {
      PVariable *v = (*it).second;
      if (!v->isMonotonic())
        continue;
      
      if (v->isDense()) {  
        if (v->isStrict()) {
          // don't add updatePropertyOfVar here since dense prop is
          // stronger and does not have an existential quantifier
          //addProperty(updatePropertyOfVar(v));
          addProperty(denseStrictProp(v)); // also implies strictProp
        } else {
          addProperty(updatePropertyOfVar(v));
          addProperty(nonStrictProp(v));
          addProperty(denseNonStrictProp(v));
        }
      } else {
        addProperty(updatePropertyOfVar(v));
        if (v->isStrict()) {
          addProperty(strictProp(v));
        } else {
          addProperty(nonStrictProp(v));
        }
      } 
    }
  }

  /** forall i, v(i) = v(0) + i [v(0) - i if v is decreasing] */
  Formula* Properties::denseStrictProp(PVariable *v)
  {
    assert(v->isUpdated());
    assert(v->isMonotonic());
    assert(v->isDense());
    assert(v->isStrict());

    LVariable* i = new LVariable(Sort::intSort());

    InterpretedSymbol interp = (v->monotonicity() > 0
                                ? InterpretedSymbol::INT_PLUS
                                : InterpretedSymbol::INT_MINUS);
    Term* v0 = v->toTerm(Theory::integerConstant(0));
    Term* lhsTerm = v->toTerm(i);
    FuncTerm* rhsTerm = new FuncTerm(Theory::getSymbol(interp), {v0, i});
    return EqualityFormula(true, lhsTerm, rhsTerm).quantify();
  }

  /** forall i j, j > i => v(j) > v(i) [v(j) < v(i) if v is
      decreasing] */
  Formula *Properties::strictProp(PVariable *v)
  {
    assert(v->isUpdated());
    assert(v->isMonotonic());
    assert(!v->isDense());
    assert(v->isStrict());

    LVariable* i = new LVariable(Sort::intSort());
    LVariable* j = new LVariable(Sort::intSort());

    InterpretedSymbol interp = (v->monotonicity() > 0
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
  Formula* Properties::denseNonStrictProp(PVariable *v)
  {
    assert(v->isUpdated());
    assert(v->isMonotonic());
    assert(v->isDense());
    assert(!v->isStrict());

    LVariable* i = new LVariable(Sort::intSort());
    LVariable* j = new LVariable(Sort::intSort());

    bool incr = v->monotonicity() > 0;
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
   Formula *Properties::nonStrictProp(PVariable *v)
  {
    assert(v->isUpdated());
    assert(v->isMonotonic());
    assert(!v->isStrict());

    LVariable* i = new LVariable(Sort::intSort());
    LVariable* j = new LVariable(Sort::intSort());

    InterpretedSymbol interp = (v->monotonicity() > 0
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
  Formula *Properties::updatePropertyOfVar(PVariable *v)
  {
    assert(v->isUpdated());
    assert(v->isMonotonic());

    LVariable* x = new LVariable(Sort::intSort());
    LVariable* i = new LVariable(Sort::intSort());
    FuncTerm* iPlusOne = new FuncTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                      {i, Theory::integerConstant(1)});
    
    bool dense = v->isDense();
    InterpretedSymbol geOrLe = (v->monotonicity() > 0
                                ? InterpretedSymbol::INT_GREATER_EQUAL
                                : InterpretedSymbol::INT_LESS_EQUAL);
    InterpretedSymbol gtOrLt = (v->monotonicity() > 0
                                ? InterpretedSymbol::INT_GREATER
                                : InterpretedSymbol::INT_LESS);
    
    // build the disjunction
    std::list<Formula*> disj {};
    for (auto it = _loop.commands().begin(); it != _loop.commands().end(); ++it) {
      // only take into account commands that do affect v
      if (!(*it)->findAssignment(*v))
        continue;
      
      std::list<Formula*> conj { (*it)->guard()->toFormula(i) } ;
      if (dense) {
        conj.push_front(new EqualityFormula(true, v->toTerm(i), x));
      } else {
        conj.push_front(new PredicateFormula(new PredTerm(Theory::getSymbol(geOrLe),
                                                          { x, v->toTerm(i) })));
        conj.push_front(new PredicateFormula(new PredTerm(Theory::getSymbol(gtOrLt),
                                                          { v->toTerm(iPlusOne), x })));
      }
      disj.push_front(new ConjunctionFormula(conj));
    }

    // since v is monotonic, there should be at least one guard that updates it
    assert(disj.size() > 0);

    Formula *f = new ConjunctionFormula( { iter(i), new DisjunctionFormula(disj) } );

    PredTerm *p1 = new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                { x, v->toTerm(Theory::integerConstant(0)) });
    PredTerm *p2 = new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER),
                                { v->toTerm(loopCounterSymbol()), x });
    std::list<Formula*> conds { new PredicateFormula(p1), new PredicateFormula(p2) };
    
    return new UniversalFormula( { x }, new ImplicationFormula(new ConjunctionFormula(conds),     
                                                               new ExistentialFormula( { i } , f)));
  }

  /*
   * Translation of guarded assignments
   */

  void Properties::translateAssignments()
  {
    for (auto it = _loop.commands().begin(); it != _loop.commands().end(); ++it) {
      addProperty(commandToFormula(*it));
    }
  }

  Formula *Properties::commandToFormula(GuardedCommand *c)
  {
    Assignment *a;
    std::list<Formula*> conj {};

    LVariable* i = new LVariable(Sort::intSort());
    Term* iPlusOne = new FuncTerm(Theory::getSymbol(InterpretedSymbol::INT_PLUS),
                                  { i, Theory::integerConstant(1) } );

    for (auto it = _vars.begin(); it != _vars.end(); ++it) {
      PVariable* v = (*it).second;
      // constant variables are constant symbols in formulas, nothing
      // to do then
      if (!v->isUpdated())
        continue;

      if (isArrayType(v->vtype())) {
        for (auto itAsg = c->assignments().begin();
             itAsg != c->assignments().end();
             ++itAsg) {
          a = *itAsg;
          if (a->hasLhs(*v))
            conj.push_front(arrayAssignment(a, i, iPlusOne));
        }
        // arrayNonAssignment needlessly complicates the prover's life 
        conj.push_front(arrayNonAssignment(v, c, i, iPlusOne));
      } else {
        // only one assignment to a given scalar variable is possible
        // in a command (unlike array variables)
        a = c->findAssignment(*v);
        if (a) {
          conj.push_front(assignment(a, i, iPlusOne));
        } else {
          // no assignment to v in this command
          conj.push_front(nonAssignment(v, i, iPlusOne));
        }
      }
    }

    assert(conj.size() > 0);
    Formula *f1 = new ConjunctionFormula( { c->guard()->toFormula(i), iter(i) } );
    Formula *f2 = new ConjunctionFormula(conj);
    
    return new UniversalFormula( { i }, new ImplicationFormula(f1, f2));

  }

  /** Given a scalar assignment v = e, return the formula v(i+1) = e(i) */
  Formula* Properties::assignment(Assignment *a,
                                  Term* index,
                                  Term* indexPlusOne)
  {
    PVariable * lhsVar = a->lhs()->varInfo();
    assert(lhsVar->isUpdated());

    return new EqualityFormula(true,
                               lhsVar->toTerm(indexPlusOne),
                               a->rhs()->toTerm(index));
  }

  /** Given an array assignment v[x] = e, return the formula v(i+1, x(i)) = e(i) */
  Formula* Properties::arrayAssignment(Assignment *a,
                                       Term* index,
                                       Term* indexPlusOne)
  {
    PVariable * lhsVar = a->lhs()->varInfo();
    assert(lhsVar->isUpdated());

    return new EqualityFormula(true,
                               lhsVar->toTerm(indexPlusOne,
                                              a->lhs()->child(0)->toTerm(index)),
                               a->rhs()->toTerm(index));
  }

  /** Given a scalar variable v, return the formula v(i+1) = v(i) */
  Formula* Properties::nonAssignment(PVariable *v,
                                     Term* index,
                                     Term* indexPlusOne)
  {
    assert(v->isUpdated());

    return new EqualityFormula(true,
                               v->toTerm(indexPlusOne),
                               v->toTerm(index));
  }

  /** Given an array variable v, return the formula forall j, cond => v(i+1, j) = v(i, j) */
  // TODO Currently not used
  Formula* Properties::arrayNonAssignment(PVariable *v,
                                          GuardedCommand *gc,
                                          Term* index,
                                          Term* indexPlusOne)
  {
    assert(v->isUpdated());
    assert(isArrayType(v->vtype()));
    
    LVariable* j = new LVariable(Sort::intSort());
    std::list<Formula*> conj {};
    for (auto it = gc->assignments().begin();
         it != gc->assignments().end();
         ++it) {
      if ((*it)->hasLhs(*v))
        conj.push_front(new EqualityFormula(false,
                                            j,
                                            (*it)->lhs()->child(0)->toTerm(index)));      
    }
    
    Formula *eq = new EqualityFormula(true,
                                      v->toTerm(indexPlusOne, j),
                                      v->toTerm(index, j));

    Formula *f = new ImplicationFormula(new ConjunctionFormula(conj), eq);
    
    return new UniversalFormula({ j }, f);
  }

  /*
   * Update predicates of arrays
   */
  void Properties::updatePredicatesOfArrays()
  {
    for (auto it = _vars.begin(); it != _vars.end(); ++it) {
      PVariable *v = (*it).second;
      // only check updates array variables
      if (!isArrayType(v->vtype()) || !v->isUpdated())
        continue;
      
      addProperty(stabilityAxiom(v));
      addProperty(uniqueUpdateAxiom(v));
    }
  }

  // counter >= 0
  void Properties::loopCounterHypothesis()
  {
    addProperty(new PredicateFormula(new PredTerm(Theory::getSymbol(InterpretedSymbol::INT_GREATER_EQUAL),
                                                  { loopCounterSymbol(), Theory::integerConstant(0) })));
  }

  // forall i, iter(i) => cond(i)
  void Properties::loopConditionHypothesis()
  {
    LVariable* i = new LVariable(Sort::intSort());

    addProperty(new UniversalFormula({i},
                                     new ImplicationFormula(iter(i),
                                                            _loop.loopCondition()->toFormula(i))));
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
  
  // if v is nullptr, updatePredicate with 2 args
  Formula* Properties::arrayUpdatePredicate(PVariable *a,
                                            Term* i,
                                            Term* p,
                                            Term* v)
  {
    std::list<Formula*> disj {};

    for (auto itCmd = _loop.commands().begin(); itCmd != _loop.commands().end(); ++itCmd) {
      GuardedCommand *gc = *itCmd;
      
      for (auto itAsg = gc->assignments().begin(); itAsg != gc->assignments().end(); ++itAsg) {
        Assignment *asg = *itAsg;
        
        if (asg->hasLhs(*a))
          disj.push_front(arrayAssignmentConditions(asg, gc->guard(), i, p, v));
      }
    }

    // a is updated, this shouldn't be empty
    assert(!disj.empty());
    
    return new DisjunctionFormula(disj);
  }

  Formula* Properties::arrayAssignmentConditions(Assignment *asg,
                                                 FExpression *guard,
                                                 Term* i,
                                                 Term* p,
                                                 Term* v)
  {
    std::list<Formula*> conj;
    conj.push_front(guard->toFormula(i));
    conj.push_front(new EqualityFormula(true,
                                        p,
                                        asg->lhs()->child(0)->toTerm(i)));
    if (v)
      conj.push_front(new EqualityFormula(true,
                                          v,
                                          asg->rhs()->toTerm(i)));
    
    return new ConjunctionFormula(conj);
  }

  /** forall p, (forall i, iter(i) => !update_a(i, p)) => a(n, p) = a(0, p) */
  Formula* Properties::stabilityAxiom(PVariable *a)
  {
    assert(isArrayType(a->vtype()));
    assert(a->isUpdated());

    LVariable* i = new LVariable(Sort::intSort());
    LVariable* p = new LVariable(Sort::intSort());

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
  Formula* Properties::uniqueUpdateAxiom(PVariable *a)
  {
    assert(isArrayType(a->vtype()));
    assert(a->isUpdated());

    LVariable* i = new LVariable(Sort::intSort());
    LVariable* j = new LVariable(Sort::intSort());
    LVariable* p = new LVariable(Sort::intSort());
    LVariable* v = new LVariable(toSort(a->vtype()));

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
  Formula* Properties::lastUpdateAxiom(PVariable *a)
  {
    assert(isArrayType(a->vtype()));
    assert(a->isUpdated());

    LVariable* i = new LVariable(Sort::intSort());
    LVariable* j = new LVariable(Sort::intSort());
    LVariable* p = new LVariable(Sort::intSort());
    LVariable* v = new LVariable(toSort(a->vtype()));

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

  void Properties::symbolEliminationAxioms()
  {
    for (auto it = _vars.begin(); it != _vars.end(); ++it) {
      PVariable *v = (*it).second;
      if (v->isUpdated())
        addSymbolEliminationAxioms(v);
    }   
  }

  void Properties::addSymbolEliminationAxioms(PVariable *v)
  {
    if (!v->isUpdated())
      return; // v's symbol won't be eliminated, no need for axiom

    LVariable* i = new LVariable(Sort::intSort());
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
      s = new Symbol(v->name() + "$init", { Sort::intSort() }, toSort(v->vtype()));
      lhsInit = v->toTerm(Theory::integerConstant(0), i);
      rhsInit = new FuncTerm(s, {i});
    } else {
      rhsCounter = v->toTerm(empty);
      lhsCounter = v->toTerm(loopCounterSymbol());
      s = new Symbol(v->name() + "$init", toSort(v->vtype()));
      lhsInit = v->toTerm(Theory::integerConstant(0));
      rhsInit = new FuncTerm(s, {});
    }    
    
    addProperty(EqualityFormula(true, lhsCounter, rhsCounter).quantify());
    addProperty(EqualityFormula(true, lhsInit, rhsInit).quantify());
  }
}
