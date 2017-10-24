#ifndef __Properties__
#define __Properties__

#include <list>
#include <map>
#include "logic/Formula.hpp"
#include "logic/Sort.hpp"
#include "logic/Term.hpp"
#include "program/Expression.hpp"
#include "program/GuardedCommandCollection.hpp"
#include "program/Variable.hpp"
#include "program/Type.hpp"

namespace program {

  class Properties
  {
  public:
    
    Properties(GuardedCommandCollection& loop, std::map<std::string, PVariable*>& vars) :
      _loop(loop),
      _vars(vars),
      _properties(),
      _postconditions()
    {}
    
    ~Properties() {}

    void addPrecondition(FExpression *e);

    void addPostcondition(FExpression *e);

    void analyze();

    void outputTPTP();

  protected:
    GuardedCommandCollection& _loop;

    std::map<std::string, PVariable*>& _vars;

    // properties of the program
    std::list<logic::Formula*> _properties;

    std::list<logic::Formula*> _postconditions;

    void addProperty(logic::Formula* f) { _properties.push_front(f); }
    
    static unsigned toVampireSort(Type t);
    // the loop counter ($counter)
    static logic::FuncTerm* loopCounterSymbol();
    static logic::FuncTerm* constant(int n);

    static logic::Formula *binaryConj(logic::Formula* a, logic::Formula* b);

    void symbolEliminationAxioms();
    void addSymbolEliminationAxioms(PVariable *v);

    // translation of assignments
    void translateAssignments();

    void loopCounterHypothesis();
    void loopConditionHypothesis();

    logic::Formula* commandToFormula(GuardedCommand *c);
    logic::Formula* assignment(Assignment *a, logic::Term* index, logic::Term* indexPlusOne);
    logic::Formula* arrayAssignment(Assignment *a, logic::Term* index, logic::Term* indexPlusOne);
    logic::Formula* nonAssignment(PVariable *v, logic::Term* index, logic::Term* indexPlusOne);
    logic::Formula* arrayNonAssignment(PVariable *v, GuardedCommand *gc, logic::Term* index, logic::Term* indexPlusOne);

    // properties derived from strictness and density of scalars
    void monotonicityProps();
    
    logic::Formula* denseStrictProp(PVariable *v);
    logic::Formula* strictProp(PVariable *v);
    logic::Formula* denseNonStrictProp(PVariable *v);
    logic::Formula* nonStrictProp(PVariable *v);

    logic::Formula* updatePropertyOfVar(PVariable *v);

    //update predicates of arrays
    void updatePredicatesOfArrays();

    logic::Formula* iter(logic::Term* i);

    logic::Formula* arrayUpdatePredicate(PVariable *A,
                                         logic::Term* i,
                                         logic::Term* p,
                                         logic::Term* v);
    logic::Formula* arrayAssignmentConditions(Assignment *asg,
                                              FExpression *guard,
                                              logic::Term* i,
                                              logic::Term* p,
                                              logic::Term* v);
    logic::Formula* stabilityAxiom(PVariable *v);
    logic::Formula* uniqueUpdateAxiom(PVariable *v);
    logic::Formula* lastUpdateAxiom(PVariable *v);
  };
}

#endif
