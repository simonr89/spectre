#ifndef __Properties__
#define __Properties__

#include <vector>
#include <map>
#include <utility>

#include "Formula.hpp"
#include "Sort.hpp"
#include "Term.hpp"
#include "Expression.hpp"
#include "GuardedCommandCollection.hpp"
#include "Variable.hpp"
#include "Type.hpp"

namespace program {

    class Properties
    {
    public:
        Properties(const GuardedCommandCollection& loop, const std::map<std::string, PVariable*>& vars, const std::vector<FExpression*>& preconditions, const std::vector<FExpression*>& postconditions) :
        _loop(loop),
        _vars(vars),
        _preconditions(preconditions),
        _postconditions(postconditions),
        _properties()
        {}
        
        void analyze();
        void outputTPTP();
        
        const GuardedCommandCollection& _loop;
        const std::map<std::string, PVariable*>& _vars;
        const std::vector<FExpression*>& _preconditions;
        const std::vector<FExpression*>& _postconditions;

    protected:
        
        /*
         * the main aim of this class is to collect all the properties
         * of the program in the member _properties.
         * after all properties are collected, the elements of
         * _properties will be dumped to TPTP
         */
        typedef std::pair<std::string, logic::Formula*> Property;
        std::vector<Property> _properties;
        void addProperty(std::string s, logic::Formula* f) { _properties.push_back(std::make_pair(s, f)); }
        
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
