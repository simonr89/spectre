#ifndef __PropertiesTime__
#define __PropertiesTime__

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
#include "Program.hpp"
#include "Analyzer.hpp"

namespace program {
    
    class PropertiesTime
    {
    public:
        PropertiesTime(const Program& program, const AnalyzerResult& aRes) :
        _loop(*program.loop),
        _vars(program.variables),
        _preconditions(program.preconditions),
        _postconditions(program.postconditions),
        
        _updated(aRes.updated),
        _monotonic(aRes.monotonic),
        _strict(aRes.strict),
        _dense(aRes.dense),
        
        _properties()
        {}
        
        void analyze();
        void output();
        
    private:
        // used as input
        const GuardedCommandCollection& _loop;
        const std::vector<const PVariable*>& _vars;
        const std::vector<const FExpression*>& _preconditions;
        const std::vector<const FExpression*>& _postconditions;
        
        const std::map<const PVariable*,bool>& _updated;
        const std::map<const PVariable*,Monotonicity>& _monotonic;
        const std::map<const PVariable*,bool>& _strict;
        const std::map<const PVariable*,bool>& _dense;
        
        /*
         * the main aim of this class is to collect all the properties
         * of the program in the member _properties.
         * after all properties are collected, the elements of
         * _properties will be dumped to TPTP
         */
        typedef std::pair<std::string, std::shared_ptr<const logic::Formula>> Property;
        std::vector<Property> _properties;
        void addProperty(std::string s, std::shared_ptr<const logic::Formula> f) { _properties.push_back(std::make_pair(s, f)); }
        
        static unsigned toVampireSort(Type t);
        // the loop counter ($counter)
        static std::shared_ptr<const logic::FuncTerm> loopCounterSymbol();
                
        void symbolEliminationAxioms();
        void addSymbolEliminationAxioms(const PVariable *v);
        
        void constnessProps();
        
        // translation of assignments
        void translateAssignments();
        
        void loopConditionHypothesis();
        
        std::shared_ptr<const logic::Formula> commandToFormula(const GuardedCommand *c);
        std::shared_ptr<const logic::Formula> assignment(const Assignment *a, std::shared_ptr<const logic::Term> i, std::shared_ptr<const logic::Term> succOfI);
        std::shared_ptr<const logic::Formula> arrayAssignment(const Assignment *a, std::shared_ptr<const logic::Term> i, std::shared_ptr<const logic::Term> succOfI);
        std::shared_ptr<const logic::Formula> nonAssignment(const PVariable *v, std::shared_ptr<const logic::Term> i, std::shared_ptr<const logic::Term> succOfI);
        std::shared_ptr<const logic::Formula> arrayNonAssignment(const PVariable *v, const GuardedCommand *gc, std::shared_ptr<const logic::Term> i, std::shared_ptr<const logic::Term> succOfI);
        
        // properties derived from strictness and density of scalars
        void monotonicityProps();
        
        std::shared_ptr<const logic::Formula> injectivityProp(const PVariable *v);

        std::shared_ptr<const logic::Formula> strictProp(const PVariable *v);
        std::shared_ptr<const logic::Formula> nonStrictProp(const PVariable *v);
        
        std::shared_ptr<const logic::Formula> updatePropertyOfVar(const PVariable *v);
        
        //update predicates of arrays
        void updatePredicatesOfArrays();
        
        std::shared_ptr<const logic::Formula> iter(std::shared_ptr<const logic::Term> i);
        
        std::shared_ptr<const logic::Formula> arrayUpdatePredicate(const PVariable *A,
                                             std::shared_ptr<const logic::Term> i,
                                             std::shared_ptr<const logic::Term> p,
                                             std::shared_ptr<const logic::Term> v);
        std::shared_ptr<const logic::Formula> arrayAssignmentConditions(const Assignment *asg,
                                                  const FExpression *guard,
                                                  std::shared_ptr<const logic::Term> i,
                                                  std::shared_ptr<const logic::Term> p,
                                                  std::shared_ptr<const logic::Term> v);
        std::shared_ptr<const logic::Formula> stabilityAxiom(const PVariable *v);
        std::shared_ptr<const logic::Formula> uniqueUpdateAxiom(const PVariable *v);
        std::shared_ptr<const logic::Formula> lastUpdateAxiom(const PVariable *v);
    };
}

#endif

