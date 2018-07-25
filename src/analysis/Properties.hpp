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
#include "Program.hpp"
#include "Analyzer.hpp"
#include "Options.hpp"

namespace program {

    class Properties
    {
    public:
        Properties(const Program& program, const AnalyzerResult& aRes) :
        loop(*program.loop),
        vars(program.variables),
        preconditions(program.preconditions),
        postconditions(program.postconditions),
        
        updated(aRes.updated),
        monotonic(aRes.monotonic),
        strict(aRes.strict),
        dense(aRes.dense),

        properties()
        {}
        
        void analyze();
        void outputTPTP();
        void outputSMTLIB();
        
    private:
        // used as input
        const GuardedCommandCollection& loop;
        const std::vector<const PVariable*>& vars;
        const std::vector<const FExpression*>& preconditions;
        const std::vector<const FExpression*>& postconditions;

        const std::map<const PVariable*,bool>& updated;
        const std::map<const PVariable*,Monotonicity>& monotonic;
        const std::map<const PVariable*,bool>& strict;
        const std::map<const PVariable*,bool>& dense;
        
        /*
         * the main aim of this class is to collect all the properties
         * of the program in the member properties.
         * after all properties are collected, the elements of
         * _properties will be dumped to TPTP
         */
        typedef std::pair<std::string, logic::FormulaPtr> Property;
        std::vector<Property> properties;
        void addProperty(std::string s, logic::FormulaPtr f) { properties.push_back(std::make_pair(s, f)); }
        
        unsigned toVampireSort(Type t);

        // return [forall vars, var_1 >= 0 & ... & var_n => f] if time
        // is represented with integers, [forall vars, f] otherwise
        logic::FormulaPtr timepointQuantified(std::vector<logic::LVariablePtr> vars, logic::FormulaPtr f);
                
        void stepAxiom();
        
        void constnessProps();

        // translation of assignments
        void translateAssignments();
        
        logic::FormulaPtr commandToFormula(const GuardedCommand *c);
        logic::FormulaPtr assignment(const Assignment *a, logic::TermPtr index, logic::TermPtr indexPlusOne);
        logic::FormulaPtr arrayAssignment(const Assignment *a, logic::TermPtr index, logic::TermPtr indexPlusOne);
        logic::FormulaPtr nonAssignment(const PVariable *v, logic::TermPtr index, logic::TermPtr indexPlusOne);
        logic::FormulaPtr arrayNonAssignment(const PVariable *v, const GuardedCommand *gc, logic::TermPtr index, logic::TermPtr indexPlusOne);
        
        // properties derived from strictness and density of scalars
        void monotonicityProps();
        
        logic::FormulaPtr denseStrictProp(const PVariable *v);
        logic::FormulaPtr strictProp(const PVariable *v);
        logic::FormulaPtr denseNonStrictProp(const PVariable *v);
        logic::FormulaPtr nonStrictProp(const PVariable *v);
        logic::FormulaPtr injectivityProp(const PVariable *v);
        
        logic::FormulaPtr updatePropertyOfVar(const PVariable *v);
        
        //update predicates of arrays
        void updatePredicatesOfArrays();
        
        logic::FormulaPtr arrayUpdatePredicate(const PVariable *A,
                                               logic::TermPtr i,
                                               logic::TermPtr p,
                                               logic::TermPtr v);
        logic::FormulaPtr arrayAssignmentConditions(const Assignment *asg,
                                                    const FExpression *guard,
                                                    logic::TermPtr i,
                                                    logic::TermPtr p,
                                                    logic::TermPtr v);
        logic::FormulaPtr stabilityAxiom(const PVariable *v);
        logic::FormulaPtr uniqueUpdateAxiom(const PVariable *v);
        logic::FormulaPtr lastUpdateAxiom(const PVariable *v);

        void preconditionsSatisfied();

        // the loop counter ($counter) corresponding to a skolem
        // symbol. Used for in verification and invariant generation
        // modes
        logic::FuncTermPtr loopCounterSymbol();
        void loopCounterNonNegative();
        void loopCondition();
        void loopExit();

        void symbolEliminationAxioms();
        void addSymbolEliminationAxioms(const PVariable *v);

        void verificationGoal();

        void terminationGoal();
    };
}

#endif
