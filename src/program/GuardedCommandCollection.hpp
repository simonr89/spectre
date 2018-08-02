/**
 * @file GuardedCommandCollection.hpp
 * Defines class Program::GuardedCommandCollection
 *
 * since 30/03/2015, Gothenburg
 */

#ifndef __GuardedCommandCollection__
#define __GuardedCommandCollection__

#include <ostream>
#include <vector>

#include "Expression.hpp"
#include "Formula.hpp"

#include "Term.hpp"
#include "Type.hpp"


namespace program {

    class Assignment {
    public:

        friend class GuardedCommand;
        
        Assignment(LocationExpression* lhs, Expression* rhs) : lhs(lhs), rhs(rhs){}
        
        const LocationExpression* lhs;
        const Expression* rhs;
       
        bool hasLhs(const PVariable &v) const { return lhs->varInfo() == &v; }
        bool isArrayAssignment() const { return lhs->isArrayLocation(); }

    protected:
        std::pair<logic::TermPtr, logic::TermPtr> weakestPreconditionSubst(const logic::TermPtr i = nullptr) const;
    };

    class GuardedCommand {
    public:

        friend class GuardedCommandCollection;
        
        GuardedCommand(FExpression *guard, std::vector<Assignment*> assignments) : guard(guard), assignments(std::move(assignments)) {}

        const FExpression* guard;
        const std::vector<Assignment*> assignments;
        
        /** Return nullptr if the variable is not assigned in the
            command */
        Assignment *findAssignment(const PVariable &v) const;

    protected:
        logic::FormulaPtr weakestPrecondition(const logic::FormulaPtr f, const std::vector<PVariable*> &variables, const logic::TermPtr i = nullptr) const;
        logic::FormulaPtr arrayAssignment(const PVariable &v, const logic::TermPtr i = nullptr) const;
    };

    class GuardedCommandCollection {
    public:
        GuardedCommandCollection(std::vector<GuardedCommand*> commands,
                                 FExpression* loopCondition,
                                 std::vector<PVariable*> variables)
            :
            commands(std::move(commands)),
            loopCondition(loopCondition),
            variables(std::move(variables))
            {}
        
        const std::vector<GuardedCommand*> commands;
        const FExpression* loopCondition;
        const std::vector<PVariable*> variables;

        /** f should be a formula in the non-extended language **/
        logic::FormulaPtr weakestPrecondition(const logic::FormulaPtr f, const logic::TermPtr i = nullptr) const;
    };

    /** pretty-printer */
    std::ostream& operator<<(std::ostream& ostr, const Assignment& a);
    std::ostream& operator<<(std::ostream& ostr, const GuardedCommand& c);
    std::ostream& operator<<(std::ostream& ostr, const GuardedCommandCollection& c);

    // Hack: these function are needed for debugging bison
    std::ostream& operator<<(std::ostream& ostr, const std::vector<GuardedCommand*>& c);
    std::ostream& operator<<(std::ostream& ostr, const std::pair<FExpression*,std::vector<Assignment*>>& c);
}
#endif
