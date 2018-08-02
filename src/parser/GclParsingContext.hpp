/**
 * @file GclParsingContext.hpp
 *
 * Defines class Parser:: GclParsingContext, the parsing context (symbol
 * table, error flag...) for the guarded command language.
 *
 * @since 20/2/2018, Vienna
 * @since 15/4/2015, Gothenburg
 */

#ifndef __GclParsingContext__
#define __GclParsingContext__

#include "Expression.hpp"
#include "GuardedCommandCollection.hpp"
#include "Program.hpp"
#include "Variable.hpp"
#include <map>
#include <string>
#include <vector>

namespace parser
{

    class GclParsingContext
    {
    public:
        GclParsingContext()
            : variables(),
              preconditions(),
              postconditions(),
              program(nullptr),
              negatedPreviousGuards(program::BooleanExpression::mkConstantBoolean(true)),
              errorFlag(false),
              _localScopes()
            {
            }

        /** symbol table */
        std::map<std::string, program::PVariable *> variables;
        std::vector<program::FExpression *> preconditions;
        std::vector<program::FExpression *> postconditions;
        std::unique_ptr<program::GuardedCommandCollection> program;

        // given the collection of commands, each guard has the negation
        // of previous guard added to it so that the guards are exclusive
        // the conjunction of the guards of all guarded-commands visited until now
        program::BooleanExpression *negatedPreviousGuards;
        std::string inputFile;

        bool errorFlag;

        //True if no variable with this name exists in the symbol table
        bool available(const std::string &name);
        program::PVariable *declareVariable(const std::string &name);
        // looks for local scoped variables first (for quantified formulas) then program variables
        program::Variable *getVariable(const std::string &name);

        void setTypeDeclarationContext(program::Type t) { _typeDeclCtx = t; }
        program::Type typeDeclarationContext() { return _typeDeclCtx; }

        // Scoped variables are used only in quantified formulas
        program::QVariable *openLocalScope(const std::string &, program::Type t);
        void closeLocalScope();

        void printInfo(program::GuardedCommandCollection &c);

        bool containsAssignment(std::pair<program::FExpression *, std::vector<program::Assignment *>> assignmentList, program::Assignment *assignment);
        void addAdditionalGuards(std::pair<program::FExpression *, std::vector<program::Assignment *>> pairGuardsAssignments, program::Assignment *assignment);

        std::vector<program::PVariable*> listVariables() const;

        std::unique_ptr<program::Program> generateProgram();

    protected:
        /** type of symbols being declared */
        program::Type _typeDeclCtx;

        std::vector<program::QVariable *> _localScopes;
    };
}
#endif
