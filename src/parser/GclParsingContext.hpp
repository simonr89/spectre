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

#include <string>
#include <vector>
#include <map>
#include "Expression.hpp"
#include "GuardedCommandCollection.hpp"
#include "Variable.hpp"
#include "Program.hpp"

namespace parser
{
    using namespace program;
    
    class GclParsingContext
    {
    public:
        
        GclParsingContext() : variables(), preconditions(), postconditions(), program(nullptr), negatedPreviousGuards(BooleanExpression::mkConstantBoolean(true)), errorFlag(false), _localScopes()  {}
        

        /** symbol table */
        std::map<std::string, PVariable*> variables;
        std::vector<FExpression*> preconditions;
        std::vector<FExpression*> postconditions;
        std::unique_ptr<GuardedCommandCollection> program;

        // given the collection of commands, each guard has the negation
        // of previous guard added to it so that the guards are exclusive
        // the conjunction of the guards of all guarded-commands visited until now
        BooleanExpression* negatedPreviousGuards;
        std::string inputFile;

        bool errorFlag;

        //True if no variable with this name exists in the symbol table
        bool available(const std::string& name);
        PVariable* declareVariable(const std::string& name);
        // looks for local scoped variables first (for quantified formulas) then program variables
        Variable* getVariable(const std::string& name);
        
        void setTypeDeclarationContext(Type t) { _typeDeclCtx = t; }
        Type typeDeclarationContext() { return _typeDeclCtx; }
        
        // Scoped variables are used only in quantified formulas
        QVariable* openLocalScope(const std::string&, Type t);
        void closeLocalScope();
        
        void printInfo(GuardedCommandCollection &c);

        bool containsAssignment(std::pair<FExpression*, std::vector<Assignment*>> assignmentList, Assignment* assignment);
        void addAdditionalGuards(std::pair<FExpression*, std::vector<Assignment*>> pairGuardsAssignments, Assignment* assignment);
    protected:
        
        /** type of symbols being declared */
        Type _typeDeclCtx;
        
        
        std::vector<QVariable*> _localScopes;

    public:
        std::unique_ptr<Program> generateProgram();
    };
    
    
    
}
#endif

