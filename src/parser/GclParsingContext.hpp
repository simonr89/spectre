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
#include <list>
#include <map>
#include "Expression.hpp"
#include "GuardedCommandCollection.hpp"
#include "Variable.hpp"

namespace parser
{
    using namespace program;
    
    class GclParsingContext
    {
    public:
        
        GclParsingContext() : errorFlag(false), _variables(), _localScopes(), _preconditions(), _postconditions() {}
        
        std::string inputFile;

        bool errorFlag;
        GuardedCommandCollection program;

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
        
        bool addAssignment(Assignment *a) { return _guardDeclCtx->addAssignment(a); }
        
        void setGuardedCommandContext(FExpression *e) { _guardDeclCtx = new GuardedCommand(e); }
        GuardedCommand* currentGuardedCommand() { return _guardDeclCtx; }
        
        // TODO: shift this into the parser
        void addPrecondition(FExpression *e) { _preconditions.push_front(e); }
        void addPostcondition(FExpression *e) { _postconditions.push_front(e); }
        
        void printInfo(GuardedCommandCollection &c);

    protected:
        /** symbol table */
        std::map<std::string, PVariable*> _variables;
        
        /** type of symbols being declared */
        Type _typeDeclCtx;
        
        /** guarded command being declared */
        GuardedCommand *_guardDeclCtx;
        
        std::list<QVariable*> _localScopes;

        // TODO: shift this into the parser
        std::list<FExpression*> _preconditions;
        std::list<FExpression*> _postconditions;
    };
    
}
#endif

