/**
 * @file GclAnalyzer.hpp
 *
 * Defines class Program::GclAnalyzer, the parsing context (symbol
 * table, error flag...) for the guarded command language.
 *
 * @since 15/4/2015, Gothenburg
 */

#ifndef __GclAnalyzer__
#define __GclAnalyzer__

#include <ostream>
#include <string>
#include <list>
#include <map>
#include "parser/GclParser.hpp"
#include "program/Expression.hpp"
#include "program/GuardedCommandCollection.hpp"
#include "program/Variable.hpp"

// Tell Flex the lexer's prototype ...
# define YY_DECL parser::GclParser::symbol_type yylex(program::GclAnalyzer &gcla)
// ... and declare it for the parser's sake.
YY_DECL;


namespace program {

  class GclAnalyzer
  {
  public:

    GclAnalyzer() :
      trace_scanning(false),
      trace_parsing(false),
      _variables(),
      _localScopes(),
      _preconditions(),
      _postconditions()
    {}
  
    ~GclAnalyzer() {}

    // Handling the scanner.
    void scan_begin();

    void scan_end();

    /** Run the parser on file F.
     * Return 0 on success.
     */
    int parse(const std::string& f);

    static void setErrorFlag() { _errorFlag = true; }

    static bool errorFlag() { return _errorFlag; }

    /** True if no variable with this name exists in the symbol table */
    bool available(const std::string& name);

    void setTypeDeclarationContext(Type t) { _typeDeclCtx = t; }

    void setGuardedCommandContext(FExpression *e) { _guardDeclCtx = new GuardedCommand(e); }

    Type typeDeclarationContext() { return _typeDeclCtx; }

    PVariable* declareVariable(const std::string& name);

    // Scoped variables are used only in quantified formulas
    QVariable* openLocalScope(const std::string&, Type t);

    void closeLocalScope();

    bool addAssignment(Assignment *a) { return _guardDeclCtx->addAssignment(a); }

    GuardedCommand* currentGuardedCommand() { return _guardDeclCtx; }

    // looks for local scoped variables first (for quantified formulas) then program variables
    Variable* getVariable(const std::string& name);

    void printInfo(std::ostream& ostr, GuardedCommandCollection &c);

    void buildProperties(GuardedCommandCollection &c);

    void addPrecondition(FExpression *e) { _preconditions.push_front(e); }

    void addPostcondition(FExpression *e) { _postconditions.push_front(e); }
  
    // The name of the file being parsed.
    // Used later to pass the file name to the location tracker.
    std::string file;

    bool trace_scanning;

    bool trace_parsing;


  protected:
    /** symbol table */
    std::map<std::string, PVariable*> _variables;

    /** type of symbols being declared */
    Type _typeDeclCtx;

    /** guarded command being declared */
    GuardedCommand *_guardDeclCtx;

    static bool _errorFlag;

    std::list<QVariable*> _localScopes;

    std::list<FExpression*> _preconditions;

    std::list<FExpression*> _postconditions;

    /** Set density and strictness flags for all variables, according to
        the loop description */
    void densityAndStrictness(GuardedCommandCollection &c);
    void densityAndStrictness(GuardedCommandCollection &c, PVariable *v);
    bool isIncremented(GuardedCommand *gc, PVariable *v, int &incr);
  };

}
#endif
