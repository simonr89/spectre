%skeleton "lalr1.cc" /* -*- C++ -*- */
%require "3.0"
%defines
%define api.namespace {parser}
%define parser_class_name {GclParser}
%define api.token.constructor
%define api.value.type variant
%define parse.assert
%code requires
{
#include <cstring>
#include <iostream>
#include "Location.hpp"
#include "Expression.hpp"
#include "GuardedCommandCollection.hpp"

#define YY_NULLPTR nullptr


namespace parser {
  class GclParsingContext;
}
}


// The parsing context.
%param { parser::GclParsingContext &gcla }
%locations
%define api.location.type {Location}
%initial-action
{
  // Initialize the initial location.
  @$.begin.filename = @$.end.filename = &gcla.inputFile;
};
%define parse.trace
%define parse.error verbose
%code
{
#include "GclParsingContext.hpp"

using namespace program;

// Tell Flex the lexer's prototype ...
# define YY_DECL parser::GclParser::symbol_type yylex(parser::GclParsingContext &gcla)
// ... and declare it for the parser's sake.
YY_DECL;

}
%define api.token.prefix {TOK_}
%token
  END 0         "EOF"
  TRUE          "true"
  FALSE         "false"
  DO            "do"
  OD            "od"
  WHILE         "while"
  REQUIRES      "requires"
  ENSURES       "ensures"
  FORALL        "forall"
  EXISTS        "exists"
  RECORD        "record"
  NULL          "null"
  ASSIGN        "="
  COLS          "::"
  ARROW         "->"
  LPAR          "("
  RPAR          ")"
  LBRA          "["
  RBRA          "]"
  LCUR          "{"
  RCUR          "}"
  SCOL          ";"
  COMMA         ","
  DOT           "."
  NOT           "!"
  MUL           "*"
  DIV           "/"
  PLUS          "+"
  MINUS         "-"
  GT            ">"
  GE            ">="
  LT            "<"
  LE            "<="
  EQ            "=="
  NEQ           "!="
  OR            "|"
  AND           "&"
  IMP           "==>"
;
%token <std::string> ID "identifier"
%token <std::string> TYPE "type identifier"
%token <int> INTEGER "number"

%type <program::Type> type_id
%type <program::Expression*> expr
%type <program::FExpression*> formula
%type <program::FExpression*> location
%type <program::GuardedCommandCollection*> guarded_command_list
%type <program::GuardedCommand*> guarded_command
%type <program::Assignment*> assignment

%printer { yyoutput << $$; } <*>;

%right ASSIGN
%right FORALL
%right EXISTS
%left  IMP
%left  OR
%left  AND
%left  EQ NEQ
%left  GT GE LT LE
%left  PLUS MINUS
%left  MUL DIV
%right NOT UPLUS UMINUS

%%

%start program;

program:
  declaration_list assertion_list loop_body { }
;

declaration_list:
  %empty
| declaration_list rec_declaration { }
| declaration_list var_declaration { }
;

rec_declaration:
  RECORD ID LCUR attr_declaration_list RCUR { }
;

attr_declaration_list:
  attr_declaration
| attr_declaration_list attr_declaration { }

attr_declaration:
  type_id ID SCOL { }
;

var_declaration:
  type_id { gcla.setTypeDeclarationContext($1); }
  var_declarators SCOL 
;

type_id:
  ID              { $$ = Type::TY_INTEGER; }
| TYPE            { if ($1 == "int")
                      $$ = Type::TY_INTEGER;
                    else if ($1 == "bool")
                      $$ = Type::TY_BOOLEAN;
                  }
| TYPE LBRA RBRA  { if ($1 == "int")
                      $$ = Type::TY_INTEGER_ARRAY;
                    else if ($1 == "bool")
                      $$ = Type::TY_BOOLEAN_ARRAY;
                  }
;

var_declarators:
  var_declarator
| var_declarators COMMA var_declarator
;

var_declarator:
  ID             { if (gcla.available($1))
                     gcla.declareVariable($1);
                   else
                     error(@1, "Variable name is already used");
                 }
;

assertion_list:
  %empty
| assertion_list pre_condition { }
| assertion_list post_condition { }
;

pre_condition:
  REQUIRES formula SCOL { gcla.addPrecondition($2); }
;

post_condition:
  ENSURES formula SCOL { gcla.addPostcondition($2); }
;

formula:
  expr { if ($1->etype() != Type::TY_BOOLEAN) error(@1, "Ill-typed expression");
         $$ = dynamic_cast<FExpression*>($1); }
| FORALL type_id ID { if (isArrayType($2))
                         error(@2, "Formulas quantifiers are limited to scalar types");
                      else
                        gcla.openLocalScope($3, $2); }
  COMMA formula { $$ = QuantifiedExpression::mkForall(static_cast<QVariable*>(gcla.getVariable($3)), $6);
                  if (!$$) error(@6, "Ill-typed expression");
                  gcla.closeLocalScope(); }
| EXISTS type_id ID { if (isArrayType($2))
                        error(@2, "Formulas quantifiers are limited to scalar types");
                      else
                        gcla.openLocalScope($3, $2); }
  COMMA formula { $$ = QuantifiedExpression::mkExists(static_cast<QVariable*>(gcla.getVariable($3)), $6);
                  if (!$$) error(@6, "Ill-typed expression");
                  gcla.closeLocalScope(); }
;

expr:
  location                 { $$ = $1; }
| NULL                     { $$ = nullptr; /* TODO */ }
| INTEGER                  { $$ = ArithmeticExpression::mkConstantInteger($1);
                             if (!$$) error(@1, "Ill-typed expression"); }
| LPAR expr RPAR           { $$ = $2; }
| NOT expr                 { $$ = BooleanExpression::mkNegation($2);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr MUL expr            { $$ = ArithmeticExpression::mkMul($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr DIV expr            { $$ = ArithmeticExpression::mkDiv($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr PLUS expr           { $$ = ArithmeticExpression::mkAdd($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr MINUS expr          { $$ = ArithmeticExpression::mkSub($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| PLUS expr %prec UPLUS    { $$ = $2; }
| MINUS expr %prec UMINUS  { $$ = ArithmeticExpression::mkMinus($2);
                             if (!$$) error(@1, "Ill-typed expression"); }
| TRUE                     { $$ = BooleanExpression::mkConstantBoolean(true); }
| FALSE                    { $$ = BooleanExpression::mkConstantBoolean(false); }
| expr GT expr             { $$ = BooleanExpression::mkGt($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr GE expr             { $$ = BooleanExpression::mkGe($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr LT expr             { $$ = BooleanExpression::mkLt($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr LE expr             { $$ = BooleanExpression::mkLe($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr EQ expr             { $$ = BooleanExpression::mkEq($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr NEQ expr            { $$ = BooleanExpression::mkNeq($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr OR expr             { $$ = BooleanExpression::mkOr($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr AND expr            { $$ = BooleanExpression::mkAnd($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
| expr IMP expr            { $$ = BooleanExpression::mkImplication($1, $3);
                             if (!$$) error(@1, "Ill-typed expression"); }
;

loop_body:
WHILE LPAR expr RPAR DO guarded_command_list OD { if ($3->etype() == Type::TY_BOOLEAN) {
                                                    $6->setLoopCondition(dynamic_cast<FExpression*>($3));
                                                    if (!gcla.errorFlag) {
                                                      gcla.program = *$6;
                                                    }
                                                  } else {
                                                    error(@1, "Loop condition does not have type bool");
                                                  }
                                                }
| DO guarded_command_list OD { $2->setLoopCondition(BooleanExpression::mkConstantBoolean(true));
                               if (!gcla.errorFlag)
                                 gcla.program = *$2;
                             }
;

guarded_command_list:
  %empty                               { $$ = new GuardedCommandCollection(); }
| guarded_command_list guarded_command { $1->addGuardedCommand($2); $$ = $1; }
;

guarded_command:
  COLS expr { if ($2->etype() == Type::TY_BOOLEAN)
                gcla.setGuardedCommandContext(dynamic_cast<FExpression*>($2));
              else
                error(@1, "Guard does not have type bool");
            }
  ARROW assignment_list { $$ = gcla.currentGuardedCommand(); }
;

assignment_list:
  %empty                          { }
| assignment_list assignment SCOL { if (!gcla.addAssignment($2))
                                      error(@1, "Duplicate assignment in guard");
                                  }
;

assignment:
  location ASSIGN expr { $$ = new Assignment(static_cast<LocationExpression*>($1), $3); $$->recordLhsInfo(); }
;

location:
  ID                { Variable *v = gcla.getVariable($1);
                      if (v) {
                        if (isArrayType(v->vtype())) {
                          error(@1, "Not a valid location");
                        } else {
                          if (v->isProgramVariable()) {
                            $$ = LocationExpression::mkProgramVariable(static_cast<PVariable*>(v));
                          } else {
                            $$ = VariableExpression::mkQuantifiedVariable(static_cast<QVariable*>(v));
                          }
                        }
                      } else {
                        error(@1, "Undeclared variable");
                      }
                    }
| ID LBRA expr RBRA { Variable *v = gcla.getVariable($1);
                      if (v) {
                        if (isArrayType(v->vtype())) {
                          if ($3->etype() == Type::TY_INTEGER) {
                            $$ = LocationExpression::mkArrayApp(static_cast<PVariable*>(v), $3);
                          } else {
                            error(@1, "Array index does not have type int");
                          }
                        } else {
                          error(@1, "Not an array");
                        }
                      } else {
                        error(@1, "Undeclared variable");
                      }
                    }
| location DOT ID { $$ = nullptr; }
;

%%
void parser::GclParser::error(const location_type& l,
                              const std::string& m)
{
  std::cout << l << m << std::endl;
  gcla.errorFlag = true;
}

