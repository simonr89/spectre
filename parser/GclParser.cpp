// A Bison parser, made by GNU Bison 3.0.4.

// Skeleton implementation for Bison LALR(1) parsers in C++

// Copyright (C) 2002-2015 Free Software Foundation, Inc.

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// As a special exception, you may create a larger work that contains
// part or all of the Bison parser skeleton and distribute that work
// under terms of your choice, so long as that work isn't itself a
// parser generator using the skeleton or a modified version thereof
// as a parser skeleton.  Alternatively, if you modify or redistribute
// the parser skeleton itself, you may (at your option) remove this
// special exception, which will cause the skeleton and the resulting
// Bison output files to be licensed under the GNU General Public
// License without this special exception.

// This special exception was added by the Free Software Foundation in
// version 2.2 of Bison.


// First part of user declarations.

#line 37 "parser/GclParser.cpp" // lalr1.cc:404

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

#include "GclParser.hpp"

// User implementation prologue.

#line 51 "parser/GclParser.cpp" // lalr1.cc:412
// Unqualified %code blocks.
#line 36 "parser/GclParser.yy" // lalr1.cc:413

#include "program/GclAnalyzer.hpp"

using namespace program;

#line 59 "parser/GclParser.cpp" // lalr1.cc:413


#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> // FIXME: INFRINGES ON USER NAME SPACE.
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K].location)
/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

# ifndef YYLLOC_DEFAULT
#  define YYLLOC_DEFAULT(Current, Rhs, N)                               \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).begin  = YYRHSLOC (Rhs, 1).begin;                   \
          (Current).end    = YYRHSLOC (Rhs, N).end;                     \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).begin = (Current).end = YYRHSLOC (Rhs, 0).end;      \
        }                                                               \
    while (/*CONSTCOND*/ false)
# endif


// Suppress unused-variable warnings by "using" E.
#define YYUSE(E) ((void) (E))

// Enable debugging if requested.
#if YYDEBUG

// A pseudo ostream that takes yydebug_ into account.
# define YYCDEBUG if (yydebug_) (*yycdebug_)

# define YY_SYMBOL_PRINT(Title, Symbol)         \
  do {                                          \
    if (yydebug_)                               \
    {                                           \
      *yycdebug_ << Title << ' ';               \
      yy_print_ (*yycdebug_, Symbol);           \
      *yycdebug_ << std::endl;                  \
    }                                           \
  } while (false)

# define YY_REDUCE_PRINT(Rule)          \
  do {                                  \
    if (yydebug_)                       \
      yy_reduce_print_ (Rule);          \
  } while (false)

# define YY_STACK_PRINT()               \
  do {                                  \
    if (yydebug_)                       \
      yystack_print_ ();                \
  } while (false)

#else // !YYDEBUG

# define YYCDEBUG if (false) std::cerr
# define YY_SYMBOL_PRINT(Title, Symbol)  YYUSE(Symbol)
# define YY_REDUCE_PRINT(Rule)           static_cast<void>(0)
# define YY_STACK_PRINT()                static_cast<void>(0)

#endif // !YYDEBUG

#define yyerrok         (yyerrstatus_ = 0)
#define yyclearin       (yyla.clear ())

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYRECOVERING()  (!!yyerrstatus_)

#line 4 "parser/GclParser.yy" // lalr1.cc:479
namespace parser {
#line 145 "parser/GclParser.cpp" // lalr1.cc:479

  /* Return YYSTR after stripping away unnecessary quotes and
     backslashes, so that it's suitable for yyerror.  The heuristic is
     that double-quoting is unnecessary unless the string contains an
     apostrophe, a comma, or backslash (other than backslash-backslash).
     YYSTR is taken from yytname.  */
  std::string
  GclParser::yytnamerr_ (const char *yystr)
  {
    if (*yystr == '"')
      {
        std::string yyr = "";
        char const *yyp = yystr;

        for (;;)
          switch (*++yyp)
            {
            case '\'':
            case ',':
              goto do_not_strip_quotes;

            case '\\':
              if (*++yyp != '\\')
                goto do_not_strip_quotes;
              // Fall through.
            default:
              yyr += *yyp;
              break;

            case '"':
              return yyr;
            }
      do_not_strip_quotes: ;
      }

    return yystr;
  }


  /// Build a parser object.
  GclParser::GclParser (program::GclAnalyzer &gcla_yyarg)
    :
#if YYDEBUG
      yydebug_ (false),
      yycdebug_ (&std::cerr),
#endif
      gcla (gcla_yyarg)
  {}

  GclParser::~GclParser ()
  {}


  /*---------------.
  | Symbol types.  |
  `---------------*/



  // by_state.
  inline
  GclParser::by_state::by_state ()
    : state (empty_state)
  {}

  inline
  GclParser::by_state::by_state (const by_state& other)
    : state (other.state)
  {}

  inline
  void
  GclParser::by_state::clear ()
  {
    state = empty_state;
  }

  inline
  void
  GclParser::by_state::move (by_state& that)
  {
    state = that.state;
    that.clear ();
  }

  inline
  GclParser::by_state::by_state (state_type s)
    : state (s)
  {}

  inline
  GclParser::symbol_number_type
  GclParser::by_state::type_get () const
  {
    if (state == empty_state)
      return empty_symbol;
    else
      return yystos_[state];
  }

  inline
  GclParser::stack_symbol_type::stack_symbol_type ()
  {}


  inline
  GclParser::stack_symbol_type::stack_symbol_type (state_type s, symbol_type& that)
    : super_type (s, that.location)
  {
      switch (that.type_get ())
    {
      case 37: // "number"
        value.move< int > (that.value);
        break;

      case 60: // assignment
        value.move< program::Assignment* > (that.value);
        break;

      case 54: // expr
        value.move< program::Expression* > (that.value);
        break;

      case 51: // formula
        value.move< program::FExpression* > (that.value);
        break;

      case 57: // guarded_command
        value.move< program::GuardedCommand* > (that.value);
        break;

      case 56: // guarded_command_list
        value.move< program::GuardedCommandCollection* > (that.value);
        break;

      case 61: // location
        value.move< program::LocationExpression* > (that.value);
        break;

      case 45: // type_id
        value.move< program::Type > (that.value);
        break;

      case 35: // "identifier"
      case 36: // "type identifier"
        value.move< std::string > (that.value);
        break;

      default:
        break;
    }

    // that is emptied.
    that.type = empty_symbol;
  }

  inline
  GclParser::stack_symbol_type&
  GclParser::stack_symbol_type::operator= (const stack_symbol_type& that)
  {
    state = that.state;
      switch (that.type_get ())
    {
      case 37: // "number"
        value.copy< int > (that.value);
        break;

      case 60: // assignment
        value.copy< program::Assignment* > (that.value);
        break;

      case 54: // expr
        value.copy< program::Expression* > (that.value);
        break;

      case 51: // formula
        value.copy< program::FExpression* > (that.value);
        break;

      case 57: // guarded_command
        value.copy< program::GuardedCommand* > (that.value);
        break;

      case 56: // guarded_command_list
        value.copy< program::GuardedCommandCollection* > (that.value);
        break;

      case 61: // location
        value.copy< program::LocationExpression* > (that.value);
        break;

      case 45: // type_id
        value.copy< program::Type > (that.value);
        break;

      case 35: // "identifier"
      case 36: // "type identifier"
        value.copy< std::string > (that.value);
        break;

      default:
        break;
    }

    location = that.location;
    return *this;
  }


  template <typename Base>
  inline
  void
  GclParser::yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const
  {
    if (yymsg)
      YY_SYMBOL_PRINT (yymsg, yysym);
  }

#if YYDEBUG
  template <typename Base>
  void
  GclParser::yy_print_ (std::ostream& yyo,
                                     const basic_symbol<Base>& yysym) const
  {
    std::ostream& yyoutput = yyo;
    YYUSE (yyoutput);
    symbol_number_type yytype = yysym.type_get ();
    // Avoid a (spurious) G++ 4.8 warning about "array subscript is
    // below array bounds".
    if (yysym.empty ())
      std::abort ();
    yyo << (yytype < yyntokens_ ? "token" : "nterm")
        << ' ' << yytname_[yytype] << " ("
        << yysym.location << ": ";
    switch (yytype)
    {
            case 35: // "identifier"

#line 89 "parser/GclParser.yy" // lalr1.cc:636
        { yyoutput << yysym.value.template as< std::string > (); }
#line 386 "parser/GclParser.cpp" // lalr1.cc:636
        break;

      case 36: // "type identifier"

#line 89 "parser/GclParser.yy" // lalr1.cc:636
        { yyoutput << yysym.value.template as< std::string > (); }
#line 393 "parser/GclParser.cpp" // lalr1.cc:636
        break;

      case 37: // "number"

#line 89 "parser/GclParser.yy" // lalr1.cc:636
        { yyoutput << yysym.value.template as< int > (); }
#line 400 "parser/GclParser.cpp" // lalr1.cc:636
        break;

      case 45: // type_id

#line 89 "parser/GclParser.yy" // lalr1.cc:636
        { yyoutput << yysym.value.template as< program::Type > (); }
#line 407 "parser/GclParser.cpp" // lalr1.cc:636
        break;

      case 51: // formula

#line 89 "parser/GclParser.yy" // lalr1.cc:636
        { yyoutput << yysym.value.template as< program::FExpression* > (); }
#line 414 "parser/GclParser.cpp" // lalr1.cc:636
        break;

      case 54: // expr

#line 89 "parser/GclParser.yy" // lalr1.cc:636
        { yyoutput << yysym.value.template as< program::Expression* > (); }
#line 421 "parser/GclParser.cpp" // lalr1.cc:636
        break;

      case 56: // guarded_command_list

#line 89 "parser/GclParser.yy" // lalr1.cc:636
        { yyoutput << yysym.value.template as< program::GuardedCommandCollection* > (); }
#line 428 "parser/GclParser.cpp" // lalr1.cc:636
        break;

      case 57: // guarded_command

#line 89 "parser/GclParser.yy" // lalr1.cc:636
        { yyoutput << yysym.value.template as< program::GuardedCommand* > (); }
#line 435 "parser/GclParser.cpp" // lalr1.cc:636
        break;

      case 60: // assignment

#line 89 "parser/GclParser.yy" // lalr1.cc:636
        { yyoutput << yysym.value.template as< program::Assignment* > (); }
#line 442 "parser/GclParser.cpp" // lalr1.cc:636
        break;

      case 61: // location

#line 89 "parser/GclParser.yy" // lalr1.cc:636
        { yyoutput << yysym.value.template as< program::LocationExpression* > (); }
#line 449 "parser/GclParser.cpp" // lalr1.cc:636
        break;


      default:
        break;
    }
    yyo << ')';
  }
#endif

  inline
  void
  GclParser::yypush_ (const char* m, state_type s, symbol_type& sym)
  {
    stack_symbol_type t (s, sym);
    yypush_ (m, t);
  }

  inline
  void
  GclParser::yypush_ (const char* m, stack_symbol_type& s)
  {
    if (m)
      YY_SYMBOL_PRINT (m, s);
    yystack_.push (s);
  }

  inline
  void
  GclParser::yypop_ (unsigned int n)
  {
    yystack_.pop (n);
  }

#if YYDEBUG
  std::ostream&
  GclParser::debug_stream () const
  {
    return *yycdebug_;
  }

  void
  GclParser::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


  GclParser::debug_level_type
  GclParser::debug_level () const
  {
    return yydebug_;
  }

  void
  GclParser::set_debug_level (debug_level_type l)
  {
    yydebug_ = l;
  }
#endif // YYDEBUG

  inline GclParser::state_type
  GclParser::yy_lr_goto_state_ (state_type yystate, int yysym)
  {
    int yyr = yypgoto_[yysym - yyntokens_] + yystate;
    if (0 <= yyr && yyr <= yylast_ && yycheck_[yyr] == yystate)
      return yytable_[yyr];
    else
      return yydefgoto_[yysym - yyntokens_];
  }

  inline bool
  GclParser::yy_pact_value_is_default_ (int yyvalue)
  {
    return yyvalue == yypact_ninf_;
  }

  inline bool
  GclParser::yy_table_value_is_error_ (int yyvalue)
  {
    return yyvalue == yytable_ninf_;
  }

  int
  GclParser::parse ()
  {
    // State.
    int yyn;
    /// Length of the RHS of the rule being reduced.
    int yylen = 0;

    // Error handling.
    int yynerrs_ = 0;
    int yyerrstatus_ = 0;

    /// The lookahead symbol.
    symbol_type yyla;

    /// The locations where the error started and ended.
    stack_symbol_type yyerror_range[3];

    /// The return value of parse ().
    int yyresult;

    // FIXME: This shoud be completely indented.  It is not yet to
    // avoid gratuitous conflicts when merging into the master branch.
    try
      {
    YYCDEBUG << "Starting parse" << std::endl;


    // User initialization code.
    #line 29 "parser/GclParser.yy" // lalr1.cc:741
{
  // Initialize the initial location.
  yyla.location.begin.filename = yyla.location.end.filename = &gcla.file;
}

#line 568 "parser/GclParser.cpp" // lalr1.cc:741

    /* Initialize the stack.  The initial state will be set in
       yynewstate, since the latter expects the semantical and the
       location values to have been already stored, initialize these
       stacks with a primary value.  */
    yystack_.clear ();
    yypush_ (YY_NULLPTR, 0, yyla);

    // A new symbol was pushed on the stack.
  yynewstate:
    YYCDEBUG << "Entering state " << yystack_[0].state << std::endl;

    // Accept?
    if (yystack_[0].state == yyfinal_)
      goto yyacceptlab;

    goto yybackup;

    // Backup.
  yybackup:

    // Try to take a decision without lookahead.
    yyn = yypact_[yystack_[0].state];
    if (yy_pact_value_is_default_ (yyn))
      goto yydefault;

    // Read a lookahead token.
    if (yyla.empty ())
      {
        YYCDEBUG << "Reading a token: ";
        try
          {
            symbol_type yylookahead (yylex (gcla));
            yyla.move (yylookahead);
          }
        catch (const syntax_error& yyexc)
          {
            error (yyexc);
            goto yyerrlab1;
          }
      }
    YY_SYMBOL_PRINT ("Next token is", yyla);

    /* If the proper action on seeing token YYLA.TYPE is to reduce or
       to detect an error, take that action.  */
    yyn += yyla.type_get ();
    if (yyn < 0 || yylast_ < yyn || yycheck_[yyn] != yyla.type_get ())
      goto yydefault;

    // Reduce or error.
    yyn = yytable_[yyn];
    if (yyn <= 0)
      {
        if (yy_table_value_is_error_ (yyn))
          goto yyerrlab;
        yyn = -yyn;
        goto yyreduce;
      }

    // Count tokens shifted since error; after three, turn off error status.
    if (yyerrstatus_)
      --yyerrstatus_;

    // Shift the lookahead token.
    yypush_ ("Shifting", yyn, yyla);
    goto yynewstate;

  /*-----------------------------------------------------------.
  | yydefault -- do the default action for the current state.  |
  `-----------------------------------------------------------*/
  yydefault:
    yyn = yydefact_[yystack_[0].state];
    if (yyn == 0)
      goto yyerrlab;
    goto yyreduce;

  /*-----------------------------.
  | yyreduce -- Do a reduction.  |
  `-----------------------------*/
  yyreduce:
    yylen = yyr2_[yyn];
    {
      stack_symbol_type yylhs;
      yylhs.state = yy_lr_goto_state_(yystack_[yylen].state, yyr1_[yyn]);
      /* Variants are always initialized to an empty instance of the
         correct type. The default '$$ = $1' action is NOT applied
         when using variants.  */
        switch (yyr1_[yyn])
    {
      case 37: // "number"
        yylhs.value.build< int > ();
        break;

      case 60: // assignment
        yylhs.value.build< program::Assignment* > ();
        break;

      case 54: // expr
        yylhs.value.build< program::Expression* > ();
        break;

      case 51: // formula
        yylhs.value.build< program::FExpression* > ();
        break;

      case 57: // guarded_command
        yylhs.value.build< program::GuardedCommand* > ();
        break;

      case 56: // guarded_command_list
        yylhs.value.build< program::GuardedCommandCollection* > ();
        break;

      case 61: // location
        yylhs.value.build< program::LocationExpression* > ();
        break;

      case 45: // type_id
        yylhs.value.build< program::Type > ();
        break;

      case 35: // "identifier"
      case 36: // "type identifier"
        yylhs.value.build< std::string > ();
        break;

      default:
        break;
    }


      // Compute the default @$.
      {
        slice<stack_symbol_type, stack_type> slice (yystack_, yylen);
        YYLLOC_DEFAULT (yylhs.location, slice, yylen);
      }

      // Perform the reduction.
      YY_REDUCE_PRINT (yyn);
      try
        {
          switch (yyn)
            {
  case 2:
#line 108 "parser/GclParser.yy" // lalr1.cc:859
    { }
#line 715 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 4:
#line 113 "parser/GclParser.yy" // lalr1.cc:859
    { }
#line 721 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 5:
#line 117 "parser/GclParser.yy" // lalr1.cc:859
    { gcla.setTypeDeclarationContext(yystack_[0].value.as< program::Type > ()); }
#line 727 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 7:
#line 122 "parser/GclParser.yy" // lalr1.cc:859
    { if (yystack_[0].value.as< std::string > () == "int")
                      yylhs.value.as< program::Type > () = Type::TY_INTEGER;
                    else if (yystack_[0].value.as< std::string > () == "bool")
                      yylhs.value.as< program::Type > () = Type::TY_BOOLEAN;
                  }
#line 737 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 8:
#line 127 "parser/GclParser.yy" // lalr1.cc:859
    { if (yystack_[2].value.as< std::string > () == "int")
                      yylhs.value.as< program::Type > () = Type::TY_INTEGER_ARRAY;
                    else if (yystack_[2].value.as< std::string > () == "bool")
                      yylhs.value.as< program::Type > () = Type::TY_BOOLEAN_ARRAY;
                  }
#line 747 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 11:
#line 140 "parser/GclParser.yy" // lalr1.cc:859
    { if (gcla.available(yystack_[0].value.as< std::string > ()))
                     gcla.declareVariable(yystack_[0].value.as< std::string > ());
                   else
                     error(yystack_[0].location, "Variable name is already used");
                 }
#line 757 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 13:
#line 149 "parser/GclParser.yy" // lalr1.cc:859
    { }
#line 763 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 14:
#line 150 "parser/GclParser.yy" // lalr1.cc:859
    { }
#line 769 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 15:
#line 154 "parser/GclParser.yy" // lalr1.cc:859
    { gcla.addPrecondition(yystack_[1].value.as< program::FExpression* > ()); }
#line 775 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 16:
#line 158 "parser/GclParser.yy" // lalr1.cc:859
    { gcla.addPostcondition(yystack_[1].value.as< program::FExpression* > ()); }
#line 781 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 17:
#line 162 "parser/GclParser.yy" // lalr1.cc:859
    { if (yystack_[0].value.as< program::Expression* > ()->etype() != Type::TY_BOOLEAN) error(yystack_[0].location, "Ill-typed expression");
         yylhs.value.as< program::FExpression* > () = dynamic_cast<FExpression*>(yystack_[0].value.as< program::Expression* > ()); }
#line 788 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 18:
#line 164 "parser/GclParser.yy" // lalr1.cc:859
    { if (isArrayType(yystack_[1].value.as< program::Type > ()))
                         error(yystack_[1].location, "Formulas quantifiers are limited to scalar types");
                      else
                        gcla.openLocalScope(yystack_[0].value.as< std::string > (), yystack_[1].value.as< program::Type > ()); }
#line 797 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 19:
#line 168 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::FExpression* > () = QuantifiedExpression::mkForall(static_cast<QVariable*>(gcla.getVariable(yystack_[3].value.as< std::string > ())), yystack_[0].value.as< program::FExpression* > ());
                  if (!yylhs.value.as< program::FExpression* > ()) error(yystack_[0].location, "Ill-typed expression");
                  gcla.closeLocalScope(); }
#line 805 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 20:
#line 171 "parser/GclParser.yy" // lalr1.cc:859
    { if (isArrayType(yystack_[1].value.as< program::Type > ()))
                        error(yystack_[1].location, "Formulas quantifiers are limited to scalar types");
                      else
                        gcla.openLocalScope(yystack_[0].value.as< std::string > (), yystack_[1].value.as< program::Type > ()); }
#line 814 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 21:
#line 175 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::FExpression* > () = QuantifiedExpression::mkExists(static_cast<QVariable*>(gcla.getVariable(yystack_[3].value.as< std::string > ())), yystack_[0].value.as< program::FExpression* > ());
                  if (!yylhs.value.as< program::FExpression* > ()) error(yystack_[0].location, "Ill-typed expression");
                  gcla.closeLocalScope(); }
#line 822 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 22:
#line 181 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = yystack_[0].value.as< program::LocationExpression* > (); }
#line 828 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 23:
#line 182 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = ArithmeticExpression::mkConstantInteger(yystack_[0].value.as< int > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[0].location, "Ill-typed expression"); }
#line 835 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 24:
#line 184 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = yystack_[1].value.as< program::Expression* > (); }
#line 841 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 25:
#line 185 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkNegation(yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[1].location, "Ill-typed expression"); }
#line 848 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 26:
#line 187 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = ArithmeticExpression::mkMul(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 855 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 27:
#line 189 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = ArithmeticExpression::mkDiv(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 862 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 28:
#line 191 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = ArithmeticExpression::mkAdd(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 869 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 29:
#line 193 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = ArithmeticExpression::mkSub(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 876 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 30:
#line 195 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = yystack_[0].value.as< program::Expression* > (); }
#line 882 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 31:
#line 196 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = ArithmeticExpression::mkMinus(yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[1].location, "Ill-typed expression"); }
#line 889 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 32:
#line 198 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkConstantBoolean(true); }
#line 895 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 33:
#line 199 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkConstantBoolean(false); }
#line 901 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 34:
#line 200 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkGt(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 908 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 35:
#line 202 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkGe(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 915 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 36:
#line 204 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkLt(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 922 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 37:
#line 206 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkLe(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 929 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 38:
#line 208 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkEq(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 936 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 39:
#line 210 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkNeq(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 943 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 40:
#line 212 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkOr(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 950 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 41:
#line 214 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkAnd(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 957 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 42:
#line 216 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Expression* > () = BooleanExpression::mkImplication(yystack_[2].value.as< program::Expression* > (), yystack_[0].value.as< program::Expression* > ());
                             if (!yylhs.value.as< program::Expression* > ()) error(yystack_[2].location, "Ill-typed expression"); }
#line 964 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 43:
#line 221 "parser/GclParser.yy" // lalr1.cc:859
    { if (yystack_[4].value.as< program::Expression* > ()->etype() == Type::TY_BOOLEAN) {
                                                    yystack_[1].value.as< program::GuardedCommandCollection* > ()->setLoopCondition(dynamic_cast<FExpression*>(yystack_[4].value.as< program::Expression* > ()));
                                                    if (!gcla.errorFlag()) {
                                                      gcla.buildProperties(*yystack_[1].value.as< program::GuardedCommandCollection* > ());
                                                    }
                                                  } else {
                                                    error(yystack_[6].location, "Loop condition does not have type bool");
                                                  }
                                                }
#line 978 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 44:
#line 230 "parser/GclParser.yy" // lalr1.cc:859
    { yystack_[1].value.as< program::GuardedCommandCollection* > ()->setLoopCondition(BooleanExpression::mkConstantBoolean(true));
                               if (!gcla.errorFlag())
                                 gcla.buildProperties(*yystack_[1].value.as< program::GuardedCommandCollection* > ());
                             }
#line 987 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 45:
#line 237 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::GuardedCommandCollection* > () = new GuardedCommandCollection(); }
#line 993 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 46:
#line 238 "parser/GclParser.yy" // lalr1.cc:859
    { yystack_[1].value.as< program::GuardedCommandCollection* > ()->addGuardedCommand(yystack_[0].value.as< program::GuardedCommand* > ()); yylhs.value.as< program::GuardedCommandCollection* > () = yystack_[1].value.as< program::GuardedCommandCollection* > (); }
#line 999 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 47:
#line 242 "parser/GclParser.yy" // lalr1.cc:859
    { if (yystack_[0].value.as< program::Expression* > ()->etype() == Type::TY_BOOLEAN)
                gcla.setGuardedCommandContext(dynamic_cast<FExpression*>(yystack_[0].value.as< program::Expression* > ()));
              else
                error(yystack_[1].location, "Guard does not have type bool");
            }
#line 1009 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 48:
#line 247 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::GuardedCommand* > () = gcla.currentGuardedCommand(); }
#line 1015 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 49:
#line 251 "parser/GclParser.yy" // lalr1.cc:859
    { }
#line 1021 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 50:
#line 252 "parser/GclParser.yy" // lalr1.cc:859
    { if (!gcla.addAssignment(yystack_[1].value.as< program::Assignment* > ()))
                                      error(yystack_[2].location, "Duplicate assignment in guard");
                                  }
#line 1029 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 51:
#line 258 "parser/GclParser.yy" // lalr1.cc:859
    { yylhs.value.as< program::Assignment* > () = new Assignment(yystack_[2].value.as< program::LocationExpression* > (), yystack_[0].value.as< program::Expression* > ()); yylhs.value.as< program::Assignment* > ()->recordLhsInfo(); }
#line 1035 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 52:
#line 262 "parser/GclParser.yy" // lalr1.cc:859
    { Variable *v = gcla.getVariable(yystack_[0].value.as< std::string > ());
                      if (v) {
                        if (isArrayType(v->vtype())) {
                          error(yystack_[0].location, "Not a valid location");
                        } else {
                          yylhs.value.as< program::LocationExpression* > () = LocationExpression::mkVariable(static_cast<PVariable*>(v));
                        }
                      } else {
                        error(yystack_[0].location, "Undeclared variable");
                      }
                    }
#line 1051 "parser/GclParser.cpp" // lalr1.cc:859
    break;

  case 53:
#line 273 "parser/GclParser.yy" // lalr1.cc:859
    { Variable *v = gcla.getVariable(yystack_[3].value.as< std::string > ());
                      if (v) {
                        if (isArrayType(v->vtype())) {
                          if (yystack_[1].value.as< program::Expression* > ()->etype() == Type::TY_INTEGER) {
                            yylhs.value.as< program::LocationExpression* > () = LocationExpression::mkArrayApp(static_cast<PVariable*>(v), yystack_[1].value.as< program::Expression* > ());
                          } else {
                            error(yystack_[3].location, "Array index does not have type int");
                          }
                        } else {
                          error(yystack_[3].location, "Not an array");
                        }
                      } else {
                        error(yystack_[3].location, "Undeclared variable");
                      }
                    }
#line 1071 "parser/GclParser.cpp" // lalr1.cc:859
    break;


#line 1075 "parser/GclParser.cpp" // lalr1.cc:859
            default:
              break;
            }
        }
      catch (const syntax_error& yyexc)
        {
          error (yyexc);
          YYERROR;
        }
      YY_SYMBOL_PRINT ("-> $$ =", yylhs);
      yypop_ (yylen);
      yylen = 0;
      YY_STACK_PRINT ();

      // Shift the result of the reduction.
      yypush_ (YY_NULLPTR, yylhs);
    }
    goto yynewstate;

  /*--------------------------------------.
  | yyerrlab -- here on detecting error.  |
  `--------------------------------------*/
  yyerrlab:
    // If not already recovering from an error, report this error.
    if (!yyerrstatus_)
      {
        ++yynerrs_;
        error (yyla.location, yysyntax_error_ (yystack_[0].state, yyla));
      }


    yyerror_range[1].location = yyla.location;
    if (yyerrstatus_ == 3)
      {
        /* If just tried and failed to reuse lookahead token after an
           error, discard it.  */

        // Return failure if at end of input.
        if (yyla.type_get () == yyeof_)
          YYABORT;
        else if (!yyla.empty ())
          {
            yy_destroy_ ("Error: discarding", yyla);
            yyla.clear ();
          }
      }

    // Else will try to reuse lookahead token after shifting the error token.
    goto yyerrlab1;


  /*---------------------------------------------------.
  | yyerrorlab -- error raised explicitly by YYERROR.  |
  `---------------------------------------------------*/
  yyerrorlab:

    /* Pacify compilers like GCC when the user code never invokes
       YYERROR and the label yyerrorlab therefore never appears in user
       code.  */
    if (false)
      goto yyerrorlab;
    yyerror_range[1].location = yystack_[yylen - 1].location;
    /* Do not reclaim the symbols of the rule whose action triggered
       this YYERROR.  */
    yypop_ (yylen);
    yylen = 0;
    goto yyerrlab1;

  /*-------------------------------------------------------------.
  | yyerrlab1 -- common code for both syntax error and YYERROR.  |
  `-------------------------------------------------------------*/
  yyerrlab1:
    yyerrstatus_ = 3;   // Each real token shifted decrements this.
    {
      stack_symbol_type error_token;
      for (;;)
        {
          yyn = yypact_[yystack_[0].state];
          if (!yy_pact_value_is_default_ (yyn))
            {
              yyn += yyterror_;
              if (0 <= yyn && yyn <= yylast_ && yycheck_[yyn] == yyterror_)
                {
                  yyn = yytable_[yyn];
                  if (0 < yyn)
                    break;
                }
            }

          // Pop the current state because it cannot handle the error token.
          if (yystack_.size () == 1)
            YYABORT;

          yyerror_range[1].location = yystack_[0].location;
          yy_destroy_ ("Error: popping", yystack_[0]);
          yypop_ ();
          YY_STACK_PRINT ();
        }

      yyerror_range[2].location = yyla.location;
      YYLLOC_DEFAULT (error_token.location, yyerror_range, 2);

      // Shift the error token.
      error_token.state = yyn;
      yypush_ ("Shifting", error_token);
    }
    goto yynewstate;

    // Accept.
  yyacceptlab:
    yyresult = 0;
    goto yyreturn;

    // Abort.
  yyabortlab:
    yyresult = 1;
    goto yyreturn;

  yyreturn:
    if (!yyla.empty ())
      yy_destroy_ ("Cleanup: discarding lookahead", yyla);

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYABORT or YYACCEPT.  */
    yypop_ (yylen);
    while (1 < yystack_.size ())
      {
        yy_destroy_ ("Cleanup: popping", yystack_[0]);
        yypop_ ();
      }

    return yyresult;
  }
    catch (...)
      {
        YYCDEBUG << "Exception caught: cleaning lookahead and stack"
                 << std::endl;
        // Do not try to display the values of the reclaimed symbols,
        // as their printer might throw an exception.
        if (!yyla.empty ())
          yy_destroy_ (YY_NULLPTR, yyla);

        while (1 < yystack_.size ())
          {
            yy_destroy_ (YY_NULLPTR, yystack_[0]);
            yypop_ ();
          }
        throw;
      }
  }

  void
  GclParser::error (const syntax_error& yyexc)
  {
    error (yyexc.location, yyexc.what());
  }

  // Generate an error message.
  std::string
  GclParser::yysyntax_error_ (state_type yystate, const symbol_type& yyla) const
  {
    // Number of reported tokens (one for the "unexpected", one per
    // "expected").
    size_t yycount = 0;
    // Its maximum.
    enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
    // Arguments of yyformat.
    char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];

    /* There are many possibilities here to consider:
       - If this state is a consistent state with a default action, then
         the only way this function was invoked is if the default action
         is an error action.  In that case, don't check for expected
         tokens because there are none.
       - The only way there can be no lookahead present (in yyla) is
         if this state is a consistent state with a default action.
         Thus, detecting the absence of a lookahead is sufficient to
         determine that there is no unexpected or expected token to
         report.  In that case, just report a simple "syntax error".
       - Don't assume there isn't a lookahead just because this state is
         a consistent state with a default action.  There might have
         been a previous inconsistent state, consistent state with a
         non-default action, or user semantic action that manipulated
         yyla.  (However, yyla is currently not documented for users.)
       - Of course, the expected token list depends on states to have
         correct lookahead information, and it depends on the parser not
         to perform extra reductions after fetching a lookahead from the
         scanner and before detecting a syntax error.  Thus, state
         merging (from LALR or IELR) and default reductions corrupt the
         expected token list.  However, the list is correct for
         canonical LR with one exception: it will still contain any
         token that will not be accepted due to an error action in a
         later state.
    */
    if (!yyla.empty ())
      {
        int yytoken = yyla.type_get ();
        yyarg[yycount++] = yytname_[yytoken];
        int yyn = yypact_[yystate];
        if (!yy_pact_value_is_default_ (yyn))
          {
            /* Start YYX at -YYN if negative to avoid negative indexes in
               YYCHECK.  In other words, skip the first -YYN actions for
               this state because they are default actions.  */
            int yyxbegin = yyn < 0 ? -yyn : 0;
            // Stay within bounds of both yycheck and yytname.
            int yychecklim = yylast_ - yyn + 1;
            int yyxend = yychecklim < yyntokens_ ? yychecklim : yyntokens_;
            for (int yyx = yyxbegin; yyx < yyxend; ++yyx)
              if (yycheck_[yyx + yyn] == yyx && yyx != yyterror_
                  && !yy_table_value_is_error_ (yytable_[yyx + yyn]))
                {
                  if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                    {
                      yycount = 1;
                      break;
                    }
                  else
                    yyarg[yycount++] = yytname_[yyx];
                }
          }
      }

    char const* yyformat = YY_NULLPTR;
    switch (yycount)
      {
#define YYCASE_(N, S)                         \
        case N:                               \
          yyformat = S;                       \
        break
        YYCASE_(0, YY_("syntax error"));
        YYCASE_(1, YY_("syntax error, unexpected %s"));
        YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
        YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
        YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
        YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
      }

    std::string yyres;
    // Argument number.
    size_t yyi = 0;
    for (char const* yyp = yyformat; *yyp; ++yyp)
      if (yyp[0] == '%' && yyp[1] == 's' && yyi < yycount)
        {
          yyres += yytnamerr_ (yyarg[yyi++]);
          ++yyp;
        }
      else
        yyres += *yyp;
    return yyres;
  }


  const signed char GclParser::yypact_ninf_ = -21;

  const signed char GclParser::yytable_ninf_ = -1;

  const short int
  GclParser::yypact_[] =
  {
     -21,     6,    -9,   -21,    33,   -21,   -21,    -4,    12,    20,
     -21,    42,    41,    41,   -21,   -21,   -21,   -21,   -21,    27,
     -21,    13,    67,   -21,   -21,    -9,    -9,    67,    67,    67,
      67,    43,   -21,    39,   132,   -21,    40,   -21,    20,   -21,
      67,   -21,    83,    29,    32,   102,   -21,   -21,   -21,    67,
     -21,    67,    67,    67,    67,    67,    67,    67,    67,    67,
      67,    67,    67,    67,   -21,   -21,   132,    56,   -21,   -21,
     -21,   119,   -21,   -21,    26,    26,     0,     0,     0,     0,
     -11,   -11,   157,   169,   145,    49,   -21,    48,    52,   -21,
     -21,    15,    41,    41,    34,   -21,   -21,   -21,    54,    62,
     -21,    67,   132
  };

  const unsigned char
  GclParser::yydefact_[] =
  {
       3,     0,    12,     1,     7,     4,     5,     0,     0,     0,
      45,     0,     0,     0,    13,    14,     2,     8,    11,     0,
       9,     0,     0,    32,    33,     0,     0,     0,     0,     0,
       0,    52,    23,     0,    17,    22,     0,     6,     0,    44,
       0,    46,     0,     0,     0,     0,    25,    30,    31,     0,
      15,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    16,    10,    47,     0,    18,    20,
      24,     0,    26,    27,    28,    29,    34,    35,    36,    37,
      38,    39,    40,    41,    42,     0,    45,     0,     0,    53,
      49,     0,     0,     0,    48,    43,    19,    21,     0,     0,
      50,     0,    51
  };

  const signed char
  GclParser::yypgoto_[] =
  {
     -21,   -21,   -21,   -21,   -21,    28,   -21,    37,   -21,   -21,
     -21,   -13,   -21,   -21,   -20,   -21,    -3,   -21,   -21,   -21,
     -21,   -17
  };

  const signed char
  GclParser::yydefgoto_[] =
  {
      -1,     1,     2,     5,     9,     6,    19,    20,     7,    14,
      15,    33,    87,    88,    34,    16,    21,    41,    85,    94,
      98,    35
  };

  const unsigned char
  GclParser::yytable_[] =
  {
      36,    10,    42,    11,    12,    13,     3,    45,    46,    47,
      48,    51,    52,    53,    54,    55,    56,    57,    58,    39,
      66,    95,    51,    52,    53,    54,    40,     4,    40,    71,
      17,    72,    73,    74,    75,    76,    77,    78,    79,    80,
      81,    82,    83,    84,    23,    24,    37,    38,    51,    52,
       8,    25,    26,    43,    44,    18,    27,    22,    50,    64,
      49,    86,    28,    90,    68,    29,    30,    69,    92,    31,
      23,    24,    93,   100,   101,    65,    31,    99,    32,    96,
      97,   102,    27,    91,     0,     0,     0,     0,    28,     0,
       0,    29,    30,     0,     0,     0,     0,     0,     0,    67,
       0,     0,    31,     0,    32,    51,    52,    53,    54,    55,
      56,    57,    58,    59,    60,    61,    62,    63,    70,     0,
       0,     0,     0,     0,    51,    52,    53,    54,    55,    56,
      57,    58,    59,    60,    61,    62,    63,    89,     0,     0,
       0,    51,    52,    53,    54,    55,    56,    57,    58,    59,
      60,    61,    62,    63,    51,    52,    53,    54,    55,    56,
      57,    58,    59,    60,    61,    62,    63,    51,    52,    53,
      54,    55,    56,    57,    58,    59,    60,    61,    62,    51,
      52,    53,    54,    55,    56,    57,    58,    59,    60,     0,
      62,    51,    52,    53,    54,    55,    56,    57,    58,    59,
      60
  };

  const signed char
  GclParser::yycheck_[] =
  {
      13,     5,    22,     7,     8,     9,     0,    27,    28,    29,
      30,    22,    23,    24,    25,    26,    27,    28,    29,     6,
      40,     6,    22,    23,    24,    25,    13,    36,    13,    49,
      18,    51,    52,    53,    54,    55,    56,    57,    58,    59,
      60,    61,    62,    63,     3,     4,    19,    20,    22,    23,
      17,    10,    11,    25,    26,    35,    15,    15,    19,    19,
      17,     5,    21,    14,    35,    24,    25,    35,    20,    35,
       3,     4,    20,    19,    12,    38,    35,    94,    37,    92,
      93,   101,    15,    86,    -1,    -1,    -1,    -1,    21,    -1,
      -1,    24,    25,    -1,    -1,    -1,    -1,    -1,    -1,    16,
      -1,    -1,    35,    -1,    37,    22,    23,    24,    25,    26,
      27,    28,    29,    30,    31,    32,    33,    34,    16,    -1,
      -1,    -1,    -1,    -1,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    34,    18,    -1,    -1,
      -1,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31,    32,    33,    34,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    34,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    22,
      23,    24,    25,    26,    27,    28,    29,    30,    31,    -1,
      33,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31
  };

  const unsigned char
  GclParser::yystos_[] =
  {
       0,    41,    42,     0,    36,    43,    45,    48,    17,    44,
       5,     7,     8,     9,    49,    50,    55,    18,    35,    46,
      47,    56,    15,     3,     4,    10,    11,    15,    21,    24,
      25,    35,    37,    51,    54,    61,    51,    19,    20,     6,
      13,    57,    54,    45,    45,    54,    54,    54,    54,    17,
      19,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31,    32,    33,    34,    19,    47,    54,    16,    35,    35,
      16,    54,    54,    54,    54,    54,    54,    54,    54,    54,
      54,    54,    54,    54,    54,    58,     5,    52,    53,    18,
      14,    56,    20,    20,    59,     6,    51,    51,    60,    61,
      19,    12,    54
  };

  const unsigned char
  GclParser::yyr1_[] =
  {
       0,    40,    41,    42,    42,    44,    43,    45,    45,    46,
      46,    47,    48,    48,    48,    49,    50,    51,    52,    51,
      53,    51,    54,    54,    54,    54,    54,    54,    54,    54,
      54,    54,    54,    54,    54,    54,    54,    54,    54,    54,
      54,    54,    54,    55,    55,    56,    56,    58,    57,    59,
      59,    60,    61,    61
  };

  const unsigned char
  GclParser::yyr2_[] =
  {
       0,     2,     3,     0,     2,     0,     4,     1,     3,     1,
       3,     1,     0,     2,     2,     3,     3,     1,     0,     6,
       0,     6,     1,     1,     3,     2,     3,     3,     3,     3,
       2,     2,     1,     1,     3,     3,     3,     3,     3,     3,
       3,     3,     3,     7,     3,     0,     2,     0,     5,     0,
       3,     3,     1,     4
  };



  // YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
  // First, the terminals, then, starting at \a yyntokens_, nonterminals.
  const char*
  const GclParser::yytname_[] =
  {
  "\"EOF\"", "error", "$undefined", "\"true\"", "\"false\"", "\"do\"",
  "\"od\"", "\"while\"", "\"requires\"", "\"ensures\"", "\"forall\"",
  "\"exists\"", "\"=\"", "\"::\"", "\"->\"", "\"(\"", "\")\"", "\"[\"",
  "\"]\"", "\";\"", "\",\"", "\"!\"", "\"*\"", "\"/\"", "\"+\"", "\"-\"",
  "\">\"", "\">=\"", "\"<\"", "\"<=\"", "\"==\"", "\"!=\"", "\"|\"",
  "\"&\"", "\"==>\"", "\"identifier\"", "\"type identifier\"",
  "\"number\"", "UPLUS", "UMINUS", "$accept", "program",
  "var_declaration_list", "var_declaration", "$@1", "type_id",
  "var_declarators", "var_declarator", "assertion_list", "pre_condition",
  "post_condition", "formula", "$@2", "$@3", "expr", "loop_body",
  "guarded_command_list", "guarded_command", "$@4", "assignment_list",
  "assignment", "location", YY_NULLPTR
  };

#if YYDEBUG
  const unsigned short int
  GclParser::yyrline_[] =
  {
       0,   108,   108,   112,   113,   117,   117,   122,   127,   135,
     136,   140,   148,   149,   150,   154,   158,   162,   164,   164,
     171,   171,   181,   182,   184,   185,   187,   189,   191,   193,
     195,   196,   198,   199,   200,   202,   204,   206,   208,   210,
     212,   214,   216,   221,   230,   237,   238,   242,   242,   251,
     252,   258,   262,   273
  };

  // Print the state stack on the debug stream.
  void
  GclParser::yystack_print_ ()
  {
    *yycdebug_ << "Stack now";
    for (stack_type::const_iterator
           i = yystack_.begin (),
           i_end = yystack_.end ();
         i != i_end; ++i)
      *yycdebug_ << ' ' << i->state;
    *yycdebug_ << std::endl;
  }

  // Report on the debug stream that the rule \a yyrule is going to be reduced.
  void
  GclParser::yy_reduce_print_ (int yyrule)
  {
    unsigned int yylno = yyrline_[yyrule];
    int yynrhs = yyr2_[yyrule];
    // Print the symbols being reduced, and their result.
    *yycdebug_ << "Reducing stack by rule " << yyrule - 1
               << " (line " << yylno << "):" << std::endl;
    // The symbols being reduced.
    for (int yyi = 0; yyi < yynrhs; yyi++)
      YY_SYMBOL_PRINT ("   $" << yyi + 1 << " =",
                       yystack_[(yynrhs) - (yyi + 1)]);
  }
#endif // YYDEBUG


#line 4 "parser/GclParser.yy" // lalr1.cc:1167
} // parser
#line 1537 "parser/GclParser.cpp" // lalr1.cc:1167
#line 290 "parser/GclParser.yy" // lalr1.cc:1168

void parser::GclParser::error(const location_type& l,
                              const std::string& m)
{
  std::cout << l << m << std::endl;
  program::GclAnalyzer::setErrorFlag();
}
