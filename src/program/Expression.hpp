/**
 * @file Expression.hpp
 *
 * Defines class Program::Expression, representing expressions in the
 * guarded command language
 *
 */

#ifndef __ProgramExpression__
#define __ProgramExpression__

#include "Term.hpp"
#include "Formula.hpp"
#include "Variable.hpp"
#include "Type.hpp"

namespace program {

  class ArithmeticExpression;
  class BooleanExpression;
  class LocationExpression;
  class QuantifiedExpression;

  /**
   * Expressions used in programs
   */
  class Expression
  {
  public:
    virtual ~Expression() = 0;
    /** return the type of the expression */
    virtual Type etype() = 0;

    // this could be a FOOL predicate
    virtual logic::Term* toTerm(logic::Term* index) = 0;

    virtual std::ostream& toStream(std::ostream& ostr) const = 0;

    /** number of sub-expressions */
    int arity() { return _arity; }

    /** return the nth sub-expression, or nullptr if n > arity */
    Expression *child(unsigned n);

    virtual bool evalToCstInt(int &value) { return false; }

    virtual bool equivToVPlusX(PVariable *v, int &value) { return false; }

    // TODO remove this and leave it only in appropriate derived classes?
    //virtual logic::Term* toTerm(logic::Term* i) { return nullptr; }

  protected:
    Expression() :
      _arity(0),
      _children(nullptr)
    {}
  
    Expression(unsigned arity) :
      _arity(arity)
    {
      _children = new Expression*[arity];
    }

    unsigned _arity;
  
    Expression** _children;
  
  }; // class Expression

  // Expressions convertible to FOL formulas
  class FExpression : public virtual Expression
  {
  public:
    
    virtual logic::Formula* toFormula(logic::Term* index) = 0;
  };
  
  class ArithmeticExpression : public Expression
  {
  public:

    enum class ArithExprKind {
      EXP_CST_INTEGER,
      EXP_ADD,
      EXP_SUB,
      EXP_MUL,
      EXP_DIV,
      EXP_MINUS
    };

    /** True iff the whole expression can be evaluated to a constant
        integer, in which case the value of that integer is copied to
        value */
    bool evalToCstInt(int &value) override;

    bool equivToVPlusX(PVariable *v, int &value) override;

    Type etype() { return Type::TY_INTEGER; }

    std::ostream& toStream(std::ostream& ostr) const;

    /** Relativised expression index at iteration, as a vampire term */
    logic::Term* toTerm(logic::Term* i) override;

    /** Static initializers, return nullptr if the sub-expressions are
        ill-typed */
    static ArithmeticExpression * mkConstantInteger(int v);
    static ArithmeticExpression * mkAdd(Expression* e1, Expression* e2);
    static ArithmeticExpression * mkSub(Expression* e1, Expression* e2);
    static ArithmeticExpression * mkMul(Expression* e1, Expression* e2);
    static ArithmeticExpression * mkDiv(Expression* e1, Expression* e2);
    static ArithmeticExpression * mkMinus(Expression* e);

  protected:
    ArithmeticExpression(ArithExprKind kind) :
      Expression(),
      _kind(kind)
    {}
  
    ArithmeticExpression(ArithExprKind kind, unsigned arity) :
      Expression(arity),
      _kind(kind)
    {}

    ArithExprKind _kind;
    
    int _constInfo;
  }; // class ArithmeticExpression

  class BooleanExpression : public FExpression
  {
  public:

    enum class BooleanExprKind {
      EXP_CST_BOOLEAN,
      EXP_NEG,
      EXP_OR,
      EXP_AND,
      EXP_GE,
      EXP_GT,
      EXP_LE,
      EXP_LT,
      EXP_EQ
    };

    bool constBooleanInfo(bool& value);

    Type etype() { return Type::TY_BOOLEAN; }

    std::ostream& toStream(std::ostream& ostr) const override;

    /** Relativised expression index at iteration, as a FOL
        term. */
    logic::Term* toTerm(logic::Term* i) override;

    logic::Formula* toFormula(logic::Term* i) override;

    /** Static initializers, return nullptr if the sub-expressions are
        ill-typed */
    static BooleanExpression* mkConstantBoolean(bool v);
    static BooleanExpression* mkNegation(Expression *e);
    static BooleanExpression* mkOr(Expression *e1, Expression *e2);
    static BooleanExpression* mkAnd(Expression *e1, Expression *e2);
    static BooleanExpression* mkGe(Expression *e1, Expression *e2);
    static BooleanExpression* mkGt(Expression *e1, Expression *e2);
    static BooleanExpression* mkLe(Expression *e1, Expression *e2);
    static BooleanExpression* mkLt(Expression *e1, Expression *e2);
    static BooleanExpression* mkEq(Expression *e1, Expression *e2);
    static BooleanExpression* mkNeq(Expression *e1, Expression *e2);
    static BooleanExpression* mkImplication(Expression *e1, Expression *e2);

  protected:
    BooleanExpression(BooleanExprKind kind) :
      Expression(),
      _kind(kind)
    {}

    BooleanExpression(BooleanExprKind kind, unsigned arity) :
      Expression(arity),
      _kind(kind)
    {}

    BooleanExprKind _kind;

    bool _constInfo;
  }; // class BooleanExpression

  class LocationExpression : public FExpression
  {
  public:

    enum class LocationExprKind {
      EXP_VAR_LOC,
      EXP_ARRAY_LOC,
      EXP_FIELD_LOC
    };

    bool equivToVPlusX(PVariable *v, int &value) override;

    PVariable *varInfo() { return _var; }

    Type etype();

    std::ostream& toStream(std::ostream& ostr) const override;

    /** Relativised expression index at iteration, as a FOL term
        (possibly a predicate) */
    logic::Term* toTerm(logic::Term* i) override;

    logic::Formula* toFormula(logic::Term* i) override;
    
    /** Static initializers, return nullptr if the sub-expressions are
        ill-typed */
    static LocationExpression * mkProgramVariable(PVariable* v);
    static LocationExpression * mkArrayApp(PVariable* v, Expression* e2);
    static LocationExpression * mkFieldAccess(Expression *e, Expression* e2); 

  protected:

    LocationExpression(LocationExprKind kind, PVariable *v) :
      Expression(),
      _kind(kind),
      _var(v)
    {}

    LocationExpression(LocationExprKind kind, PVariable *v, unsigned arity) :
      Expression(arity),
      _kind(kind),
      _var(v)
    {}

    LocationExprKind _kind;
  
    PVariable *_var;
  }; // class LocationExpression

  class VariableExpression : public FExpression
  {
  public:
    Type etype() { return _var->vtype(); }

    std::ostream& toStream(std::ostream& ostr) const override;

    /** Relativised expression index at iteration, as a vampire
        predicate. */
    logic::Term* toTerm(logic::Term* i) override;

    logic::Formula* toFormula(logic::Term* i) override;
    
    /** Static initializers, return nullptr if the sub-expressions are
        ill-typed */
    static VariableExpression * mkQuantifiedVariable(QVariable *v);
  protected:
    VariableExpression(QVariable *v) :
      Expression(),
      _var(v)
    {}
    
    QVariable* _var;
  }; // class VariableExpression
  
  class QuantifiedExpression : public FExpression
  {
  public:
  
    enum class QuantifiedExprKind {
      EXP_FORALL,
      EXP_EXISTS
    };

    Type etype() { return Type::TY_FORMULA; }

    std::ostream& toStream(std::ostream& ostr) const override;

    /** Relativised expression index at iteration, as a vampire
        predicate. */
    logic::Term* toTerm(logic::Term* i) override;

    logic::Formula* toFormula(logic::Term* i) override;
    
    /** Static initializers, return nullptr if the sub-expressions are
        ill-typed */
    static QuantifiedExpression * mkForall(QVariable *v, Expression *e);
    static QuantifiedExpression * mkExists(QVariable *v, Expression *e);

  protected:

    QuantifiedExpression(QuantifiedExprKind kind) :
      Expression(1),
      _kind(kind)
    {}

    QuantifiedExprKind _kind;
  
    QVariable *_var;

  }; // class QuantifiedExpression
  
  /** Pretty-printer. Well not so pretty since it puts parentheses everywhere. */
  inline std::ostream& operator<<(std::ostream& ostr, const Expression& e) { return e.toStream(ostr); }

}
#endif
