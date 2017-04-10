/**
 *
 * @file Variable.hpp
 *
 * Program variables (and variables coming from assertion quantifiers)
 */

#ifndef __ProgramVariable__
#define __ProgramVariable__


#include <string>
#include <ostream>
#include "logic/Formula.hpp"
#include "logic/Signature.hpp"
#include "logic/Sort.hpp"
#include "logic/Term.hpp"
#include "program/Type.hpp"

namespace program {

  class Variable {
  public:
    virtual ~Variable() = 0;

    /** the name of this variable */
    const std::string& name() { return _name; }

    const Type vtype() { return _type; }
    
  protected:
    
    Variable(const std::string& name, Type ty) :
      _name(name),
      _type(ty)
    {}
    
    std::string _name;

    Type _type;
  };
  
  class PVariable : public Variable {
  public:
  
    /** the main constructors */
    PVariable(const std::string& name, Type ty) :
      Variable(name, ty),
      _updated(false),
      _monotonic(false),
      _strict(false),
      _dense(false)
    {
      if (isArrayType(ty)) {
        _symbol = new logic::Symbol(name, { logic::Sort::intSort() }, toSort(ty));
        _extendedSymbol = new logic::Symbol(name, { logic::Sort::intSort(), logic::Sort::intSort() }, toSort(ty));
      } else {
        _symbol = new logic::Symbol(name, { }, toSort(ty));
        _extendedSymbol = new logic::Symbol(name, { logic::Sort::intSort() }, toSort(ty));

      }
    }

    ~PVariable() {}

    /** true if the variable is on the LHS of at least one assignment in
        the loop */
    bool isUpdated() { return _updated; }

    /** true if the variable is only incremented by positive constants,
        or only by negative constants */
    bool isMonotonic() { return _monotonic; }

    /** true if the variable is incremented/decremented by at least one
        at every iteration */
    bool isStrict() { return _strict; }

    /** true if the variable is incremented/decremented by at most one
        at every iteration */
    bool isDense() { return _dense; }

    /** 1 if the variable is monotonic increasing, -1 if it is monotonic
        decreasing, 0 if constant or otherwise non-monotonic*/
    int monotonicity() { return _monotonic; }
  
    void setUpdated() { _updated = true; }

    void setStrict() { _strict = true; }

    void setDense() { _dense = true; }

    void setMonotonic(bool b) { _monotonic = b; }

    void recordScalarIncrement(int n);

    bool isBoolean() { return _type == Type::TY_BOOLEAN || _type == Type::TY_BOOLEAN_ARRAY; }
  
    /** Return the vampire term representing the relatived expression of
     * this variable at iteration i. If i is an empty termlist, return
     * the final expression instead
     * 
     * This version only for scalar variables.
     *
     * This function should be called only after the loop has been
     * constructed, since the arity of the symbol depends on the value
     * of 'updated'
     */
    logic::Term *toTerm(logic::Term* i);

    /** Same as above for array variables */
    logic::Term *toTerm(logic::Term* i, logic::Term* arrayIndex);

    /** Same as above for boolean variables */
    //logic::PredTerm* toPred(logic::Term* i);

    /** Same as above for boolean arrays */
    //logic::PredTerm* toPred(logic::Term* i, logic::Term* arrayIndex);

    friend std::ostream& operator<<(std::ostream& ostr, const PVariable& v);

  protected:
    
    /** Whether the variable is updated by the loop */
    bool _updated;
    /** -1, 0, or 1 */
    short _monotonic;

    bool _strict;

    bool _dense;

    /** the symbol associated to that variable in FOL terms. If extended
        is set to true, this is the symbol for extended expressions
        (used internally), else it is the one used for output
        invariants. nullptr for variables used in quantified
        expressions */
    logic::Symbol* _symbol;
    logic::Symbol* _extendedSymbol;

    unsigned arityOfSymbol(bool extended);
  
    //Kernel::BaseType * typeOfSymbol(bool extended);
  
  }; // class PVariable

  class QVariable : public Variable {
  public:

    QVariable(const std::string& name, Type ty) :
      Variable(name, ty)
    {
      switch (ty) {
      case Type::TY_INTEGER:
        _lvariable = new logic::LVariable(logic::Sort::intSort());
        break;
      case Type::TY_BOOLEAN:
        _lvariable = new logic::LVariable(logic::Sort::boolSort());
        break;
      default:
        _lvariable = nullptr;
      }
    }

    ~QVariable() {}

    logic::LVariable* toVar() { return _lvariable; }
    
    friend std::ostream& operator<<(std::ostream& ostr, const QVariable& v);

  protected:    
    unsigned _id;

    logic::LVariable* _lvariable;
    
  }; // class QVariable
  
  std::ostream& operator<<(std::ostream& ostr, const PVariable& v);

  std::ostream& operator<<(std::ostream& ostr, const QVariable& v);

}

#endif // __ProgramVariable__