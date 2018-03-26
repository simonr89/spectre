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
#include "Formula.hpp"
#include "Signature.hpp"
#include "Sort.hpp"
#include "Term.hpp"
#include "Type.hpp"

namespace program {

  class Variable {
  public:
    virtual bool isProgramVariable() = 0;

    virtual logic::Term *toTerm(const logic::Term* i, bool updated=true) const = 0;
    
    /** the name of this variable */
    const std::string& name() const { return _name; }

    const Type vtype() const { return _type; }
    
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
    PVariable(const std::string& name, Type ty);

    ~PVariable() {}

    bool isProgramVariable() { return true; }

//    /** true if the variable is on the LHS of at least one assignment in
//        the loop */
//    bool isUpdated() { return _updated; }
//
//    /** true if the variable is only incremented by positive constants,
//        or only by negative constants */
//    bool isMonotonic() { return _monotonic; }
//
//    /** true if the variable is incremented/decremented by at least one
//        at every iteration */
//    bool isStrict() { return _strict; }
//
//    /** true if the variable is incremented/decremented by at most one
//        at every iteration */
//    bool isDense() { return _dense; }
//
//    /** 1 if the variable is monotonic increasing, -1 if it is monotonic
//        decreasing, 0 if constant or otherwise non-monotonic*/
//    int monotonicity() { return _monotonic; }
//
//    void setUpdated() { _updated = true; }
//
//    void setStrict() { _strict = true; }
//
//    void setDense() { _dense = true; }
//
//    void setMonotonic(bool b) { _monotonic = b; }

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
    logic::Term *toTerm(const logic::Term* i, bool updated=true) const override;

    /** Same as above for array variables */
    logic::Term *toTerm(const logic::Term* i, const logic::Term* arrayIndex, bool updated=true) const;

    friend std::ostream& operator<<(std::ostream& ostr, const PVariable& v);

      std::string toString() const;
  protected:
//
//    /** Whether the variable is updated by the loop */
//    bool _updated;
//    /** -1, 0, or 1 */
//    short _monotonic;
//
//    bool _strict;
//
//    bool _dense;

    /** the symbol associated to that variable in FOL terms. If extended
        is set to true, this is the symbol for extended expressions
        (used internally), else it is the one used for output
        invariants. nullptr for variables used in quantified
        expressions */
    logic::Symbol* _symbol;
    logic::Symbol* _extendedSymbol;
    
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

    bool isProgramVariable() { return false; }

    logic::Term *toTerm(const logic::Term* i, bool updated=true) const { return _lvariable; }

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
