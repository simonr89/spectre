/**
 * @file Variable.cpp
 *
 */

#include "Variable.hpp"

#include <cassert>
#include "logic/Theory.hpp"
#include "util/Options.hpp"

namespace program {

  using namespace logic;

  /** the main constructors */
  PVariable::PVariable(const std::string& name, Type ty) :
    Variable(name, ty),
    _updated(false),
    _monotonic(false),
    _strict(false),
    _dense(false)
  {
    if (isArrayType(ty)) {
      if (util::Configuration::instance().arrayRepresentation().getValue() == "function") {
        // representation of arrays as functions
        _symbol = new logic::Symbol(name, { logic::Sort::intSort() }, toSort(ty));
        _extendedSymbol = new logic::Symbol(name, { logic::Sort::intSort(), logic::Sort::intSort() }, toSort(ty));
      } else {
        // representation of arrays using array axioms
        _symbol = new logic::Symbol(name, {}, logic::Sort::intArraySort());
        _extendedSymbol = new logic::Symbol(name, { logic::Sort::intSort() }, logic::Sort::intArraySort());
      }
    } else {
      _symbol = new logic::Symbol(name, {}, toSort(ty));
      _extendedSymbol = new logic::Symbol(name, { logic::Sort::intSort() }, toSort(ty));
    }
  }

  void PVariable::recordScalarIncrement(int n)
  {
    if (n > 0) {
      if (!_updated)
        _monotonic = 1;
      else if (_monotonic < 0)
        _monotonic = 0;
    } else if (n < 0) {
      if (!_updated)
        _monotonic = -1;
      else if (_monotonic > 0)
        _monotonic = 0;
    }
  }

  unsigned PVariable::arityOfSymbol(bool extended)
  {
    unsigned arity = _updated && extended ? 1 : 0;
    if (isArrayType(_type))
      arity++;
    return arity;
  }

  Term* PVariable::toTerm(Term* index)
  {
    if (_updated && index) {
      // extended symbol (and the variable is not constant)
      if (_type == Type::TY_BOOLEAN) {
        return new PredTerm(_extendedSymbol, { index });
      } else {
        return new FuncTerm(_extendedSymbol, { index });
      }
    } else {
      if (_type == Type::TY_BOOLEAN) {
        return new PredTerm(_symbol, {});
      } else {
        return new FuncTerm(_symbol, {});
      }
    }
  }

  Term* PVariable::toTerm(Term* index, Term* arrayIndex)
  {
    assert(isArrayType(_type));
    
    if (util::Configuration::instance().arrayRepresentation().getValue() == "function") {
      // representation of arrays as function
      if (_updated && index) {
        if (_type == Type::TY_BOOLEAN) {
          return new PredTerm(_extendedSymbol, { index, arrayIndex });
        } else {
          return new FuncTerm(_extendedSymbol, { index, arrayIndex });
        }
      } else {
        if (_type == Type::TY_BOOLEAN) {
          return new PredTerm(_symbol, { arrayIndex });
        } else {
          return new FuncTerm(_symbol, { arrayIndex });
        }
      }
    } else {
      // representation using array axioms
      Term *array;
      
      if (_updated && index) {
        array = new FuncTerm(_extendedSymbol, { index });
      } else {
        array = new FuncTerm(_symbol, {});
      }
      assert(array);

      if (_type == Type::TY_BOOLEAN) {
        return new PredTerm(Theory::getSymbol(InterpretedSymbol::ARRAY_SELECT), { array, arrayIndex });
      } else {
        return new FuncTerm(Theory::getSymbol(InterpretedSymbol::ARRAY_SELECT), { array, arrayIndex });
      }
    }
  }

  std::ostream& operator<<(std::ostream& ostr, const PVariable& v)
  {
    ostr << v._name << " : " << v._type;
    
    ostr << " {";
    if (v._updated)
      ostr << "updated,";
    switch (v._monotonic) {
    case -1:
      ostr << "monotonic decreasing,";
      break;
    case 1:
      ostr << "monotonic increasing,";
      break;
    }
    if (v._dense)
      ostr << "dense,";
    if (v._strict)
      ostr << "strict";
    ostr << "}";
    return ostr;
  }

  std::ostream& operator<<(std::ostream& ostr, const QVariable& v)
  {
    ostr << "X" << v._id << " : " << v._type;
    
    return ostr;
  }
}
