/**
 * @file Variable.cpp
 *
 */

#include "Variable.hpp"

#include <iostream>
#include <cassert>
#include "logic/Theory.hpp"
#include "util/Options.hpp"

namespace program {

  using namespace logic;

  Variable::~Variable() {}

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
        // representation of arrays as function
        _symbol = new logic::Symbol(name, { logic::Sort::intSort() }, toSort(ty));
        _extendedSymbol = new logic::Symbol(name, { logic::Sort::intSort(), logic::Sort::intSort() }, toSort(ty));
      } else {
        // representation of using array axioms
        _symbol = new logic::Symbol(name, {}, logic::Sort::arraySort());
        _extendedSymbol = new logic::Symbol(name, { logic::Sort::intSort() }, logic::Sort::arraySort());
      }
    } else {
      _symbol = new logic::Symbol(name, { }, toSort(ty));
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
    assert(_type == Type::TY_BOOLEAN || _type == Type::TY_INTEGER);
    if (_updated && index) {
      // extended symbol (and the variable is not constant)
      if (_type == Type::TY_BOOLEAN) {
        return new PredTerm(Symbol::getSymbol(_name, 1), { index });
      } else {
        return new FuncTerm(Symbol::getSymbol(_name, 1), { index });
      }
    } else {
      if (_type == Type::TY_BOOLEAN) {
        return new PredTerm(Symbol::getSymbol(_name, 0), { });
      } else {
        return new FuncTerm(Symbol::getSymbol(_name, 0), { });
      }
    }
  }

  Term* PVariable::toTerm(Term* index, Term* arrayIndex)
  {
    assert(_type == Type::TY_BOOLEAN_ARRAY || _type == Type::TY_INTEGER_ARRAY);

    Symbol *sym = nullptr;
    
    if (util::Configuration::instance().arrayRepresentation().getValue() == "function") {
      // representation of arrays as function
      sym = Symbol::getSymbol(_name, _updated && index ? 2 : 1);
      assert(sym);
      if (_updated && index) {
        if (_type == Type::TY_BOOLEAN) {
          return new PredTerm(sym, { index, arrayIndex });
        } else {
          return new FuncTerm(sym, { index, arrayIndex });
        }
      } else {
        if (_type == Type::TY_BOOLEAN) {
          return new PredTerm(sym, { arrayIndex });
        } else {
          return new FuncTerm(sym, { arrayIndex });
        }
      }
    } else {
      // representation using array axioms
      Term *array;
      sym = Theory::getSymbol(InterpretedSymbol::ARRAY_SELECT);
      assert(sym);
      
      if (_updated && index) {
        array = new FuncTerm(Symbol::getSymbol(_name, 1), { index });
      } else {
        array = new FuncTerm(Symbol::getSymbol(_name, 0), {});
      }
      assert(array);

      if (_type == Type::TY_BOOLEAN) {
        return new PredTerm(sym, { array, arrayIndex });
      } else {
        return new FuncTerm(sym, { array, arrayIndex });
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
