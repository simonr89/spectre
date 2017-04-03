/**
 * @file Variable.cpp
 *
 */

#include "Variable.hpp"

#include <cassert>
#include "logic/Signature.hpp"
#include "logic/Theory.hpp"

namespace program {

  Variable::~Variable() {}

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

  /*unsigned Variable::symbolNumber(bool extended)
  {
    bool added, isPred;
    int res;
    switch (_type) {
    case TY_INTEGER:
    case TY_INTEGER_ARRAY:
      isPred = false;
      res = Lib::env.signature->addFunction(_name, arityOfSymbol(extended), added);
      break;
    case TY_BOOLEAN:
    case TY_BOOLEAN_ARRAY:
      isPred = true;
      res = Lib::env.signature->addPredicate(_name, arityOfSymbol(extended), added);
      break;
    }
    if (added) {
      Kernel::Signature::Symbol* symb;
      if (isPred)
        symb = Lib::env.signature->getPredicate(res);
      else
        symb = Lib::env.signature->getFunction(res);
      
      symb->setType(typeOfSymbol(extended));
      if (_updated && extended)
        symb->addColor(Kernel::COLOR_LEFT);
      symb->markIntroduced();
    }

    return res;
    }*/

  unsigned PVariable::arityOfSymbol(bool extended)
  {
    unsigned arity = _updated && extended ? 1 : 0;
    if (isArrayType(_type))
      arity++;
    return arity;
  }

  /*Kernel::BaseType * Variable::typeOfSymbol(bool extended)
  {
    return mkBaseType(arityOfSymbol(extended), _type);
    }*/

  logic::Term* PVariable::toTerm(logic::Term* index)
  {
    assert(_type == Type::TY_BOOLEAN || _type == Type::TY_INTEGER);
    if (_updated && index) {
      // extended symbol (and the variable is not constant)
      if (_type == Type::TY_BOOLEAN) {
        return new logic::PredTerm(logic::Symbol::getSymbol(_name, 1), { index });
      } else {
        return new logic::FuncTerm(logic::Symbol::getSymbol(_name, 1), { index });
      }
    } else {
      if (_type == Type::TY_BOOLEAN) {
        return new logic::PredTerm(logic::Symbol::getSymbol(_name, 0), { });
      } else {
        return new logic::FuncTerm(logic::Symbol::getSymbol(_name, 0), { });
      }
    }
  }

  logic::Term* PVariable::toTerm(logic::Term* index, logic::Term* arrayIndex)
  {
    assert(_type == Type::TY_BOOLEAN_ARRAY || _type == Type::TY_INTEGER_ARRAY);

    if (_updated && index) {
      // extended symbol (and the array is not constant)
      if (_type == Type::TY_BOOLEAN) {
        return new logic::PredTerm(logic::Symbol::getSymbol(_name, 2), { index, arrayIndex });
      } else {
        return new logic::FuncTerm(logic::Symbol::getSymbol(_name, 2), { index, arrayIndex });
      }
    } else {
      if (_type == Type::TY_BOOLEAN) {
        return new logic::PredTerm(logic::Symbol::getSymbol(_name, 1), { arrayIndex });
      } else {
        return new logic::FuncTerm(logic::Symbol::getSymbol(_name, 1), { arrayIndex });
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
