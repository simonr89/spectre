#include "Signature.hpp"

namespace logic {

  std::map<std::pair<std::string, unsigned>, Symbol*> Symbol::_signature;

  Symbol* Symbol::getSymbol(std::string name, unsigned arity) {
    auto it = _signature.find(std::pair<std::string, unsigned>(name, arity));
    return it == _signature.end() ? nullptr : (*it).second;
  }

  std::string Symbol::declareTPTP(std::string decl) const {
    std::string s = "tff(" + decl + ", type, " + _name + " : ";
    if (arity() == 0) {
      s += _rngSort->name() + ").";
    } else if (arity() == 1) {
      s += _argSorts[0]->name() + " > " + _rngSort->name() + ").";
    } else {
      s += "(";
      for (unsigned i = 0; i < _argSorts.size() - 1; i++) {
        s += _argSorts[i]->name() + " * ";
      }
      s += _argSorts[_argSorts.size() - 1]->name() + ") > " + _rngSort->name() + ").";
    }
    return s;
  }
  
}
