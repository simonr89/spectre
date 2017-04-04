#include "Term.hpp"

namespace logic {

  unsigned LVariable::freshId = 0;

  std::string FuncTerm::toTPTP() const {
    if (_head->arity() == 0) {
      return _head->name();
    } else {
      std::string str = _head->name() + "(";
      for (unsigned i = 0; i < _subterms.size() - 1; i++) {
        str += _subterms[i]->toTPTP() + ",";
      }
      str += _subterms[_subterms.size() - 1]->toTPTP() + ")";
      return str;
    }
  }

  std::string LVariable::toTPTP() const {
    return "X" + std::to_string(_id) + " : " + _s->name();
  }

  std::string PredTerm::toTPTP() const {
    if (_head->arity() == 0) {
      return _head->name();
    } else {
      std::string str = _head->name() + "(";
      for (unsigned i = 0; i < _subterms.size() - 1; i++) {
        str += _subterms[i]->toTPTP() + ",";
      }
      str += _subterms[_subterms.size() - 1]->toTPTP() + ")";
      return str;
    }
  }
}

