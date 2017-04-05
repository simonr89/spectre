#include "Term.hpp"

namespace logic {

  unsigned LVariable::freshId = 0;

  std::string LVariable::toTPTP() const {
    return name();
  }
  
  std::string FuncTerm::toTPTP() const {
    if (_subterms.size() == 0) {
      return _head->name();
    } else {
      std::string str = _head->name() + "(";
      for (unsigned i = 0; i < _subterms.size(); i++) {
        str += _subterms[i]->toTPTP();
        str += (i == _subterms.size() - 1) ? ")" : ",";
      }
      return str;
    }
  }

  std::string PredTerm::toTPTP() const {
    if (_subterms.size() == 0) {
      return _head->name();
    } else {
      std::string str = _head->name() + "(";
      for (unsigned i = 0; i < _subterms.size(); i++) {
        str += _subterms[i]->toTPTP();
        str += (i == _subterms.size() - 1) ? ")" : ",";
      }
      return str;
    }
  }

  std::list<LVariable*> LVariable::freeVariables() const {
    LVariable *v = new LVariable(*this);
    return { v };
  }

  std::list<LVariable*> FuncTerm::freeVariables() const {
    std::list<LVariable*> l;
    for (unsigned i = 0; i < _subterms.size(); i++) {
      l.splice(l.end(), _subterms[i]->freeVariables());
    }
    return l;
  }

  std::list<LVariable*> PredTerm::freeVariables() const {
    std::list<LVariable*> l;
    for (unsigned i = 0; i < _subterms.size(); i++) {
      l.splice(l.end(), _subterms[i]->freeVariables());
    }
    return l;
  }
}

