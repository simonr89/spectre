#include "Term.hpp"

namespace logic {

  unsigned LVariable::freshId = 0;

  std::ostream& FuncTerm::toStream(std::ostream& ostr) const {
    if (_head->arity() == 0) {
      ostr << _head->name();
    } else {
      ostr << _head->name() << "(";
      for (unsigned i = 0; i < _subterms.size() - 1; i++) {
        ostr << *_subterms[i] << ",";
      }
      ostr << *_subterms[_subterms.size() - 1];
      ostr << ")";
    }
    return ostr;
  }

  std::ostream& LVariable::toStream(std::ostream& ostr) const {
    ostr << "X" << _id;
    return ostr;
  }

  std::ostream& PredTerm::toStream(std::ostream& ostr) const {
    if (_head->arity() == 0) {
      ostr << _head->name();
    } else {
      ostr << _head->name() << "(";
      for (unsigned i = 0; i < _subterms.size() - 1; i++) {
        ostr << *_subterms[i] << ",";
      }
      ostr << *_subterms[_subterms.size() - 1];
      ostr << ")";
    }
    return ostr;
  }
}

