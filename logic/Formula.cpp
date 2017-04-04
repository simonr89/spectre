#include "Formula.hpp"

namespace logic {

  Formula* Formula::quantify(const Formula& f) {
    // TODO
    return nullptr;
  }

  std::string PredicateFormula::toTPTP() const
  {
    return _p->toTPTP();
  }

  std::string EqualityFormula::toTPTP() const
  {
    return "(" + _left->toTPTP() + " == " + _right->toTPTP() + ")";
  }

  std::string ConjunctionFormula::toTPTP() const
  {
    std::string str = "(";
    for (unsigned i = 0; i < _conj.size() - 1; i++) {
      str += _conj[i]->toTPTP() + " & ";
    }
    str += _conj[_conj.size() - 1]->toTPTP() + ")";
    return str;
  }

  std::string DisjunctionFormula::toTPTP() const
  {
    std::string str = "(";
    for (unsigned i = 0; i < _disj.size() - 1; i++) {
      str += _disj[i]->toTPTP() + " | ";
    }
    str += _disj[_disj.size() - 1]->toTPTP() + ")";
    return str;
  }

  std::string NegationFormula::toTPTP() const
  {
    return "~(" + _f->toTPTP() + ")";
  }

  std::string ExistentialFormula::toTPTP() const
  {
    std::string str = "? [";
    for (unsigned i = 0; i < _vars.size() - 1; i++) {
      str += _vars[i]->toTPTP() + ",";
    }
    str += _vars[_vars.size() - 1]->toTPTP() + "] (" + _f->toTPTP() + ")";
    return str;
  }

  std::string UniversalFormula::toTPTP() const
  {
    std::string str = "! [";
    for (unsigned i = 0; i < _vars.size() - 1; i++) {
      str += _vars[i]->toTPTP() + ",";
    }
    str += _vars[_vars.size() - 1]->toTPTP() + "] (" + _f->toTPTP() + ")";
    return str;
  }

  std::string ImplicationFormula::toTPTP() const
  {
    return "(" + _f1->toTPTP() + " ==> " + _f2->toTPTP() + ")";
  }

}
