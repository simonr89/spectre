#include "Formula.hpp"

namespace logic {

  Formula* Formula::quantify(const Formula& f) {
    // TODO
    return nullptr;
  }

  //TODO
  std::ostream& PredicateFormula::toStream(std::ostream& ostr) const
  {
    ostr << *_p;
    return ostr;
  }

  std::ostream& EqualityFormula::toStream(std::ostream& ostr) const
  {
    ostr << "(" << *_left << " == " << _right << ")";
    return ostr;
  }

  std::ostream& ConjunctionFormula::toStream(std::ostream& ostr) const
  {
    ostr << "conj";
    return ostr;
  }

  std::ostream& DisjunctionFormula::toStream(std::ostream& ostr) const
  {
    ostr << "disj";
    return ostr;
  }

  std::ostream& NegationFormula::toStream(std::ostream& ostr) const
  {
    ostr << "neg";
    return ostr;
  }

  std::ostream& ExistentialFormula::toStream(std::ostream& ostr) const
  {
    ostr << "ex";
    return ostr;
  }

  std::ostream& UniversalFormula::toStream(std::ostream& ostr) const
  {
    ostr << "forall";
    return ostr;
  }

  std::ostream& ImplicationFormula::toStream(std::ostream& ostr) const
  {
    ostr << "imp";
    return ostr;
  }

}
