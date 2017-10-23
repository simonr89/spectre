#include "Formula.hpp"

#include <functional>

namespace logic {

  std::string Formula::declareTPTP(std::string decl) const
  {
    return "tff(" + decl + ", axiom, " + toTPTP() + ").";
  }

  std::string PredicateFormula::toTPTP() const
  {
    return _p->toTPTP();
  }

  std::string EqualityFormula::toTPTP() const
  {
    if (_polarity)
      return _left->toTPTP() + " = " + _right->toTPTP();
    else
      return _left->toTPTP() + " != " + _right->toTPTP();
  }

  std::string ConjunctionFormula::toTPTP() const
  {   
    std::string str = "(";
    for (unsigned i = 0; i < _conj.size(); i++) {
      str += _conj[i]->toTPTP();
      
      str += (i == _conj.size() - 1) ? ")" : " & ";
    }
    return str;
  }

  std::string DisjunctionFormula::toTPTP() const
  {
    std::string str = "(";
    for (unsigned i = 0; i < _disj.size(); i++) {
      str += _disj[i]->toTPTP();
      
      str += (i == _disj.size() - 1) ? ")" : " | ";
    }
    return str;  }

  std::string NegationFormula::toTPTP() const
  {
    return "~(" + _f->toTPTP() + ")";
  }

  std::string ExistentialFormula::toTPTP() const
  {
    std::string str = "? [";
    for (unsigned i = 0; i < _vars.size(); i++) {
      str += _vars[i]->name() + " : " + _vars[i]->sort()->name();
      if (i != _vars.size() - 1) { str += ", "; }
    }
    str += "] : " + _f->toTPTP();
    return str;
  }

  std::string UniversalFormula::toTPTP() const
  {
    std::string str = "! [";
    for (unsigned i = 0; i < _vars.size(); i++) {
      str += _vars[i]->name() + " : " + _vars[i]->sort()->name();
      if (i != _vars.size() - 1) { str += ", "; }
    }
    str += "] : " + _f->toTPTP();
    return str;
  }

  std::string ImplicationFormula::toTPTP() const
  {
    return "(" + _f1->toTPTP() + " => " + _f2->toTPTP() + ")";
  }

  bool compareLVarPointers(LVariable* p1, LVariable* p2) {
    return p1->id() < p2->id();
  }

  bool eqLVarPointers(LVariable* p1, LVariable* p2) {
    return p1->id() == p2->id();
  }

  Formula* Formula::quantify(bool univ) const
  {
    std::list<LVariable*> vars = freeVariables();
    vars.sort(compareLVarPointers);
    vars.unique(eqLVarPointers);
    Formula *f = clone();

    if (vars.empty()) {
      return f;
    }
    
    if (univ) {
      return new UniversalFormula(vars, f);
    } else {
      return new ExistentialFormula(vars, f);
    }
  }

  std::list<LVariable*> PredicateFormula::freeVariables() const
  {
    return _p->freeVariables();
  }

  std::list<LVariable*> EqualityFormula::freeVariables() const
  {
    std::list<LVariable*> l = _left->freeVariables();
    l.splice(l.end(), _right->freeVariables());
    return l;
  }

  std::list<LVariable*> ConjunctionFormula::freeVariables() const
  {
    std::list<LVariable*> l;
    for (unsigned i = 0; i < _conj.size(); i++) {
      l.splice(l.end(), _conj[i]->freeVariables());
    }
    return l;
  }

  std::list<LVariable*> DisjunctionFormula::freeVariables() const
  {
    std::list<LVariable*> l;
    for (unsigned i = 0; i < _disj.size(); i++) {
      l.splice(l.end(), _disj[i]->freeVariables());
    }
    return l;
  }

  std::list<LVariable*> NegationFormula::freeVariables() const
  {
    return _f->freeVariables();
  }

  std::list<LVariable*> ExistentialFormula::freeVariables() const
  {
    std::list<LVariable*> l = _f->freeVariables();
    for (auto it = _vars.begin(); it != _vars.end(); ++it) {
      l.remove_if(std::bind(eqLVarPointers, *it, std::placeholders::_1));
    }
    return l;
  }

  std::list<LVariable*> UniversalFormula::freeVariables() const
  {
    std::list<LVariable*> l = _f->freeVariables();
    for (auto it = _vars.begin(); it != _vars.end(); ++it) {
      l.remove_if(std::bind(eqLVarPointers, *it, std::placeholders::_1));
    }
    return l;
  }

  std::list<LVariable*> ImplicationFormula::freeVariables() const
  {
    std::list<LVariable*> l = _f1->freeVariables();
    l.splice(l.end(), _f2->freeVariables());
    return l;
  }

}
