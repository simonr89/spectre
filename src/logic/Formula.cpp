#include "Formula.hpp"

#include <algorithm>

namespace logic {

  std::string Formula::declareTPTP(std::string decl, bool conjecture) const
  {
    return "tff(" + decl + ", " + (conjecture ? "conjecture, " : "hypothesis, ") + toTPTP() + ").";
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
    if (_conj.size() == 0)
      return "$true";
    std::string str = "(";
    for (unsigned i = 0; i < _conj.size(); i++) {
      str += _conj[i]->toTPTP();
      
      str += (i == _conj.size() - 1) ? ")" : " & ";
    }
    return str;
  }

  std::string DisjunctionFormula::toTPTP() const
  {
    if (_disj.size() == 0)
      return "$false";
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
        std::vector<LVariable*> vars = freeVariables();
        std::sort(vars.begin(),vars.end(),compareLVarPointers);
        std::unique(vars.begin(), vars.end(), eqLVarPointers);
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

    std::vector<LVariable*> PredicateFormula::freeVariables() const
    {
        return _p->freeVariables();
    }

    std::vector<LVariable*> EqualityFormula::freeVariables() const
    {
        std::vector<LVariable*> l = _left->freeVariables();
        std::vector<LVariable*> r = _right->freeVariables();
        l.insert(l.end(), r.begin(),r.end());
        return l;
    }
    
    std::vector<LVariable*> ConjunctionFormula::freeVariables() const {
        std::vector<LVariable*> freeVars;
        for (const auto& conjunct : _conj)
        {
            auto freeVarsConjunct = conjunct->freeVariables();
            freeVars.insert(freeVars.end(), freeVarsConjunct.begin(), freeVarsConjunct.end());
        }
        return freeVars;
    }
    
    std::vector<LVariable*> DisjunctionFormula::freeVariables() const {
        std::vector<LVariable*> freeVars;
        for (const auto& disjunct : _disj)
        {
            auto freeVarsDisjunct = disjunct->freeVariables();
            freeVars.insert(freeVars.end(), freeVarsDisjunct.begin(), freeVarsDisjunct.end());
        }
        return freeVars;
    }

    std::vector<LVariable*> NegationFormula::freeVariables() const
    {
        return _f->freeVariables();
    }

    std::vector<LVariable*> ExistentialFormula::freeVariables() const
    {
        std::vector<LVariable*> l = _f->freeVariables();
        
        for (const auto& var : _vars)
        {
            l.erase(std::remove(l.begin(), l.end(), var), l.end());
        }
        return l;
    }

    std::vector<LVariable*> UniversalFormula::freeVariables() const
    {
        std::vector<LVariable*> l = _f->freeVariables();
        
        for (const auto& var : _vars)
        {
            l.erase(std::remove(l.begin(), l.end(), var), l.end());
        }
        return l;
    }

    std::vector<LVariable*> ImplicationFormula::freeVariables() const
    {
        std::vector<LVariable*> l = _f1->freeVariables();
        std::vector<LVariable*> r = _f2->freeVariables();
        l.insert(l.end(), r.begin(),r.end());
        return l;
    }

}
