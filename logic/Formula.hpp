#ifndef __Formula__
#define __Formula__

#include <initializer_list>
#include <list>
#include <ostream>
#include "logic/Term.hpp"

namespace logic {

  class Formula {
  public:
    virtual std::ostream& toStream(std::ostream& ostr) const = 0;

    static Formula* quantify(const Formula& f);
  };

  class PredicateFormula : public Formula {
  public:
    PredicateFormula(PredTerm* p) :
      _p(p)
    {}

    ~PredicateFormula()
    {}

    std::ostream& toStream(std::ostream& ostr) const;
    
  protected:
    PredTerm* _p;
  };

  class EqualityFormula : public Formula {
  public:
    EqualityFormula(bool polarity, Term* left, Term* right) :
      _polarity(polarity),
      _left(left),
      _right(right)
    {}

    ~EqualityFormula()
    {}

    std::ostream& toStream(std::ostream& ostr) const;
    
  protected:
    bool _polarity;
    Term* _left;
    Term* _right;
  };

  class ConjunctionFormula : public Formula {
  public:
    ConjunctionFormula(const std::list<Formula*>& conj) :
      _conj(conj.size())
    {
      unsigned i = 0;
      for (auto it = conj.begin(); it != conj.end(); ++it) {
        _conj[i++] = *it;
      }
    }
    
    ConjunctionFormula(std::initializer_list<Formula*> conj) :
      _conj(conj)
    {}

    ~ConjunctionFormula()
    {}

    std::ostream& toStream(std::ostream& ostr) const;
    
  protected:
    std::vector<Formula*> _conj;
  };

  class DisjunctionFormula : public Formula {
  public:
    DisjunctionFormula(std::list<Formula*>& disj) :
      _disj(disj.size())
    {
      unsigned i = 0;
      for (auto it = disj.begin(); it != disj.end(); ++it) {
        _disj[i++] = *it;
      }
    }
    
    DisjunctionFormula(std::initializer_list<Formula*> disj) :
      _disj(disj)
    {}

    ~DisjunctionFormula()
    {}

    std::ostream& toStream(std::ostream& ostr) const;
    
  protected:
    std::vector<Formula*> _disj;
  };

  class NegationFormula : public Formula {
  public:
    NegationFormula(Formula *f) :
      _f(f)
    {}

    ~NegationFormula()
    {}

    std::ostream& toStream(std::ostream& ostr) const;
    
  protected:
    Formula *_f;
  };

  class ExistentialFormula : public Formula {
  public:
    ExistentialFormula(const std::list<LVariable*>& vars, Formula* f) :
      _vars(vars.size()),
      _f(f)
    {
      unsigned i = 0;
      for (auto it = vars.begin(); it != vars.end(); ++it) {
        _vars[i++] = *it;
      }
    }
    
    ExistentialFormula(std::initializer_list<LVariable*> vars, Formula* f) :
      _vars(vars),
      _f(f)
    {}

    ~ExistentialFormula()
    {}

    std::ostream& toStream(std::ostream& ostr) const;
    
  protected:
    std::vector<LVariable*> _vars;
    Formula* _f;
  };

  class UniversalFormula : public Formula {
  public:
    UniversalFormula(const std::list<LVariable*>& vars, Formula* f) :
      _vars(vars.size()),
      _f(f)
    {
      unsigned i = 0;
      for (auto it = vars.begin(); it != vars.end(); ++it) {
        _vars[i++] = *it;
      }
    }
    
    UniversalFormula(std::initializer_list<LVariable*> vars, Formula* f) :
      _vars(vars),
      _f(f)
    {}

    ~UniversalFormula()
    {}

    std::ostream& toStream(std::ostream& ostr) const;
    
  protected:
    std::vector<LVariable*> _vars;
    Formula* _f;
  };

  class ImplicationFormula : public Formula {
  public:
    ImplicationFormula(Formula* f1, Formula* f2) :
      _f1(f1),
      _f2(f2)
    {}

    ~ImplicationFormula()
    {}

    std::ostream& toStream(std::ostream& ostr) const;
    
  protected:
    Formula* _f1;
    Formula* _f2;
  };

  inline std::ostream& operator<<(std::ostream& ostr, const Formula& e) { return e.toStream(ostr); }
}

#endif
