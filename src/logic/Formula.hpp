#ifndef __Formula__
#define __Formula__

#include <initializer_list>
#include <list>
#include <ostream>
#include "logic/Term.hpp"

namespace logic {

  class Formula {
  public:
    virtual std::string toTPTP() const = 0;

    std::string declareTPTP(std::string decl) const;
    
    Formula* quantify(bool univ = true) const;

    virtual std::list<LVariable*> freeVariables() const = 0;

    virtual Formula* clone() const = 0;
  protected:
  };

  class PredicateFormula : public Formula {
  public:
    PredicateFormula(PredTerm* p) :
      _p(p)
    {}

    ~PredicateFormula()
    {}

    std::string toTPTP() const;

    Formula* clone() const { return new PredicateFormula(*this); }
    
    std::list<LVariable*> freeVariables() const;
    
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

    std::string toTPTP() const;

    Formula* clone() const { return new EqualityFormula(*this); }
    
    std::list<LVariable*> freeVariables() const;

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

    std::string toTPTP() const;

    Formula* clone() const { return new ConjunctionFormula(*this); }

    std::list<LVariable*> freeVariables() const;
    
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

    std::string toTPTP() const;

    Formula* clone() const { return new DisjunctionFormula(*this); }

    std::list<LVariable*> freeVariables() const;
    
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

    std::string toTPTP() const;

    Formula* clone() const { return new NegationFormula(*this); }
    
    std::list<LVariable*> freeVariables() const;

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

    std::string toTPTP() const;

    Formula* clone() const { return new ExistentialFormula(*this); }
    
    std::list<LVariable*> freeVariables() const;

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

    std::string toTPTP() const;

    Formula* clone() const { return new UniversalFormula(*this); }
    
    std::list<LVariable*> freeVariables() const;

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

    std::string toTPTP() const;

    Formula* clone() const { return new ImplicationFormula(*this); }
    
    std::list<LVariable*> freeVariables() const;

  protected:
    Formula* _f1;
    Formula* _f2;

  };

  inline std::ostream& operator<<(std::ostream& ostr, const Formula& e) { ostr << e.toTPTP(); return ostr; }
}

#endif
