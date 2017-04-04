#ifndef __Term__
#define __Term__

#include <cassert>
#include <initializer_list>
#include <ostream>
#include <string>
#include <vector>
#include "logic/Signature.hpp"
#include "logic/Sort.hpp"

namespace logic {

  class Term
  {
  public:
    virtual std::string toTPTP() const = 0;
  };

  class FuncTerm : public Term {
  public:
    FuncTerm(Symbol* head, std::initializer_list<Term*> subterms) :
      _head(head),
      _subterms(subterms)
    {
      assert(!head->isPredicateSymbol());
      assert(head->arity() == subterms.size());
    }

    ~FuncTerm() {}

    std::string toTPTP() const;
    
  protected:
    Symbol* _head;
    std::vector<Term*> _subterms;
  };

  class LVariable : public Term {
  public:
    LVariable(Sort* s) :
      _id(freshId++),
      _s(s)
    {}

    ~LVariable() {}

    std::string name() { return "X" + std::to_string(_id); }

    Sort* sort() { return _s; }

    std::string toTPTP() const;
    
  protected:
    unsigned _id;
    Sort* _s;

    static unsigned freshId;
  };

  // taking the FOOL approach, predicates are alse terms
  class PredTerm : public Term {
  public:

    PredTerm(Symbol* head, std::initializer_list<Term*> subterms) :
      _head(head),
      _subterms(subterms)
    {
      assert(head->isPredicateSymbol());
      assert(head->arity() == subterms.size());
    }

    ~PredTerm() {}

    std::string toTPTP() const;

  protected:
    Symbol* _head;
    std::vector<Term*> _subterms;
  };

  inline std::ostream& operator<<(std::ostream& ostr, const Term& e) { ostr << e.toTPTP(); return ostr; }
}

#endif
