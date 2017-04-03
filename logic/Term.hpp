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
    virtual std::ostream& toStream(std::ostream& ostr) const = 0;
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

    std::ostream& toStream(std::ostream& ostr) const;
    
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

    std::ostream& toStream(std::ostream& ostr) const;
    
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

    std::ostream& toStream(std::ostream& ostr) const;

  protected:
    Symbol* _head;
    std::vector<Term*> _subterms;
  };

  inline std::ostream& operator<<(std::ostream& ostr, const Term& e) { return e.toStream(ostr); }
}

#endif
