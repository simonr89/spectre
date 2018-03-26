#ifndef __Term__
#define __Term__

#include <cassert>
#include <initializer_list>
#include <list>
#include <ostream>
#include <string>
#include <vector>
#include "Signature.hpp"
#include "Sort.hpp"

namespace logic {

  class LVariable;

  class Term
  {
  public:
    virtual std::string toTPTP() const = 0;

    virtual std::vector<LVariable*> freeVariables() const = 0;
  };

  class LVariable : public Term {
  public:
    LVariable(Sort* s) :
      _id(freshId++),
      _s(s)
    {}

    ~LVariable() {}

    unsigned id() { return _id; }

    std::string name() const { return "X" + std::to_string(_id); }

    Sort* sort() const { return _s; }

    std::string toTPTP() const;

    std::vector<LVariable*> freeVariables() const;
    
  protected:
    unsigned _id;
    Sort* _s;

    static unsigned freshId;
  };

  class FuncTerm : public Term {
  public:
    FuncTerm(Symbol* head, std::initializer_list<const Term*> subterms) :
      _head(head),
      _subterms(subterms)
    {
      assert(head);
      assert(!head->isPredicateSymbol());
      assert(head->arity() == subterms.size());
    }

    ~FuncTerm() {}

    std::string toTPTP() const;

    std::vector<LVariable*> freeVariables() const;
    
  protected:
    Symbol* _head;
    std::vector<const Term*> _subterms;
  };

  // taking the FOOL approach, predicates are alse terms
  class PredTerm : public Term {
  public:

    PredTerm(Symbol* head, std::initializer_list<const Term*> subterms) :
      _head(head),
      _subterms(subterms)
    {
      assert(head);
      assert(head->isPredicateSymbol());
      assert(head->arity() == subterms.size());
    }

    ~PredTerm() {}

    std::string toTPTP() const;

    std::vector<LVariable*> freeVariables() const;

  protected:
    Symbol* _head;
    std::vector<const Term*> _subterms;
  };

  inline std::ostream& operator<<(std::ostream& ostr, const Term& e) { ostr << e.toTPTP(); return ostr; }
}

#endif
