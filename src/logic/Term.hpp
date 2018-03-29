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
        virtual std::vector<LVariable*> freeVariables() const = 0;

        virtual std::string toTPTP() const = 0;
        virtual std::string prettyString() const = 0;
    };
    
    class LVariable : public Term {
    public:
        LVariable(Sort* s) : _id(freshId++), _s(s){}
        
        unsigned id() const { return _id; }
        
        std::string name() const { return "X" + std::to_string(_id); }
        
        Sort* sort() const { return _s; }
        
        std::vector<LVariable*> freeVariables() const override;

        std::string toTPTP() const override;
        virtual std::string prettyString() const override;

    protected:
        unsigned _id;
        Sort* _s;
        
        static unsigned freshId;
    };
    
    bool compareLVarPointers(LVariable* p1, LVariable* p2);
    bool eqLVarPointers(const LVariable* p1, const LVariable* p2);
    
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
        
        std::vector<LVariable*> freeVariables() const override;

        std::string toTPTP() const override;
        virtual std::string prettyString() const override;
        
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
        
        std::vector<LVariable*> freeVariables() const override;
        
        std::string toTPTP() const override;
        virtual std::string prettyString() const override;

    protected:
        Symbol* _head;
        std::vector<const Term*> _subterms;
    };
    
    inline std::ostream& operator<<(std::ostream& ostr, const Term& e) { ostr << e.toTPTP(); return ostr; }
}

#endif

