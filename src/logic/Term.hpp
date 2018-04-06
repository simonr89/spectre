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
        LVariable(Sort* s) : id(freshId++), sort(s), name("X" + std::to_string(id)){}
        LVariable(Sort* s, const std::string name) : id(freshId++), sort(s), name(name){}

        const unsigned id;
        const Sort* sort;
        const std::string name;
        
        std::vector<LVariable*> freeVariables() const override;

        std::string toTPTP() const override;
        virtual std::string prettyString() const override;
        
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

