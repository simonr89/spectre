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
//        virtual std::vector<std::shared_ptr<const LVariable>> freeVariables() const = 0;

        virtual std::string toTPTP() const = 0;
        virtual std::string toSMTLIB() const = 0;
        virtual std::string prettyString() const = 0;
    };
    
    class LVariable : public Term
    {
        friend class Terms;
        
        LVariable(const Sort* s) : id(freshId++), sort(s), name("X" + std::to_string(id)){}
        LVariable(const Sort* s, const std::string name) : id(freshId++), sort(s), name(name){}
    public:
        const unsigned id;
        const Sort* sort;
        const std::string name;
        
//        std::vector<std::shared_ptr<const LVariable>> freeVariables() const override;

        std::string toTPTP() const override;
        std::string toSMTLIB() const override;
        virtual std::string prettyString() const override;
        
        static unsigned freshId;
    };
    
    bool compareLVarPointers(const LVariable* p1, const LVariable* p2);
    bool eqLVarPointers(const LVariable* p1, const LVariable* p2);
    
    class FuncTerm : public Term
    {
        friend class Terms;

        FuncTerm(const Symbol* head, std::initializer_list<std::shared_ptr<const Term>> subterms) :
        head(head),
        subterms(subterms)
        {
            assert(head);
            assert(!head->isPredicateSymbol());
            assert(head->argSorts.size() == subterms.size());
        }
    public:

        const Symbol* const head;
        const std::vector<std::shared_ptr<const Term>> subterms;
        
//        std::vector<std::shared_ptr<const LVariable>> freeVariables() const override;

        std::string toTPTP() const override;
        std::string toSMTLIB() const override;
        virtual std::string prettyString() const override;
    };
    
    // taking the FOOL approach, predicates are alse terms
    class PredTerm : public Term
    {
        friend class Terms;

        PredTerm(const Symbol* head, std::initializer_list<std::shared_ptr<const Term>> subterms) :
        head(head),
        subterms(subterms)
        {
            assert(head);
            assert(head->isPredicateSymbol());
            assert(head->argSorts.size() == subterms.size());
        }
    public:

        const Symbol* head;
        const std::vector<std::shared_ptr<const Term>> subterms;
        
//        std::vector<std::shared_ptr<const LVariable>> freeVariables() const override;
        
        std::string toTPTP() const override;
        std::string toSMTLIB() const override;
        virtual std::string prettyString() const override;
    };
    
    inline std::ostream& operator<<(std::ostream& ostr, const Term& e) { ostr << e.toTPTP(); return ostr; }

    
# pragma mark - Terms
    
    // We use Terms as a manager-class for Term-instances
    class Terms
    {
    public:

        // construct new terms
        static std::shared_ptr<const LVariable> lVariable(const Sort* s);
        static std::shared_ptr<const LVariable> lVariable(const Sort* s, const std::string name);
        static std::shared_ptr<const FuncTerm> funcTerm(const Symbol* head, std::initializer_list<std::shared_ptr<const Term>> subterms);
        static std::shared_ptr<const PredTerm> predTerm(const Symbol* head, std::initializer_list<std::shared_ptr<const Term>> subterms);
    };
}
#endif

