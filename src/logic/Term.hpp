#ifndef __Term__
#define __Term__

#include <cassert>
#include <initializer_list>
#include <list>
#include <memory>
#include <ostream>
#include <string>
#include <vector>
#include "Signature.hpp"
#include "Sort.hpp"

namespace logic {
    
    class LVariable;

    typedef std::shared_ptr<const LVariable> LVariablePtr;
    
    class Term
    {
    public:
//        virtual std::vector<LVariablePtr> freeVariables() const = 0;

        virtual std::string toTPTP() const = 0;
        virtual std::string toSMTLIB() const = 0;
        virtual std::string prettyString() const = 0;
    };

    typedef std::shared_ptr<const Term> TermPtr;
    
    class LVariable : public Term
    {
        friend class Terms;
        
        LVariable(const Sort* s) : id(freshId++), sort(s), name("X" + std::to_string(id)){}
        LVariable(const Sort* s, const std::string name) : id(freshId++), sort(s), name(name){}
    public:
        const unsigned id;
        const Sort* sort;
        const std::string name;
        
//        std::vector<LVariablePtr> freeVariables() const override;

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

        FuncTerm(const Symbol* head, std::initializer_list<TermPtr> subterms) :
        head(head),
        subterms(subterms)
        {
            assert(head);
            assert(!head->isPredicateSymbol());
            assert(head->argSorts.size() == subterms.size());
        }
    public:

        const Symbol* const head;
        const std::vector<TermPtr> subterms;
        
//        std::vector<LVariablePtr> freeVariables() const override;

        std::string toTPTP() const override;
        std::string toSMTLIB() const override;
        virtual std::string prettyString() const override;
    };

    typedef std::shared_ptr<const FuncTerm> FuncTermPtr;
    
    // taking the FOOL approach, predicates are also terms
    class PredTerm : public Term
    {
        friend class Terms;

        PredTerm(const Symbol* head, std::initializer_list<TermPtr> subterms) :
        head(head),
        subterms(subterms)
        {
            assert(head);
            assert(head->isPredicateSymbol());
            assert(head->argSorts.size() == subterms.size());
        }
    public:

        const Symbol* head;
        const std::vector<TermPtr> subterms;
        
//        std::vector<LVariablePtr> freeVariables() const override;
        
        std::string toTPTP() const override;
        std::string toSMTLIB() const override;
        virtual std::string prettyString() const override;
    };

    typedef std::shared_ptr<const PredTerm> PredTermPtr;
    
    inline std::ostream& operator<<(std::ostream& ostr, const Term& e) { ostr << e.toTPTP(); return ostr; }

    
# pragma mark - Terms
    
    // We use Terms as a manager-class for Term-instances
    class Terms
    {
    public:

        // construct new terms
        static LVariablePtr lVariable(const Sort* s);
        static LVariablePtr lVariable(const Sort* s, const std::string name);
        static FuncTermPtr funcTerm(const Symbol* head, std::initializer_list<TermPtr> subterms);
        static PredTermPtr predTerm(const Symbol* head, std::initializer_list<TermPtr> subterms);
    };
}
#endif

