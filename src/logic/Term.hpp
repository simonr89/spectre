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

    class Term;    
    typedef std::shared_ptr<const Term> TermPtr;
       
    class Term
    {
    public:
        friend class Terms;
//        virtual std::vector<LVariablePtr> freeVariables() const = 0;

        virtual std::string toTPTP() const = 0;
        virtual std::string toSMTLIB() const = 0;
        virtual std::string prettyString() const = 0;
        virtual unsigned occurrences(const Term& t) const = 0;

        virtual bool operator ==(const Term& t) const = 0;
        bool operator !=(const Term& t) const { return !(*this == t); }

    protected:
        // this should be called under the assumption this != *oldsub
        // and this contains an occurrence of oldsub
        virtual Term* replace(const TermPtr oldsub, const TermPtr newsub) const = 0;
    };
    
    class LVariable : public Term
    {
    public:
        friend class Terms;
        
        const unsigned id;
        const Sort* sort;
        const std::string name;
        
//        std::vector<LVariablePtr> freeVariables() const override;

        std::string toTPTP() const override;
        std::string toSMTLIB() const override;
        virtual std::string prettyString() const override;
        unsigned occurrences(const Term& t) const override;

        bool operator ==(const Term& t) const override;
        
        static unsigned freshId;

    protected:
        LVariable(const Sort* s) :
            id(freshId++),
            sort(s),
            name("X" + std::to_string(id))
            {}
        
        LVariable(const Sort* s, const std::string name) :
            id(freshId++),
            sort(s),
            name(name)
            {}
        
        Term* replace(const TermPtr oldsub, const TermPtr newsub) const;
    };

    typedef std::shared_ptr<const LVariable> LVariablePtr;
    
    class FuncTerm : public Term
    {
   public:
        friend class Terms;

        const Symbol* const head;
        const std::vector<TermPtr> subterms;
        
//        std::vector<LVariablePtr> freeVariables() const override;

        std::string toTPTP() const override;
        std::string toSMTLIB() const override;
        virtual std::string prettyString() const override;
        unsigned occurrences(const Term& t) const override;

        bool operator ==(const Term& t) const override;
        
    protected:
        FuncTerm(const Symbol* head, std::vector<TermPtr> subterms) :
            head(head),
            subterms(subterms)
            {
                assert(head);
                assert(!head->isPredicateSymbol());
                assert(head->argSorts.size() == subterms.size());
            }
        
        FuncTerm(const Symbol* head, std::initializer_list<TermPtr> subterms) :
            head(head),
            subterms(subterms)
            {
                assert(head);
                assert(!head->isPredicateSymbol());
                assert(head->argSorts.size() == subterms.size());
            }

        Term* replace(const TermPtr oldsub, const TermPtr newsub) const;
    };

    typedef std::shared_ptr<const FuncTerm> FuncTermPtr;
    
    // taking the FOOL approach, predicates are also terms
    class PredTerm : public Term
    {
    public:
        friend class Terms;

        const Symbol* head;
        const std::vector<TermPtr> subterms;
        
//        std::vector<LVariablePtr> freeVariables() const override;
        
        std::string toTPTP() const override;
        std::string toSMTLIB() const override;
        virtual std::string prettyString() const override;
        unsigned occurrences(const Term& t) const override;

        bool operator ==(const Term& t) const override;

    protected:
        PredTerm(const Symbol* head, std::vector<TermPtr> subterms) :
            head(head),
            subterms(subterms)
            {
                assert(head);
                assert(head->isPredicateSymbol());
                assert(head->argSorts.size() == subterms.size());
            }
        
        PredTerm(const Symbol* head, std::initializer_list<TermPtr> subterms) :
            head(head),
            subterms(subterms)
            {
                assert(head);
                assert(head->isPredicateSymbol());
                assert(head->argSorts.size() == subterms.size());
            }

        Term* replace(const TermPtr oldsub, const TermPtr newsub) const;
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

        static TermPtr replace(const TermPtr t, const TermPtr oldsub, const TermPtr newsub);
    };
}
#endif

