#ifndef __Formula__
#define __Formula__

#include <initializer_list>
#include <ostream>
#include "Term.hpp"

namespace logic {
    
    class Formula {
    public:

//        std::shared_ptr<const Formula> quantify(bool univ = true) const;

        std::string declareTPTP(std::string decl, bool conjecture = false) const;
        std::string declareSMTLIB(std::string decl, bool conjecture = false) const;

        // returns a vector of the unbound variables of the formula
//        virtual std::vector<std::shared_ptr<const LVariable>> freeVariables() const = 0;
        
        virtual std::string toTPTP() const = 0;
        virtual std::string toSMTLIB(unsigned indentation = 0) const = 0;
        virtual std::string prettyString(unsigned indentation = 0) const = 0;

    protected:
    };
    
    class PredicateFormula : public Formula
    {
        friend class Formulas;
        
    public:
        PredicateFormula(std::shared_ptr<const PredTerm> p) : p(p) {}
        
//        std::vector<std::shared_ptr<const LVariable>> freeVariables() const override;
        
        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
        
        const std::shared_ptr<const PredTerm> p;
    };
    
    class EqualityFormula : public Formula
    {
        friend class Formulas;
        
    public:
        EqualityFormula(bool polarity, std::shared_ptr<const Term> left, std::shared_ptr<const Term> right) :
        polarity(polarity),
        left(left),
        right(right)
        {}

        const bool polarity;
        const std::shared_ptr<const Term> left;
        const std::shared_ptr<const Term> right;
        
//        std::vector<std::shared_ptr<const LVariable>> freeVariables() const override;

        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
    };
    
    class ConjunctionFormula : public Formula
    {
        friend class Formulas;
        
    public:
        ConjunctionFormula(std::vector<std::shared_ptr<const Formula>> conj) : conj(conj){}
        ConjunctionFormula(std::initializer_list<std::shared_ptr<const Formula>> conj) : conj(conj){}
        
//        std::vector<std::shared_ptr<const LVariable>> freeVariables() const override;
        
        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;

        const std::vector<std::shared_ptr<const Formula>> conj;
    };
    
    class DisjunctionFormula : public Formula
    {
        friend class Formulas;
        
    public:
        DisjunctionFormula(std::vector<std::shared_ptr<const Formula>> disj) : disj(disj){}
        DisjunctionFormula(std::initializer_list<std::shared_ptr<const Formula>> disj) : disj(disj){}
        
//        std::vector<std::shared_ptr<const LVariable>> freeVariables() const override;

        std::string toTPTP() const override ;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;

        const std::vector<std::shared_ptr<const Formula>> disj;
    };
    
    class NegationFormula : public Formula
    {
        friend class Formulas;
        
    public:
        NegationFormula(std::shared_ptr<const Formula> f) : f(f) {}
        
//        std::vector<std::shared_ptr<const LVariable>> freeVariables() const override;

        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
        
        const std::shared_ptr<const Formula> f;
    };
    
    class ExistentialFormula : public Formula
    {
        friend class Formulas;
        
    public:
        ExistentialFormula(std::vector<std::shared_ptr<const LVariable>> vars, std::shared_ptr<const Formula> f) : vars(vars), f(f){}
        ExistentialFormula(std::initializer_list<std::shared_ptr<const LVariable>> vars, std::shared_ptr<const Formula> f) : vars(vars), f(f){}
        
//        std::vector<std::shared_ptr<const LVariable>> freeVariables() const override;

        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;

        const std::vector<std::shared_ptr<const LVariable>> vars;
        const std::shared_ptr<const Formula> f;
    };
    
    class UniversalFormula : public Formula
    {
        friend class Formulas;
        
    public:
        UniversalFormula(std::vector<std::shared_ptr<const LVariable>> vars, std::shared_ptr<const Formula> f) : vars(vars), f(f){}
        UniversalFormula(std::initializer_list<std::shared_ptr<const LVariable>> vars, std::shared_ptr<const Formula> f) : vars(vars), f(f){}
        
//        std::vector<std::shared_ptr<const LVariable>> freeVariables() const override;
        
        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
        
        const std::vector<std::shared_ptr<const LVariable>> vars;
        const std::shared_ptr<const Formula> f;
    };
    
    class ImplicationFormula : public Formula
    {
        friend class Formulas;
        
    public:
        ImplicationFormula(std::shared_ptr<const Formula> f1, std::shared_ptr<const Formula> f2) : f1(f1), f2(f2) {}
        
//        std::vector<std::shared_ptr<const LVariable>> freeVariables() const override;

        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;

        const std::shared_ptr<const Formula> f1;
        const std::shared_ptr<const Formula> f2;
    };
    
    inline std::ostream& operator<<(std::ostream& ostr, const Formula& e) { ostr << e.toTPTP(); return ostr; }
    
# pragma mark - Formulas
    
    // We use Formulas as a manager-class for Formula-instances
    class Formulas
    {
    public:
        
        // construct new terms
        static std::shared_ptr<const PredicateFormula> predicateFormula(std::shared_ptr<const PredTerm> p);
        static std::shared_ptr<const EqualityFormula> equalityFormula(bool polarity, std::shared_ptr<const Term> left, std::shared_ptr<const Term> right);

        static std::shared_ptr<const NegationFormula>  negationFormula(std::shared_ptr<const Formula> f);

        static std::shared_ptr<const ConjunctionFormula> conjunctionFormula(std::vector<std::shared_ptr<const Formula>> conj);
        static std::shared_ptr<const ConjunctionFormula> conjunctionFormula(std::initializer_list<std::shared_ptr<const Formula>> conj);
        static std::shared_ptr<const DisjunctionFormula> disjunctionFormula(std::vector<std::shared_ptr<const Formula>> disj);
        static std::shared_ptr<const DisjunctionFormula> disjunctionFormula(std::initializer_list<std::shared_ptr<const Formula>> disj);
        
        static std::shared_ptr<const ImplicationFormula> implicationFormula(std::shared_ptr<const Formula> f1, std::shared_ptr<const Formula> f2);
        
        static std::shared_ptr<const ExistentialFormula> existentialFormula(std::vector<std::shared_ptr<const LVariable>> vars, std::shared_ptr<const Formula> f);
        static std::shared_ptr<const UniversalFormula> universalFormula(std::vector<std::shared_ptr<const LVariable>> vars, std::shared_ptr<const Formula> f);
    };
}

#endif

