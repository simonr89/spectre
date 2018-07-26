#ifndef __Formula__
#define __Formula__

#include <initializer_list>
#include <memory>
#include <ostream>
#include "Term.hpp"

namespace logic {
    
    class Formula {
    public:
        std::string declareTPTP(std::string decl, bool conjecture = false) const;
        std::string declareSMTLIB(std::string decl, bool conjecture = false) const;
       
        virtual std::string toTPTP() const = 0;
        virtual std::string toSMTLIB(unsigned indentation = 0) const = 0;
        virtual std::string prettyString(unsigned indentation = 0) const = 0;
        virtual unsigned occurrences(const Term& t) const = 0;
    };

    typedef std::shared_ptr<const Formula> FormulaPtr;
    
    class PredicateFormula : public Formula
    {
        friend class Formulas;
        
    public:
        PredicateFormula(PredTermPtr p) : p(p) {}

        const PredTermPtr p;

        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
        unsigned occurrences(const Term& t) const override;
    };
    
    class EqualityFormula : public Formula
    {
        friend class Formulas;
        
    public:
        EqualityFormula(bool polarity, TermPtr left, TermPtr right) :
        polarity(polarity),
        left(left),
        right(right)
        {}

        const bool polarity;
        const TermPtr left;
        const TermPtr right;
        
        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
        unsigned occurrences(const Term& t) const override;
    };
    
    class ConjunctionFormula : public Formula
    {
        friend class Formulas;
        
    public:
        ConjunctionFormula(std::vector<FormulaPtr> conj) : conj(conj){}
        ConjunctionFormula(std::initializer_list<FormulaPtr> conj) : conj(conj){}
        
        const std::vector<FormulaPtr> conj;

        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
        unsigned occurrences(const Term& t) const override;
    };
    
    class DisjunctionFormula : public Formula
    {
        friend class Formulas;
        
    public:
        DisjunctionFormula(std::vector<FormulaPtr> disj) : disj(disj){}
        DisjunctionFormula(std::initializer_list<FormulaPtr> disj) : disj(disj){}
        
        const std::vector<FormulaPtr> disj;

        std::string toTPTP() const override ;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
        unsigned occurrences(const Term& t) const override;
    };
    
    class NegationFormula : public Formula
    {
        friend class Formulas;
        
    public:
        NegationFormula(FormulaPtr f) : f(f) {}
        
        const FormulaPtr f;

        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
        unsigned occurrences(const Term& t) const override;
        
    };
    
    class ExistentialFormula : public Formula
    {
        friend class Formulas;
        
    public:
        ExistentialFormula(std::vector<LVariablePtr> vars, FormulaPtr f) : vars(vars), f(f){}
        ExistentialFormula(std::initializer_list<LVariablePtr> vars, FormulaPtr f) : vars(vars), f(f){}
        
        const std::vector<LVariablePtr> vars;
        const FormulaPtr f;
        
        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
        unsigned occurrences(const Term& t) const override;
    };
    
    class UniversalFormula : public Formula
    {
        friend class Formulas;
        
    public:
        UniversalFormula(std::vector<LVariablePtr> vars, FormulaPtr f) : vars(vars), f(f){}
        UniversalFormula(std::initializer_list<LVariablePtr> vars, FormulaPtr f) : vars(vars), f(f){}

        const std::vector<LVariablePtr> vars;
        const FormulaPtr f;
        
        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
        unsigned occurrences(const Term& t) const override;
    };
    
    class ImplicationFormula : public Formula
    {
        friend class Formulas;
        
    public:
        ImplicationFormula(FormulaPtr f1, FormulaPtr f2) : f1(f1), f2(f2) {}
        
        const FormulaPtr f1;
        const FormulaPtr f2;
        
        std::string toTPTP() const override;
        std::string toSMTLIB(unsigned indentation = 0) const override;
        std::string prettyString(unsigned indentation = 0) const override;
        unsigned occurrences(const Term& t) const override;
    };
    
    inline std::ostream& operator<<(std::ostream& ostr, const Formula& e) { ostr << e.toTPTP(); return ostr; }
    
# pragma mark - Formulas
    
    // We use Formulas as a manager-class for Formula-instances
    class Formulas
    {
    public:
        
        // construct new terms
        static FormulaPtr predicateFormula(PredTermPtr p);
        static FormulaPtr equalityFormula(bool polarity, TermPtr left, TermPtr right);

        static FormulaPtr negationFormula(FormulaPtr f);

        static FormulaPtr conjunctionFormula(std::vector<FormulaPtr> conj);
        static FormulaPtr conjunctionFormula(std::initializer_list<FormulaPtr> conj);
        static FormulaPtr disjunctionFormula(std::vector<FormulaPtr> disj);
        static FormulaPtr disjunctionFormula(std::initializer_list<FormulaPtr> disj);
        
        static FormulaPtr implicationFormula(FormulaPtr f1, FormulaPtr f2);
        
        static FormulaPtr existentialFormula(std::vector<LVariablePtr> vars, FormulaPtr f);
        static FormulaPtr universalFormula(std::vector<LVariablePtr> vars, FormulaPtr f);
    };
}

#endif

