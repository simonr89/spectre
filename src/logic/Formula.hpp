#ifndef __Formula__
#define __Formula__

#include <initializer_list>
#include <ostream>
#include "Term.hpp"

namespace logic {
    
    class Formula {
    public:
        virtual Formula* clone() const = 0;

        Formula* quantify(bool univ = true) const;

        std::string declareTPTP(std::string decl, bool conjecture = false) const;

        // returns a vector of the unbound variables of the formula
        virtual std::vector<LVariable*> freeVariables() const = 0;
        
        virtual std::string toTPTP() const = 0;
        virtual std::string prettyString(unsigned indentation = 0) const = 0;

    protected:
    };
    
    class PredicateFormula : public Formula {
    public:
        PredicateFormula(PredTerm* p) : _p(p) {}
        
        Formula* clone() const override { return new PredicateFormula(*this); }
        
        std::vector<LVariable*> freeVariables() const override;
        
        std::string toTPTP() const override;
        std::string prettyString(unsigned indentation = 0) const override;

    protected:
        
        PredTerm* _p;
    };
    
    class EqualityFormula : public Formula {
    public:
        EqualityFormula(bool polarity, const Term* left, const Term* right) :
        _polarity(polarity),
        _left(left),
        _right(right)
        {}

        Formula* clone() const override { return new EqualityFormula(*this); }

        std::vector<LVariable*> freeVariables() const override;

        std::string toTPTP() const override;
        std::string prettyString(unsigned indentation = 0) const override;
        
    protected:
        bool _polarity;
        const Term* _left;
        const Term* _right;
        
    };
    
    class ConjunctionFormula : public Formula {
    public:
        ConjunctionFormula(const std::vector<Formula*>& conj) :
        _conj(conj.size())
        {
            unsigned i = 0;
            for (auto it = conj.begin(); it != conj.end(); ++it) {
                _conj[i++] = *it;
            }
        }
        
        ConjunctionFormula(std::initializer_list<Formula*> conj) :
        _conj(conj)
        {}
        
        Formula* clone() const override { return new ConjunctionFormula(*this); }
        
        std::vector<LVariable*> freeVariables() const override;
        
        std::string toTPTP() const override;
        std::string prettyString(unsigned indentation = 0) const override;

    protected:
        std::vector<Formula*> _conj;
        
    };
    
    class DisjunctionFormula : public Formula {
    public:
        DisjunctionFormula(std::vector<Formula*>& disj) : _disj(disj.size())
        {
            unsigned i = 0;
            for (auto it = disj.begin(); it != disj.end(); ++it) {
                _disj[i++] = *it;
            }
        }
        
        DisjunctionFormula(std::initializer_list<Formula*> disj) : _disj(disj) {}
        
        Formula* clone() const override { return new DisjunctionFormula(*this); }

        std::vector<LVariable*> freeVariables() const override;

        std::string toTPTP() const override ;
        std::string prettyString(unsigned indentation = 0) const override;

    protected:
        std::vector<Formula*> _disj;
    };
    
    class NegationFormula : public Formula {
    public:
        NegationFormula(Formula *f) : _f(f) {}
        
        Formula* clone() const override { return new NegationFormula(*this); }

        std::vector<LVariable*> freeVariables() const override;

        std::string toTPTP() const override;
        std::string prettyString(unsigned indentation = 0) const override;
        
    protected:
        Formula *_f;
    };
    
    class ExistentialFormula : public Formula {
    public:
        ExistentialFormula(const std::vector<LVariable*>& vars, Formula* f) : _vars(vars.size()), _f(f)
        {
            unsigned i = 0;
            for (auto it = vars.begin(); it != vars.end(); ++it) {
                _vars[i++] = *it;
            }
        }
        
        ExistentialFormula(std::initializer_list<LVariable*> vars, Formula* f) : _vars(vars), _f(f) {}
        
        Formula* clone() const override { return new ExistentialFormula(*this); }

        std::vector<LVariable*> freeVariables() const override;

        std::string toTPTP() const override;
        std::string prettyString(unsigned indentation = 0) const override;

    protected:
        std::vector<LVariable*> _vars;
        Formula* _f;
    };
    
    class UniversalFormula : public Formula {
    public:
        UniversalFormula(const std::vector<LVariable*>& vars, Formula* f) : _vars(vars.size()), _f(f)
        {
            unsigned i = 0;
            for (auto it = vars.begin(); it != vars.end(); ++it) {
                _vars[i++] = *it;
            }
        }
        
        UniversalFormula(std::initializer_list<LVariable*> vars, Formula* f) : _vars(vars), _f(f) {}
        
        Formula* clone() const override { return new UniversalFormula(*this); }

        std::vector<LVariable*> freeVariables() const override;

        std::string toTPTP() const override;
        std::string prettyString(unsigned indentation = 0) const override;

    protected:
        std::vector<LVariable*> _vars;
        Formula* _f;
    };
    
    class ImplicationFormula : public Formula {
    public:
        ImplicationFormula(Formula* f1, Formula* f2) : _f1(f1), _f2(f2) {}
        
        Formula* clone() const override { return new ImplicationFormula(*this); }

        std::vector<LVariable*> freeVariables() const override;

        std::string toTPTP() const override;
        std::string prettyString(unsigned indentation = 0) const override;

    protected:
        Formula* _f1;
        Formula* _f2;
        
    };
    
    inline std::ostream& operator<<(std::ostream& ostr, const Formula& e) { ostr << e.toTPTP(); return ostr; }
}

#endif

