#include "Formula.hpp"

#include <set>
#include <algorithm>
#include <iostream>

namespace logic {
    
    std::string Formula::declareTPTP(std::string decl, bool conjecture) const
    {
        return "tff(" + decl + ", " + (conjecture ? "conjecture, " : "hypothesis, ") + toTPTP() + ").";
    }
    
    std::string PredicateFormula::toTPTP() const
    {
        return _p->toTPTP();
    }
    
    std::string EqualityFormula::toTPTP() const
    {
        if (_polarity)
            return _left->toTPTP() + " = " + _right->toTPTP();
        else
            return _left->toTPTP() + " != " + _right->toTPTP();
    }
    
    std::string ConjunctionFormula::toTPTP() const
    {
        if (_conj.size() == 0)
            return "$true";
        std::string str = "(";
        for (unsigned i = 0; i < _conj.size(); i++) {
            str += _conj[i]->toTPTP();
            
            str += (i == _conj.size() - 1) ? ")" : " & ";
        }
        return str;
    }
    
    std::string DisjunctionFormula::toTPTP() const
    {
        if (_disj.size() == 0)
            return "$false";
        std::string str = "(";
        for (unsigned i = 0; i < _disj.size(); i++) {
            str += _disj[i]->toTPTP();
            
            str += (i == _disj.size() - 1) ? ")" : " | ";
        }
        return str;  }
    
    std::string NegationFormula::toTPTP() const
    {
        return "~(" + _f->toTPTP() + ")";
    }
    
    std::string ExistentialFormula::toTPTP() const
    {
        std::string str = "? [";
        for (unsigned i = 0; i < _vars.size(); i++) {
            str += _vars[i]->name() + " : " + _vars[i]->sort()->name();
            if (i != _vars.size() - 1) { str += ", "; }
        }
        str += "] : " + _f->toTPTP();
        return str;
    }
    
    std::string UniversalFormula::toTPTP() const
    {
        std::string str = "! [";
        for (unsigned i = 0; i < _vars.size(); i++) {
            str += _vars[i]->name() + " : " + _vars[i]->sort()->name();
            if (i != _vars.size() - 1) { str += ", "; }
        }
        str += "] : " + _f->toTPTP();
        return str;
    }

    std::string ImplicationFormula::toTPTP() const
    {
        return "(" + _f1->toTPTP() + " => " + _f2->toTPTP() + ")";
    }

    Formula* Formula::quantify(bool univ) const
    {
        std::vector<LVariable*> vars = freeVariables();
        std::sort(vars.begin(),vars.end(),compareLVarPointers);
        std::unique(vars.begin(), vars.end(), eqLVarPointers);
        Formula *f = clone();
        
        if (vars.empty()) {
            return f;
        }
        
        if (univ) {
            return new UniversalFormula(vars, f);
        } else {
            return new ExistentialFormula(vars, f);
        }
    }
    
    std::vector<LVariable*> PredicateFormula::freeVariables() const
    {
        return _p->freeVariables();
    }
    
    std::vector<LVariable*> EqualityFormula::freeVariables() const
    {
        auto l = _left->freeVariables();
        auto r = _right->freeVariables();
        
        std::sort(l.begin(), l.end(), compareLVarPointers);
        std::sort(r.begin(), r.end(), compareLVarPointers);
        
        std::vector<LVariable*> res;
        std::set_union(l.begin(), l.end(),
                       r.begin(), r.end(),
                       std::back_inserter(res),compareLVarPointers);
        return res;
    }
    
    std::vector<LVariable*> ConjunctionFormula::freeVariables() const
    {
        // collect free variables from all conjuncts
        std::vector<LVariable*> freeVars;
        for(const auto& conjunct : _conj)
        {
            auto freeVarsConjunct = conjunct->freeVariables();
            freeVars.insert(freeVars.end(), freeVarsConjunct.begin(), freeVarsConjunct.end());
        }
        
        // sort and remove duplicates
        std::sort(freeVars.begin(), freeVars.end(), compareLVarPointers);
        freeVars.erase(unique(freeVars.begin(), freeVars.end(), compareLVarPointers), freeVars.end());
        
        return freeVars;
    }
    
    std::vector<LVariable*> DisjunctionFormula::freeVariables() const
    {
        // collect free variables from all disjuncts
        std::vector<LVariable*> freeVars;
        for(const auto& disjunct : _disj)
        {
            auto freeVarsDisjunct = disjunct->freeVariables();
            freeVars.insert(freeVars.end(), freeVarsDisjunct.begin(), freeVarsDisjunct.end());
        }
        
        // sort and remove duplicates
        std::sort(freeVars.begin(), freeVars.end(), compareLVarPointers);
        freeVars.erase( unique(freeVars.begin(), freeVars.end(), compareLVarPointers), freeVars.end());
        
        return freeVars;
    }
    
    std::vector<LVariable*> NegationFormula::freeVariables() const
    {
        return _f->freeVariables();
    }
    
    std::vector<LVariable*> ExistentialFormula::freeVariables() const
    {
        std::vector<LVariable*> l = _f->freeVariables();
        
        for (const auto& var : _vars)
        {
            l.erase(std::remove(l.begin(), l.end(), var), l.end());
        }
        return l;
    }
    
    std::vector<LVariable*> UniversalFormula::freeVariables() const
    {
        // could be done more efficient if we would be able to assume that _vars are ordered too.
        std::vector<LVariable*> l = _f->freeVariables();
        
        for (const auto& var : _vars)
        {
            l.erase(std::remove(l.begin(), l.end(), var), l.end());
        }
        return l;
    }
    
    std::vector<LVariable*> ImplicationFormula::freeVariables() const
    {
        auto l = _f1->freeVariables();
        auto r = _f2->freeVariables();
        std::sort(l.begin(), l.end(), compareLVarPointers);
        std::sort(r.begin(), r.end(), compareLVarPointers);
        
        std::vector<LVariable*> res;
        std::set_union(l.begin(), l.end(),
                       r.begin(), r.end(),
                       std::back_inserter(res), compareLVarPointers);
        return res;
    }
 
    std::string PredicateFormula::prettyString(unsigned indentation) const
    {
        return std::string(indentation, ' ') + _p->prettyString();
    }
    
    std::string EqualityFormula::prettyString(unsigned indentation) const
    {
        if (_polarity)
            return std::string(indentation, ' ') + _left->prettyString() + " = " + _right->prettyString();
        else
            return std::string(indentation, ' ') + _left->prettyString() + " != " + _right->prettyString();
    }
    
    std::string ConjunctionFormula::prettyString(unsigned indentation) const
    {
        if (_conj.size() == 0)
            return std::string(indentation, ' ') + "True";
        
        std::string str = std::string(indentation, ' ') + "AND\n";
        
        for (unsigned i = 0; i < _conj.size(); i++)
        {
            str += _conj[i]->prettyString(indentation + 3);
            str += (i+1 < _conj.size()) ? "\n" : "";
        }
        
        return str;
    }
    
    std::string DisjunctionFormula::prettyString(unsigned indentation) const
    {
        if (_disj.size() == 0)
            return std::string(indentation, ' ') + "False";
        
        std::string str = std::string(indentation, ' ') + "OR\n";
        
        for (unsigned i = 0; i < _disj.size(); i++)
        {
            str += _disj[i]->prettyString(indentation + 3);
            str += (i+1 < _disj.size()) ? "\n" : "";
        }
        
        return str;
    }
    
    std::string NegationFormula::prettyString(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "NOT\n";
        str += _f->prettyString(indentation + 3);
        return  str;
    }
    
    std::string ExistentialFormula::prettyString(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "EXISTS ";
        for (unsigned i = 0; i < _vars.size(); i++) {
            str += _vars[i]->name() + " : " + _vars[i]->sort()->name();
            if (i != _vars.size() - 1) { str += ", "; }
        }
        str += ".\n" + _f->prettyString(indentation + 3);
        return str;
    }
    
    std::string UniversalFormula::prettyString(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "FORALL ";
        for (unsigned i = 0; i < _vars.size(); i++) {
            str += _vars[i]->name() + " : " + _vars[i]->sort()->name();
            if (i != _vars.size() - 1) { str += ", "; }
        }
        str += ".\n";
        str += _f->prettyString(indentation + 3);
        
        return str;
    }
    std::string ImplicationFormula::prettyString(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "=>\n";
        str += _f1->prettyString(indentation + 3) + "\n";
        str += _f2->prettyString(indentation + 3);
        return  str;
    }
}

