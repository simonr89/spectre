#include "Formula.hpp"

#include <set>
#include <algorithm>
#include <iostream>

namespace logic {
    
    std::string Formula::declareTPTP(std::string decl, bool conjecture) const
    {
        return "tff(" + decl + ", " + (conjecture ? "conjecture, " : "hypothesis, ") + toTPTP() + ").";
    }
    
    std::string Formula::declareSMTLIB(std::string decl, bool conjecture) const
    {
        if (conjecture)
        {
            // custom vampire smtlib-extension for asserting conjectures.
            return "; " + decl + "\n" + "(assert-not " + toSMTLIB() + ")";
        }
        else
        {
            return "; " + decl + "\n" + "(assert " + toSMTLIB() + ")";
        }
    }
    
    std::string PredicateFormula::toTPTP() const
    {
        return _p->toTPTP();
    }
    
    std::string PredicateFormula::toSMTLIB() const
    {
        return _p->toSMTLIB();
    }
    
    std::string EqualityFormula::toTPTP() const
    {
        if (_polarity)
            return _left->toTPTP() + " = " + _right->toTPTP();
        else
            return _left->toTPTP() + " != " + _right->toTPTP();
    }
    
    std::string EqualityFormula::toSMTLIB() const
    {
        if (_polarity)
        {
            return "(= " + _left->toSMTLIB() + " " + _right->toSMTLIB() + ")";
        }
        else
        {
            return "(not (= " + _left->toSMTLIB() + " " + _right->toSMTLIB() + "))";
        }
    }
    
    std::string ConjunctionFormula::toTPTP() const
    {
        if (_conj.size() == 0)
            return "$true";
        std::string str = "";
        for (unsigned i = 0; i < _conj.size(); i++) {
            str += "(" + _conj[i]->toTPTP() + ")";
            
            str += (i == _conj.size() - 1) ? "" : " & ";
        }
        return str;
    }
    
    std::string ConjunctionFormula::toSMTLIB() const
    {
        if (_conj.size() == 0)
            return "true";
        std::string str = "(and ";
        for (unsigned i = 0; i < _conj.size(); i++) {
            str += _conj[i]->toSMTLIB();
            str += (i == _conj.size() - 1) ? ")" : " ";
        }
        return str;
    }
    
    std::string DisjunctionFormula::toTPTP() const
    {
        if (_disj.size() == 0)
            return "$false";
        std::string str = "";
        for (unsigned i = 0; i < _disj.size(); i++) {
            str += "(" + _disj[i]->toTPTP() + ")";
            
            str += (i == _disj.size() - 1) ? "" : " | ";
        }
        return str;
    }
    
    std::string DisjunctionFormula::toSMTLIB() const
    {
        if (_disj.size() == 0)
            return "false";
        std::string str = "(or ";
        for (unsigned i = 0; i < _disj.size(); i++) {
            str += _disj[i]->toSMTLIB();
            str += (i == _disj.size() - 1) ? ")" : " ";
        }
        return str;
    }
    
    std::string NegationFormula::toTPTP() const
    {
        return "~(" + _f->toTPTP() + ")";
    }
    
    std::string NegationFormula::toSMTLIB() const
    {
        return "(not " + _f->toSMTLIB() + ")";
    }
    
    std::string ExistentialFormula::toTPTP() const
    {
        std::string str = "? [";
        for (unsigned i = 0; i < _vars.size(); i++) {
            str += _vars[i]->name + " : " + _vars[i]->sort->toTPTP();
            if (i != _vars.size() - 1) { str += ", "; }
        }
        str += "] : (" + _f->toTPTP() + ")";
        return str;
    }
    
    std::string ExistentialFormula::toSMTLIB() const
    {
        std::string str = "(exists ";
        
        //list of quantified variables
        str += "(";
        for (const auto& var : _vars)
        {
            str += "(" + var->name + " " + var->sort->toSMTLIB() + ")";
        }
        str += ")";
        
        // formula
        str += _f->toSMTLIB();
        
        str += ")";
        return str;
    }
    
    std::string UniversalFormula::toTPTP() const
    {
        std::string str = "! [";
        for (unsigned i = 0; i < _vars.size(); i++) {
            str += _vars[i]->name + " : " + _vars[i]->sort->toTPTP();
            if (i != _vars.size() - 1) { str += ", "; }
        }
        str += "] : (" + _f->toTPTP() + ")";
        return str;
    }

    std::string UniversalFormula::toSMTLIB() const
    {
        std::string str = "(forall ";
        
        //list of quantified variables
        str += "(";
        for (const auto& var : _vars)
        {
            str += "(" + var->name + " " + var->sort->toSMTLIB() + ")";
        }
        str += ")";
        
        // formula
        str += _f->toSMTLIB();
        
        str += ")";
        return str;
    }
    
    std::string ImplicationFormula::toTPTP() const
    {
        return "(" + _f1->toTPTP() + ")" + " => (" + _f2->toTPTP() + ")";
    }
    
    std::string ImplicationFormula::toSMTLIB() const
    {
        return "(=>" + _f1->toSMTLIB() + " " + _f2->toSMTLIB() + ")";
    }

    Formula* Formula::quantify(bool univ) const
    {
        std::vector<LVariable*> vars = freeVariables();
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
        std::vector<LVariable*> res;
        for(const auto& conjunct : _conj)
        {
            auto freeVarsConjunct = conjunct->freeVariables();
            res.insert(res.end(), freeVarsConjunct.begin(), freeVarsConjunct.end());
        }

        // sort and remove duplicates
        std::sort(res.begin(), res.end(), compareLVarPointers);
        res.erase(std::unique(res.begin(), res.end(), eqLVarPointers), res.end());
        
        return res;
    }
    
    std::vector<LVariable*> DisjunctionFormula::freeVariables() const
    {
        // collect free variables from all disjuncts
        std::vector<LVariable*> res;
        for(const auto& disjunct : _disj)
        {
            auto freeVarsDisjunct = disjunct->freeVariables();
            res.insert(res.end(), freeVarsDisjunct.begin(), freeVarsDisjunct.end());
        }
        
        // sort and remove duplicates
        std::sort(res.begin(), res.end(), compareLVarPointers);
        res.erase( unique(res.begin(), res.end(), eqLVarPointers), res.end());

        return res;
    }
    
    std::vector<LVariable*> NegationFormula::freeVariables() const
    {
        return _f->freeVariables();
    }
    
    std::vector<LVariable*> ExistentialFormula::freeVariables() const
    {
        // could be done more efficient if we would be able to assume that _vars are ordered too.
        std::vector<LVariable*> res = _f->freeVariables();
        
        // perform std::remove,
        // couldn't figure out how to pass eqLVarPointers as custom comparison function
        auto first = res.begin();
        for (; first != res.end(); ++first)
        {
            bool shouldBeRemoved = false;
            for (const auto& var : _vars)
            {
                if (eqLVarPointers(var,*first))
                {
                    shouldBeRemoved = true;
                    break;
                }
            }
            if (shouldBeRemoved)
            {
                break;
            }
        }
        if (first != res.end())
        {
            for(auto i = first; ++i != res.end(); )
            {
                bool shouldBeRemoved = false;
                for (const auto& var : _vars)
                {
                    if (eqLVarPointers(var,*i))
                    {
                        shouldBeRemoved = true;
                        break;
                    }
                }
                if (!shouldBeRemoved)
                {
                    *first++ = std::move(*i);
                }
            }
        }
        
        // now first points to first element which should be erased
        res.erase(first,res.end());
        
        return res;
    }
    
    std::vector<LVariable*> UniversalFormula::freeVariables() const
    {
        // could be done more efficient if we would be able to assume that _vars are ordered too.
        std::vector<LVariable*> res = _f->freeVariables();
        
        // perform std::remove,
        // couldn't figure out how to pass eqLVarPointers as custom comparison function
        auto first = res.begin();
        for (; first != res.end(); ++first)
        {
            bool shouldBeRemoved = false;
            for (const auto& var : _vars)
            {
                if (eqLVarPointers(var,*first))
                {
                    shouldBeRemoved = true;
                    break;
                }
            }
            if (shouldBeRemoved)
            {
                break;
            }
        }
        if (first != res.end())
        {
            for(auto i = first; ++i != res.end(); )
            {
                bool shouldBeRemoved = false;
                for (const auto& var : _vars)
                {
                    if (eqLVarPointers(var,*i))
                    {
                        shouldBeRemoved = true;
                        break;
                    }
                }
                if (!shouldBeRemoved)
                {
                    *first++ = std::move(*i);
                }
            }
        }

        // now first points to first element which should be erased
        res.erase(first,res.end());
        
        return res;
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
            str += _vars[i]->name + " : " + _vars[i]->sort->name;
            if (i != _vars.size() - 1) { str += ", "; }
        }
        str += ".\n" + _f->prettyString(indentation + 3);
        return str;
    }
    
    std::string UniversalFormula::prettyString(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "FORALL ";
        for (unsigned i = 0; i < _vars.size(); i++) {
            str += _vars[i]->name + " : " + _vars[i]->sort->name;
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

