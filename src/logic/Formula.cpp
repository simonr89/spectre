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
            return "; " + decl + "\n" + "(assert-not\n" + toSMTLIB(3) + "\n)\n";
        }
        else
        {
            return "; " + decl + "\n" + "(assert\n" + toSMTLIB(3) + "\n)\n";
        }
    }
    
    std::string PredicateFormula::toTPTP() const
    {
        return p->toTPTP();
    }
    
    std::string PredicateFormula::toSMTLIB(unsigned indentation) const
    {
        return std::string(indentation, ' ') + p->toSMTLIB();
    }
    
    std::string EqualityFormula::toTPTP() const
    {
        if (polarity)
            return left->toTPTP() + " = " + right->toTPTP();
        else
            return left->toTPTP() + " != " + right->toTPTP();
    }
    
    std::string EqualityFormula::toSMTLIB(unsigned indentation) const
    {
        if (polarity)
        {
            return std::string(indentation, ' ') + "(= " + left->toSMTLIB() + " " + right->toSMTLIB() + ")";
        }
        else
        {
            return std::string(indentation, ' ')  + "(not (= " + left->toSMTLIB() + " " + right->toSMTLIB() + "))";
        }
    }
    
 
    std::string ConjunctionFormula::toTPTP() const
    {
        if (conj.size() == 0)
            return "$true";
        std::string str = "";
        for (unsigned i = 0; i < conj.size(); i++) {
            str += "(" + conj[i]->toTPTP() + ")";
            
            str += (i == conj.size() - 1) ? "" : " & ";
        }
        return str;
    }
    
    std::string ConjunctionFormula::toSMTLIB(unsigned indentation) const
    {
        if (conj.size() == 0)
        {
            return std::string(indentation, ' ') + "true";
        }
        std::string str = std::string(indentation, ' ') + "(and\n";
        for (unsigned i = 0; i < conj.size(); i++) {
            str += conj[i]->toSMTLIB(indentation + 3) + "\n";
        }
        str += std::string(indentation, ' ') + ")";
        return str;
    }
    
    std::string DisjunctionFormula::toTPTP() const
    {
        if (disj.size() == 0)
            return "$false";
        std::string str = "";
        for (unsigned i = 0; i < disj.size(); i++) {
            str += "(" + disj[i]->toTPTP() + ")";
            
            str += (i == disj.size() - 1) ? "" : " | ";
        }
        return str;
    }
    
    std::string DisjunctionFormula::toSMTLIB(unsigned indentation) const
    {
        if (disj.size() == 0)
        {
            return std::string(indentation, ' ') + "false";
        }
        std::string str = std::string(indentation, ' ') + "(or\n";
        for (unsigned i = 0; i < disj.size(); i++) {
            str += disj[i]->toSMTLIB(indentation + 3) + "\n";
        }
        str += std::string(indentation, ' ') + ")";
        return str;
    }
    
    std::string NegationFormula::toTPTP() const
    {
        return "~(" + f->toTPTP() + ")";
    }
    
    std::string NegationFormula::toSMTLIB(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "(not\n";
        str += f->toSMTLIB(indentation + 3) + "\n";
        str += std::string(indentation, ' ') + ")";
        return  str;
    }
    
    std::string ExistentialFormula::toTPTP() const
    {
        std::string str = "? [";
        for (unsigned i = 0; i < vars.size(); i++) {
            str += vars[i]->name + " : " + vars[i]->sort->toTPTP();
            if (i != vars.size() - 1) { str += ", "; }
        }
        str += "] : (" + f->toTPTP() + ")";
        return str;
    }
    
    std::string ExistentialFormula::toSMTLIB(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "(exists ";
        
        //list of quantified variables
        str += "(";
        for (const auto& var : vars)
        {
            str += "(" + var->name + " " + var->sort->toSMTLIB() + ")";
        }
        str += ")\n";
        
        // formula
        str += f->toSMTLIB(indentation + 3) + "\n";
        
        str += std::string(indentation, ' ') + ")";
        return str;
    }
    
    std::string UniversalFormula::toTPTP() const
    {
        std::string str = "! [";
        for (unsigned i = 0; i < vars.size(); i++) {
            str += vars[i]->name + " : " + vars[i]->sort->toTPTP();
            if (i != vars.size() - 1) { str += ", "; }
        }
        str += "] : (" + f->toTPTP() + ")";
        return str;
    }

    std::string UniversalFormula::toSMTLIB(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "(forall ";
        
        //list of quantified variables
        str += "(";
        for (const auto& var : vars)
        {
            str += "(" + var->name + " " + var->sort->toSMTLIB() + ")";
        }
        str += ")\n";
        
        // formula
        str += f->toSMTLIB(indentation + 3) + "\n";
        
        str += std::string(indentation, ' ') + ")";
        return str;
    }
    
    std::string ImplicationFormula::toTPTP() const
    {
        return "(" + f1->toTPTP() + ")" + " => (" + f2->toTPTP() + ")";
    }
    
    std::string ImplicationFormula::toSMTLIB(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "(=>\n";
        str += f1->toSMTLIB(indentation + 3) + "\n";
        str += f2->toSMTLIB(indentation + 3) + "\n";
        str += std::string(indentation, ' ') + ")";
        return  str;
    }

//    std::shared_ptr<const Formula> Formula::quantify(bool univ) const
//    {
//        std::vector<std::shared_ptr<const LVariable>> vars = freeVariables();
//
//        if (vars.empty())
//        {
//            return std::make_shared<const Formula>(this);
//        }
//
//        if (univ)
//        {
//            return std::make_shared<UniversalFormula>(vars, std::make_shared<const Formula>(this));
//        }
//        else
//        {
//            return std::make_shared<ExistentialFormula>(vars, std::make_shared<const Formula>(this));
//        }
//    }
//
//    std::vector<std::shared_ptr<const LVariable>> PredicateFormula::freeVariables() const
//    {
//        return p->freeVariables();
//    }
//
//    std::vector<std::shared_ptr<const LVariable>> EqualityFormula::freeVariables() const
//    {
//        auto l = left->freeVariables();
//        auto r = right->freeVariables();
//
//        std::sort(l.begin(), l.end(), compareLVarPointers);
//        std::sort(r.begin(), r.end(), compareLVarPointers);
//
//        std::vector<std::shared_ptr<const LVariable>> res;
//        std::set_union(l.begin(), l.end(),
//                       r.begin(), r.end(),
//                       std::back_inserter(res),compareLVarPointers);
//
//        return res;
//    }
//
//    std::vector<std::shared_ptr<const LVariable>> ConjunctionFormula::freeVariables() const
//    {
//        // collect free variables from all conjuncts
//        std::vector<std::shared_ptr<const LVariable>> res;
//        for(const auto& conjunct : conj)
//        {
//            auto freeVarsConjunct = conjunct->freeVariables();
//            res.insert(res.end(), freeVarsConjunct.begin(), freeVarsConjunct.end());
//        }
//
//        // sort and remove duplicates
//        std::sort(res.begin(), res.end(), compareLVarPointers);
//        res.erase(std::unique(res.begin(), res.end(), eqLVarPointers), res.end());
//
//        return res;
//    }
//
//    std::vector<std::shared_ptr<const LVariable>> DisjunctionFormula::freeVariables() const
//    {
//        // collect free variables from all disjuncts
//        std::vector<std::shared_ptr<const LVariable>> res;
//        for(const auto& disjunct : disj)
//        {
//            auto freeVarsDisjunct = disjunct->freeVariables();
//            res.insert(res.end(), freeVarsDisjunct.begin(), freeVarsDisjunct.end());
//        }
//
//        // sort and remove duplicates
//        std::sort(res.begin(), res.end(), compareLVarPointers);
//        res.erase( unique(res.begin(), res.end(), eqLVarPointers), res.end());
//
//        return res;
//    }
//
//    std::vector<std::shared_ptr<const LVariable>> NegationFormula::freeVariables() const
//    {
//        return f->freeVariables();
//    }
//
//    std::vector<std::shared_ptr<const LVariable>> ExistentialFormula::freeVariables() const
//    {
//        // could be done more efficient if we would be able to assume that vars are ordered too.
//        std::vector<std::shared_ptr<const LVariable>> res = f->freeVariables();
//
//        // perform std::remove,
//        // couldn't figure out how to pass eqLVarPointers as custom comparison function
//        auto first = res.begin();
//        for (; first != res.end(); ++first)
//        {
//            bool shouldBeRemoved = false;
//            for (const auto& var : vars)
//            {
//                if (eqLVarPointers(var,*first))
//                {
//                    shouldBeRemoved = true;
//                    break;
//                }
//            }
//            if (shouldBeRemoved)
//            {
//                break;
//            }
//        }
//        if (first != res.end())
//        {
//            for(auto i = first; ++i != res.end(); )
//            {
//                bool shouldBeRemoved = false;
//                for (const auto& var : vars)
//                {
//                    if (eqLVarPointers(var,*i))
//                    {
//                        shouldBeRemoved = true;
//                        break;
//                    }
//                }
//                if (!shouldBeRemoved)
//                {
//                    *first++ = std::move(*i);
//                }
//            }
//        }
//
//        // now first points to first element which should be erased
//        res.erase(first,res.end());
//
//        return res;
//    }
//
//    std::vector<std::shared_ptr<const LVariable>> UniversalFormula::freeVariables() const
//    {
//        // could be done more efficient if we would be able to assume that vars are ordered too.
//        std::vector<std::shared_ptr<const LVariable>> res = f->freeVariables();
//
//        // perform std::remove,
//        // couldn't figure out how to pass eqLVarPointers as custom comparison function
//        auto first = res.begin();
//        for (; first != res.end(); ++first)
//        {
//            bool shouldBeRemoved = false;
//            for (const auto& var : vars)
//            {
//                if (eqLVarPointers(var,*first))
//                {
//                    shouldBeRemoved = true;
//                    break;
//                }
//            }
//            if (shouldBeRemoved)
//            {
//                break;
//            }
//        }
//        if (first != res.end())
//        {
//            for(auto i = first; ++i != res.end(); )
//            {
//                bool shouldBeRemoved = false;
//                for (const auto& var : vars)
//                {
//                    if (eqLVarPointers(var,*i))
//                    {
//                        shouldBeRemoved = true;
//                        break;
//                    }
//                }
//                if (!shouldBeRemoved)
//                {
//                    *first++ = std::move(*i);
//                }
//            }
//        }
//
//        // now first points to first element which should be erased
//        res.erase(first,res.end());
//
//        return res;
//    }
//
//    std::vector<std::shared_ptr<const LVariable>> ImplicationFormula::freeVariables() const
//    {
//        auto l = f1->freeVariables();
//        auto r = f2->freeVariables();
//        std::sort(l.begin(), l.end(), compareLVarPointers);
//        std::sort(r.begin(), r.end(), compareLVarPointers);
//
//        std::vector<std::shared_ptr<const LVariable>> res;
//        std::set_union(l.begin(), l.end(),
//                       r.begin(), r.end(),
//                       std::back_inserter(res), compareLVarPointers);
//        
//        return res;
//    }
 
    std::string PredicateFormula::prettyString(unsigned indentation) const
    {
        return std::string(indentation, ' ') + p->prettyString();
    }
    
    std::string EqualityFormula::prettyString(unsigned indentation) const
    {
        if (polarity)
            return std::string(indentation, ' ') + left->prettyString() + " = " + right->prettyString();
        else
            return std::string(indentation, ' ') + left->prettyString() + " != " + right->prettyString();
    }
    
    std::string ConjunctionFormula::prettyString(unsigned indentation) const
    {
        if (conj.size() == 0)
            return std::string(indentation, ' ') + "True";
        
        std::string str = std::string(indentation, ' ') + "AND\n";
        
        for (unsigned i = 0; i < conj.size(); i++)
        {
            str += conj[i]->prettyString(indentation + 3);
            str += (i+1 < conj.size()) ? "\n" : "";
        }
        
        return str;
    }
    
    std::string DisjunctionFormula::prettyString(unsigned indentation) const
    {
        if (disj.size() == 0)
            return std::string(indentation, ' ') + "False";
        
        std::string str = std::string(indentation, ' ') + "OR\n";
        
        for (unsigned i = 0; i < disj.size(); i++)
        {
            str += disj[i]->prettyString(indentation + 3);
            str += (i+1 < disj.size()) ? "\n" : "";
        }
        
        return str;
    }
    
    std::string NegationFormula::prettyString(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "NOT\n";
        str += f->prettyString(indentation + 3);
        return  str;
    }
    
    std::string ExistentialFormula::prettyString(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "EXISTS ";
        for (unsigned i = 0; i < vars.size(); i++) {
            str += vars[i]->name + " : " + vars[i]->sort->name;
            if (i != vars.size() - 1) { str += ", "; }
        }
        str += ".\n" + f->prettyString(indentation + 3);
        return str;
    }
    
    std::string UniversalFormula::prettyString(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "FORALL ";
        for (unsigned i = 0; i < vars.size(); i++) {
            str += vars[i]->name + " : " + vars[i]->sort->name;
            if (i != vars.size() - 1) { str += ", "; }
        }
        str += ".\n";
        str += f->prettyString(indentation + 3);
        
        return str;
    }
    std::string ImplicationFormula::prettyString(unsigned indentation) const
    {
        std::string str = std::string(indentation, ' ') + "=>\n";
        str += f1->prettyString(indentation + 3) + "\n";
        str += f2->prettyString(indentation + 3);
        return  str;
    }
    
# pragma mark - Formulas
    
    std::shared_ptr<const PredicateFormula> Formulas::predicateFormula(std::shared_ptr<const PredTerm> p)
    {
        return std::shared_ptr<const PredicateFormula>(new PredicateFormula(p));
    }
    std::shared_ptr<const EqualityFormula> Formulas::equalityFormula(bool polarity, std::shared_ptr<const Term> left, std::shared_ptr<const Term> right)
    {
        return std::shared_ptr<const EqualityFormula>(new EqualityFormula(polarity, left, right));
    }
    std::shared_ptr<const NegationFormula>  Formulas::negationFormula(std::shared_ptr<const Formula> f)
    {
        return std::shared_ptr<const NegationFormula>(new NegationFormula(f));
    }
    std::shared_ptr<const ConjunctionFormula> Formulas::conjunctionFormula(std::vector<std::shared_ptr<const Formula>> conj)
    {
        return std::shared_ptr<const ConjunctionFormula>(new ConjunctionFormula(conj));
    }
    std::shared_ptr<const ConjunctionFormula> Formulas::conjunctionFormula(std::initializer_list<std::shared_ptr<const Formula>> conj)
    {
        return std::shared_ptr<const ConjunctionFormula>(new ConjunctionFormula(conj));
    }
    std::shared_ptr<const DisjunctionFormula> Formulas::disjunctionFormula(std::vector<std::shared_ptr<const Formula>> disj)
    {
        return std::shared_ptr<const DisjunctionFormula>(new DisjunctionFormula(disj));
    }
    std::shared_ptr<const DisjunctionFormula> Formulas::disjunctionFormula(std::initializer_list<std::shared_ptr<const Formula>> disj)
    {
        return std::shared_ptr<const DisjunctionFormula>(new DisjunctionFormula(disj));
    }
    
    std::shared_ptr<const ImplicationFormula> Formulas::implicationFormula(std::shared_ptr<const Formula> f1, std::shared_ptr<const Formula> f2)
    {
        return std::shared_ptr<const ImplicationFormula>(new ImplicationFormula(f1, f2));
    }
    
    std::shared_ptr<const ExistentialFormula> Formulas::existentialFormula(std::vector<std::shared_ptr<const LVariable>> vars, std::shared_ptr<const Formula> f)
    {
        return std::shared_ptr<const ExistentialFormula>(new ExistentialFormula(vars, f));
    }
    std::shared_ptr<const UniversalFormula> Formulas::universalFormula(std::vector<std::shared_ptr<const LVariable>> vars, std::shared_ptr<const Formula> f)
    {
        return std::shared_ptr<const UniversalFormula>(new UniversalFormula(vars, f));
    }
}

