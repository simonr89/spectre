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

    unsigned PredicateFormula::occurrences(const Term& t) const
    {
        return p->occurrences(t);
    }

    Formula* PredicateFormula::apply(const Substitution subst) const
    {
        PredTermPtr newp = std::static_pointer_cast<const PredTerm>(Terms::apply(p, subst));
        return new PredicateFormula(newp);
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

    unsigned EqualityFormula::occurrences(const Term& t) const
    {
        return left->occurrences(t) + right->occurrences(t);
    }

    Formula* EqualityFormula::apply(const Substitution subst) const
    {
        TermPtr newleft = Terms::apply(left, subst);
        TermPtr newright = Terms::apply(right, subst);
        return new EqualityFormula(polarity, newleft, newright);
    }
 
    std::string ConjunctionFormula::toTPTP() const
    {
        if (conj.size() == 0)
            return "$true";
        if (conj.size() == 1)
            return conj[0]->toTPTP();
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
        if (conj.size() == 1)
        {
            return conj[0]->toSMTLIB(indentation);
        }
        std::string str = std::string(indentation, ' ') + "(and\n";
        for (unsigned i = 0; i < conj.size(); i++) {
            str += conj[i]->toSMTLIB(indentation + 3) + "\n";
        }
        str += std::string(indentation, ' ') + ")";
        return str;
    }

    unsigned ConjunctionFormula::occurrences(const Term& t) const
    {
        unsigned r = 0;
        for (FormulaPtr f: conj) {
            r += f->occurrences(t);
        }
        return r;
    }

    Formula* ConjunctionFormula::apply(const Substitution subst) const
    {
        std::vector<FormulaPtr> newconj(conj.size());

        for (unsigned i = 0; i < conj.size(); i++)
        {
            newconj[i] = Formulas::apply(conj[i], subst);
        }
        
        return new ConjunctionFormula(newconj);
    }
    
    std::string DisjunctionFormula::toTPTP() const
    {
        if (disj.size() == 0)
            return "$false";
        if (disj.size() == 1)
            return disj[0]->toTPTP();
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
        if (disj.size() == 1)
        {
            return disj[0]->toSMTLIB(indentation);
        }
        std::string str = std::string(indentation, ' ') + "(or\n";
        for (unsigned i = 0; i < disj.size(); i++) {
            str += disj[i]->toSMTLIB(indentation + 3) + "\n";
        }
        str += std::string(indentation, ' ') + ")";
        return str;
    }

    unsigned DisjunctionFormula::occurrences(const Term& t) const
    {
        unsigned r = 0;
        for (FormulaPtr f: disj) {
            r += f->occurrences(t);
        }
        return r;
    }

    Formula* DisjunctionFormula::apply(const Substitution subst) const
    {
        std::vector<FormulaPtr> newdisj(disj.size());

        for (unsigned i = 0; i < disj.size(); i++)
        {
            newdisj[i] = Formulas::apply(disj[i], subst);
        }
        
        return new DisjunctionFormula(newdisj);
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

    unsigned NegationFormula::occurrences(const Term& t) const
    {
        return f->occurrences(t);
    }

    Formula* NegationFormula::apply(const Substitution subst) const
    {
        FormulaPtr newf = Formulas::apply(f, subst);
        return new NegationFormula(newf);
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

    unsigned ExistentialFormula::occurrences(const Term& t) const
    {
        return f->occurrences(t);
    }

    Formula* ExistentialFormula::apply(const Substitution subst) const
    {
        FormulaPtr newf = Formulas::apply(f, subst);
        return new ExistentialFormula(vars, newf);
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

    unsigned UniversalFormula::occurrences(const Term& t) const
    {
        return f->occurrences(t);
    }

    Formula* UniversalFormula::apply(const Substitution subst) const
    {
        FormulaPtr newf = Formulas::apply(f, subst);
        return new UniversalFormula(vars, newf);
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

    unsigned ImplicationFormula::occurrences(const Term& t) const
    {
        return f1->occurrences(t) + f2->occurrences(t);
    }

    Formula* ImplicationFormula::apply(const Substitution subst) const
    {
        FormulaPtr newf1 = Formulas::apply(f1, subst);
        FormulaPtr newf2 = Formulas::apply(f2, subst);
        return new ImplicationFormula(newf1, newf2);
    }

//    FormulaPtr Formula::quantify(bool univ) const
//    {
//        std::vector<LVariablePtr> vars = freeVariables();
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
//    std::vector<LVariablePtr> PredicateFormula::freeVariables() const
//    {
//        return p->freeVariables();
//    }
//
//    std::vector<LVariablePtr> EqualityFormula::freeVariables() const
//    {
//        auto l = left->freeVariables();
//        auto r = right->freeVariables();
//
//        std::sort(l.begin(), l.end(), compareLVarPointers);
//        std::sort(r.begin(), r.end(), compareLVarPointers);
//
//        std::vector<LVariablePtr> res;
//        std::set_union(l.begin(), l.end(),
//                       r.begin(), r.end(),
//                       std::back_inserter(res),compareLVarPointers);
//
//        return res;
//    }
//
//    std::vector<LVariablePtr> ConjunctionFormula::freeVariables() const
//    {
//        // collect free variables from all conjuncts
//        std::vector<LVariablePtr> res;
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
//    std::vector<LVariablePtr> DisjunctionFormula::freeVariables() const
//    {
//        // collect free variables from all disjuncts
//        std::vector<LVariablePtr> res;
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
//    std::vector<LVariablePtr> NegationFormula::freeVariables() const
//    {
//        return f->freeVariables();
//    }
//
//    std::vector<LVariablePtr> ExistentialFormula::freeVariables() const
//    {
//        // could be done more efficient if we would be able to assume that vars are ordered too.
//        std::vector<LVariablePtr> res = f->freeVariables();
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
//    std::vector<LVariablePtr> UniversalFormula::freeVariables() const
//    {
//        // could be done more efficient if we would be able to assume that vars are ordered too.
//        std::vector<LVariablePtr> res = f->freeVariables();
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
//    std::vector<LVariablePtr> ImplicationFormula::freeVariables() const
//    {
//        auto l = f1->freeVariables();
//        auto r = f2->freeVariables();
//        std::sort(l.begin(), l.end(), compareLVarPointers);
//        std::sort(r.begin(), r.end(), compareLVarPointers);
//
//        std::vector<LVariablePtr> res;
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
    
    FormulaPtr Formulas::predicateFormula(PredTermPtr p)
    {
        return FormulaPtr(new PredicateFormula(p));
    }
    
    FormulaPtr Formulas::equalityFormula(bool polarity, TermPtr left, TermPtr right)
    {
        return FormulaPtr(new EqualityFormula(polarity, left, right));
    }
    
    FormulaPtr Formulas::negationFormula(FormulaPtr f)
    {
        return FormulaPtr(new NegationFormula(f));
    }
    
    FormulaPtr Formulas::conjunctionFormula(std::vector<FormulaPtr> conj)
    {
        return FormulaPtr(new ConjunctionFormula(conj));
    }
    
    FormulaPtr Formulas::conjunctionFormula(std::initializer_list<FormulaPtr> conj)
    {
        return FormulaPtr(new ConjunctionFormula(conj));
    }
    
    FormulaPtr Formulas::disjunctionFormula(std::vector<FormulaPtr> disj)
    {
        return FormulaPtr(new DisjunctionFormula(disj));
    }
    
    FormulaPtr Formulas::disjunctionFormula(std::initializer_list<FormulaPtr> disj)
    {
        return FormulaPtr(new DisjunctionFormula(disj));
    }
    
    FormulaPtr Formulas::implicationFormula(FormulaPtr f1, FormulaPtr f2)
    {
        return FormulaPtr(new ImplicationFormula(f1, f2));
    }
    
    FormulaPtr Formulas::existentialFormula(std::vector<LVariablePtr> vars, FormulaPtr f)
    {
        return FormulaPtr(new ExistentialFormula(vars, f));
    }
    
    FormulaPtr Formulas::universalFormula(std::vector<LVariablePtr> vars, FormulaPtr f)
    {
        return FormulaPtr(new UniversalFormula(vars, f));
    }

    FormulaPtr Formulas::apply(const FormulaPtr f, const Substitution subst)
    {
        bool occ;
        for (auto& p: subst) {
            // check occurrences (if one hasn't already been found)
            occ |= (f->occurrences(*p.first) > 0);
        }
        
        if (occ)
        {
            return FormulaPtr(f->apply(subst));
        }
        else
        {
            return f;
        }
    }
}

