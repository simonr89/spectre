#include "Term.hpp"

#include <algorithm>
#include <cassert>

namespace logic {

  unsigned LVariable::freshId = 0;

    std::string LVariable::toTPTP() const
    {
        return name + std::to_string(id);
    }
    
    std::string LVariable::toSMTLIB() const
    {
        return name + std::to_string(id);
    }
    
    std::string LVariable::prettyString() const
    {
        return name + std::to_string(id);
    }

    unsigned LVariable::occurrences(const Term& t) const
    {
        return (*this == t ? 1 : 0);
    }

    bool LVariable::operator ==(const Term& t) const
    {
        try
        {
            const LVariable& v = dynamic_cast<const LVariable&> (t);
            return v.id == id;
        }
        catch (std::bad_cast e)
        {
            return false;
        }
    }

    Term* LVariable::apply(const Substitution subst) const
    {
        assert(false); // target terms cannot be a subterm of this
        
        return nullptr;
    }
  
    std::string FuncTerm::toTPTP() const
    {
        if (subterms.size() == 0) {
            return head->toTPTP();
        } else {
            std::string str = head->toTPTP() + "(";
            for (unsigned i = 0; i < subterms.size(); i++) {
                str += subterms[i]->toTPTP();
                str += (i == subterms.size() - 1) ? ")" : ",";
            }
            return str;
        }
    }
    
    std::string FuncTerm::toSMTLIB() const
    {
        if (subterms.size() == 0)
        {
            return head->toSMTLIB();
        }
        else
        {
            std::string str = "(" + head->toSMTLIB() + " ";
            for (unsigned i = 0; i < subterms.size(); i++)
            {
                str += subterms[i]->toSMTLIB();
                str += (i == subterms.size() - 1) ? ")" : " ";
            }
            return str;
        }
    }
    
    std::string FuncTerm::prettyString() const
    {
        if (subterms.size() == 0)
        {
            return head->toSMTLIB();
        }
        else
        {
            std::string str = head->toSMTLIB() + "(";
            for (unsigned i = 0; i < subterms.size(); i++) {
                str += subterms[i]->toTPTP();
                str += (i == subterms.size() - 1) ? ")" : ",";
            }
            return str;
        }
    }

    unsigned FuncTerm::occurrences(const Term& t) const
    {
        if (*this == t)
        {
            return 1;
        }
        else
        {
            unsigned n = 0;
            for (TermPtr s: subterms)
            {
                n += s->occurrences(t);
            }
            return n;
        }
    }

    bool FuncTerm::operator ==(const Term& t) const
    {
        try
        {
            const FuncTerm& f = dynamic_cast<const FuncTerm&> (t);
            if (f.head != head)
            {
                return false;
            }
            for (unsigned i = 0; i < subterms.size(); i++)
            {
                if (*subterms[i] != *(f.subterms[i]))
                {
                    return false;
                }
            }
            return true;
        }
        catch (std::bad_cast e)
        {
            return false;
        }
    }

    Term* FuncTerm::apply(const Substitution subst) const
    {
        std::vector<TermPtr> newsubs(subterms.size());
        for (unsigned i=0; i < subterms.size(); i++) {
            newsubs[i] = Terms::apply(subterms[i], subst);
        }
        return new FuncTerm(head, newsubs);
    }

    std::string PredTerm::toTPTP() const {
        if (subterms.size() == 0) {
            return head->toTPTP();
        } else {
            std::string str = head->toTPTP() + "(";
            for (unsigned i = 0; i < subterms.size(); i++) {
                str += subterms[i]->toTPTP();
                str += (i == subterms.size() - 1) ? ")" : ",";
            }
            return str;
        }
    }
    
    std::string PredTerm::toSMTLIB() const
    {
        if (subterms.size() == 0)
        {
            return head->toSMTLIB();
        }
        else
        {
            std::string str = "(" + head->toSMTLIB() + " ";
            for (unsigned i = 0; i < subterms.size(); i++)
            {
                str += subterms[i]->toSMTLIB();
                str += (i == subterms.size() - 1) ? ")" : " ";
            }
            return str;
        }
    }
    
    // TODO: refactor symbols so that the _head->name gives back a pretty string
    // eg + instead of $add, >= instead of greaterEq
    // switch also to infix for the usual infix-predicates
    std::string PredTerm::prettyString() const
    {
        if (subterms.size() == 0)
        {
            return head->toSMTLIB();
        }
        else
        {
            std::string str = head->toSMTLIB() + "(";
            for (unsigned i = 0; i < subterms.size(); i++) {
                str += subterms[i]->toSMTLIB();
                str += (i == subterms.size() - 1) ? ")" : ",";
            }
            return str;
        }
    }

    unsigned PredTerm::occurrences(const Term& t) const
    {
        if (*this == t)
        {
            return 1;
        }
        else
        {
            unsigned n = 0;
            for (TermPtr s: subterms)
            {
                n += s->occurrences(t);
            }
            return n;
        }
    }

    bool PredTerm::operator ==(const Term& t) const
    {
        try
        {
            const PredTerm& p = dynamic_cast<const PredTerm&> (t);
            if (p.head != head)
            {
                return false;
            }
            for (unsigned i = 0; i < subterms.size(); i++)
            {
                if (*subterms[i] != *(p.subterms[i]))
                {
                    return false;
                }
            }
            return true;
        }
        catch (std::bad_cast e)
        {
            return false;
        }
    }

    Term* PredTerm::apply(const Substitution subst) const
    {
        std::vector<TermPtr> newsubs(subterms.size());
        for (unsigned i =0; i < subterms.size(); i++) {
            newsubs[i] = Terms::apply(subterms[i], subst);
        }
        return new PredTerm(head, newsubs);
    }

    // bool compareLVarPointers(const LVariable* p1, const LVariable* p2)
    // {
    //     return p1->id < p2->id;
    // }
    
    // bool eqLVarPointers(const LVariable* p1, const LVariable* p2) {
    //     return p1->id == p2->id;
    // }

//    std::vector<LVariablePtr> LVariable::freeVariables() const
//    {
//        return { std::make_shared<const LVariable>(this) };
//    }
//
//    std::vector<LVariablePtr> FuncTerm::freeVariables() const {
//        std::vector<LVariablePtr> freeVars;
//        // collect free vars from all subterms
//        for (const auto& subterm : subterms)
//        {
//            auto freeVarsSubterm = subterm->freeVariables();
//            freeVars.insert(freeVars.end(), freeVarsSubterm.begin(), freeVarsSubterm.end());
//        }
//        // sort and remove duplicates
//        std::sort(freeVars.begin(), freeVars.end(), compareLVarPointers);
//        freeVars.erase( unique(freeVars.begin(), freeVars.end(), eqLVarPointers), freeVars.end());
//
//        return freeVars;
//    }
//
//    std::vector<LVariablePtr> PredTerm::freeVariables() const
//    {
//        std::vector<LVariablePtr> freeVars;
//        // collect free vars from all subterms
//        for (const auto& subterm : subterms)
//        {
//            auto freeVarsSubterm = subterm->freeVariables();
//            freeVars.insert(freeVars.end(), freeVarsSubterm.begin(), freeVarsSubterm.end());
//        }
//        // sort and remove duplicates
//        std::sort(freeVars.begin(), freeVars.end(), compareLVarPointers);
//        freeVars.erase( unique(freeVars.begin(), freeVars.end(), eqLVarPointers), freeVars.end());
//
//        return freeVars;
//    }
    
# pragma mark - Terms
    
    LVariablePtr Terms::lVariable(const Sort* s)
    {
        return LVariablePtr(new LVariable(s));
    }
    
    LVariablePtr Terms::lVariable(const Sort* s, const std::string name)
    {
        return LVariablePtr(new LVariable(s, name));
    }
    
    FuncTermPtr Terms::funcTerm(const Symbol* head, std::initializer_list<TermPtr> subterms)
    {
        return FuncTermPtr(new FuncTerm(head, subterms));
    }
    
    PredTermPtr Terms::predTerm(const Symbol* head, std::initializer_list<TermPtr> subterms)
    {
        return PredTermPtr(new PredTerm(head, subterms));
    }

    TermPtr Terms::apply(const TermPtr t, const Substitution subst)
    {
        bool occ = false;
        for (auto& p: subst) {
            if (p.first == t || *p.first == *t)
            {
                return p.second;
            }
            // check occurrences (if one hasn't already been found)
            occ |= (t->occurrences(*p.first) > 0);
        }
        
        if (occ)
        {
            return TermPtr(t->apply(subst));
        }
        else
        {
            return t;
        }
    }
}

