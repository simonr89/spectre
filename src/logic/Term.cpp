#include <algorithm>

#include "Term.hpp"

namespace logic {

  unsigned LVariable::freshId = 0;

    std::string LVariable::toTPTP() const
    {
        return name;
    }
    
    std::string LVariable::toSMTLIB() const
    {
        return name;
    }
    
    std::string LVariable::prettyString() const
    {
        return name;
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

    bool compareLVarPointers(const LVariable* p1, const LVariable* p2)
    {
        return p1->id < p2->id;
    }
    
    bool eqLVarPointers(const LVariable* p1, const LVariable* p2) {
        return p1->id == p2->id;
    }

//    std::vector<std::shared_ptr<const LVariable>> LVariable::freeVariables() const
//    {
//        return { std::make_shared<const LVariable>(this) };
//    }
//
//    std::vector<std::shared_ptr<const LVariable>> FuncTerm::freeVariables() const {
//        std::vector<std::shared_ptr<const LVariable>> freeVars;
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
//    std::vector<std::shared_ptr<const LVariable>> PredTerm::freeVariables() const
//    {
//        std::vector<std::shared_ptr<const LVariable>> freeVars;
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
    
    std::shared_ptr<const LVariable> Terms::lVariable(const Sort* s)
    {
        return std::shared_ptr<const LVariable>(new LVariable(s));
    }
    
    std::shared_ptr<const LVariable> Terms::lVariable(const Sort* s, const std::string name)
    {
        return std::shared_ptr<const LVariable>(new LVariable(s, name));
    }
    std::shared_ptr<const FuncTerm> Terms::funcTerm(const Symbol* head, std::initializer_list<std::shared_ptr<const Term>> subterms)
    {
        return std::shared_ptr<const FuncTerm>(new FuncTerm(head, subterms));
    }
    std::shared_ptr<const PredTerm> Terms::predTerm(const Symbol* head, std::initializer_list<std::shared_ptr<const Term>> subterms)
    {
        return std::shared_ptr<const PredTerm>(new PredTerm(head, subterms));
    }
}

