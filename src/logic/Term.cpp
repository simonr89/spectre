#include "Term.hpp"

namespace logic {

  unsigned LVariable::freshId = 0;

  std::string LVariable::toTPTP() const {
    return name();
  }
  
  std::string FuncTerm::toTPTP() const {
    if (_subterms.size() == 0) {
      return _head->name();
    } else {
      std::string str = _head->name() + "(";
      for (unsigned i = 0; i < _subterms.size(); i++) {
        str += _subterms[i]->toTPTP();
        str += (i == _subterms.size() - 1) ? ")" : ",";
      }
      return str;
    }
  }

  std::string PredTerm::toTPTP() const {
    if (_subterms.size() == 0) {
      return _head->name();
    } else {
      std::string str = _head->name() + "(";
      for (unsigned i = 0; i < _subterms.size(); i++) {
        str += _subterms[i]->toTPTP();
        str += (i == _subterms.size() - 1) ? ")" : ",";
      }
      return str;
    }
  }
    
    bool compareLVarPointers(LVariable* p1, LVariable* p2) {
        return p1->id() < p2->id();
    }
    
    bool eqLVarPointers(LVariable* p1, LVariable* p2) {
        return p1->id() == p2->id();
    }

    std::vector<LVariable*> LVariable::freeVariables() const {
        LVariable *v = new LVariable(*this);
        return { v };
    }

    std::vector<LVariable*> FuncTerm::freeVariables() const {
        std::vector<LVariable*> freeVars;
        // collect free vars from all subterms
        for (const auto& subterm : _subterms)
        {
            auto freeVarsSubterm = subterm->freeVariables();
            freeVars.insert(freeVars.end(), freeVarsSubterm.begin(), freeVarsSubterm.end());
        }
        // sort and remove duplicates
        std::sort(freeVars.begin(), freeVars.end(), compareLVarPointers);
        freeVars.erase( unique(freeVars.begin(), freeVars.end(), compareLVarPointers), freeVars.end());
        
        return freeVars;
    }
    
    std::vector<LVariable*> PredTerm::freeVariables() const {
        std::vector<LVariable*> freeVars;
        for (const auto& subterm : _subterms)
        {
            auto freeVarsSubterm = subterm->freeVariables();
            freeVars.insert(freeVars.end(), freeVarsSubterm.begin(), freeVarsSubterm.end());
        }
        return freeVars;
    }
}

