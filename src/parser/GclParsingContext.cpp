#include "GclParsingContext.hpp"

#include <fstream>
#include <ostream>

#include "Output.hpp"

namespace parser {
    using namespace program;
    
    bool GclParsingContext::available(const std::string& name) {
        return _variables.find(name) == _variables.end();
    }
    
    PVariable* GclParsingContext::declareVariable(const std::string& name)
    {
        PVariable *v = new PVariable(name, _typeDeclCtx);
        _variables[name] = v;
        return v;
    }
    
    Variable* GclParsingContext::getVariable(const std::string& name)
    {
        for (auto it1 = _localScopes.begin(); it1 != _localScopes.end(); ++it1) {
            if ((*it1)->name() == name)
                return *it1;
        }
        auto it2 = _variables.find(name);
        if (it2 != _variables.end()) {
            return (*it2).second;
        } else {
            return nullptr;
        }
    }
    
    QVariable* GclParsingContext::openLocalScope(const std::string& name, Type t)
    {
        // TODO prevent variable capture (disallow same name)
        QVariable *v = new QVariable(name, t);
        _localScopes.push_back(v);
        return v;
    }
    
    void GclParsingContext::closeLocalScope()
    {
        _localScopes.pop_back();
    }
    
    void GclParsingContext::printInfo(GuardedCommandCollection &c) {
        std::ostream& ostr = util::Output::stream();
        
        ostr << util::Output::comment
        << "-------------------------------------------------\n"
        << " This file was generated automatically by INVGEN \n"
        << "-------------------------------------------------\n"
        << '\n'
        << "------------------ Parsed loop ------------------\n"
        << c
        << "-------------------------------------------------\n"
        << '\n'
        << "--------------- Table of symbols ----------------\n";
        for (auto it = _variables.begin(); it != _variables.end(); ++it) {
            ostr << *(*it).second << "\n";
        }
        ostr << "-------------------------------------------------\n"
        << util::Output::nocomment
        << std::endl;
    }
}

