#include "GclParsingContext.hpp"

#include <fstream>
#include <ostream>

#include "Output.hpp"

namespace parser {
    using namespace program;
    
    bool GclParsingContext::available(const std::string& name) {
        return variables.find(name) == variables.end();
    }
    
    PVariable* GclParsingContext::declareVariable(const std::string& name)
    {
        PVariable *v = new PVariable(name, _typeDeclCtx);
        variables[name] = v;
        return v;
    }
    
    Variable* GclParsingContext::getVariable(const std::string& name)
    {
        for (auto it1 = _localScopes.begin(); it1 != _localScopes.end(); ++it1) {
            if ((*it1)->name == name)
                return *it1;
        }
        auto it2 = variables.find(name);
        if (it2 != variables.end()) {
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
    
    bool GclParsingContext::containsAssignment(std::pair<FExpression*, std::vector<Assignment*>> assignmentList, Assignment* assignment)
    {
        
        PVariable *lhs = assignment->lhs->varInfo();
        for (const auto a : assignmentList.second)
        {
            if (a->hasLhs(*lhs))
            {
                return true;
            }
        }
        return false;
    }
    
    void GclParsingContext::addAdditionalGuards(std::pair<FExpression*, std::vector<Assignment*>> pairGuardsAssignments, Assignment* assignment)
    {
        PVariable *lhs = assignment->lhs->varInfo();
        assert(isArrayType(lhs->type));
        
        for (const auto a : pairGuardsAssignments.second)
        {
            if (a->hasLhs(*lhs))
            {
                pairGuardsAssignments.first = BooleanExpression::mkAnd(pairGuardsAssignments.first,BooleanExpression::mkNeq(a->lhs->child(0), a->lhs->child(0)));
            }
        }
    }
    
    void GclParsingContext::printInfo(GuardedCommandCollection &c) {
        std::ostream& ostr = util::Output::stream();
        
        ostr << util::Output::comment
        << "-------------------------------------------------\n"
        << " This file was generated automatically by SPECTRE\n"
        << "-------------------------------------------------\n"
        << '\n'
        << "------------------ Parsed loop ------------------\n"
        << c
        << "-------------------------------------------------\n"
        << '\n'
        << "--------------- Table of symbols ----------------\n";
        for (auto it = variables.begin(); it != variables.end(); ++it) {
            ostr << *(*it).second << "\n";
        }
        ostr << "-------------------------------------------------\n"
        << util::Output::nocomment
        << std::endl;
    }
    
    // provide a wrapper around the parsing code, in order to hide
    // both the leaks and the non-constness of the legacy code
    // TODO: refactor this at some point
    std::unique_ptr<Program> GclParsingContext::generateProgram()
    {
        std::vector<const PVariable*> vars;
        for (const auto& pairNameVar : variables)
        {
            vars.push_back(pairNameVar.second);
        }
        std::vector<const FExpression*> constPreconditions;
        for (const auto& element : preconditions)
        {
            constPreconditions.push_back(element);
        }
        std::vector<const FExpression*> constPostconditions;
        for (const auto& element : postconditions)
        {
            constPostconditions.push_back(element);
        }

        return std::unique_ptr<Program>(new Program(std::move(program), std::move(constPreconditions), std::move(constPostconditions), std::move(vars)));
    }
}

