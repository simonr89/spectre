

#ifndef __ProgramRule__
#define __ProgramRule__

#include <vector>
#include <memory>

#include "Assignment.hpp"
#include "Formula.hpp"

namespace program
{
    class ProgramRule
    {
    public:
        ProgramRule(std::vector<std::unique_ptr<FExpression>> guards, std::vector<std::unique_ptr<Assignment>> assignments, FExpression head);
    private:
        
        std::vector<std::unique_ptr<FExpression>> guards;
        std::vector<std::unique_ptr<Assignment>> assignments;
        logic::PredicateFormula location;
    };
}

#endif
