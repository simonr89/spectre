

#ifndef __ProgramRule__
#define __ProgramRule__

#include <vector>
#include <memory>

#include "Assignment.hpp"
#include "Formula.hpp"

namespace program
{
    class ProgramLocation;

    class ProgramRule
    {
        ProgramLocation& location; // points to the source-location of this rule.

        std::vector<std::unique_ptr<BooleanExpression>> guards;
        std::vector<std::unique_ptr<Assignment>> assignments;
        
    public:
        ProgramRule(ProgramLocation& location, std::vector<std::unique_ptr<BooleanExpression>> guards, std::vector<std::unique_ptr<Assignment>> assignments) : location(location), guards(std::move(guards)), assignments(std::move(assignments)){}

        const ProgramLocation& getLocation() const;
        const std::vector<std::unique_ptr<BooleanExpression>>& getGuards() const {return guards;}
        const std::vector<std::unique_ptr<Assignment>>& getAssignments() const {return assignments;}
    };
}

#endif
