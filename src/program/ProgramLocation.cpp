#include "ProgramLocation.hpp"
#include "ProgramRule.hpp"

namespace program
{
    ProgramLocation::ProgramLocation(logic::PredicateFormula name, std::vector<std::unique_ptr<LocationExpression>> variables, std::vector<std::unique_ptr<ProgramRule>> rules, std::vector<std::unique_ptr<BooleanExpression>> assertions) : name(std::move(name)), variables(std::move(variables)), rules(std::move(rules)), assertions(std::move(assertions)){}

    ProgramLocation::~ProgramLocation(){} // needed so that we can use a unique_ptr for the incomplete type ProgramRule, see https://stackoverflow.com/questions/34072862/why-is-error-invalid-application-of-sizeof-to-an-incomplete-type-using-uniqu
    
    const std::vector<std::unique_ptr<ProgramRule>>& ProgramLocation::getRules() const
    {
        return rules;
    }
    
    std::ostream& operator<<(std::ostream& os, const ProgramLocation& pl)
    {
        for (const auto& r : pl.getRules())
        {
            // print source location
            os << "( " << r->getLocation().getName() << "(";
            bool firstVar = true;
            for (const auto& var : r->getLocation().getVariables())
            {
                if (firstVar)
                {
                    firstVar = false;
                }
                else
                {
                    os << ",";
                }
                os << *var;
            }
            os << ")";
            
            // print guards
            bool firstGuard = false;
            for (const auto& guard  : r->getGuards())
            {
                if (firstGuard)
                {
                    firstGuard = false;
                }
                else
                {
                    os << " and ";
                }
                os << *guard;
            }
            
            if (!r->getGuards().empty() && !r->getAssignments().empty())
            {
                os << " and ";
            }
            // print assignments
            bool firstAssignment = false;
            for (const auto& assignment  : r->getAssignments())
            {
                if (firstAssignment)
                {
                    firstAssignment = false;
                }
                else
                {
                    os << " and ";
                }
                os << *assignment;
            }
            os << ") => ";
            
            os << pl.getName() << "(";
            firstVar = true;
            for (const auto& var : r->getLocation().getVariables())
            {
                if (firstVar)
                {
                    firstVar = false;
                }
                else
                {
                    os << ",";
                }
                os << *var;
            }
            os << ")\n";
        }
        return os;
    }
}
