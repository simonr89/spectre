
#ifndef __ProgramLocation__
#define __ProgramLocation__

#include <vector>
#include <iostream>
#include <memory>

#include "Expression.hpp"

namespace program
{
    class ProgramRule;
    
    class ProgramLocation
    {
        logic::PredicateFormula name;                                   // name of the location
        std::vector<std::unique_ptr<LocationExpression>> variables;     // variables of the location, cf. Single Static Assignment Form
        std::vector<std::unique_ptr<ProgramRule>> rules;                // the incoming edges in the transition relation
        std::vector<std::unique_ptr<BooleanExpression>> assertions;     // assertions at the location, which we want to check
        
    public:
        ProgramLocation(logic::PredicateFormula name, std::vector<std::unique_ptr<LocationExpression>> variables, std::vector<std::unique_ptr<ProgramRule>> rules, std::vector<std::unique_ptr<BooleanExpression>> assertions);
        ~ProgramLocation(); 

        const logic::PredicateFormula& getName() const {return name;}
        const std::vector<std::unique_ptr<LocationExpression>>& getVariables() const {return variables;}
        const std::vector<std::unique_ptr<ProgramRule>>& getRules() const;
        const std::vector<std::unique_ptr<BooleanExpression>>& getAssertions() const {return assertions;}
    };
    
    std::ostream& operator<<(std::ostream& os, const ProgramLocation& pl);
}


#endif
