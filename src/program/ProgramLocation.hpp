
#ifndef __ProgramLocation__
#define __ProgramLocation__

#include <vector>
#include "ProgramRule"
#include "Expression"

namespace program
{
    class ProgramLocation
    {
        std::string name; // name of the location
        std::vector<LocationExpression> variables; // variables of the location, cf. Single Static Assignment Form
        
        std::vector<ProgramRule> rules; // the incoming edges in the transition relation
        
        std::vector<FExpression> assertions; // assertions at the location, which we want to check
    };
}


#endif
