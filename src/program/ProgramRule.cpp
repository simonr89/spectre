#include "ProgramRule.hpp"
#include "ProgramLocation.hpp"

namespace program
{
    const ProgramLocation& ProgramRule::getLocation() const
    {
        return location;
    }
    
}
