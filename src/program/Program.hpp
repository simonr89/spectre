


#ifndef __Program__
#define __Program__

#include <vector>
#include "ProgramLocation.hpp"

namespace program
{
    class Program
    {
        std::vector<ProgramLocation> locations;

    public:
        Program(std::vector<ProgramLocation> locations) : locations(std::move(locations)){}

        const std::vector<ProgramLocation>& getLocations() const {return locations;}
    };

    std::ostream& operator<<(std::ostream& os, const Program& p)
    {
        for (const auto& pl : p.getLocations())
        {
            os << pl << "\n";
        }
        return os;
    }
}

#endif
