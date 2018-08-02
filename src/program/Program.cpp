#include "Program.hpp"

namespace program
{
    std::ostream& operator<<(std::ostream& ostr, const Program& p)
    {
        ostr << "Vars:\n";
        for (const auto& variable : p.loop->variables)
        {
            ostr << *variable << "\n";
        }
        ostr << "\nRequires:\n";
        for (const auto& precondition : p.preconditions)
        {
            ostr << *precondition << "\n";
        }
        ostr << "\nEnsures:\n";
        for (const auto& postcondition : p.postconditions)
        {
            ostr << *postcondition << "\n";
        }
        ostr << "\n" << *p.loop;
        return ostr;
    }
}
