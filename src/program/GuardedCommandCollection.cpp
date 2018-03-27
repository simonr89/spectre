#include "GuardedCommandCollection.hpp"

namespace program
{
    Assignment *GuardedCommand::findAssignment(const PVariable &v) const
    {
        for (auto it = assignments.begin(); it != assignments.end(); ++it) {
            if ((*it)->hasLhs(v))
                return *it;
        }
        return nullptr;
    }
    
    std::ostream& operator<<(std::ostream& ostr, const Assignment &a)
    {
        ostr << *(a.lhs) << " = " << *(a.rhs) << ";";
        return ostr;
    }

    std::ostream& operator<<(std::ostream& ostr, const GuardedCommand &c)
    {
        ostr << ":: " << *(c.guard) << " ->";
        for (const auto& assignment : c.assignments)
        {
            ostr << " " << *assignment;
        }
        return ostr;
    }
    
    std::ostream& operator<<(std::ostream& ostr, const GuardedCommandCollection &c)
    {
        ostr << "while " << *c.loopCondition << " do\n";
        for (const auto& command : c.commands)
        {
            ostr << *command << " \n";
        }
        ostr << "od\n";
        return ostr;
    }
    
    std::ostream& operator<<(std::ostream& ostr, const std::vector<GuardedCommand*>& c)
    {
        ostr << "not implemented";
        return ostr;
    }
    
    std::ostream& operator<<(std::ostream& ostr, const std::pair<FExpression*,std::vector<Assignment*>>& c)
    {
        ostr << "not implemented";
        return ostr;
    }
    
}

