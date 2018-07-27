#include "GuardedCommandCollection.hpp"

namespace program
{

    logic::FormulaPtr GuardedCommandCollection::weakestPrecondition(logic::FormulaPtr f) const
    {
        std::vector<logic::FormulaPtr> conj;
        for (GuardedCommand* c: commands)
        {
            conj.push_back(c->weakestPrecondition(f));
        }
        return logic::Formulas::conjunctionFormula(conj);
    }

    logic::FormulaPtr GuardedCommand::weakestPrecondition(logic::FormulaPtr f) const
    {
        logic::FormulaPtr g = f;
        // since the semantics are parallel assignment and the guard
        // ensures that no location is assigned twice, the order of
        // substitutions doesn't matter
        for (Assignment* a: assignments)
        {
            // TODO could be optimized to avoid copying the formulas so many times
            g = a->weakestPrecondition(g);
        }
        return logic::Formulas::implicationFormula(guard->toFormula(nullptr), g);
    }
    
    Assignment* GuardedCommand::findAssignment(const PVariable &v) const
    {
        for (Assignment* a : assignments)
        {
            if (a->hasLhs(v))
            {
                return a;
            }
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

