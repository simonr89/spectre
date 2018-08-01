#include "GuardedCommandCollection.hpp"

#include <cassert>

#include "Options.hpp"
#include "Term.hpp"
#include "Theory.hpp"

using namespace logic;

namespace program
{

    FormulaPtr GuardedCommandCollection::weakestPrecondition(FormulaPtr f) const
    {
        std::vector<FormulaPtr> conj;
        for (GuardedCommand* c: commands)
        {
            conj.push_back(c->weakestPrecondition(f));
        }
        return Formulas::conjunctionFormula(conj);
    }

    FormulaPtr GuardedCommand::weakestPrecondition(FormulaPtr f) const
    {
        FormulaPtr g = f;
        // TODO important: substitution must be parallel
        for (Assignment* a: assignments)
        {
            // TODO could be optimized to avoid copying the formulas so many times
            g = a->weakestPrecondition(g);
        }
        return Formulas::implicationFormula(guard->toFormula(nullptr), g);
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

    FormulaPtr Assignment::weakestPrecondition(FormulaPtr f) const
    {
        if (lhs->isArrayLocation())
        {
            if (util::Configuration::instance().arrayTheory().getValue())
            {
                FuncTermPtr store = Terms::funcTerm(Theory::getSymbol(InterpretedSymbol::ARRAY_STORE),
                                                    { lhs->varInfo()->toTerm(nullptr),
                                                      lhs->child(0)->toTerm(nullptr),
                                                      rhs->toTerm(nullptr) });
                return Formulas::replace(f,
                                         lhs->varInfo()->toTerm(nullptr),
                                         store);
            }
            else
            {
                // TODO weakest precondition of array assignment with
                // functional representation of array requires
                // introducing a new symbol
                assert(0);
            }
        }
        else
        {
            return Formulas::replace(f,
                                     lhs->varInfo()->toTerm(nullptr),
                                     rhs->toTerm(nullptr));
        }
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

