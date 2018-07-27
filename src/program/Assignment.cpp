#include "Assignment.hpp"

#include <cassert>

#include "Options.hpp"
#include "Term.hpp"
#include "Theory.hpp"

using namespace logic;

namespace program
{
    logic::FormulaPtr Assignment::weakestPrecondition(logic::FormulaPtr f) const
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
}
