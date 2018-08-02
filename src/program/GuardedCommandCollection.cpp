#include "GuardedCommandCollection.hpp"

#include <cassert>

#include "Options.hpp"
#include "Theory.hpp"

using namespace logic;

namespace program
{

    FormulaPtr GuardedCommandCollection::weakestPrecondition(const FormulaPtr f, const TermPtr i) const
    {
        std::vector<FormulaPtr> conj;
        for (GuardedCommand* c: commands)
        {
            conj.push_back(c->weakestPrecondition(f, variables, i));
        }
        return Formulas::conjunctionFormula(conj);
    }

    FormulaPtr GuardedCommand::weakestPrecondition(const FormulaPtr f, const std::vector<PVariable*> &variables, const TermPtr i) const
    {
        Substitution subst;
        
        for (Assignment* a: assignments)
        {
            if (!a->isArrayAssignment()
                || util::Configuration::instance().arrayTheory().getValue())
            {
                // for array assignment with functional representation
                // of arrays, we have a formula rather than a subst
                subst.push_back(a->weakestPreconditionSubst(i));
            }
        }
        
        if (!util::Configuration::instance().arrayTheory().getValue())
        {
            std::vector<FormulaPtr> conj;
            // with the functional representation of arrays, we must
            // add formulas to define the new function
            for (PVariable *v : variables)
            {
                if (isArrayType(v->type))
                {
                    conj.push_back(arrayAssignment(*v, i));
                }
            }
            conj.push_back(Formulas::apply(f, subst));
            return Formulas::implicationFormula(guard->toFormula(i),
                                                Formulas::conjunctionFormula(conj));
        }
        else
        {
            return Formulas::implicationFormula(guard->toFormula(i), Formulas::apply(f, subst));
        }
    }

    FormulaPtr GuardedCommand::arrayAssignment(const PVariable &v, const TermPtr i) const
    {
        assert(isArrayType(v.type));
        assert(i); // currently only support if generating the
                   // relativised WP. TODO: extend support

        TermPtr iPlusOne = Theory::timeSucc(i);
        LVariablePtr p = Terms::lVariable(Sorts::intSort(), "P");
        std::vector<FormulaPtr> conj1;
        std::vector<FormulaPtr> conj2;
        for (Assignment *a : assignments)
        {
            if (a->hasLhs(v))
            {
                conj1.push_back(Formulas::equalityFormula(false,
                                                          p,
                                                          a->lhs->child(0)->toTerm(i)));
                conj2.push_back(Formulas::equalityFormula(true,
                                                          a->lhs->varInfo()->toTerm(iPlusOne,
                                                                                    a->lhs->child(0)->toTerm(i)),
                                                          a->rhs->toTerm(i)));
            }
        }
        
        FormulaPtr eq = Formulas::equalityFormula(true,
                                                  v.toTerm(iPlusOne, p),
                                                  v.toTerm(i, p));
        
        FormulaPtr f = Formulas::implicationFormula(Formulas::conjunctionFormula(conj1), eq);
        conj2.push_back(Formulas::universalFormula({ p }, f));
        
        return Formulas::conjunctionFormula(conj2);
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

    std::pair<TermPtr, TermPtr> Assignment::weakestPreconditionSubst(const TermPtr i) const
    {
        assert(util::Configuration::instance().arrayTheory().getValue()
               || !isArrayAssignment());

        TermPtr asg;
        
        if (isArrayAssignment())
        {
            asg = Terms::funcTerm(Theory::getSymbol(InterpretedSymbol::ARRAY_STORE),
                                  { lhs->varInfo()->toTerm(i),
                                    lhs->child(0)->toTerm(i),
                                    rhs->toTerm(i) });
        }
        else
        {
            asg = rhs->toTerm(i);
        }
        return std::make_pair(lhs->varInfo()->toTerm(i),
                              asg);
    
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

