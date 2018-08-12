/**
 * @file Variable.cpp
 *
 */

#include "Variable.hpp"

#include <cassert>
#include "Theory.hpp"
#include "Options.hpp"

namespace program {
    
    using namespace logic;
    
    /** the main constructors */
    PVariable::PVariable(const std::string& name, Type ty) :
        Variable(name, ty),
        _updated(false)
    {
        if (isArrayType(ty)) {
            if (util::Configuration::instance().arrayTheory().getValue())
            {
                // representation of arrays using array axioms
                _symbol = Signature::fetchOrDeclare(name + "_nonext",
                                                    {},
                                                    logic::Sorts::intArraySort());
                _extendedSymbol = Signature::fetchOrDeclare(name,
                                                            { logic::Sorts::timeSort() },
                                                            logic::Sorts::intArraySort(),
                                                            false,
                                                            true);
            } else {
                // representation of arrays as functions
                _symbol = Signature::fetchOrDeclare(name + "_nonext",
                                                    { logic::Sorts::intSort() },
                                                    toSort(ty));
                _extendedSymbol = Signature::fetchOrDeclare(name,
                                                            { logic::Sorts::timeSort(), logic::Sorts::intSort() },
                                                            toSort(ty),
                                                            false,
                                                            true);
            }
        } else {
            _symbol = Signature::fetchOrDeclare(name + "_nonext",
                                                {},
                                                toSort(ty));
            _extendedSymbol = Signature::fetchOrDeclare(name,
                                                        { logic::Sorts::timeSort() },
                                                        toSort(ty),
                                                        false,
                                                        true);
        }
    }
    
    
    
    
    TermPtr PVariable::toTerm(TermPtr index) const
    {
        assert(util::Configuration::instance().arrayTheory().getValue()
               || !isArrayType(type));

        if (index && _updated)
        {
            // extended symbol
            if (type == Type::TY_BOOLEAN)
            {
                return logic::Terms::predTerm(_extendedSymbol, { index });
            }
            else
            {
                return logic::Terms::funcTerm(_extendedSymbol, { index });
            }
        }
        else
        {
            if (type == Type::TY_BOOLEAN)
            {
                return logic::Terms::predTerm(_symbol, {});
            }
            else
            {
                return logic::Terms::funcTerm(_symbol, {});
            }
        }
    }
    
    TermPtr PVariable::toTerm(TermPtr index, TermPtr arrayIndex) const
    {
        assert(isArrayType(type));
        
        if (util::Configuration::instance().arrayTheory().getValue())
        {
            // representation using array axioms
            TermPtr array;
            
            if (index && _updated)
            {
                array = logic::Terms::funcTerm(_extendedSymbol, { index });
            }
            else
            {
                array = logic::Terms::funcTerm(_symbol, {});
            }
            assert(array);
            
            if (type == Type::TY_BOOLEAN)
            {
                return logic::Terms::predTerm(Theory::getSymbol(InterpretedSymbol::ARRAY_SELECT), { array, arrayIndex });
            }
            else
            {
                return logic::Terms::funcTerm(Theory::getSymbol(InterpretedSymbol::ARRAY_SELECT), { array, arrayIndex });
            }
        }
        else
        {
            // representation of arrays as function
            if (index && _updated)
            {
                if (type == Type::TY_BOOLEAN)
                {
                    return logic::Terms::predTerm(_extendedSymbol, { index, arrayIndex });
                }
                else
                {
                    return logic::Terms::funcTerm(_extendedSymbol, { index, arrayIndex });
                }
            }
            else
            {
                if (type == Type::TY_BOOLEAN)
                {
                    return logic::Terms::predTerm(_symbol, { arrayIndex });
                }
                else
                {
                    return logic::Terms::funcTerm(_symbol, { arrayIndex });
                }
            }
        }
    }
    
    std::string PVariable::toString() const
    {
        return name; // TODO: also print type
    }
    
    std::ostream& operator<<(std::ostream& ostr, const PVariable& v)
    {
        ostr << v.name << " : " << v.type;
        return ostr;
    }
    
    std::ostream& operator<<(std::ostream& ostr, const QVariable& v)
    {
        ostr << v.name << " : " << v.type;
        return ostr;
    }
}

