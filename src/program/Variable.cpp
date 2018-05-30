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
    PVariable::PVariable(const std::string& name, Type ty) : Variable(name, ty)
    {
        if (isArrayType(ty)) {
            if (util::Configuration::instance().arrayTheory().getValue()) {
                // representation of arrays using array axioms
                _symbol = new logic::Symbol(name + "_nonext", {}, logic::Sorts::intArraySort());
                _extendedSymbol = new logic::Symbol(name, { logic::Sorts::intSort() }, logic::Sorts::intArraySort(), false, true);
            } else {
                // representation of arrays as functions
                _symbol = new logic::Symbol(name + "_nonext", { logic::Sorts::intSort() }, toSort(ty));
                _extendedSymbol = new logic::Symbol(name, { logic::Sorts::intSort(), logic::Sorts::intSort() }, toSort(ty), false, true);
            }
        } else {
            _symbol = new logic::Symbol(name + "_nonext", {}, toSort(ty));
            _extendedSymbol = new logic::Symbol(name, { logic::Sorts::intSort() }, toSort(ty), false, true);
        }
    }
    
    
    
    
    Term* PVariable::toTerm(const Term* index) const
    {
        assert(!isArrayType(_type));

        if (index)
        {
            // extended symbol
            if (_type == Type::TY_BOOLEAN)
            {
                return new PredTerm(_extendedSymbol, { index });
            }
            else
            {
                return new FuncTerm(_extendedSymbol, { index });
            }
        }
        else
        {
            if (_type == Type::TY_BOOLEAN)
            {
                return new PredTerm(_symbol, {});
            }
            else
            {
                return new FuncTerm(_symbol, {});
            }
        }
    }
    
    Term* PVariable::toTerm(const Term* index, const Term* arrayIndex) const
    {
        assert(isArrayType(_type));
        
        if (util::Configuration::instance().arrayTheory().getValue())
        {
            // representation using array axioms
            Term *array;
            
            if (index)
            {
                array = new FuncTerm(_extendedSymbol, { index });
            }
            else
            {
                array = new FuncTerm(_symbol, {});
            }
            assert(array);
            
            if (_type == Type::TY_BOOLEAN)
            {
                return new PredTerm(Theory::getSymbol(InterpretedSymbol::ARRAY_SELECT), { array, arrayIndex });
            }
            else
            {
                return new FuncTerm(Theory::getSymbol(InterpretedSymbol::ARRAY_SELECT), { array, arrayIndex });
            }
        }
        else
        {
            // representation of arrays as function
            if (index)
            {
                if (_type == Type::TY_BOOLEAN)
                {
                    return new PredTerm(_extendedSymbol, { index, arrayIndex });
                }
                else
                {
                    return new FuncTerm(_extendedSymbol, { index, arrayIndex });
                }
            }
            else
            {
                if (_type == Type::TY_BOOLEAN)
                {
                    return new PredTerm(_symbol, { arrayIndex });
                }
                else
                {
                    return new FuncTerm(_symbol, { arrayIndex });
                }
            }
        }
    }
    
    std::string PVariable::toString() const
    {
        return _name; // TODO: also print type
    }
    
    std::ostream& operator<<(std::ostream& ostr, const PVariable& v)
    {
        ostr << v._name << " : " << v._type;
        return ostr;
    }
    
    std::ostream& operator<<(std::ostream& ostr, const QVariable& v)
    {
        ostr << "X" << v._id << " : " << v._type;
        return ostr;
    }
}

