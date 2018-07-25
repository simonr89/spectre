#include "Signature.hpp"

#include <algorithm>

namespace logic {
    
#pragma mark - Symbol

    std::string Symbol::declareSymbolTPTP() const
    {
        if (interpreted)
        {
            return ""; // don't  need to declare symbols, which are already known to TPTP-solvers.
        }
        
        std::string s = "tff(symb_" + name + ", type, " + name + " : ";
        if (argSorts.size() == 0)
        {
            s += rngSort->toTPTP() + ").\n";
        }
        else if (argSorts.size() == 1)
        {
            s += argSorts[0]->toTPTP() + " > " + rngSort->toTPTP() + ").\n";
        }
        else
        {
            s += "(";
            for (unsigned i = 0; i < argSorts.size() - 1; i++)
            {
                s += argSorts[i]->toTPTP() + " * ";
            }
            s += argSorts[argSorts.size() - 1]->toTPTP() + ") > " + rngSort->toTPTP() + ").\n";
        }
        return s;
    }
    
    std::string Symbol::toTPTP() const
    {
        if (name == "time_zero" || name == "time_succ" || name == "time_pre" || name == "time_sub")
        {
            assert(false); // term algebras are not supported with TPTP-syntax
            return "";
        }

        if (name == "int_plus")
        {
            return "$sum";
        }
        else if (name == "int_minus")
        {
            return "$difference";
        }
        else if (name == "int_multiply")
        {
            return "$product";
        }
        else if (name == "int_quotient_e")
        {
            return "$quotient_e";
        }
        else if (name == "int_unary_minus")
        {
            return "$uminus";
        }
        else if (name == "int_greater")
        {
            return "$greater";
        }
        else if (name == "int_greater_eq")
        {
            return "$greatereq";
        }
        else if (name == "int_less")
        {
            return "$less";
        }
        else if (name == "int_less_eq")
        {
            return "$lesseq";
        }
        else if (name == "array_select")
        {
            return "select";
        }
        else if (name == "array_store")
        {
            return "store";
        }
        else if (name == "bool_true")
        {
            return "$true";
        }
        else if (name == "bool_false")
        {
            return "$false";
        }
        // test whether integer constant
        else if (std::all_of(name.begin(), name.end(), ::isdigit) ||
                 (name[0]=='-' && std::all_of(name.begin()+1, name.end(), ::isdigit)))
        {
            return name;
        }
        else
        {
            assert(!interpreted);
            return name;
        }
    }

    std::string Symbol::declareSymbolSMTLIB() const
    {
        if (interpreted)
        {
            return ""; // don't  need to declare symbols, which are already known to TPTP-solvers.
        }
        if (argSorts.size() == 0)
        {
            return "(declare-const " + toSMTLIB() + " " + rngSort->toSMTLIB() + ")\n";
        }
        else
        {
            std::string res = "(declare-fun " + toSMTLIB() + " (";
            for (int i=0; i < argSorts.size(); ++i)
            {
                res += argSorts[i]->toSMTLIB() + (i+1 == argSorts.size() ? "" : " ");
            }
            res += ") " + rngSort->toSMTLIB() + ")\n";
            return res;
        }
    }
    
    std::string Symbol::toSMTLIB() const
    {
        if (name == "int_plus")
        {
            return "+";
        }
        else if (name == "int_minus")
        {
            return "-";
        }
        else if (name == "int_multiply")
        {
            return "*";
        }
        else if (name == "int_quotient_e")
        {
            return "div";
        }
        else if (name == "int_unary_minus")
        {
            return "-";
        }
        else if (name == "int_greater")
        {
            return ">";
        }
        else if (name == "int_greater_eq")
        {
            return ">=";
        }
        else if (name == "int_less")
        {
            return "<";
        }
        else if (name == "int_less_eq")
        {
            return "<=";
        }
        else if (name == "array_select")
        {
            return "array_select";
        }
        else if (name == "array_store")
        {
            return "array_store";
        }
        else if (name == "bool_true")
        {
            return "true";
        }
        else if (name == "bool_false")
        {
            return "false";
        }
        else if (name == "time_zero")
        {
            return "zero";
        }
        else if (name == "time_succ")
        {
            return "s";
        }
        else if (name == "time_pre")
        {
            return "p";
        }
        else if (name == "time_sub")
        {
            return "sub";
        }
        // if non-negative integer constant
        else if (std::all_of(name.begin(), name.end(), ::isdigit))
        {
            return name;
        }
        // if negative integer constant
        else if (name[0]=='-' && std::all_of(name.begin()+1, name.end(), ::isdigit))
        {
            // need to encode negative integer as unary minus of positive integer
            return  "(- " + name.substr(1,name.size()-1) + ")";
        }
        else
        {
            assert(!interpreted);
            return name;
        }
    }
    
    std::string Symbol::declareSymbolColorTPTP() const
    {
        assert(!interpreted);
        
        std::string s = "vampire(symbol, ";
        s += "function, "; // predicate or function
        s += name + ", ";
        s += std::to_string(argSorts.size()) + ", "; // arity
        s += colored ? "left" : "skip";
        s += ").\n";
        return s;
    }
    
    std::string Symbol::declareSymbolColorSMTLIB() const
    {
        assert(!interpreted);
        
        return colored ? "(color-symbol " + toSMTLIB() + " :left)\n" : "";
    }
    
#pragma mark - Signature
    
    std::unordered_set<std::unique_ptr<Symbol>, SymbolPtrHash, SymbolPtrEquality> Signature::_signature;

    Symbol* Signature::fetchOrDeclare(std::string name, Sort* rngSort, bool interpreted, bool colored)
    {
        auto pair = _signature.insert(std::unique_ptr<Symbol>(new Symbol(name, rngSort, interpreted, colored)));
        return pair.first->get();
    }
    
    Symbol* Signature::fetchOrDeclare(std::string name, std::initializer_list<Sort*> argSorts, Sort* rngSort, bool interpreted, bool colored)
    {
        auto pair = _signature.insert(std::unique_ptr<Symbol>(new Symbol(name, argSorts, rngSort, interpreted, colored)));
        return pair.first->get();
    }

}
