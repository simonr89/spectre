#include "Signature.hpp"

namespace logic {
    
    std::map<std::pair<std::string, unsigned>, Symbol*> Symbol::_signature;
    
    std::string Symbol::declareSymbolTPTP() const
    {
        // if the name of a symbol is different from the TPTP-encoding, we know it's an interpreted symbol
        if (toTPTP()==name)
        {
            return ""; // don't  need to declare symbols, which are already known to TPTP-solvers.
        }
        
        std::string s = "tff(symb_" + name + ", type, " + name + " : ";
        if (argSorts.size() == 0)
        {
            s += rngSort->toTPTP() + ").";
        }
        else if (argSorts.size() == 1)
        {
            s += argSorts[0]->toTPTP() + " > " + rngSort->toTPTP() + ").";
        }
        else
        {
            s += "(";
            for (unsigned i = 0; i < argSorts.size() - 1; i++)
            {
                s += argSorts[i]->toTPTP() + " * ";
            }
            s += argSorts[argSorts.size() - 1]->toTPTP() + ") > " + rngSort->toTPTP() + ").";
        }
        return s;
    }
    
    std::string Symbol::toTPTP() const
    {
        if (name == "int_sum")
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
            return "$select";
        }
        else if (name == "array_store")
        {
            return "$store";
        }
        else
        {
            return name;
        }
    }

    std::string Symbol::declareSymbolSMTLIB() const
    {
        // if the name of a symbol is different from the TPTP-encoding, we know it's an interpreted symbol
        if (toSMTLIB()==name)
        {
            return ""; // don't  need to declare symbols, which are already known to TPTP-solvers.
        }
        if (argSorts.size() == 0)
        {
            return "(declare-const " + toSMTLIB() + " " + rngSort->toSMTLIB() + ")";
        }
        else
        {
            std::string res = "(declare-fun " + toSMTLIB() + " (";
            for (const auto& arg : argSorts)
            {
                res += arg->toSMTLIB() + (arg == argSorts.back() ? "" : " ");
            }
            res += ") " + rngSort->toSMTLIB() + ")";
            return res;
        }
    }
    
    std::string Symbol::toSMTLIB() const
    {
        if (name == "int_sum")
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
            assert(false); // TODO: not implemented yet
            return "$select";
        }
        else if (name == "array_store")
        {
            assert(false); // TODO: not implemented yet
            return "$store";
        }
        else
        {
            return name;
        }
    }
    
    std::string Symbol::declareSymbolColorTPTP() const
    {
        std::string s = "vampire(symbol, ";
        s += "function, "; // predicate or function
        s += name + ", ";
        s += std::to_string(argSorts.size()) + ", "; // arity
        s += colored ? "left" : "skip";
        s += ").";
        return s;
    }
    
    std::string Symbol::declareSymbolColorSMTLIB() const
    {
        return "color-symbol " + toSMTLIB() + " " + (colored ? "left" : "right") + ")";
    }
    
}
