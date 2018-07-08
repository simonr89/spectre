#include "Sort.hpp"

#include <cassert>
#include "Options.hpp"

namespace logic {
    
#pragma mark - Sort
    std::string Sort::toTPTP() const
    {
        // not implemented yet
        assert(!util::Configuration::instance().arrayTheory().getValue());
        
        if (name == "int")
        {
            return "$int";
        }
        else if (name == "bool")
        {
            return "$o";
        }
        else
        {
            return name;
        }
    }
    
    std::string Sort::toSMTLIB() const
    {
        // not implemented yet
        assert(!util::Configuration::instance().arrayTheory().getValue());
        
        if (name == "int")
        {
            return "Int";
        }
        else if (name == "bool")
        {
            return "Bool";
        }
        else
        {
            return name;
        }
    }
    
    std::string declareSortTPTP(const Sort& s)
    {
        // not implemented yet
        assert(!util::Configuration::instance().arrayTheory().getValue());
        
        if (s.toTPTP() == "$o" || s.toTPTP() == "$int")
        {
            // TPTP already knows bool and int.
            return "";
        }
        else if (s.toTPTP() == "Time")
        {
            assert(false); // TPTP doesn't support term algebras
            return "";
        }
        else
        {
            return "tff(sort_" + s.toTPTP() + ", type, " + s.toTPTP() + " : $tType).\n";
        }
    }
    
    std::string declareSortSMTLIB(const Sort& s)
    {
        // not implemented yet
        assert(!util::Configuration::instance().arrayTheory().getValue());
        
        if (s.toSMTLIB() == "Int" || s.toSMTLIB() == "Bool")
        {
            // SMTLIB already knows Int and Bool.
            return "";
        }
        else if (s.toSMTLIB() == "Time")
        {
            return "(declare-datatypes ((Time 0)) (( (zero) (s (p Time)) )) )\n";
        }
        else
        {
            return "(declare-sort " + s.toSMTLIB() + " 0)\n";
        }
    }
    
    bool Sort::operator==(Sort& o)
    {
        return name == o.name;
    }
    
    std::ostream& operator<<(std::ostream& ostr, const Sort& s) {
        ostr << s.name;
        return ostr;
    }
    
#pragma mark - Sorts

    std::map<std::string, std::unique_ptr<Sort>> Sorts::_sorts;

    Sort* Sorts::fetchOrDeclare(std::string name)
    {
        auto it = _sorts.find(name);
        
        if (it == _sorts.end())
        {
            auto ret = _sorts.insert(std::make_pair(name, std::unique_ptr<Sort>(new Sort(name))));
            return ret.first->second.get();
        }
        else
        {
            return (*it).second.get();
        }
    }
    
}

