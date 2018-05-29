#include "Sort.hpp"
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

    std::map<std::string, Sort*> Sorts::_sorts;

    Sort* Sorts::fetchOrDeclare(std::string name) {
        auto it = _sorts.find(name);
        
        if (it == _sorts.end()) {
            Sort* s = new Sort(name);
            _sorts.insert(std::pair<std::string, Sort*>(name, s));
            return s;
        } else {
            return (*it).second;
        }
    }
    
}

