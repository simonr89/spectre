#include "Sort.hpp"

#include <cassert>
#include "Options.hpp"

namespace logic {
    
#pragma mark - Sort
    std::string Sort::toTPTP() const
    {       
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
    
    std::string Sort::declareSortTPTP() const
    {        
        if (name == "int" || name == "bool")
        {
            // TPTP already knows bool and int.
            return "";
        }
        else if (name == "Time")
        {
            assert(false); // TPTP doesn't support term algebras
            return "";
        }
        else
        {
            return "tff(sort_" + name + ", type, " + name + " : $tType).\n";
        }
    }
    
    std::string Sort::declareSortSMTLIB() const
    {        
        if (name == "int" || name == "bool")
        {
            // SMTLIB already knows Int and Bool.
            return "";
        }
        else if (name == "Time")
        {
            return "(declare-datatypes ((Time 0)) (( (zero) (s (p Time)) )) )\n";
        }
        else
        {
            return "(declare-sort " + name + " 0)\n";
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

    Sort* Sorts::timeSort()
    {
        if (util::Configuration::instance().timepoints().getValue())
        {
            return fetchOrDeclare("Time");
        } else {
            return fetchOrDeclare("int");
        }
    }

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

