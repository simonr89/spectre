#ifndef __Signature__
#define __Signature__

#include <initializer_list>
#include <map>
#include <string>
#include <vector>
#include "Sort.hpp"

namespace logic {
    
    // TODO: we could simplify _signature to a std::unordered_set, if we make Symbol comply with the requirements of std::unordered_set
    class Symbol {
    public:
        Symbol(std::string name, Sort* rngSort, bool colored=false) :
        name(name),
        argSorts(),
        rngSort(rngSort),
        colored(colored)
        {
            _signature.insert(std::pair<std::pair<std::string, unsigned>, Symbol*>(std::pair<std::string, unsigned>(name, 0), this));
        }
        
        Symbol(std::string name, std::initializer_list<Sort*> argSorts, Sort* rngSort, bool colored=false) :
        name(name),
        argSorts(argSorts),
        rngSort(rngSort),
        colored(colored)
        {
            _signature.insert(std::pair<std::pair<std::string, unsigned>, Symbol*>(std::pair<std::string, unsigned>(name, argSorts.size()), this));
        }
        
        const std::string name;
        const std::vector<Sort*> argSorts;
        const Sort* rngSort;
        const bool colored;
        
        bool isPredicateSymbol() const { return rngSort == Sorts::boolSort(); }
        
        std::string toTPTP() const;
        std::string declareSymbolTPTP() const;
        std::string declareSymbolColorTPTP() const;
 
        std::string toSMTLIB() const;
        std::string declareSymbolSMTLIB() const;
        std::string declareSymbolColorSMTLIB() const;
        
        static const std::map<std::pair<std::string, unsigned>, Symbol*> signature(){return _signature;}
        
    private:
        // _signature collects all symbols used so far.
        //
        // maps each pair (symbolname/arity) to a symbol
        // not sure why we need the arity here,
        // this enables the case of two symbols with different arity
        // which could easily lead to errors
        static std::map<std::pair<std::string, unsigned>, Symbol*> _signature;
    };

}

#endif

