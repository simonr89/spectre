#ifndef __Signature__
#define __Signature__

#include <cassert>
#include <initializer_list>
#include <unordered_set>
#include <string>
#include <vector>
#include "Sort.hpp"

# pragma mark - Symbol

namespace logic {
    
    class Symbol {
        // we need each symbol to be defined in the signature
        // We therefore use the Signature-class below as a manager-class for Symbol-objects
        friend class Signature;
        
    private:
        Symbol(std::string name, Sort* rngSort, bool interpreted=false, bool colored=false) :
        name(name),
        argSorts(),
        rngSort(rngSort),
        interpreted(interpreted),
        colored(colored)
        {
            assert(!name.empty());
        }
        
        Symbol(std::string name, std::initializer_list<Sort*> argSorts, Sort* rngSort, bool interpreted=false, bool colored=false) :
        name(name),
        argSorts(argSorts),
        rngSort(rngSort),
        interpreted(interpreted),
        colored(colored)
        {
            assert(!name.empty());
        }
     
    public:
        const std::string name;
        const std::vector<Sort*> argSorts;
        const Sort* rngSort;
        const bool interpreted; // true iff the symbol is interpreted, i.e. it is assumed to be already declared and defined
        const bool colored;

        bool isPredicateSymbol() const { return rngSort == Sorts::boolSort(); }
        
        std::string toTPTP() const;
        std::string declareSymbolTPTP() const;
        std::string declareSymbolColorTPTP() const;
 
        std::string toSMTLIB() const;
        std::string declareSymbolSMTLIB() const;
        std::string declareSymbolColorSMTLIB() const;
        
        bool operator==(const Symbol &s) const {return name == s.name;}
    };
}

namespace std
{
    template<> struct hash<logic::Symbol>
    {
        using argument_type = logic::Symbol;
        using result_type = std::size_t;
        
        result_type operator ()(argument_type const& s) const
        {
            return std::hash<std::string>()(s.name);
        }
    };
}

# pragma mark - Signature

namespace logic {

    struct SymbolPtrEquality
    {
        bool operator()(const std::unique_ptr<Symbol>& a, const std::unique_ptr<Symbol>& b) const {return *a == *b;}
    };
    
    struct SymbolPtrHash
    {
        size_t operator()(const std::unique_ptr<Symbol>& ptr) const {return std::hash<Symbol>()(*ptr);}
    };
    
    // We use Signature as a manager-class for Symbol-instances
    class Signature
    {
    public:
        // construct new symbols
        static Symbol* fetchOrDeclare(std::string name, Sort* rngSort, bool interpreted=false, bool colored=false);
        static Symbol* fetchOrDeclare(std::string name, std::initializer_list<Sort*> argSorts, Sort* rngSort, bool interpreted=false, bool colored=false);

        static const std::unordered_set<std::unique_ptr<Symbol>, SymbolPtrHash, SymbolPtrEquality>& signature(){return _signature;}
        
    private:
        // _signature collects all symbols used so far.
        static std::unordered_set<std::unique_ptr<Symbol>, SymbolPtrHash, SymbolPtrEquality> _signature;
    };
}
#endif

