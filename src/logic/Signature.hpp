#ifndef __Signature__
#define __Signature__

#include <initializer_list>
#include <map>
#include <string>
#include <vector>
#include "logic/Sort.hpp"

namespace logic {

  class Symbol {
  public:
    Symbol(std::string name, Sort* rngSort, bool userDefined = true) :
      _name(name),
      _argSorts(),
      _rngSort(rngSort),
      _userDefined(userDefined),
      _colored(false)
    {
      _signature.insert(std::pair<std::pair<std::string, unsigned>, Symbol*>(std::pair<std::string, unsigned>(name, 0), this));
    }
    
    Symbol(std::string name, std::initializer_list<Sort*> argSorts, Sort* rngSort, bool userDefined = true) :
      _name(name),
      _argSorts(argSorts),
      _rngSort(rngSort),
      _userDefined(userDefined),
      _colored(false)
    {
      _signature.insert(std::pair<std::pair<std::string, unsigned>, Symbol*>(std::pair<std::string, unsigned>(name, argSorts.size()), this));
    }

    ~Symbol() {}

    std::string name() const { return _name; }

    unsigned arity() const { return _argSorts.size(); }

    bool isUserDefined() const { return _userDefined; }

    bool isColored() const { return _colored; }

    void makeColored() { _colored = true; }

    bool isPredicateSymbol() const { return _rngSort == Sort::boolSort(); }

    std::string declareTPTP(std::string decl) const;

    std::string declareVampireColor() const;

    static Symbol* getSymbol(std::string name, unsigned arity);

    class const_iterator {
    public:
      const_iterator(std::map<std::pair<std::string, unsigned>, Symbol*>::const_iterator it) :
        _it(it)
      {}

      ~const_iterator() {}
      
      const Symbol& operator*() { return *(*_it).second; }
      
      bool operator==(const_iterator other) { return _it == other._it; }

      bool operator!=(const_iterator other) { return !(_it == other._it); }

      const_iterator & operator++() { ++_it; return (*this); }

    protected:      
      std::map<std::pair<std::string, unsigned>, Symbol*>::const_iterator _it;
    };
    
    static const_iterator sigBegin() { return const_iterator(_signature.cbegin()); }

    static const_iterator sigEnd() { return const_iterator(_signature.cend()); }
    
  protected:
    std::string _name;
    std::vector<Sort*> _argSorts;
    Sort* _rngSort;
    bool _userDefined;
    bool _colored;

    static std::map<std::pair<std::string, unsigned>, Symbol*> _signature;
  };
}

#endif
