#ifndef __Signature__
#define __Signature__

#include <list>
#include <map>
#include <string>
#include "logic/Sort.hpp"

namespace logic {

  class Symbol {
  public:
    Symbol(std::string name, Sort* rngSort) :
      _name(name),
      _argSorts(),
      _rngSort(rngSort),
      _colored(false)
    {
      _signature.insert(std::pair<std::pair<std::string, unsigned>, Symbol*>(std::pair<std::string, unsigned>(name, 0), this));
    }
    
    Symbol(std::string name, std::list<Sort*> argSorts, Sort* rngSort) :
      _name(name),
      _argSorts(argSorts),
      _rngSort(rngSort),
      _colored(false)
    {
      _signature.insert(std::pair<std::pair<std::string, unsigned>, Symbol*>(std::pair<std::string, unsigned>(name, argSorts.size()), this));
    }

    ~Symbol() {}

    std::string name() { return _name; }

    unsigned arity() { return _argSorts.size(); }

    bool isColored() { return _colored; }

    void makeColored() { _colored = true; }

    bool isPredicateSymbol() { return _rngSort == Sort::boolSort(); }

    static Symbol* getSymbol(std::string name, unsigned arity);
    
  protected:
    std::string _name;
    std::list<Sort*> _argSorts;
    Sort* _rngSort;
    bool _colored;

    static std::map<std::pair<std::string, unsigned>, Symbol*> _signature;
  };
}

#endif
