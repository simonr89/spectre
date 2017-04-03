#include "Signature.hpp"

namespace logic {

  std::map<std::pair<std::string, unsigned>, Symbol*> Symbol::_signature;

  Symbol* Symbol::getSymbol(std::string name, unsigned arity) {
    auto it = _signature.find(std::pair<std::string, unsigned>(name, arity));
    return it == _signature.end() ? nullptr : (*it).second;
  }
  
}
