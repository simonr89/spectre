#include "Sort.hpp"

namespace logic {

  std::map<std::string, Sort*> Sort::_sorts;

  Sort* Sort::fetchOrDeclare(std::string name, bool userDefined) {
    auto it = _sorts.find(name);
    
    if (it == _sorts.end()) {
      Sort* s = new Sort(name, userDefined);
      _sorts.insert(std::pair<std::string, Sort*>(name, s)); 
      return s;
    } else {
      return (*it).second;
    }
  }

  std::string Sort::declareTPTP(std::string decl) const {
    if (!_userDefined)
      return "";

    return "tff(" + decl + ", type," + _name + " : $tType).";
  }

  bool Sort::operator==(Sort& o) {
    return _name == o._name;
  }

  std::ostream& operator<<(std::ostream& ostr, const Sort& s) {
    ostr << s.name();
    return ostr;
  }

}
