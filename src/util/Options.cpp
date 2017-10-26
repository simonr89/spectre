#include "Options.hpp"

#include <iostream>

namespace util {

  bool BooleanOption::setValue(std::string v) {
    if (v == "on") {
      _value = true;
      return true;
    } else if (v == "off") {
      _value = false;
      return true;
    } else {
      return false;
    }
  }

  bool MultiChoiceOption::setValue(std::string v) {
    for (auto it = _choices.begin(); it != _choices.end(); ++it) {
      if (*it == v) {
        _value = v;
        return true;
      }
    }

    return false;
  }

  bool Configuration::setAllValues(int argc, char *argv[]) {
    int i = 1;
    bool b = true;

    // ignore first argument (program name) and last (input file)
    while (i < argc - 1) {
      auto it = _allOptions.find(std::string(argv[i]));
      if (it != _allOptions.end()) {
        if (!(*it).second->setValue(argv[i + 1])) {
          b = false;
          std::cout << argv[i + 1] << " is not a correct value for option " << argv[i] << std::endl;
        }
      } else {
        b = false;
        std::cout << "Unknown option " << argv[i] << std::endl;
      }
      i += 2;
    }
    return b;
  }

  void Configuration::registerOption(Option* o) {
    _allOptions.insert(std::pair<std::string, Option*>(o->name(), o));
  }

  Configuration Configuration::_instance;

}
