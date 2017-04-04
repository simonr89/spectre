#include "Sort.hpp"

namespace logic {

  std::string Sort::name() const {
    if (_userDefined)
      return _name;

    switch (_d) {
    case DefaultSort::SRT_INT:
      return "$int";
    case DefaultSort::SRT_BOOL:
      return "$bool";
    default:
      return "";
    }
  }

  Sort* Sort::boolSort() {
    static Sort s(DefaultSort::SRT_BOOL);

    return &s;
  }

  Sort* Sort::intSort() {
    static Sort s(DefaultSort::SRT_INT);

    return &s;
  }

  bool Sort::operator==(Sort& o) {
    if (_userDefined) {
      return o._userDefined && _d == o._d;
    } else {
      return !o._userDefined && _name == o._name;
    }
  }

  std::ostream& operator<<(std::ostream& ostr, const Sort& s) {
    ostr << s.name();
    return ostr;
  }

}
