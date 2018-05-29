/**
 *  @file Type.cpp
 *  Implements Program::Type
 *
 * @since 20/08/2010, Torrevieja
 */

#include "Type.hpp"

namespace program {

  bool isArrayType(Type t) {
    switch (t) {
    case Type::TY_BOOLEAN_ARRAY:
    case Type::TY_INTEGER_ARRAY:
      return true;
    default:
      return false;
    }
  }

  Type returnType(Type t) {
    switch (t) {
    case Type::TY_BOOLEAN_ARRAY:
      return Type::TY_BOOLEAN;
    case Type::TY_INTEGER_ARRAY:
      return Type::TY_INTEGER;
    default:
      // shouldn't be reached
      return t;
    }
  }

  logic::Sort* toSort(Type t) {
    switch (t) {
    case Type::TY_BOOLEAN:
    case Type::TY_BOOLEAN_ARRAY:
      return logic::Sorts::boolSort();
    case Type::TY_INTEGER:
    case Type::TY_INTEGER_ARRAY:
      return logic::Sorts::intSort();
    default:
      return nullptr;
    }
  }
  
  std::ostream& operator<<(std::ostream& ostr, const Type ty)
  {
    switch (ty) {
    case Type::TY_INTEGER:
      ostr << "int";
      break;
    case Type::TY_BOOLEAN:
      ostr << "bool";
      break;
    case Type::TY_INTEGER_ARRAY:
      ostr << "int[]";
      break;
    case Type::TY_BOOLEAN_ARRAY:
      ostr << "bool[]";
      break;
    case Type::TY_FORMULA:
      ostr << "formula";
    }
    return ostr;
  }

}
