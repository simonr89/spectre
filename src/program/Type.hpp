#ifndef __ProgramType__
#define __ProgramType__

#include <ostream>
#include "Sort.hpp"

namespace program {

  /**
   * Types used in the program, currently just integers and arrays.
   * @since 20/08/2010, Torrevieja
   */
  enum class Type {
    TY_BOOLEAN,
    TY_INTEGER,
    TY_BOOLEAN_ARRAY,
    TY_INTEGER_ARRAY,
    TY_FORMULA        // the type of quantified boolean expressions used in assertions
  };

  bool isArrayType(Type t);

  Type returnType(Type t);

  logic::Sort* toSort(Type t);

  std::ostream& operator<<(std::ostream& ostr, const Type ty);

}

#endif // __ProgramType__
