#include "Theory.hpp"

#include <cassert>

namespace logic {

  Symbol* Theory::getSymbol(InterpretedSymbol s) {
    switch (s) {
    case InterpretedSymbol::INT_PLUS:
      static Symbol plus("int_plus", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
      return &plus;
    case InterpretedSymbol::INT_MINUS:
      static Symbol minus("int_minus", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
      return &minus;
    case InterpretedSymbol::INT_MULTIPLY:
      static Symbol times("int_multiply", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
      return &times;
    case InterpretedSymbol::INT_QUOTIENT_E:
      static Symbol divide("int_quotient_e", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort(), true);
      return &divide;
    case InterpretedSymbol::INT_UNARY_MINUS:
      static Symbol uminus("int_unary_minus", { Sorts::intSort() } , Sorts::intSort(), true);
      return &uminus;
    case InterpretedSymbol::INT_GREATER:
      static Symbol greater("int_greater", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
      return &greater;
    case InterpretedSymbol::INT_GREATER_EQUAL:
      static Symbol greatereq("int_greater_eq", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
      return &greatereq;
    case InterpretedSymbol::INT_LESS:
      static Symbol less("int_less", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
      return &less;
    case InterpretedSymbol::INT_LESS_EQUAL:
      static Symbol lesseq("int_less_eq", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort(), true);
      return &lesseq;
    case InterpretedSymbol::ARRAY_SELECT:
      static Symbol select("array_select", { Sorts::intArraySort(), Sorts::intSort() }, Sorts::intSort(), true);
      return &select;
    case InterpretedSymbol::ARRAY_STORE:
      static Symbol store("array_store", { Sorts::intArraySort(), Sorts::intSort(), Sorts::intSort() }, Sorts::intArraySort(), true);
      return &store;
    default:
      assert(0); //unreachable
      return nullptr;
    }
  }

  FuncTerm* Theory::integerConstant(int i) {
    Symbol *s = new Symbol(std::to_string(i), Sorts::intSort(), true);
    return new FuncTerm(s, {});
  }

  PredTerm* Theory::booleanConstant(bool b) {
    static Symbol t("bool_true", Sorts::boolSort(), true);
    static Symbol f("bool_false", Sorts::boolSort(), true);
    return b ? new PredTerm(&t, {}) : new PredTerm(&f, {});
  }
}
