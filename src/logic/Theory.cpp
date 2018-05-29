#include "Theory.hpp"

#include <cassert>

namespace logic {

  Symbol* Theory::getSymbol(InterpretedSymbol s) {
    switch (s) {
    case InterpretedSymbol::INT_PLUS:
      static Symbol plus("$sum", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort());
      return &plus;
    case InterpretedSymbol::INT_MINUS:
      static Symbol minus("$difference", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort());
      return &minus;
    case InterpretedSymbol::INT_MULTIPLY:
      static Symbol times("$product", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort());
      return &times;
    case InterpretedSymbol::INT_QUOTIENT_E:
      static Symbol divide("$quotient_e", { Sorts::intSort(), Sorts::intSort() }, Sorts::intSort());
      return &divide;
    case InterpretedSymbol::INT_UNARY_MINUS:
      static Symbol uminus("$uminus", { Sorts::intSort() } , Sorts::intSort());
      return &uminus;
    case InterpretedSymbol::INT_GREATER:
      static Symbol greater("$greater", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort());
      return &greater;
    case InterpretedSymbol::INT_GREATER_EQUAL:
      static Symbol greatereq("$greatereq", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort());
      return &greatereq;
    case InterpretedSymbol::INT_LESS:
      static Symbol less("$less", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort());
      return &less;
    case InterpretedSymbol::INT_LESS_EQUAL:
      static Symbol lesseq("$lesseq", { Sorts::intSort(), Sorts::intSort() }, Sorts::boolSort());
      return &lesseq;
    case InterpretedSymbol::ARRAY_SELECT:
      static Symbol select("$select", { Sorts::intArraySort(), Sorts::intSort() }, Sorts::intSort());
      return &select;
    case InterpretedSymbol::ARRAY_STORE:
      static Symbol store("$store", { Sorts::intArraySort(), Sorts::intSort(), Sorts::intSort() }, Sorts::intArraySort());
      return &store;
    default:
      assert(0); //unreachable
      return nullptr;
    }
  }

  FuncTerm* Theory::integerConstant(int i) {
    Symbol *s = new Symbol(std::to_string(i), Sorts::intSort());
    return new FuncTerm(s, {});
  }

  PredTerm* Theory::booleanConstant(bool b) {
    static Symbol t("$true", Sorts::boolSort());
    static Symbol f("$false", Sorts::boolSort());
    return b ? new PredTerm(&t, {}) : new PredTerm(&f, {});
  }
}
