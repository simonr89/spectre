#include "Theory.hpp"

#include <cassert>

namespace logic {

  Symbol* Theory::getSymbol(InterpretedSymbol s) {
    switch (s) {
    case InterpretedSymbol::INT_PLUS:
      static Symbol plus("$sum", { Sort::intSort(), Sort::intSort() }, Sort::intSort(), false);
      return &plus;
    case InterpretedSymbol::INT_MINUS:
      static Symbol minus("$difference", { Sort::intSort(), Sort::intSort() }, Sort::intSort(), false);
      return &minus;
    case InterpretedSymbol::INT_MULTIPLY:
      static Symbol times("$product", { Sort::intSort(), Sort::intSort() }, Sort::intSort(), false);
      return &times;
    case InterpretedSymbol::INT_QUOTIENT_E:
      static Symbol divide("$quotient_e", { Sort::intSort(), Sort::intSort() }, Sort::intSort(), false);
      return &divide;
    case InterpretedSymbol::INT_UNARY_MINUS:
      static Symbol uminus("$uminus", { Sort::intSort() } , Sort::intSort(), false);
      return &uminus;
    case InterpretedSymbol::INT_GREATER:
      static Symbol greater("$greater", { Sort::intSort(), Sort::intSort() }, Sort::boolSort(), false);
      return &greater;
    case InterpretedSymbol::INT_GREATER_EQUAL:
      static Symbol greatereq("$greatereq", { Sort::intSort(), Sort::intSort() }, Sort::boolSort(), false);
      return &greatereq;
    case InterpretedSymbol::INT_LESS:
      static Symbol less("$less", { Sort::intSort(), Sort::intSort() }, Sort::boolSort(), false);
      return &less;
    case InterpretedSymbol::INT_LESS_EQUAL:
      static Symbol lesseq("$lesseq", { Sort::intSort(), Sort::intSort() }, Sort::boolSort(), false);
      return &lesseq;
    case InterpretedSymbol::ARRAY_SELECT:
      static Symbol select("$select", { Sort::defaultSort(), Sort::defaultSort() }, Sort::defaultSort(), false);
      return &select;
    case InterpretedSymbol::ARRAY_STORE:
      static Symbol store("$store", { Sort::defaultSort(), Sort::defaultSort(), Sort::defaultSort() }, Sort::defaultSort(), false);
      return &store;
    default:
      assert(0); //unreachable
      return nullptr;
    }
  }

  FuncTerm* Theory::integerConstant(int i) {
    Symbol *s = new Symbol(std::to_string(i), Sort::intSort(), false);
    return new FuncTerm(s, {});
  }

  PredTerm* Theory::booleanConstant(bool b) {
    static Symbol t("$true", Sort::boolSort(), false);
    static Symbol f("$false", Sort::boolSort(), false);
    return b ? new PredTerm(&t, {}) : new PredTerm(&f, {});
  }
}
