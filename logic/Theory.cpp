#include "Theory.hpp"

#include <cassert>

namespace logic {
  
  unsigned Theory::getArity(InterpretedSymbol s) {
    switch (s) {
    case InterpretedSymbol::INT_PLUS:
    case InterpretedSymbol::INT_MINUS:
    case InterpretedSymbol::INT_MULTIPLY:
    case InterpretedSymbol::INT_QUOTIENT_E:
      return 2;
    case InterpretedSymbol::INT_UNARY_MINUS:
      return 1;
    case InterpretedSymbol::INT_GREATER:
    case InterpretedSymbol::INT_GREATER_EQUAL:
    case InterpretedSymbol::INT_LESS:
    case InterpretedSymbol::INT_LESS_EQUAL:
      return 2;
    default:
      assert(0); //unreachable
      return 0;
    }
  }

  std::string Theory::getString(InterpretedSymbol s) {
    switch (s) {
    case InterpretedSymbol::INT_PLUS:
      return "$sum";
    case InterpretedSymbol::INT_MINUS:
      return "$difference";
    case InterpretedSymbol::INT_MULTIPLY:
      return "$product";
    case InterpretedSymbol::INT_QUOTIENT_E:
      return "$quotient_e";
    case InterpretedSymbol::INT_UNARY_MINUS:
      return "$eminus";
    case InterpretedSymbol::INT_GREATER:
      return "$greater";
    case InterpretedSymbol::INT_GREATER_EQUAL:
      return "$greatereq";
    case InterpretedSymbol::INT_LESS:
      return "$less";
    case InterpretedSymbol::INT_LESS_EQUAL:
      return "$lesseq";
    default:
      assert(0); //unreachable
      return "";
    }
  }

  Symbol* Theory::getSymbol(InterpretedSymbol s) {
    switch (s) {
    case InterpretedSymbol::INT_PLUS:
      static Symbol plus("$plus", { Sort::intSort(), Sort::intSort() }, Sort::intSort(), false);
      return &plus;
    case InterpretedSymbol::INT_MINUS:
      static Symbol minus("$minus", { Sort::intSort(), Sort::intSort() }, Sort::intSort(), false);
      return &minus;
    case InterpretedSymbol::INT_MULTIPLY:
      static Symbol times("$times", { Sort::intSort(), Sort::intSort() }, Sort::intSort(), false);
      return &times;
    case InterpretedSymbol::INT_QUOTIENT_E:
      static Symbol divide("$divide", { Sort::intSort(), Sort::intSort() }, Sort::intSort(), false);
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
