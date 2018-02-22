#include "GuardedCommandCollection.hpp"

namespace program {

  Assignment *GuardedCommand::findAssignment(const PVariable &v) {
    for (auto it = _assignments.begin(); it != _assignments.end(); ++it) {
      if ((*it)->hasLhs(v))
        return *it;
    }
    return nullptr;
  }

  bool GuardedCommand::addAssignment(Assignment *a)
  {
    PVariable *lhs = a->lhs()->varInfo();
    // look for duplicate assignments
    for (auto it = _assignments.begin(); it != _assignments.end(); ++it) {
      if ((*it)->hasLhs(*lhs)) {
        if (isArrayType(lhs->vtype())) {
          // array assignment, add condition to guard
          addCondition(BooleanExpression::mkNeq(a->lhs()->child(0),
                                                (*it)->lhs()->child(0)));
        } else {
          // duplicate assignment to scalar
          return false;
        }        
      }
    }
    // the order of assignments does not matter
    _assignments.push_front(a);
    
    return true;
  }

  void GuardedCommand::addCondition(FExpression *e)
  {
    _guard = BooleanExpression::mkAnd(_guard, e);
  }

  void GuardedCommandCollection::addGuardedCommand(GuardedCommand *gc)
  {
    _collection.push_front(gc);
  }

  void GuardedCommandCollection::finalizeGuards()
  {
    Expression *e = nullptr;
    // the guards are stored in reverse order
    // modify the guard so that it includes the negation of all
    // previous guards (i.e.  guard after it in the list)
    for (auto it1 = _collection.begin(); it1 != _collection.end(); ++it1) {
      e = e ? BooleanExpression::mkOr(e, (*it1)->_guard) : (*it1)->_guard;
      // TODO double check that this works
      for (auto it2(it1); ++it2 != _collection.end(); ) {
        (*it1)->addCondition(BooleanExpression::mkNegation((*it2)->_guard));
      }
    }
    _condition = BooleanExpression::mkAnd(_condition, e);
  }

  std::ostream& operator<<(std::ostream& ostr, const Assignment &a)
  {
    ostr << *(a._lhs) << " = " << *(a._rhs) << ";";
    return ostr;
  }

  std::ostream& operator<<(std::ostream& ostr, const GuardedCommand &c)
  {
    ostr << ":: " << *(c._guard) << " ->";
    for (auto it = c._assignments.begin(); it != c._assignments.end(); ++it) {
      ostr << " " << *(*it);
    }
    return ostr;
  }
  
  std::ostream& operator<<(std::ostream& ostr, const GuardedCommandCollection &c)
  {
    ostr << "while " << *c._condition << " do\n";
    for (auto it = c._collection.begin(); it != c._collection.end(); ++it) {
      ostr << *(*it) << " \n";
    }
    ostr << "od\n";
    return ostr;
  }
};
