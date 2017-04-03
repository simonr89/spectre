/**
 * @file GuardedCommandCollection.hpp
 * Defines class Program::GuardedCommandCollection
 *
 * since 30/03/2015, Gothenburg
 */

#ifndef __GuardedCommandCollection__
#define __GuardedCommandCollection__

#include <ostream>
#include <list>
#include "program/Expression.hpp"
#include "program/Type.hpp"

namespace program {

  class GuardedCommandCollection;

  class Assignment {
  public:
    
    Assignment(LocationExpression *lhs, Expression *rhs) :
      _lhs(lhs),
      _rhs(rhs)
    {}
    ~Assignment() {}

    LocationExpression *lhs() { return _lhs; }
    Expression *rhs() { return _rhs; }

    bool hasLhs(const PVariable &v) { return _lhs->varInfo() == &v; }

    /**
     * True iff the assignment has the form x = x + c, where x is an
     * integer variable and c an integer constant, c is then copied to
     * incr
     */
    bool isScalarIncrement(int &incr);
    
    /** Modifies the information associated with the lhs
        variable. Should be executed immediately after the
        constructor */
    void recordLhsInfo();

    friend std::ostream& operator<<(std::ostream&, const Assignment&);
    
  protected:
    LocationExpression *_lhs;
    Expression *_rhs;

    bool isScalarIncrement(Expression *e, PVariable *v, int &incr);
  };

  class GuardedCommand {
  public:
    GuardedCommand(FExpression *guard) :
      _guard(guard),
      _assignments()
    {}
    ~GuardedCommand() {}

    /** Return nullptr if the variable is not assigned in the
        command */
    Assignment *findAssignment(const PVariable &v);

    FExpression *guard() { return _guard; }
    
    std::list<Assignment*>& assignments() { return _assignments; }

    /** Return true if the assignment was added, false if an
        assignment with the same LHS already exists in the guarded
        command. In the case of array assignments, if e.g. A[i] = x is
        added where the command already contains an assignment to
        A[j], the condition i != j is added to the guard (so this will
        never return false but potentially add i != i to the guard
        ) */
    bool addAssignment(Assignment *a);

    void addCondition(FExpression *e);

    friend class GuardedCommandCollection;
    friend std::ostream& operator<<(std::ostream&, const GuardedCommand&);

  protected:
    FExpression *_guard;
    std::list<Assignment*> _assignments;
  };

  class GuardedCommandCollection {
  public:
    GuardedCommandCollection() :
      _collection(0)
    {}
    ~GuardedCommandCollection() {}

    std::list<GuardedCommand*>& commands() { return _collection; }

    FExpression *_condition;

    void addGuardedCommand(GuardedCommand* gc);

    // given the collection of commands, each guard has the negation
    // of previous guard added to it so that the guards are exclusive
    // must be called after all commands have been added
    void finalizeGuards();

    void setLoopCondition(FExpression *e) { _condition = e; }

    FExpression *loopCondition() { return _condition; }

    friend std::ostream& operator<<(std::ostream&, const GuardedCommandCollection&);
    
  protected:
    /** The guarded commands stored in reverse order */
    std::list<GuardedCommand*> _collection;
  };

  /** pretty-printer */
  std::ostream& operator<<(std::ostream& ostr, const Assignment& a);
  std::ostream& operator<<(std::ostream& ostr, const GuardedCommand& c);
  std::ostream& operator<<(std::ostream& ostr, const GuardedCommandCollection& c);

}
#endif
