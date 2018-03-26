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
#include "Expression.hpp"
#include "Type.hpp"
#include "Assignment.hpp"

namespace program {

  class GuardedCommandCollection;

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

    const std::list<GuardedCommand*>& commands() const { return _collection; }

    FExpression *_condition;

    void addGuardedCommand(GuardedCommand* gc);

    // given the collection of commands, each guard has the negation
    // of previous guard added to it so that the guards are exclusive
    // must be called after all commands have been added
    void finalizeGuards();

    void setLoopCondition(FExpression *e) { _condition = e; }

    const FExpression* loopCondition() const { return _condition; }

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
