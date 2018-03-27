/**
 * @file GuardedCommandCollection.hpp
 * Defines class Program::GuardedCommandCollection
 *
 * since 30/03/2015, Gothenburg
 */

#ifndef __GuardedCommandCollection__
#define __GuardedCommandCollection__

#include <ostream>
#include <vector>
#include "Expression.hpp"
#include "Type.hpp"
#include "Assignment.hpp"

namespace program {

  class GuardedCommandCollection;

    class GuardedCommand {
    public:
        GuardedCommand(FExpression *guard, std::vector<Assignment*> assignments) : guard(guard), assignments(std::move(assignments)) {}
        
        const FExpression* guard;
        const std::vector<Assignment*> assignments;
        
        /** Return nullptr if the variable is not assigned in the
         command */
        Assignment *findAssignment(const PVariable &v) const;
        
        friend class GuardedCommandCollection;
        friend std::ostream& operator<<(std::ostream&, const GuardedCommand&);
    };

    class GuardedCommandCollection {
    public:
        GuardedCommandCollection(std::vector<GuardedCommand*> commands, FExpression* loopCondition) : commands(std::move(commands)), loopCondition(loopCondition) {}
        
        const std::vector<GuardedCommand*> commands;
        const FExpression* loopCondition;
        
        friend std::ostream& operator<<(std::ostream&, const GuardedCommandCollection&);        
    };

  /** pretty-printer */
  std::ostream& operator<<(std::ostream& ostr, const Assignment& a);
  std::ostream& operator<<(std::ostream& ostr, const GuardedCommand& c);
  std::ostream& operator<<(std::ostream& ostr, const GuardedCommandCollection& c);

    // Hack: these function are needed for debugging bison
    std::ostream& operator<<(std::ostream& ostr, const std::vector<GuardedCommand*>& c);
    std::ostream& operator<<(std::ostream& ostr, const std::pair<FExpression*,std::vector<Assignment*>>& c);
}
#endif
