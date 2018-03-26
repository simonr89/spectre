


#ifndef __Program__
#define __Program__

#include <vector>
#include "GuardedCommandCollection.hpp"
#include "Variable.hpp"
#include "Expression.hpp"


namespace program
{
    class Program
    {
    public:
        Program(GuardedCommandCollection loop,
                std::vector<const FExpression*> preconditions,
                std::vector<const FExpression*> postconditions,
                std::vector<const PVariable*> variables
                ) : loop(loop), variables(variables), preconditions(preconditions), postconditions(postconditions) {}
        
        const GuardedCommandCollection loop;
        const std::vector<const PVariable*> variables;
        const std::vector<const FExpression*> preconditions;
        const std::vector<const FExpression*> postconditions;
    };
}

#endif
