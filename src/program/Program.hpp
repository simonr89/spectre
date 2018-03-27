


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
        Program(std::unique_ptr<GuardedCommandCollection> loop,
                std::vector<const FExpression*> preconditions,
                std::vector<const FExpression*> postconditions,
                std::vector<const PVariable*> variables
                ) : loop(std::move(loop)), variables(std::move(variables)), preconditions(std::move(preconditions)), postconditions(std::move(postconditions)) {}
        
        const std::unique_ptr<GuardedCommandCollection> loop;
        const std::vector<const PVariable*> variables;
        const std::vector<const FExpression*> preconditions;
        const std::vector<const FExpression*> postconditions;        
    };
    std::ostream& operator<<(std::ostream& ostr, const Program& p);

}

#endif
