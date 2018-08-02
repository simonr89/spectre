#ifndef __Program__
#define __Program__

#include <memory>
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
                std::vector<FExpression*> preconditions,
                std::vector<FExpression*> postconditions) :
          loop(std::move(loop)),
          preconditions(std::move(preconditions)),
          postconditions(std::move(postconditions))
      {}
        
        const std::unique_ptr<GuardedCommandCollection> loop;
        const std::vector<FExpression*> preconditions;
        const std::vector<FExpression*> postconditions;        
    };
    std::ostream& operator<<(std::ostream& ostr, const Program& p);

}

#endif
