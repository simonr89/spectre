
#ifndef __Analyzer__
#define __Analyzer__

#include <string>
#include <vector>
#include <map>
#include "Expression.hpp"
#include "GuardedCommandCollection.hpp"
#include "Variable.hpp"
#include "Program.hpp"

namespace program
{
    // the aim of this class is to compute the monotonicity
    // attribute of the variables
    class Analyzer
    {
    public:       
        static void computeVariableProperties(const Program& p);
        
    private:
        // methods for computing constness and monotonicity of variables
        /**
         * True iff the assignment has the form x = x + c, where x is an
         * integer variable and c an integer constant, c is then copied to
         * incr
         */
        static bool isScalarIncrement(Assignment* a, int &incr);
        static void recordLhsInfo(Assignment* a);
        static void recordScalarIncrement(PVariable *v, int n);
        
        // methods for marking dense and strict variables
        static void densityAndStrictness(const Program& p);
        static void densityAndStrictness(const Program& p, PVariable *v);
        static bool isIncremented(const GuardedCommand *gc, const PVariable *v, int &incr);
    };
    
}
#endif

