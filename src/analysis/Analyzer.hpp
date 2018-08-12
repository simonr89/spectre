
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
    enum class Monotonicity {DEC, INC, OTHER};
    
    struct AnalyzerResult
    {
        AnalyzerResult(std::map<const PVariable*,Monotonicity> monotonic,
                       std::map<const PVariable*,bool> strict,
                       std::map<const PVariable*,bool> dense
                       ) : monotonic(std::move(monotonic)), strict(std::move(strict)), dense(std::move(dense)){}
        
        const std::map<const PVariable*,Monotonicity> monotonic;
        const std::map<const PVariable*,bool> strict;
        const std::map<const PVariable*,bool> dense;
        
        /*std::string toString()
        {
            std::string result = "";
            for(const auto& keyValuePair : updated)
            {
                auto var = keyValuePair.first;
                result += var->name;
                
                result += " {";
                switch (monotonic.at(var))
                {
                    case Monotonicity::DEC:
                        result += "monotonic decreasing,";
                        break;
                    case Monotonicity::INC:
                        result += "monotonic increasing,";
                        break;
                    case Monotonicity::OTHER:
                        break;
                }
                if (dense.at(var))
                    result += "dense,";
                if (strict.at(var))
                    result += "strict";
                result += "}\n";
            }
            return result + "\n";
            }*/
    };
    
    class Analyzer
    {
    public:
        Analyzer(const Program& program) :
            _loop(*program.loop),
            _preconditions(program.preconditions),
            _postconditions(program.postconditions)
        {
            // set all map-entries to false
            // TODO: is this really the correct start-value???
            for (const auto& var : program.loop->variables)
            {
                _monotonic[var] = Monotonicity::OTHER;
                _strict[var] = false;
                _dense[var] = false;
            }
        }
        
        AnalyzerResult computeVariableProperties();
        
    private:
        // used as input
        const GuardedCommandCollection& _loop;
        const std::vector<FExpression*> _preconditions;
        const std::vector<FExpression*> _postconditions;
        
        // the aim of this class is to compute the following 4 maps
        std::map<const PVariable*,Monotonicity> _monotonic;
        std::map<const PVariable*,bool> _strict;
        std::map<const PVariable*,bool> _dense;
        
        // methods for computing _updated and _monotonic
        /**
         * True iff the assignment has the form x = x + c, where x is an
         * integer variable and c an integer constant, c is then copied to
         * incr
         */
        bool isScalarIncrement(Assignment* a, int &incr);
        void recordLhsInfo(Assignment* a);
        void recordScalarIncrement(PVariable *v, int n);
        
        // methods for computing _dense and _strict
        void densityAndStrictness();
        void densityAndStrictness(const PVariable *v);
        bool isIncremented(const GuardedCommand *gc, const PVariable *v, int &incr);
    };
    
}
#endif

