#include <iostream>
#include <fstream>
#include <string>

#include "parser/GclParsingContext.hpp"
#include "util/Options.hpp"
#include "util/Output.hpp"

#include "parser/GclParser.hpp"
#include "analysis/Analyzer.hpp"

extern FILE* yyin;

void outputUsage() {
    std::cout << "Usage: invgen <filename>" << std::endl;
}

int main(int argc, char *argv[]) {
    if (argc <= 1) {
        outputUsage();
    } else {
        if (util::Configuration::instance().setAllValues(argc, argv)) {
            if (util::Output::initialize())
            {
                std::string inputFile = argv[argc - 1];
                
                // test readbility, easier than catching exception thrown by parser
                std::ifstream istr(inputFile);
                if (!istr) {
                    std::cerr << "Unable to read file " << inputFile << std::endl;
                    return 0;
                }
                
                program::GuardedCommandCollection p;
                // TODO: switch between parsers here
                if (true)
                {
                    // set input for parser
                    // TODO: remove double checking of file,move setting yyin into parser?
                    const char *fname = inputFile.c_str();
                    yyin = fopen (fname, "r");
                    
                    // generate a context, whose fields are used as in/out-parameters for parsing
                    parser::GclParsingContext c;
                    c.inputFile = inputFile;
                    
                    // parse the input-program into c
                    parser::GclParser parser(c);
                    parser.set_debug_level(false); // no traces
                    parser.parse();
                    
                    if (!c.errorFlag)
                    {
                        c.program.finalizeGuards();

                        program::Analyzer a(c.program, c._preconditions,c._postconditions,c._variables);
                        
                        // run analysis
                        a.buildProperties();
                    }
                    else
                    {
                        exit(1);
                    }
                    fclose (yyin);
                }
                
                util::Output::close();
                
                // start analysis of the program
                // TODO:
            }
        }
        return 0;
    }
}
