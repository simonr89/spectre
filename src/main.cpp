#include <iostream>
#include <fstream>
#include <string>

#include "program/GclAnalyzer.hpp"
#include "util/Options.hpp"
#include "util/Output.hpp"

#include "parser/GclParser.hpp"

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
                
                program::GclAnalyzer gcla; // the data-structure representing the input-program
                
                // test readbility, easier than catching exception thrown by parser
                std::ifstream istr(inputFile);
                if (!istr) {
                    std::cerr << "Unable to read file " << inputFile << std::endl;
                    return 0;
                }
                
                gcla.file = inputFile;

                // set input of flex
//                yy_flex_debug = trace_scanning;
                const char *fname = inputFile.c_str();
                if (!fname)
                    yyin = stdin;
                else if (!(yyin = fopen (fname, "r")))
                    throw std::runtime_error("cannot open " + inputFile + ": " + strerror(errno));
                
                // parse the input-program into gcla
                parser::GclParser parser(gcla);
                parser.set_debug_level(false); // no traces
                int res = parser.parse();
                
                fclose (yyin);
                util::Output::close();
                
                // start analysis of the program
                // TODO:
            }
        }
        return 0;
    }
}
