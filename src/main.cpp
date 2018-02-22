#include <iostream>
#include <fstream>
#include <string>

#include "parser/GclParsingContext.hpp"
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
                // test readbility, easier than catching exception thrown by parser
                std::ifstream istr(inputFile);
                if (!istr) {
                    std::cerr << "Unable to read file " << inputFile << std::endl;
                    return 0;
                }
                
                // generate a context, whose fields are used as in/out-parameters for parsing
                parser::GclParsingContext c;
                c.inputFile = inputFile;

                const char *fname = inputFile.c_str();
                if (!fname)
                    yyin = stdin;
                else if (!(yyin = fopen (fname, "r")))
                    throw std::runtime_error("cannot open " + inputFile + ": " + strerror(errno));
                
                // parse the input-program into c
                parser::GclParser parser(c);
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
