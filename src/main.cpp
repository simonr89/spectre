#include <fstream>
#include <iostream>
#include <string>

#include "parser/GclParsingContext.hpp"
#include "util/Options.hpp"
#include "util/Output.hpp"

#include "parser/GclParser.hpp"

#include "analysis/Analyzer.hpp"
#include "analysis/Properties.hpp"

#include "program/Program.hpp"

extern FILE *yyin;
extern bool yy_flex_debug;

void outputUsage()
{
    std::cout << "Usage: spectre <options> <filename>" << std::endl;
    std::cout << std::endl;
    std::cout << "Options:" << std::endl;
    std::cout << util::Configuration::instance().help() << std::endl;
}

int main(int argc, char *argv[])
{
    if (argc <= 1)
    {
        outputUsage();
    }
    else
    {
        if (util::Configuration::instance().setAllValues(argc, argv))
        {
            if (util::Output::initialize())
            {
                std::string inputFile = argv[argc - 1];

                // test readbility, easier than catching exception thrown by parser
                std::ifstream istr(inputFile);
                if (!istr)
                {
                    std::cerr << "Unable to read file " << inputFile << std::endl;
                    return 0;
                }

                // TODO: switch between parsers here
                std::unique_ptr<program::Program> p;
                if (true)
                {
                    // set input for parser
                    // TODO: remove double checking of file,move setting yyin into parser?
                    const char *fname = inputFile.c_str();
                    yy_flex_debug = false;
                    yyin = fopen(fname, "r");

                    // generate a context, whose fields are used as in/out-parameters for parsing
                    parser::GclParsingContext c;
                    c.inputFile = inputFile;

                    // parse the input-program into c
                    parser::GclParser parser(c);
                    parser.set_debug_level(false); // no traces
                    parser.parse();
                    fclose(yyin);

                    if (!c.errorFlag)
                    {
                        p = c.generateProgram();
                    }
                    else
                    {
                        exit(1);
                    }
                }
                assert(p);
                util::Output::stream() << util::Output::comment;
                util::Output::stream() << *p;
                util::Output::stream() << util::Output::nocomment;

                // run lightweight analysis
                program::Analyzer a(*p);
                program::AnalyzerResult aRes = a.computeVariableProperties();

                // TODO print result of analysis for each variable

                // create properties and dump them to TPTP/SMTLIB
                program::Properties props(*p, aRes);
                if (util::Configuration::instance().mainMode().getValue() == "postcondition")
                {
                    props.outputPostConditionForInvariantMode();
                    return 0;
                }
                
                props.analyze();

                if (util::Configuration::instance().outputFormat().getValue() == "tptp")
                {
                    props.outputTPTP();
                }
                else
                {
                    assert(util::Configuration::instance().outputFormat().getValue() == "smtlib" ||
                           util::Configuration::instance().outputFormat().getValue() == "smtlib-vext");
                    props.outputSMTLIB();
                }
            }
        }
        return 0;
    }
}
