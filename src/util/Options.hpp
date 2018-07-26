#ifndef __Options__
#define __Options__

#include <initializer_list>
#include <map>
#include <vector>
#include <string>

namespace util {
    
    class Option {
    public:       
        // return true if the value was succesfully set
        virtual bool setValue(std::string v) = 0;

        virtual std::string help() const = 0;

        const std::string name;
        
    protected:
        Option(std::string name) :
            name(name)
            {}
       
    };
    
    class BooleanOption : public Option {
    public:
        BooleanOption(std::string name, bool defaultValue) :
            Option(name),
            value(defaultValue)
            {}
        
        bool setValue(std::string v);
        bool getValue() const { return value; }

        std::string help() const;
        
    protected:
        bool value;
    };
    
    class PathOption : public Option {
    public:
        PathOption(std::string name, std::string defaultValue) :
            Option(name),
            value(defaultValue)
            {}
        
        bool setValue(std::string v) { value = v; return true; }
        std::string getValue() const { return value; }

        std::string help() const;
        
    protected:
        std::string value;
    };
    
    class MultiChoiceOption : public Option {
    public:
        MultiChoiceOption(std::string name, std::initializer_list<std::string> choices, std::string defaultValue) :
            Option(name),
            value(defaultValue),
            choices(choices)
            {}
        
        bool setValue(std::string v);
        std::string getValue() const { return value; }

        std::string help() const;
        
    protected:
        std::string value;
        
        const std::vector<std::string> choices;
    };
    
    class Configuration {
    public:
        Configuration() :
            outputFileOpt("output", ""),
            outputFormatOpt("format", {"tptp", "smtlib"}, "smtlib"),
            mainModeOpt("mode", { "generation", "verification", "termination" }, "verification"),
            timepointsOpt("timepoints", false),
            arrayTheoryOpt("arraytheory", false),
            existentialAxiomsOpt("eaxioms", true),
            allOptions()
            {
                registerOption(&outputFileOpt);
                registerOption(&outputFormatOpt);
                registerOption(&mainModeOpt);
                registerOption(&timepointsOpt);
                registerOption(&arrayTheoryOpt);
                registerOption(&existentialAxiomsOpt);
            }
        
        bool setAllValues(int argc, char *argv[]);
        
        Option* getOption(std::string name) const;
        
        std::string help() const;
        
        PathOption outputFile() { return outputFileOpt; }
        MultiChoiceOption outputFormat() { return outputFormatOpt; }
        MultiChoiceOption mainMode() { return mainModeOpt; }
        BooleanOption timepoints() { return timepointsOpt; }
        BooleanOption arrayTheory() { return arrayTheoryOpt; }
        BooleanOption existentialAxioms() { return existentialAxiomsOpt; }

        static Configuration instance() { return theInstance; };
        
    protected:

        PathOption outputFileOpt;
        MultiChoiceOption outputFormatOpt;
        MultiChoiceOption mainModeOpt;
        BooleanOption timepointsOpt;
        BooleanOption arrayTheoryOpt;
        BooleanOption existentialAxiomsOpt;

        static Configuration theInstance;
        
        std::map<const std::string, Option*> allOptions;
        
        void registerOption(Option* o);
    };
}

#endif

