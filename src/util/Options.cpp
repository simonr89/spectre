#include "Options.hpp"

#include <iostream>

namespace util {

    #define PADDING_WIDTH 20

    bool BooleanOption::setValue(std::string v)
    {
        if (v == "on")
        {
            value = true;
            return true;
        }
        else if (v == "off")
        {
            value = false;
            return true;
        }
        else
        {
            return false;
        }
    }

    std::string BooleanOption::help() const
    {
        std::string s;
        s += name + std::string(PADDING_WIDTH - name.length(), ' ');
        s += "<on|off>";
        return s;
    }

    std::string PathOption::help() const
    {
        std::string s;
        s += name + std::string(PADDING_WIDTH - name.length(), ' ');
        s += "<path>";
        return s;
    }

    bool MultiChoiceOption::setValue(std::string v)
    {
        for (const auto& s : choices)
        {
            if (s == v)
            {
                value = v;
                return true;
            }
        }

        return false;
    }

    std::string MultiChoiceOption::help() const
    {
        std::string s;
        s += name + std::string(PADDING_WIDTH - name.length(), ' ');
        s += "<";

        for (unsigned i = 0; i < choices.size(); i++)
        {
            s += choices[i];
            
            s += (i == choices.size() - 1 ? "" : "|");
        }
        s += ">";
        return s;
    }

    bool Configuration::setAllValues(int argc, char *argv[])
    {
        int i = 1;
        bool b = true;

        // ignore first argument (program name) and last (input file)
        while (i < argc - 1)
        {
            auto it = allOptions.find(std::string(argv[i]));
            if (it != allOptions.end()) {
                if (!(*it).second->setValue(argv[i + 1]))
                {
                    b = false;
                    std::cout << argv[i + 1] << " is not a correct value for option " << argv[i] << std::endl;
                }
            }
            else
            {
                b = false;
                std::cout << "Unknown option " << argv[i] << std::endl;
            }
            i += 2;
        }
        return b;
    }

    void Configuration::registerOption(Option* o)
    {
        allOptions.insert(std::pair<std::string, Option*>(o->name, o));
    }

    std::string Configuration::help() const
    {
        std::string res = "";
        for (const auto& it : allOptions)
        {
            res += it.second->help() + "\n";
        }
        return res;
    }

    Configuration Configuration::theInstance;

}
