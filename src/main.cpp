#include <iostream>
#include <string>
#include "program/GclAnalyzer.hpp"
#include "util/Options.hpp"

void outputUsage() {
  std::cout << "Usage: invgen <filename>" << std::endl;
}

int main(int argc, char *argv[]) {
  if (argc <= 1) {
    outputUsage();
  } else {
    if (util::Configuration::instance().setAllValues(argc, argv)) {
      std::string inputFile = argv[argc - 1];
      program::GclAnalyzer gcla;
      gcla.parse(inputFile);
    }
    return 0;
  }
}
