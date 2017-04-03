#include <iostream>
#include <string>
#include "program/GclAnalyzer.hpp"

int main(int argc, char *argv[]) {
  if (argc <= 1) {
    if (argv[0]) {
      std::cout << "Usage: " << argv[0] << " <filename>" << std::endl;
    } else {
      std::cout << "Usage: invgen <filename>" << std::endl;
    }
  } else {
    std::string f = argv[1];
    program::GclAnalyzer gcla;
    gcla.parse(f);
    return 0;
  }
}
