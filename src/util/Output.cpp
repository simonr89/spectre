#include "Output.hpp"

#include <fstream>
#include <sstream>
#include <ostream>

#include "util/Options.hpp"

namespace util {

  std::ostream* Output::_stream = nullptr;

  bool Output::_isFile = false;

  bool Output::initialize() {
    std::string path = util::Configuration::instance().outputFile().getValue();
    if (path == "") {
      _stream = &std::cout;
    } else {
      _stream = new std::ofstream();
      static_cast<std::ofstream*>(_stream)->open(path);
      if (!static_cast<std::ofstream*>(_stream)->is_open()) {
        std::cerr << "Unable to open file " << path << std::endl;
        return false;
      }
    }
    return true;
  }

  void Output::close() {
    if (_isFile) {
      static_cast<std::ofstream*>(_stream)->close();
      _isFile = false;
    }
    _stream = nullptr;
  }

  /*std::ostream& Output::comment(std::ostream& ostr) {
    return ostr;
    }*/
}
