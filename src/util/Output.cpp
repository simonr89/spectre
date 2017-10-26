#include "Output.hpp"

#include <fstream>
#include <ios>
#include <iostream>
#include <sstream>

#include "util/Options.hpp"

namespace util {

  std::ostream* Output::_stream = nullptr;

  bool Output::_isFile = false;

  int Output::_commentIndex = std::ios_base::xalloc();

  bool Output::initialize() {
    std::string path = util::Configuration::instance().outputFile().getValue();
    if (path == "") {
      _stream = &std::cout;
    } else {
      _stream = new std::ofstream(path, std::ofstream::out);
      if (!*_stream) {
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

  std::ostream& Output::comment(std::ostream& ostr) {
    if (ostr.iword(_commentIndex) != 1) {
      std::streambuf* buf = new CommentingStreambuf(ostr.rdbuf());
      ostr.rdbuf(buf);
      ostr.iword(_commentIndex) = 1;
    }
    return ostr;
  }

  std::ostream& Output::nocomment(std::ostream& ostr) {
    if (ostr.iword(_commentIndex) != 0) {
      CommentingStreambuf* cbuf = static_cast<CommentingStreambuf*>(ostr.rdbuf());
      std::streambuf* dest = cbuf->dest();
      ostr.rdbuf(dest);
      delete cbuf;
      ostr.iword(_commentIndex) = 0;
    }
    return ostr;
  }

  int CommentingStreambuf::overflow(int c)
  {
    if (c == EOF || !_dest) {
      return EOF;
    }
    if (_atLineStart) {
      _dest->sputc('%');
      _dest->sputc(' ');
      _atLineStart = false;
    }
    if (c == '\n') {
      _atLineStart = true;
    }
    return _dest->sputc(c);
  }
  
}
