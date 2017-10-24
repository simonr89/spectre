#ifndef __Output__
#define __Output__

#include <ios>
#include <iostream>

namespace util {

  class Output
  {
  public:

    // must be called after options have been set
    static bool initialize();

    // call only after initialize()
    static std::ostream& stream() { return *_stream; }

    // must be called before exiting
    static void close();

    //static std::ostream& comment(std::ostream& str);

  private:
    static std::ostream* _stream;

    static bool _isFile;
  };
}

#endif
