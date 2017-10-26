#ifndef __Output__
#define __Output__

#include <ostream>
#include <streambuf>

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

    // stream manipulators to add '%' at the start of each line (TPTP
    // comments)
    static std::ostream& comment(std::ostream& str);
    static std::ostream& nocomment(std::ostream& str);

  private:
    static std::ostream* _stream;

    static bool _isFile;

    // in any ostream, the value of the iword stored at this index is
    // 0 or 1. If 1, the streambuf of the stream is a
    // CommentingStreamBuf
    static int _commentIndex;
  };

  class CommentingStreambuf : public std::streambuf
  {
  public:
    
    CommentingStreambuf(std::streambuf* dest) :
      _dest(dest),
      _atLineStart(true)
    {}

    ~CommentingStreambuf() {}

    std::streambuf* dest() { return _dest; }

  protected:
    int overflow(int c) override;

    int underflow() override { return EOF; }

    std::streambuf* _dest;

    bool _atLineStart;
  };
  
}

#endif
