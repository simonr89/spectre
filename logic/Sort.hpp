#ifndef __Sort__
#define __Sort__

#include <list>
#include <string>

namespace logic {

  enum class DefaultSort {
    SRT_INT,
    SRT_BOOL
  };
  
  class Sort {
  public:
    Sort(std::string name) :
      _userDefined(true),
      _name(name)
    {}

    ~Sort() {}
    
    std::string name() const;

    static Sort* boolSort();
    static Sort* intSort();

    bool operator==(Sort& o);
    
  protected:
    Sort(DefaultSort d) :
      _userDefined(false),
      _d(d)
    {}
    
    bool _userDefined;
    DefaultSort _d;
    std::string _name;
  };

  std::ostream& operator<<(std::ostream& ostr, const Sort& s);

}

#endif
