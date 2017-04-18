#ifndef __Sort__
#define __Sort__

#include <map>
#include <string>

namespace logic {

  class Sort {
  public:
    ~Sort() {}

    bool isUserDefined() const { return _userDefined; }
    
    std::string name() const { return _name; }

    std::string declareTPTP(std::string decl) const;

    bool operator==(Sort& o);

    // fetch a sort or declare it
    static Sort* getSort(std::string name) { return fetchOrDeclare(name, true); }
    static Sort* defaultSort() { return fetchOrDeclare("$i", false); }
    static Sort* boolSort() { return fetchOrDeclare("$o", false); }
    static Sort* intSort() { return fetchOrDeclare("$int", false); }
    

    class const_iterator {
    public:
      const_iterator(std::map<std::string, Sort*>::const_iterator it) :
        _it(it)
      {}

      ~const_iterator() {}
      
      const Sort& operator*() { return *(*_it).second; }
      
      bool operator==(const_iterator other) { return _it == other._it; }

      bool operator!=(const_iterator other) { return !(_it == other._it); }

      const_iterator & operator++() { ++_it; return (*this); }

    protected:      
      std::map<std::string, Sort*>::const_iterator _it;
    };
    
    static const_iterator sortsBegin() { return const_iterator(_sorts.cbegin()); }
    
    static const_iterator sortsEnd() { return const_iterator(_sorts.cend()); }
    
  protected:
    Sort(std::string name, bool userDefined) :
      _userDefined(userDefined),
      _name(name)
    {
      
    }
    
    bool _userDefined;
    std::string _name;

    static std::map<std::string, Sort*> _sorts;

    static Sort* fetchOrDeclare(std::string name, bool userDefined);
  };

  std::ostream& operator<<(std::ostream& ostr, const Sort& s);

}

#endif
