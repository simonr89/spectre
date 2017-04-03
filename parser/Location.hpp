#ifndef __ParseLocation__
#define __ParseLocation__

#include <cstring>
#include <algorithm> // std::max
#include <iostream>

namespace parser {
  /// Abstract a position.
  class Position
  {
  public:

    /// Construct a position.
    explicit Position (std::string* f = nullptr,
                       unsigned int l = 1u,
                       unsigned int c = 1u)
      : filename (f)
      , line (l)
      , column (c)
    {
    }


    /// Initialization.
    void initialize (std::string* fn = nullptr,
                     unsigned int l = 1u,
                     unsigned int c = 1u)
    {
      filename = fn;
      line = l;
      column = c;
    }

    /** \name Line and Column related manipulators
     ** \{ */
    /// (line related) Advance to the COUNT next lines.
    void lines (int count = 1)
    {
      if (count)
        {
          column = 1u;
          line = add_ (line, count, 1);
        }
    }

    /// (column related) Advance to the COUNT next columns.
    void columns (int count = 1)
    {
      column = add_ (column, count, 1);
    }
    /** \} */

    /// File name to which this position refers.
    std::string* filename;
    /// Current line number.
    unsigned int line;
    /// Current column number.
    unsigned int column;

  private:
    /// Compute max(min, lhs+rhs) (provided min <= lhs).
    static unsigned int add_ (unsigned int lhs, int rhs, unsigned int min)
    {
      return (0 < rhs || -static_cast<unsigned int>(rhs) < lhs
              ? rhs + lhs
              : min);
    }
  };

  /// Add and assign a position.
  inline Position&
  operator+= (Position& res, int width)
  {
    res.columns (width);
    return res;
  }

  /// Add two position objects.
  inline Position
  operator+ (Position res, int width)
  {
    return res += width;
  }

  /// Add and assign a position.
  inline Position&
  operator-= (Position &res, int width)
  {
    return res += -width;
  }

  /// Add two position objects.
  inline Position
  operator- (Position res, int width)
  {
    return res -= width;
  }

  /// Compare two position objects.
  inline bool
  operator== (const Position& pos1, const Position& pos2)
  {
    return (pos1.line == pos2.line
            && pos1.column == pos2.column
            && (pos1.filename == pos2.filename
                || (pos1.filename && pos2.filename
                    && *pos1.filename == *pos2.filename)));
  }

  /// Compare two position objects.
  inline bool
  operator!= (const Position& pos1, const Position& pos2)
  {
    return !(pos1 == pos2);
  }

  /** \brief Intercept output stream redirection.
   ** \param ostr the destination output stream
   ** \param pos a reference to the position to redirect
   */
  template <typename YYChar>
  inline std::basic_ostream<YYChar>&
  operator<< (std::basic_ostream<YYChar>& ostr, const Position& pos)
  {
    if (pos.filename)
      ostr << *pos.filename << ':';
    return ostr << pos.line << '.' << pos.column;
  }

  /// Abstract a location.
  class Location
  {
  public:
    /// Construct a location from \a b to \a e.
    Location (const Position& b, const Position& e)
      : begin (b)
      , end (e)
    {
    }

    /// Construct a 0-width location in \a p.
    explicit Location (const Position& p = Position ())
      : begin (p)
      , end (p)
    {
    }

    /// Construct a 0-width location in \a f, \a l, \a c.
    explicit Location (std::string* f,
                       unsigned int l = 1u,
                       unsigned int c = 1u)
      : begin (f, l, c)
      , end (f, l, c)
    {
    }


    /// Initialization.
    void initialize (std::string* f = nullptr,
                     unsigned int l = 1u,
                     unsigned int c = 1u)
    {
      begin.initialize (f, l, c);
      end = begin;
    }

    // \name Line and Column related manipulators
  public:
    /// Reset initial location to final location.
    void step ()
    {
      begin = end;
    }

    /// Extend the current location to the COUNT next columns.
    void columns (int count = 1)
    {
      end += count;
    }

    /// Extend the current location to the COUNT next lines.
    void lines (int count = 1)
    {
      end.lines (count);
    }


  public:
    /// Beginning of the located region.
    Position begin;
    /// End of the located region.
    Position end;
  };

  /// Join two location objects to create a location.
  inline Location operator+ (Location res, const Location& end)
  {
    res.end = end.end;
    return res;
  }

  /// Change end position in place.
  inline Location& operator+= (Location& res, int width)
  {
    res.columns (width);
    return res;
  }

  /// Change end position.
  inline Location operator+ (Location res, int width)
  {
    return res += width;
  }

  /// Change end position in place.
  inline Location& operator-= (Location& res, int width)
  {
    return res += -width;
  }

  /// Change end position.
  inline Location operator- (const Location& begin, int width)
  {
    return begin + -width;
  }

  /// Compare two location objects.
  inline bool
  operator== (const Location& loc1, const Location& loc2)
  {
    return loc1.begin == loc2.begin && loc1.end == loc2.end;
  }

  /// Compare two location objects.
  inline bool
  operator!= (const Location& loc1, const Location& loc2)
  {
    return !(loc1 == loc2);
  }

  /** \brief Intercept output stream redirection.
   ** \param ostr the destination output stream
   ** \param loc a reference to the location to redirect
   **
   ** Avoid duplicate information.
   */
  template <typename YYChar>
  inline std::basic_ostream<YYChar>&
  operator<< (std::basic_ostream<YYChar>& ostr, const Location& loc)
  {
    unsigned int end_col = 0 < loc.end.column ? loc.end.column - 1 : 0;
    ostr << loc.begin << "(" << loc.end << ") ";
    if (loc.end.filename &&
        (!loc.begin.filename || *loc.begin.filename != *loc.end.filename))
      ostr << '-' << loc.end.filename << ':' << loc.end.line << '.' << end_col;
    else if (loc.begin.line < loc.end.line)
      ostr << '-' << loc.end.line << '.' << end_col;
    else if (loc.begin.column < end_col)
      ostr << '-' << end_col;
    return ostr;
  }

} // Parse

#endif
