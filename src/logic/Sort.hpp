#ifndef __Sort__
#define __Sort__

#include <map>
#include <memory>
#include <string>

namespace logic {
    
#pragma mark - Sort

    class Sort
    {
        // we need each sort to be unique.
        // We therefore use the Sorts-class below as a manager-class for Sort-objects
        friend class Sorts;
        
    private:
        // constructor is private to prevent accidental usage.
        Sort(std::string name) : name(name){};
        
    public:
        const std::string name;
        
        bool operator==(Sort& o);
        
        std::string toTPTP() const;
        
        std::string toSMTLIB() const;
    };
    std::ostream& operator<<(std::ostream& ostr, const Sort& s);
    
    std::string declareSortTPTP(const Sort& s);
    std::string declareSortSMTLIB(const Sort& s);


#pragma mark - Sorts

    // we need each sort to be unique.
    // We therefore use Sorts as a manager-class for Sort-instances
    class Sorts
    {
    public:
        // construct various sorts
        static Sort* boolSort() { return fetchOrDeclare("bool"); }
        static Sort* intSort() { return fetchOrDeclare("int"); }
        static Sort* intArraySort() { return fetchOrDeclare("array_int"); }
        // time can either be represented by int or by a dedicated term algebra sort
        static Sort* timeSort();

        // returns map containing all previously constructed sorts as pairs (nameOfSort, Sort)
        static const std::map<std::string, std::unique_ptr<Sort>>& nameToSort(){return _sorts;};
        
    private:
        static Sort* fetchOrDeclare(std::string name);
        static std::map<std::string, std::unique_ptr<Sort>> _sorts;
    };


    
}

#endif

