set(INVGEN_PROGRAM_SOURCES
    Expression.cpp
    GclAnalyzer.cpp
    GuardedCommandCollection.cpp
    Properties.cpp
    Type.cpp
    Variable.cpp
)

set(INVGEN_PROGRAM_HEADERS
    Expression.hpp
    GclAnalyzer.hpp
    GuardedCommandCollection.hpp
    Properties.hpp
    Type.hpp
    Variable.hpp
)

add_library(program ${INVGEN_PROGRAM_SOURCES} ${INVGEN_PROGRAM_HEADERS})
target_include_directories(program PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(program logic util)
