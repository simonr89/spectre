set(INVGEN_PROGRAM_SOURCES
    Expression.cpp
    GuardedCommandCollection.cpp
    Type.cpp
    Variable.cpp
    Assignment.cpp
)

set(INVGEN_PROGRAM_HEADERS
    Expression.hpp
    GuardedCommandCollection.hpp
    Type.hpp
    Variable.hpp
    Assignment.hpp
)

add_library(program ${INVGEN_PROGRAM_SOURCES} ${INVGEN_PROGRAM_HEADERS})
target_include_directories(program PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(program logic util)
