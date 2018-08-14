set(QUIT_PROGRAM_SOURCES
    Expression.cpp
    GuardedCommandCollection.cpp
    Type.cpp
    Variable.cpp
    Program.cpp
)

set(QUIT_PROGRAM_HEADERS
    Expression.hpp
    GuardedCommandCollection.hpp
    Type.hpp
    Variable.hpp
    Program.hpp
)

add_library(program ${QUIT_PROGRAM_SOURCES} ${QUIT_PROGRAM_HEADERS})
target_include_directories(program PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(program logic util)
