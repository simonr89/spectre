set(QUIT_LOGIC_SOURCES
    Formula.cpp
    Signature.cpp
    Sort.cpp
    Term.cpp
    Theory.cpp
)
set(QUIT_LOGIC_HEADERS
    Formula.hpp
    Signature.hpp
    Sort.hpp
    Term.hpp
    Theory.hpp
)

add_library(logic ${QUIT_LOGIC_SOURCES} ${QUIT_LOGIC_HEADERS})
target_include_directories(logic PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(logic util)
