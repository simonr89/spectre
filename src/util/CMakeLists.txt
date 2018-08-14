set(QUIT_UTIL_SOURCES
    Options.cpp
    Output.cpp
)

set(QUIT_UTIL_HEADERS
    Options.hpp
    Output.hpp
)

add_library(util ${QUIT_UTIL_SOURCES} ${QUIT_UTIL_HEADERS})
target_include_directories(util PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
