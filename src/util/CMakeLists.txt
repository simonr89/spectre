set(INVGEN_UTIL_SOURCES
    Options.cpp
    Output.cpp
)

set(INVGEN_UTIL_HEADERS
    Options.hpp
    Output.hpp
)

add_library(util ${INVGEN_UTIL_SOURCES} ${INVGEN_UTIL_HEADERS})
target_include_directories(util PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
