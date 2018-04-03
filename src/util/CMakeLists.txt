set(SPECTRE_UTIL_SOURCES
    Options.cpp
    Output.cpp
)

set(SPECTRE_UTIL_HEADERS
    Options.hpp
    Output.hpp
)

add_library(util ${SPECTRE_UTIL_SOURCES} ${SPECTRE_UTIL_HEADERS})
target_include_directories(util PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
