set(QUIT_ANALYSIS_SOURCES
    Properties.cpp
    Analyzer.cpp
)
set(QUIT_ANALYSIS_HEADERS
    Properties.hpp
    Analyzer.hpp
)

add_library(analysis ${QUIT_ANALYSIS_SOURCES} ${QUIT_ANALYSIS_HEADERS})
target_include_directories(analysis PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(analysis program logic)
