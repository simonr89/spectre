set(INVGEN_PARSER_SOURCES
    GclParser.cpp
    GclScanner.cpp
    GclParsingContext.cpp
)
set(INVGEN_PARSER_HEADERS
    GclParser.hpp
    GclParsingContext.hpp
)

add_library(parser ${INVGEN_PARSER_SOURCES} ${INVGEN_PARSER_HEADERS})
target_include_directories(parser PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
target_link_libraries(parser program)
