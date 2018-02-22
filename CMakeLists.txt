cmake_minimum_required (VERSION 3.6.3)

################################################################
project (Invgen)
################################################################

# require the compiler to use C++11
set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# add directoy, where we store all custom files for finding libraries which are not build using cmake (i.e. currently nothing), to the search path of cmake
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/")

# add top level directory to the search path of compiler
include_directories(${CMAKE_CURRENT_SOURCE_DIR})

# Set the output folder where the binary will be created (i.e. build/dir)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

add_executable(invgen src/main.cpp)
#target_compile_definitions(invgen PRIVATE VZ3=1 CHECK_LEAKS=0)

#set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -D VDEBUG=1") 
#set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -D VDEBUG=0") 



add_subdirectory(src/analysis)
add_subdirectory(src/logic)
add_subdirectory(src/parser)
add_subdirectory(src/program)
add_subdirectory(src/util)

target_link_libraries(invgen analysis logic parser program util)
