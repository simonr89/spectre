cmake_minimum_required (VERSION 3.6.3)

################################################################
project (QuIt)
################################################################

# require the compiler to use C++14
set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# compiler flags
set(CMAKE_CXX_FLAGS "-Wfatal-errors")

# debug and release mode flags
if(NOT CMAKE_BUILD_TYPE)
   set(CMAKE_BUILD_TYPE "Release" CACHE STRING
       "Choose the type of build, options are: Debug Release"
       FORCE)
endif(NOT CMAKE_BUILD_TYPE)
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -o0")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -DNDEBUG")

# add directoy, where we store all custom files for finding libraries which are not build using cmake (i.e. currently nothing), to the search path of cmake
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/")

# add top level directory to the search path of compiler
include_directories(${CMAKE_CURRENT_SOURCE_DIR})

# Set the output folder where the binary will be created (i.e. build/dir)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

add_executable(quit src/main.cpp)


add_subdirectory(src/analysis)
add_subdirectory(src/logic)
add_subdirectory(src/parser)
add_subdirectory(src/program)
add_subdirectory(src/util)

target_link_libraries(quit analysis logic parser program util)
