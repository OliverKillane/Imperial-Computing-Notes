cmake_minimum_required(VERSION 3.22)
project(Bitmaps)

include(FetchContent)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED YES)
set(CMAKE_CXX_EXTENSIONS NO)

FetchContent_Declare(
    googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG main
)

FetchContent_Declare(
    googlebenchmark
    GIT_REPOSITORY https://github.com/google/benchmark.git
    GIT_TAG main
)


FetchContent_MakeAvailable(
    googletest
    googlebenchmark
)

# Setup for CRoaring
# FetchContent_Declare(
#   roaring
#   GIT_REPOSITORY https://github.com/RoaringBitmap/CRoaring.git
#   GIT_TAG v0.2.66
#   GIT_SHALLOW TRUE)
# set(ENABLE_ROARING_TESTS OFF CACHE INTERNAL "")
# set(ROARING_BUILD_STATIC ON CACHE INTERNAL "")
# FetchContent_MakeAvailable(roaring)
# FetchContent_GetProperties(roaring)
# SET(CPP_ROARING_HEADERS ${roaring_SOURCE_DIR}/cpp/roaring64map.hh  ${roaring_SOURCE_DIR}/cpp/roaring.hh)
# file(COPY ${CPP_ROARING_HEADERS} DESTINATION ${roaring_SOURCE_DIR}/include/roaring)
# can then target_link_libraries(... roaring)

add_executable(Benchmark benchmarks.cpp)
target_link_libraries(Benchmark benchmark::benchmark)

add_executable(Test tests.cpp)
add_library(GTest::GTest INTERFACE IMPORTED)
target_link_libraries(GTest::GTest INTERFACE gtest_main)
target_link_libraries(Test GTest::GTest)

add_executable(Examples examples.cpp)
