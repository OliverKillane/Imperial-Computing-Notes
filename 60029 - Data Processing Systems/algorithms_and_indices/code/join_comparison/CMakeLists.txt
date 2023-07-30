cmake_minimum_required(VERSION 3.22)
project(Joins)

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


add_executable(Benchmark benchmarks.cpp)
target_link_libraries(Benchmark benchmark::benchmark)

add_executable(Test tests.cpp)
add_library(GTest::GTest INTERFACE IMPORTED)
target_link_libraries(GTest::GTest INTERFACE gtest_main)
target_link_libraries(Test GTest::GTest)

add_executable(Examples examples.cpp)
