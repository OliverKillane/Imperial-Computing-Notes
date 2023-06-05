cmake_minimum_required(VERSION 3.14)
project(Partition-Benchmarks)

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

add_executable(${PROJECT_NAME} benchmarks.cpp)
target_link_libraries(${PROJECT_NAME} benchmark::benchmark)