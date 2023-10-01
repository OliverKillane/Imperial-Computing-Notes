cmake_minimum_required(VERSION 3.22)
project(Functions)

include(FetchContent)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED YES)
set(CMAKE_CXX_EXTENSIONS NO)

add_executable(Examples examples.cpp)
