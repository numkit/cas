cmake_minimum_required(VERSION 3.21)

project(numkit_cas VERSION 0.2.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

option(NKCAS_BUILD_TESTS "Build the numkit-cas test suite" ON)

add_subdirectory(src)
add_subdirectory(apps)
add_subdirectory(examples)

if(NKCAS_BUILD_TESTS)
    enable_testing()
    add_subdirectory(tests)
endif()
