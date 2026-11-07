cmake_minimum_required(VERSION 3.21)

project(numkit_cas VERSION 0.10.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

option(NKCAS_BUILD_TESTS "Build the numkit-cas test suite" ON)
option(NUMKIT_BUILD_TESTS "Build GoogleTest suite" OFF)

# When built standalone inside a multi-module checkout, pull in local value & sys if available.
if(NOT TARGET numkit_value AND EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/../value/CMakeLists.txt")
    add_subdirectory("${CMAKE_CURRENT_SOURCE_DIR}/../value" _deps/numkit_value)
endif()
if(NOT TARGET numkit_sys AND EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/../sys/CMakeLists.txt")
    add_subdirectory("${CMAKE_CURRENT_SOURCE_DIR}/../sys" _deps/numkit_sys)
endif()

add_subdirectory(src)
add_subdirectory(apps)
add_subdirectory(examples)

if(NKCAS_BUILD_TESTS OR NUMKIT_BUILD_TESTS)
    enable_testing()
    add_subdirectory(tests)
endif()
