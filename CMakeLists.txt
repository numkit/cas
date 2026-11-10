cmake_minimum_required(VERSION 3.21)

project(numkit_cas VERSION 0.10.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

option(NKCAS_BUILD_TESTS "Build the numkit-cas test suite" ON)
option(NUMKIT_BUILD_TESTS "Build GoogleTest suite" OFF)
option(NUMKIT_BUILD_C_TESTS "Build standalone C-ABI GoogleTest suite" OFF)

include(FetchContent)

if(NOT TARGET numkit_value)
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/../value/CMakeLists.txt")
        add_subdirectory("${CMAKE_CURRENT_SOURCE_DIR}/../value" _deps/numkit_value)
    else()
        FetchContent_Declare(
            numkit_value
            GIT_REPOSITORY https://github.com/numkit/value.git
            GIT_TAG main
        )
        FetchContent_MakeAvailable(numkit_value)
    endif()
endif()

if(NOT TARGET numkit_sys)
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/../sys/CMakeLists.txt")
        add_subdirectory("${CMAKE_CURRENT_SOURCE_DIR}/../sys" _deps/numkit_sys)
    else()
        FetchContent_Declare(
            numkit_sys
            GIT_REPOSITORY https://github.com/numkit/sys.git
            GIT_TAG main
        )
        FetchContent_MakeAvailable(numkit_sys)
    endif()
endif()

add_subdirectory(src)
add_subdirectory(apps)
add_subdirectory(examples)

if(NKCAS_BUILD_TESTS OR NUMKIT_BUILD_TESTS OR NUMKIT_BUILD_C_TESTS)
    enable_testing()
    add_subdirectory(tests)
endif()
