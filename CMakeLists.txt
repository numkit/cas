cmake_minimum_required(VERSION 3.21)

project(numkit_cas VERSION 0.10.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
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

if(NOT TARGET keel::bignum)
    find_package(keel_bignum QUIET CONFIG)
    if(TARGET keel::keel_bignum AND NOT TARGET keel::bignum)
        add_library(keel::bignum ALIAS keel::keel_bignum)
    endif()
endif()
if(NOT TARGET keel::bignum)
    set(KEEL_BIGNUM_BUILD_TESTS OFF CACHE BOOL "" FORCE)
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/../../../keelcpp/bignum/CMakeLists.txt" AND NOT DEFINED FETCHCONTENT_SOURCE_DIR_KEEL_BIGNUM)
        set(FETCHCONTENT_SOURCE_DIR_KEEL_BIGNUM "${CMAKE_CURRENT_SOURCE_DIR}/../../../keelcpp/bignum" CACHE PATH "Local keel_bignum checkout")
    endif()
    FetchContent_Declare(
        keel_bignum
        GIT_REPOSITORY https://github.com/keelcpp/bignum.git
        GIT_TAG        71a36b19fcdddc3b205db91343899c68c57b8ebe
    )
    FetchContent_MakeAvailable(keel_bignum)
endif()

add_subdirectory(src)
add_subdirectory(apps)
add_subdirectory(examples)

if(NKCAS_BUILD_TESTS OR NUMKIT_BUILD_TESTS OR NUMKIT_BUILD_C_TESTS)
    enable_testing()
    add_subdirectory(tests)
endif()
