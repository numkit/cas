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
        GIT_TAG        f773bfd14f29ac523f60cf2b6001400026a10d5a
    )
    FetchContent_MakeAvailable(keel_bignum)
endif()

if(NOT TARGET keel::cas)
    find_package(keel_cas QUIET CONFIG)
    if(TARGET keel::keel_cas AND NOT TARGET keel::cas)
        add_library(keel::cas ALIAS keel::keel_cas)
    endif()
endif()
if(NOT TARGET keel::cas)
    set(KEEL_CAS_BUILD_TESTS OFF CACHE BOOL "" FORCE)
    if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/../../../keelcpp/cas/CMakeLists.txt" AND NOT DEFINED FETCHCONTENT_SOURCE_DIR_KEEL_CAS)
        set(FETCHCONTENT_SOURCE_DIR_KEEL_CAS "${CMAKE_CURRENT_SOURCE_DIR}/../../../keelcpp/cas" CACHE PATH "Local keel_cas checkout")
    endif()
    FetchContent_Declare(
        keel_cas
        GIT_REPOSITORY https://github.com/keelcpp/cas.git
        GIT_TAG        9667d80ecac031bf2e351676f6dc2f49608afb1f
    )
    FetchContent_MakeAvailable(keel_cas)
endif()

add_subdirectory(src)
add_subdirectory(apps)
add_subdirectory(examples)

if(NKCAS_BUILD_TESTS OR NUMKIT_BUILD_TESTS OR NUMKIT_BUILD_C_TESTS)
    enable_testing()
    add_subdirectory(tests)
endif()
