if(NOT TARGET GTest::gtest_main)
    include(FetchContent)
    FetchContent_Declare(
        googletest
        GIT_REPOSITORY https://github.com/google/googletest.git
        GIT_TAG v1.14.0
    )
    set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
    FetchContent_MakeAvailable(googletest)
endif()

if(TARGET numkit AND TARGET numkit_cas_core)
    add_executable(numkit_cas_test
        cas_plugin_test.cpp
    )
    target_include_directories(numkit_cas_test PRIVATE
        ${PROJECT_SOURCE_DIR}
        ${PROJECT_SOURCE_DIR}/include
        ${PROJECT_SOURCE_DIR}/src
        ${PROJECT_SOURCE_DIR}/tests
    )
    target_link_libraries(numkit_cas_test PRIVATE
        numkit_cas_core
        numkit
        GTest::gtest_main
    )
    if(TARGET hwy AND TARGET hwy_contrib)
        target_link_libraries(numkit_cas_test PRIVATE hwy hwy_contrib)
    endif()
    if(TARGET numkit_cas)
        add_dependencies(numkit_cas_test numkit_cas)
    endif()
    if(MSVC)
        target_compile_options(numkit_cas_test PRIVATE /W3 /MP /bigobj)
    endif()
    add_test(NAME numkit_cas_test COMMAND numkit_cas_test)
endif()

if(TARGET numkit_cas)
    add_executable(numkit_cas_c_test
        c_api/cas_c_api.cpp
    )
    target_link_libraries(numkit_cas_c_test PRIVATE numkit_cas GTest::gtest_main)
    add_test(NAME numkit_cas_c_test COMMAND numkit_cas_c_test)
endif()
