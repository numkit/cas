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

add_executable(nkcas_gtest
    num/bigint_test.cpp
    num/rational_test.cpp
    num/ifactor_test.cpp
    core/expr_test.cpp
    core/diff_test.cpp
    core/rootof_test.cpp
    core/parser_test.cpp
    core/subs_test.cpp
    core/eval_test.cpp
    core/expand_test.cpp
    core/series_test.cpp
    core/simplify_test.cpp
    core/symsolve_test.cpp
    poly/upoly_test.cpp
    poly/sturm_test.cpp
    poly/solve_test.cpp
    poly/algebraic_test.cpp
    poly/modcpoly_test.cpp
    poly/fppoly_test.cpp
    poly/zassenhaus_test.cpp
    poly/groebner_test.cpp
    integrate/ratint_test.cpp
    linalg/symmatrix_test.cpp
    ode/dsolve_test.cpp
    corpus_runner_test.cpp
    rubi/rules_test.cpp
    transform/fourier_test.cpp
    transform/laplace_test.cpp
    transform/ztrans_test.cpp
    ../apps/corpus_runner.cpp
)

target_include_directories(nkcas_gtest PRIVATE ${PROJECT_SOURCE_DIR}/apps)
target_link_libraries(nkcas_gtest PRIVATE numkit::cas GTest::gtest_main)

if(MSVC)
    target_compile_options(nkcas_gtest PRIVATE /MP /bigobj)
endif()

add_test(NAME nkcas_gtest COMMAND nkcas_gtest)

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
