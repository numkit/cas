include(FetchContent)

FetchContent_Declare(
    googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG v1.14.0
)
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

add_executable(nkcas_gtest
    num/bigint_test.cpp
    num/rational_test.cpp
    core/expr_test.cpp
    core/diff_test.cpp
    poly/upoly_test.cpp
    poly/sturm_test.cpp
    poly/algebraic_test.cpp
    poly/modcpoly_test.cpp
    poly/fppoly_test.cpp
    integrate/ratint_test.cpp
)

target_link_libraries(nkcas_gtest PRIVATE numkit::cas GTest::gtest_main)

include(GoogleTest)
gtest_discover_tests(nkcas_gtest)
