add_library(numkit_cas STATIC
    num/bigint.cpp
    num/rational.cpp
    core/expr.cpp
    core/diff.cpp
    core/parser.cpp
    core/series.cpp
    core/simplify.cpp
    core/symsolve.cpp
    poly/upoly.cpp
    poly/sturm.cpp
    poly/solve.cpp
    poly/algebraic.cpp
    poly/modcpoly.cpp
    poly/fppoly.cpp
    poly/zassenhaus.cpp
    integrate/ratint.cpp
    integrate/verify.cpp
    linalg/symmatrix.cpp
    ode/dsolve.cpp
    rubi/rules.cpp
)

add_library(numkit::cas ALIAS numkit_cas)

target_include_directories(numkit_cas
    PUBLIC ${PROJECT_SOURCE_DIR}/include
)

target_compile_features(numkit_cas PUBLIC cxx_std_17)
