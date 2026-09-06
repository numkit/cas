add_library(numkit_cas STATIC
    num/bigint.cpp
    num/rational.cpp
)

add_library(numkit::cas ALIAS numkit_cas)

target_include_directories(numkit_cas
    PUBLIC ${PROJECT_SOURCE_DIR}/include
)

target_compile_features(numkit_cas PUBLIC cxx_std_17)
