add_executable(nkcas_demo
    demo.cpp
)

target_link_libraries(nkcas_demo PRIVATE numkit::cas)
target_compile_features(nkcas_demo PRIVATE cxx_std_17)
