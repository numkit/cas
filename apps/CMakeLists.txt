add_executable(nkcas nkcas.cpp corpus_runner.cpp)
target_link_libraries(nkcas PRIVATE numkit::cas)
