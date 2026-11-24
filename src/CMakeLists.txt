if(TARGET numkit_value AND TARGET numkit_sys)
    add_library(numkit_cas_core STATIC
        bridge/sym_value.cpp
    )
    add_library(numkit::cas_core ALIAS numkit_cas_core)
    add_library(numkit::cas ALIAS numkit_cas_core)
    set_target_properties(numkit_cas_core PROPERTIES POSITION_INDEPENDENT_CODE ON)

    target_include_directories(numkit_cas_core
        PUBLIC ${PROJECT_SOURCE_DIR}/include
    )
    target_link_libraries(numkit_cas_core PUBLIC numkit_value numkit_sys keel::cas)
    target_compile_features(numkit_cas_core PUBLIC cxx_std_20)

    if(MSVC)
        target_compile_options(numkit_cas_core PRIVATE /MP /bigobj)
    else()
        target_compile_options(numkit_cas_core PRIVATE -fPIC)
    endif()

    # Shared plugin module + self-contained C-ABI
    add_library(numkit_cas SHARED
        register/cas_reg.cpp
        module.cpp
        c_api.cpp
    )
    target_compile_definitions(numkit_cas PRIVATE NUMKIT_PLUGIN_BUILD=1)
    target_include_directories(numkit_cas
        PUBLIC ${PROJECT_SOURCE_DIR}/include
        PRIVATE ${PROJECT_SOURCE_DIR}/src
    )
    target_link_libraries(numkit_cas PUBLIC numkit_cas_core numkit_value numkit_sys numkit_value_c keel::cas)
    target_compile_features(numkit_cas PUBLIC cxx_std_20)

    if(APPLE)
        set_target_properties(numkit_cas PROPERTIES
            BUILD_RPATH "@loader_path;@loader_path/..;@loader_path/../../lib;@loader_path/../../../lib"
            INSTALL_RPATH "@loader_path;@loader_path/../lib"
        )
    elseif(UNIX)
        set_target_properties(numkit_cas PROPERTIES
            BUILD_RPATH "$ORIGIN;$ORIGIN/..;$ORIGIN/../../lib;$ORIGIN/../../../lib"
            INSTALL_RPATH "$ORIGIN;$ORIGIN/../lib"
        )
    endif()

    if(MSVC)
        target_compile_options(numkit_cas PRIVATE /MP /bigobj)
    else()
        target_compile_options(numkit_cas PRIVATE -fPIC)
    endif()
else()
    add_library(numkit_cas INTERFACE)
    add_library(numkit::cas ALIAS numkit_cas)
    target_include_directories(numkit_cas
        INTERFACE ${PROJECT_SOURCE_DIR}/include
    )
    target_link_libraries(numkit_cas INTERFACE keel::cas)
endif()
