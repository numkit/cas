// src/module.cpp
//
// Plugin entry point for numkit_cas dynamic module.
// Exports numkit_plugin_init conforming to NUMKIT_PLUGIN_ABI_VERSION.

#include <numkit/sys/plugin.hpp>
#include <numkit/cas/library.hpp>

extern "C" NUMKIT_PLUGIN_EXPORT bool numkit_plugin_init(numkit::PluginContext &ctx)
{
    if (ctx.abiVersion() != NUMKIT_PLUGIN_ABI_VERSION) {
        return false;
    }
    numkit::CasLibrary::install(ctx);
    return true;
}
