/// @file library.hpp
/// @ingroup group_cas
// include/numkit/cas/library.hpp

#pragma once

namespace numkit {

class PluginContext;

class CasLibrary
{
public:
    static void install(PluginContext &engine);
};

} // namespace numkit
