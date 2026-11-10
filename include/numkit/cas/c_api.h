/* include/numkit/cas/c_api.h
 *
 * Self-contained C-ABI for the `numkit/cas` toolbox.
 *
 * Supports both:
 *   1. Pre-resolved O(1) dispatch (`numkit_cas_resolve` + `numkit_cas_invoke`)
 *      with zero string hashing on the hot path.
 *   2. Dynamic name/method dispatch (`numkit_cas_call`) for MATLAB overloads,
 *      Name-Value pairs, and toolbox object methods.
 */
#ifndef NUMKIT_CAS_C_API_H
#define NUMKIT_CAS_C_API_H

#include <numkit/value/c_api.h>

#ifdef __cplusplus
extern "C" {
#endif

#if defined(_WIN32) || defined(__CYGWIN__)
#  if defined(NUMKIT_PLUGIN_BUILD)
#    define NUMKIT_CAS_API __declspec(dllexport)
#  elif defined(NUMKIT_CAS_STATIC)
#    define NUMKIT_CAS_API
#  else
#    define NUMKIT_CAS_API __declspec(dllimport)
#  endif
#else
#  if defined(__GNUC__) && __GNUC__ >= 4
#    define NUMKIT_CAS_API __attribute__((visibility("default")))
#  else
#    define NUMKIT_CAS_API
#  endif
#endif

/* Opaque isolated `cas` toolbox context */
typedef struct numkit_cas_ctx_s numkit_cas_ctx;

/* Create an isolated `cas` toolbox context (engine-free, zero interpreter overhead). */
NUMKIT_CAS_API numkit_cas_ctx *numkit_cas_ctx_create(numkit_error *err);

/* Destroy `cas` toolbox context and release its resources. */
NUMKIT_CAS_API void numkit_cas_ctx_destroy(numkit_cas_ctx *ctx);

/* Seed the `cas` context's random number stream (MATLAB `rng(seed)` semantics). */
NUMKIT_CAS_API void numkit_cas_seed_rng(numkit_cas_ctx *ctx, uint64_t seed);

/* Return 1 if function `name` is registered in `cas`, 0 otherwise. */
NUMKIT_CAS_API int numkit_cas_has_function(const numkit_cas_ctx *ctx, const char *name);

/* Register a host-language callback (`numkit_host_fn`) into this context. */
NUMKIT_CAS_API int numkit_cas_register_fn(numkit_cas_ctx *ctx,
                                            const char *name,
                                            numkit_host_fn fn,
                                            void *user_data,
                                            numkit_error *err);

/* Resolve function `name` once into an O(1) function pointer (`NULL` if not found). */
NUMKIT_CAS_API const numkit_fn *numkit_cas_resolve(const numkit_cas_ctx *ctx,
                                                     const char *name);

/* Invoke a pre-resolved function pointer directly with zero lookup overhead. */
NUMKIT_CAS_API int numkit_cas_invoke(numkit_cas_ctx *ctx,
                                       const numkit_fn *fn,
                                       const numkit_val *const *args,
                                       size_t nargs,
                                       size_t nargout,
                                       numkit_val **outs,
                                       numkit_error *err);

/* Dynamically invoke `cas` function or object method `name`. */
NUMKIT_CAS_API int numkit_cas_call(numkit_cas_ctx *ctx,
                                     const char *name,
                                     const numkit_val *const *args,
                                     size_t nargs,
                                     size_t nargout,
                                     numkit_val **outs,
                                     numkit_error *err);

/* Format a value or `cas` class object (e.g. `sym`, `tf`, `ss`) to UTF-8 text. */
NUMKIT_CAS_API size_t numkit_cas_format(const numkit_cas_ctx *ctx,
                                          const numkit_val *v,
                                          char *buf,
                                          size_t buf_cap);

#ifdef __cplusplus
}
#endif

#endif /* NUMKIT_CAS_C_API_H */
