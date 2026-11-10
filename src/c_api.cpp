// src/c_api.cpp
//
// Self-contained C-ABI implementation for `numkit/cas`.
#include <numkit/cas/c_api.h>
#include <numkit/cas/library.hpp>
#include <numkit/sys/lite_context.hpp>
#include <numkit/value/c_api_bridge.hpp>

#include <algorithm>
#include <cstring>
#include <exception>
#include <string>
#include <vector>

struct numkit_cas_ctx_s {
    numkit::sys::LitePluginContext ctx;

    numkit_cas_ctx_s() : ctx(nullptr)
    {
        numkit::CasLibrary::install(ctx);
    }
};

namespace {

constexpr const char *kToolboxNs = "cas";

template <typename InvokeFn>
int runDispatch(const numkit_val *const *args,
                size_t nargs,
                size_t nargout,
                numkit_val **outs,
                numkit_error *err,
                InvokeFn &&doInvoke) noexcept
{
    using numkit::Span;
    using numkit::Value;
    using numkit::c_abi::boxValue;
    using numkit::c_abi::clearError;
    using numkit::c_abi::setError;
    using numkit::c_abi::unboxValue;

    clearError(err);
    try {
        if (nargout > 0 && !outs) {
            setError(err, 1, "outs array must be non-null when nargout > 0");
            return 1;
        }

        Value inStack[8];
        std::vector<Value> inHeap;
        Value *inPtr = inStack;
        if (nargs > 8) {
            inHeap.resize(nargs);
            inPtr = inHeap.data();
        }
        for (size_t i = 0; i < nargs; ++i) {
            inPtr[i] = args && args[i] ? unboxValue(args[i]) : Value::Empty;
        }

        size_t outSlots = nargout == 0 ? 1 : nargout;
        Value outStack[4];
        std::vector<Value> outHeap;
        Value *outPtr = outStack;
        if (outSlots > 4) {
            outHeap.resize(outSlots);
            outPtr = outHeap.data();
        }

        doInvoke(Span<const Value>(inPtr, nargs), nargout, Span<Value>(outPtr, outSlots));

        for (size_t i = 0; i < nargout; ++i) {
            outs[i] = boxValue(std::move(outPtr[i]));
        }
        return 0;
    } catch (const std::exception &ex) {
        setError(err, 1, ex.what());
        return 1;
    } catch (...) {
        setError(err, 1, "Unknown C++ exception in numkit_cas");
        return 1;
    }
}

} // namespace

extern "C" {

numkit_cas_ctx *numkit_cas_ctx_create(numkit_error *err)
{
    numkit::c_abi::clearError(err);
    try {
        return new numkit_cas_ctx_s();
    } catch (const std::exception &ex) {
        numkit::c_abi::setError(err, 1, ex.what());
        return nullptr;
    }
}

void numkit_cas_ctx_destroy(numkit_cas_ctx *ctx)
{
    delete ctx;
}

void numkit_cas_seed_rng(numkit_cas_ctx *ctx, uint64_t seed)
{
    (void)ctx;
    (void)seed;
}

int numkit_cas_has_function(const numkit_cas_ctx *ctx, const char *name)
{
    if (!ctx || !name || !*name) return 0;
    return ctx->ctx.hasFunction(kToolboxNs, name) ? 1 : 0;
}

int numkit_cas_register_fn(numkit_cas_ctx *ctx,
                            const char *name,
                            numkit_host_fn fn,
                            void *user_data,
                            numkit_error *err)
{
    numkit::c_abi::clearError(err);
    if (!ctx || !name || !*name || !fn) {
        numkit::c_abi::setError(err, 1, "Invalid arguments to numkit_cas_register_fn");
        return 1;
    }
    try {
        auto cb = [fn, user_data](numkit::Span<const numkit::Value> args,
                                  size_t nargout,
                                  numkit::Span<numkit::Value> outs,
                                  numkit::CallContext & /*c*/) {
            numkit::c_abi::invokeHostCallback(fn, user_data, args, nargout, outs);
        };
        ctx->ctx.registerFunction(kToolboxNs, name, std::move(cb));
        return 0;
    } catch (const std::exception &ex) {
        numkit::c_abi::setError(err, 1, ex.what());
        return 1;
    }
}

const numkit_fn *numkit_cas_resolve(const numkit_cas_ctx *ctx, const char *name)
{
    if (!ctx || !name || !*name) return nullptr;
    const numkit::ExternalFunc *fn = ctx->ctx.resolve(kToolboxNs, name);
    return reinterpret_cast<const numkit_fn *>(fn);
}

int numkit_cas_invoke(numkit_cas_ctx *ctx,
                       const numkit_fn *fn,
                       const numkit_val *const *args,
                       size_t nargs,
                       size_t nargout,
                       numkit_val **outs,
                       numkit_error *err)
{
    if (!ctx || !fn) {
        numkit::c_abi::setError(err, 1, "Null context or pre-resolved function pointer");
        return 1;
    }
    const auto *extFn = reinterpret_cast<const numkit::ExternalFunc *>(fn);
    return runDispatch(args, nargs, nargout, outs, err,
                       [&](numkit::Span<const numkit::Value> inSpan,
                           size_t nOut,
                           numkit::Span<numkit::Value> outSpan) {
                           ctx->ctx.invokeResolved(extFn, inSpan, nOut, outSpan);
                       });
}

int numkit_cas_call(numkit_cas_ctx *ctx,
                     const char *name,
                     const numkit_val *const *args,
                     size_t nargs,
                     size_t nargout,
                     numkit_val **outs,
                     numkit_error *err)
{
    if (!ctx || !name || !*name) {
        numkit::c_abi::setError(err, 1, "Null context or empty function name");
        return 1;
    }
    return runDispatch(args, nargs, nargout, outs, err,
                       [&](numkit::Span<const numkit::Value> inSpan,
                           size_t nOut,
                           numkit::Span<numkit::Value> outSpan) {
                           ctx->ctx.invoke(kToolboxNs, name, inSpan, nOut, outSpan);
                       });
}

size_t numkit_cas_format(const numkit_cas_ctx *ctx,
                          const numkit_val *v,
                          char *buf,
                          size_t buf_cap)
{
    if (!ctx || !v) {
        if (buf && buf_cap > 0) buf[0] = '\0';
        return 0;
    }
    try {
        std::string s = ctx->ctx.formatValue(numkit::c_abi::unboxValue(v));
        if (!buf || buf_cap == 0) return s.size();
        size_t n = std::min(s.size(), buf_cap - 1);
        if (n > 0) std::memcpy(buf, s.data(), n);
        buf[n] = '\0';
        return s.size();
    } catch (...) {
        if (buf && buf_cap > 0) buf[0] = '\0';
        return 0;
    }
}

} // extern "C"
