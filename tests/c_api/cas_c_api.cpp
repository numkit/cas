#include <numkit/cas/c_api.h>
#include <gtest/gtest.h>
#include <string>

TEST(NumkitCasCApi, SymbolicIntegrationAndFormat)
{
    const int64_t base = numkit_debug_live_values();
    numkit_error err{};
    numkit_cas_ctx *ctx = numkit_cas_ctx_create(&err);
    ASSERT_NE(ctx, nullptr) << err.message;

    numkit_val *exprStr = numkit_val_char("2*x + 3");
    numkit_val *varStr = numkit_val_char("x");
    const numkit_val *s1[1] = {exprStr};
    const numkit_val *s2[1] = {varStr};
    numkit_val *f = nullptr, *x = nullptr;
    ASSERT_EQ(numkit_cas_call(ctx, "sym", s1, 1, 1, &f, &err), 0) << err.message;
    ASSERT_EQ(numkit_cas_call(ctx, "sym", s2, 1, 1, &x, &err), 0) << err.message;

    const numkit_val *intArgs[2] = {f, x};
    numkit_val *F = nullptr;
    ASSERT_EQ(numkit_cas_call(ctx, "int", intArgs, 2, 1, &F, &err), 0) << err.message;

    char buf[128]{};
    ASSERT_GT(numkit_cas_format(ctx, F, buf, sizeof(buf)), 0u);
    EXPECT_NE(std::string(buf).find("x^2"), std::string::npos);

    numkit_val_release(F);
    numkit_val_release(x);
    numkit_val_release(f);
    numkit_val_release(varStr);
    numkit_val_release(exprStr);
    numkit_cas_ctx_destroy(ctx);
    EXPECT_EQ(numkit_debug_live_values(), base);
}
