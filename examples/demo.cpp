// examples/demo.cpp — a showcase of what the numkit-cas core can do.
#include <numkit/cas/core/expr.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/num/bigint.hpp>
#include <numkit/cas/num/rational.hpp>
#include <numkit/cas/poly/algebraic.hpp>

#include <cstdio>
#include <string>
#include <vector>

using namespace numkit::cas;

namespace {

void header(const std::string &s)
{
    std::printf("\n=== %s ===\n\n", s.c_str());
}

BigInt factorial(int n)
{
    BigInt r(1);
    for (int i = 2; i <= n; ++i)
        r = r * BigInt(i);
    return r;
}

} // namespace

int main()
{
    header("exact arithmetic");
    std::printf("2^256      = %s\n", BigInt::powUInt(BigInt(2), 256).toString().c_str());
    std::printf("100!       = %s\n", factorial(100).toString().c_str());
    std::printf("1/3 + 1/6  = %s\n",
                (Rational(std::int64_t{1}, BigInt(3)) +
                 Rational(std::int64_t{1}, BigInt(6))).toString().c_str());

    Ctx c;
    const Expr x = c.symbol("x");

    header("expression DAG: canonical form and differentiation");
    const Expr f = c.mul({x, x, c.func("sin", x)});
    std::printf("f      = %s\n", c.toString(f).c_str());
    std::printf("d f    = %s\n", c.toString(c.diff(f, x)).c_str());
    const Expr g = c.pow(c.add({x, c.one()}), c.number(std::int64_t{2}));
    std::printf("g      = %s\n", c.toString(g).c_str());
    std::printf("d g    = %s\n", c.toString(c.diff(g, x)).c_str());
    const Expr h = c.pow(x, x);
    std::printf("h      = %s\n", c.toString(h).c_str());
    std::printf("d h    = %s\n", c.toString(c.diff(h, x)).c_str());

    header("rational integration with PROVED_SYMBOLIC certificates");
    const Expr x2 = c.mul({x, x});
    const Expr x3 = c.mul({x, x, x});
    const Expr q1 = c.add({c.one(), x2});        // 1 + x^2
    const auto integrate = [&](const char *src, Expr f) {
        const RationalIntegral r = integrateRational(c, f, x);
        if (r.proved())
            std::printf("INT %-16s = %-46s [%s]\n", src, c.toString(r.F).c_str(),
                        "PROVED_SYMBOLIC");
        else
            std::printf("INT %-16s : %-46s [%s]\n", src, r.reason.c_str(),
                        "Unevaluated");
    };
    integrate("1/(1+x^2)", c.div(c.one(), q1));
    integrate("x/(1+x^2)", c.div(x, q1));
    integrate("1/(x^3+x)", c.div(c.one(), c.mul({x, q1})));
    integrate("1/(1+x^2)^2", c.div(c.one(), c.pow(q1, c.number(std::int64_t{2}))));
    integrate("1/(1+4x^2)",
              c.div(c.one(), c.add({c.one(), c.mul({c.number(std::int64_t{4}), x2})})));
    integrate("x^3/(1+x^2)", c.div(x3, q1));
    integrate("(3x+1)/(1+x^2)^2",
              c.div(c.add({c.one(), c.mul({c.number(std::int64_t{3}), x})}),
                    c.pow(q1, c.number(std::int64_t{2}))));
    // Outside the M0 splitting scope: honest refusals with reasons.
    integrate("1/(x^3+2)", c.div(c.one(), c.add({c.number(std::int64_t{2}), x3})));
    integrate("1/(2+x^2)", c.div(c.one(), c.add({c.number(std::int64_t{2}), x2})));

    header("the verification loop closes (diff of an integral)");
    const RationalIntegral r0 = integrateRational(c, c.div(c.one(), q1), x);
    std::printf("F        = %s\n", c.toString(r0.F).c_str());
    std::printf("d F      = %s\n", c.toString(c.diff(r0.F, x)).c_str());
    std::printf("f        = %s\n", c.toString(c.div(c.one(), q1)).c_str());

    header("node arena stats");
    std::printf("interned expression nodes: %zu\n", c.nodeCount());
    return 0;
}
