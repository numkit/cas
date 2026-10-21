#include <numkit/cas/core/expr.hpp>

#include <unordered_map>

namespace numkit::cas {

Expr Ctx::diff(Expr e, Expr var)
{
    if (e.isNull() || var.isNull())
        return Expr();
    assert(kind(var) == NodeKind::Symbol && "diff variable must be a Symbol");
    std::unordered_map<std::uint32_t, Expr> memo;
    return diffRec(e, var, memo);
}

Expr Ctx::diffRec(Expr e, Expr var, std::unordered_map<std::uint32_t, Expr> &memo)
{
    if (e.isNull())
        return Expr();
    const auto cached = memo.find(id(e));
    if (cached != memo.end())
        return cached->second;

    Expr result;
    switch (kind(e)) {
    case NodeKind::Number:
        result = zero();
        break;
    case NodeKind::Symbol:
        result = (e == var) ? one() : zero();
        break;
    case NodeKind::Add: {
        std::vector<Expr> ds;
        bool failed = false;
        for (std::size_t i = 0; i < childCount(e); ++i) {
            const Expr di = diffRec(child(e, i), var, memo);
            if (di.isNull()) {
                failed = true;
                break;
            }
            ds.push_back(di);
        }
        if (!failed)
            result = add(ds);
        break;
    }
    case NodeKind::Mul: {
        // n-ary product rule: sum_i (d(fi) * prod_{j != i} fj).
        const std::size_t n = childCount(e);
        std::vector<Expr> terms;
        bool failed = false;
        for (std::size_t i = 0; i < n; ++i) {
            const Expr di = diffRec(child(e, i), var, memo);
            if (di.isNull()) {
                failed = true;
                break;
            }
            std::vector<Expr> factors;
            factors.push_back(di);
            for (std::size_t j = 0; j < n; ++j)
                if (j != i)
                    factors.push_back(child(e, j));
            terms.push_back(mul(factors));
        }
        if (!failed)
            result = add(terms);
        break;
    }
    case NodeKind::Pow: {
        const Expr u = child(e, 0);
        const Expr v = child(e, 1);
        if (kind(v) == NodeKind::Number) {
            // d(u^c) = c * u^(c-1) * u'
            const Expr du = diffRec(u, var, memo);
            if (du.isNull())
                break;
            if (isZero(du)) {
                result = zero();
                break;
            }
            const Rational c = numberValue(v);
            result = mul({number(c),
                          pow(u, number(c - Rational(std::int64_t{1}))),
                          du});
        } else if (kind(u) == NodeKind::Number) {
            // d(a^v) = a^v * log(a) * v'
            const Expr dv = diffRec(v, var, memo);
            if (dv.isNull())
                break;
            if (isZero(dv)) {
                result = zero();
                break;
            }
            result = mul({e, func("log", u), dv});
        } else {
            // d(u^v) = u^v * (v' * log(u) + v * u'/u). The guards keep the
            // u^(-1) factor from being built when u is a constant (its
            // evaluation could be singular, e.g. log(0)).
            const Expr du = diffRec(u, var, memo);
            const Expr dv = diffRec(v, var, memo);
            if (du.isNull() || dv.isNull())
                break;
            if (isZero(du) && isZero(dv)) {
                result = zero();
            } else if (isZero(du)) {
                result = mul({e, mul({dv, func("log", u)})});
            } else {
                result = mul({e,
                              add({mul({dv, func("log", u)}),
                                   mul({v, mul({du, pow(u, number(std::int64_t{-1}))})})})});
            }
        }
        break;
    }
    case NodeKind::RootOf:
        result = zero();
        break;
    case NodeKind::Func: {
        const Expr u = child(e, 0);
        const Expr du = diffRec(u, var, memo);
        if (du.isNull())
            break;
        if (isZero(du)) {
            result = zero();
            break;
        }
        const std::string &name = funcName(e);
        if (name == "sqrt")
            result = mul({number(Rational(std::int64_t{1}, BigInt(2))),
                          pow(u, number(Rational(std::int64_t{-1}, BigInt(2)))),
                          du});
        else if (name == "exp")
            result = mul({e, du});
        else if (name == "log")
            result = mul({du, pow(u, number(std::int64_t{-1}))});
        else if (name == "sin")
            result = mul({func("cos", u), du});
        else if (name == "cos")
            result = mul({neg(func("sin", u)), du});
        else if (name == "tan")
            result = mul({du, add({one(), pow(e, number(std::int64_t{2}))})});
        else if (name == "cot")
            result = neg(mul({du, add({one(), pow(e, number(std::int64_t{2}))})}));
        else if (name == "sec")
            result = mul({e, func("tan", u), du});
        else if (name == "csc")
            result = neg(mul({e, func("cot", u), du}));
        else if (name == "atan")
            result = mul({du, pow(add({one(), pow(u, number(std::int64_t{2}))}),
                                  number(std::int64_t{-1}))});
        else if (name == "acot")
            result = neg(mul({du, pow(add({one(), pow(u, number(std::int64_t{2}))}),
                                      number(std::int64_t{-1}))}));
        else if (name == "asin")
            result = mul({du, pow(add({one(), neg(pow(u, number(std::int64_t{2})))}),
                                  number(Rational(std::int64_t{-1}, BigInt(2))))});
        else if (name == "acos")
            result = neg(mul({du, pow(add({one(), neg(pow(u, number(std::int64_t{2})))}),
                                      number(Rational(std::int64_t{-1}, BigInt(2))))}));
        else if (name == "sinh")
            result = mul({func("cosh", u), du});
        else if (name == "cosh")
            result = mul({func("sinh", u), du});
        else if (name == "tanh")
            result = mul({du, add({one(), neg(pow(e, number(std::int64_t{2})))})});
        else if (name == "coth")
            result = mul({du, add({one(), neg(pow(e, number(std::int64_t{2})))})});
        else if (name == "sech")
            result = neg(mul({e, func("tanh", u), du}));
        else if (name == "csch")
            result = neg(mul({e, func("coth", u), du}));
        else if (name == "asinh")
            result = mul({du, pow(add({one(), pow(u, number(std::int64_t{2}))}),
                                  number(Rational(std::int64_t{-1}, BigInt(2))))});
        else if (name == "acosh")
            result = mul({du, pow(add({number(std::int64_t{-1}), pow(u, number(std::int64_t{2}))}),
                                  number(Rational(std::int64_t{-1}, BigInt(2))))});
        else if (name == "atanh")
            result = mul({du, pow(add({one(), neg(pow(u, number(std::int64_t{2})))}),
                                  number(std::int64_t{-1}))});
        else if (name == "erf")
            result = mul({number(std::int64_t{2}),
                          pow(symbol("pi"),
                              number(Rational(std::int64_t{-1}, BigInt(2)))),
                          func("exp", neg(pow(u, number(std::int64_t{2})))),
                          du});
        else if (name == "erfc")
            result = neg(mul({number(std::int64_t{2}),
                              pow(symbol("pi"),
                                  number(Rational(std::int64_t{-1}, BigInt(2)))),
                              func("exp", neg(pow(u, number(std::int64_t{2})))),
                              du}));
        else if (name == "erfi")
            result = mul({number(std::int64_t{2}),
                          pow(symbol("pi"),
                              number(Rational(std::int64_t{-1}, BigInt(2)))),
                          func("exp", pow(u, number(std::int64_t{2}))),
                          du});
        else if (name == "Ei")
            result = mul({func("exp", u), pow(u, number(std::int64_t{-1})), du});
        else if (name == "li")
            result = mul(
                {pow(func("log", u), number(std::int64_t{-1})), du});
        else if (name == "Si")
            result = mul({func("sin", u), pow(u, number(std::int64_t{-1})), du});
        else if (name == "Ci")
            result = mul({func("cos", u), pow(u, number(std::int64_t{-1})), du});
        else if (name == "FresnelS")
            result = mul(
                {func("sin", mul({number(Rational(std::int64_t{1}, BigInt(2))),
                                  symbol("pi"),
                                  pow(u, number(std::int64_t{2}))})),
                 du});
        else if (name == "FresnelC")
            result = mul(
                {func("cos", mul({number(Rational(std::int64_t{1}, BigInt(2))),
                                  symbol("pi"),
                                  pow(u, number(std::int64_t{2}))})),
                 du});
        else if (name == "dilog" || name == "Li2" || name == "polylog2")
            result = neg(mul({func("log", add({one(), neg(u)})),
                              pow(u, number(std::int64_t{-1})), du}));
        else {
            assert(!"diff: unsupported function");
            result = Expr();
        }
        break;
    }
    }

    memo.emplace(id(e), result);
    return result;
}

} // namespace numkit::cas
