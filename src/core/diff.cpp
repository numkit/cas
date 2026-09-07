#include <numkit/cas/core/expr.hpp>

#include <unordered_map>

namespace numkit::cas {

Expr Ctx::diff(Expr e, Expr var)
{
    assert(kind(var) == NodeKind::Symbol && "diff variable must be a Symbol");
    std::unordered_map<std::uint32_t, Expr> memo;
    return diffRec(e, var, memo);
}

Expr Ctx::diffRec(Expr e, Expr var, std::unordered_map<std::uint32_t, Expr> &memo)
{
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
        for (std::size_t i = 0; i < childCount(e); ++i)
            ds.push_back(diffRec(child(e, i), var, memo));
        result = add(ds);
        break;
    }
    case NodeKind::Mul: {
        // n-ary product rule: sum_i (d(fi) * prod_{j != i} fj).
        const std::size_t n = childCount(e);
        std::vector<Expr> terms;
        for (std::size_t i = 0; i < n; ++i) {
            std::vector<Expr> factors;
            factors.push_back(diffRec(child(e, i), var, memo));
            for (std::size_t j = 0; j < n; ++j)
                if (j != i)
                    factors.push_back(child(e, j));
            terms.push_back(mul(factors));
        }
        result = add(terms);
        break;
    }
    case NodeKind::Pow: {
        const Expr u = child(e, 0);
        const Expr v = child(e, 1);
        if (kind(v) == NodeKind::Number) {
            // d(u^c) = c * u^(c-1) * u'
            const Expr du = diffRec(u, var, memo);
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
        if (isZero(du)) {
            result = zero();
            break;
        }
        const std::string &name = funcName(e);
        if (name == "exp")
            result = mul({e, du});
        else if (name == "log")
            result = mul({du, pow(u, number(std::int64_t{-1}))});
        else if (name == "sin")
            result = mul({func("cos", u), du});
        else if (name == "cos")
            result = mul({neg(func("sin", u)), du});
        else if (name == "tan")
            result = mul({du, add({one(), pow(e, number(std::int64_t{2}))})});
        else if (name == "atan")
            result = mul({du, pow(add({one(), pow(u, number(std::int64_t{2}))}),
                                  number(std::int64_t{-1}))});
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
