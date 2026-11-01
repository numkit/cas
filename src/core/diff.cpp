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
        const std::string &name = funcName(e);
        if (childCount(e) == 4 && name == "hypergeom2F1") {
            const Expr a = child(e, 0);
            const Expr b = child(e, 1);
            const Expr cParam = child(e, 2);
            const Expr u = child(e, 3);
            const Expr da = diffRec(a, var, memo);
            const Expr db = diffRec(b, var, memo);
            const Expr dc = diffRec(cParam, var, memo);
            const Expr du = diffRec(u, var, memo);
            if (da.isNull() || db.isNull() || dc.isNull() || du.isNull())
                break;
            if (isZero(da) && isZero(db) && isZero(dc)) {
                if (isZero(du) || isZero(a) || isZero(b)) {
                    result = zero();
                } else {
                    const Expr a1 = add({a, one()});
                    const Expr b1 = add({b, one()});
                    const Expr c1 = add({cParam, one()});
                    result = mul({
                        a, b, pow(cParam, number(std::int64_t{-1})),
                        func("hypergeom2F1", {a1, b1, c1, u}), du});
                }
            }
            break;
        }
        if (childCount(e) == 3 && name == "hypergeom1F1") {
            const Expr a = child(e, 0);
            const Expr b = child(e, 1);
            const Expr u = child(e, 2);
            const Expr da = diffRec(a, var, memo);
            const Expr db = diffRec(b, var, memo);
            const Expr du = diffRec(u, var, memo);
            if (da.isNull() || db.isNull() || du.isNull())
                break;
            if (isZero(da) && isZero(db)) {
                if (isZero(du) || isZero(a)) {
                    result = zero();
                } else {
                    const Expr a1 = add({a, one()});
                    const Expr b1 = add({b, one()});
                    result = mul({
                        a, pow(b, number(std::int64_t{-1})),
                        func("hypergeom1F1", {a1, b1, u}), du});
                }
            }
            break;
        }
        if (childCount(e) == 2) {
            const Expr n = child(e, 0);
            const Expr u = child(e, 1);
            const Expr dn = diffRec(n, var, memo);
            const Expr du = diffRec(u, var, memo);
            if (dn.isNull() || du.isNull())
                break;
            if (isZero(dn) && isZero(du)) {
                result = zero();
                break;
            }
            if (name == "ellipticF" || name == "ellipticEInc" ||
                name == "ellipticE") {
                const Expr half = number(Rational(std::int64_t{1}, BigInt(2)));
                const Expr mHalf = number(Rational(std::int64_t{-1}, BigInt(2)));
                const Expr sinPhi = func("sin", n);
                const Expr cosPhi = func("cos", n);
                const Expr radArg = add({
                    one(),
                    neg(mul({u, pow(sinPhi, number(std::int64_t{2}))}))});
                const Expr fInc = func("ellipticF", n, u);
                const Expr eInc = func("ellipticEInc", n, u);
                std::vector<Expr> totalTerms;
                if (!isZero(dn)) {
                    const Expr dPhi =
                        (name == "ellipticF") ? pow(radArg, mHalf)
                                              : pow(radArg, half);
                    totalTerms.push_back(mul({dPhi, dn}));
                }
                if (!isZero(du)) {
                    const Expr oneMinusM = add({one(), neg(u)});
                    Expr dM;
                    if (name == "ellipticF") {
                        const Expr t1 = mul({
                            half,
                            add({eInc, neg(mul({oneMinusM, fInc}))}),
                            pow(u, number(std::int64_t{-1})),
                            pow(oneMinusM, number(std::int64_t{-1}))});
                        const Expr t2 = neg(mul({
                            half, sinPhi, cosPhi,
                            pow(oneMinusM, number(std::int64_t{-1})),
                            pow(radArg, mHalf)}));
                        dM = add({t1, t2});
                    } else {
                        dM = mul({
                            half,
                            add({eInc, neg(fInc)}),
                            pow(u, number(std::int64_t{-1}))});
                    }
                    totalTerms.push_back(mul({dM, du}));
                }
                result = totalTerms.size() == 1 ? totalTerms[0] : add(totalTerms);
                break;
            }
            if (name == "ellipticPi") {
                const Expr half = number(Rational(std::int64_t{1}, BigInt(2)));
                const Expr km = func("ellipticK", u);
                const Expr em = func("ellipticE", u);
                const Expr mMinusN = add({u, neg(n)});
                const Expr nMinus1 = add({n, number(std::int64_t{-1})});
                const Expr oneMinusM = add({one(), neg(u)});
                std::vector<Expr> totalTerms;
                if (!isZero(dn)) {
                    const Expr numN = add({
                        em,
                        mul({mMinusN, pow(n, number(std::int64_t{-1})), km}),
                        mul({add({pow(n, number(std::int64_t{2})), neg(u)}),
                             pow(n, number(std::int64_t{-1})), e})});
                    const Expr dN = mul({
                        half, numN,
                        pow(mMinusN, number(std::int64_t{-1})),
                        pow(nMinus1, number(std::int64_t{-1}))});
                    totalTerms.push_back(mul({dN, dn}));
                }
                if (!isZero(du)) {
                    const Expr numM = add({em, neg(mul({oneMinusM, e}))});
                    const Expr dM = mul({
                        half, numM,
                        pow(mMinusN, number(std::int64_t{-1})),
                        pow(oneMinusM, number(std::int64_t{-1}))});
                    totalTerms.push_back(mul({dM, du}));
                }
                result = totalTerms.size() == 1 ? totalTerms[0] : add(totalTerms);
                break;
            }
            if (name == "beta") {
                const Expr nPlusU = add({n, u});
                const Expr psiSum = func("digamma", nPlusU);
                std::vector<Expr> totalTerms;
                if (!isZero(dn)) {
                    totalTerms.push_back(mul({
                        e, add({func("digamma", n), neg(psiSum)}), dn}));
                }
                if (!isZero(du)) {
                    totalTerms.push_back(mul({
                        e, add({func("digamma", u), neg(psiSum)}), du}));
                }
                result = totalTerms.size() == 1 ? totalTerms[0] : add(totalTerms);
                break;
            }
            if (name == "pochhammer") {
                const Expr nPlusU = add({n, u});
                const Expr psiSum = func("digamma", nPlusU);
                std::vector<Expr> totalTerms;
                if (!isZero(dn)) {
                    totalTerms.push_back(mul({
                        e, add({psiSum, neg(func("digamma", n))}), dn}));
                }
                if (!isZero(du)) {
                    totalTerms.push_back(mul({e, psiSum, du}));
                }
                result = totalTerms.size() == 1 ? totalTerms[0] : add(totalTerms);
                break;
            }
            if (!isZero(dn))
                break;
            if (name == "igamma") {
                const Expr nm1 = add({n, number(std::int64_t{-1})});
                result = neg(mul({pow(u, nm1), func("exp", neg(u)), du}));
                break;
            }
            if (name == "gammainc") {
                const Expr nm1 = add({n, number(std::int64_t{-1})});
                result = mul({pow(u, nm1), func("exp", neg(u)), du});
                break;
            }
            if (name == "hypergeom0F1") {
                const Expr np1 = add({n, one()});
                result = mul({
                    pow(n, number(std::int64_t{-1})),
                    func("hypergeom0F1", np1, u), du});
                break;
            }
            if (name == "legendreP") {
                if (isZero(n)) {
                    result = zero();
                } else {
                    const Expr nm1 = add({n, number(std::int64_t{-1})});
                    const Expr num = mul({
                        n,
                        add({func("legendreP", nm1, u), neg(mul({u, e}))})});
                    const Expr den =
                        add({one(), neg(pow(u, number(std::int64_t{2})))});
                    result = mul({num, pow(den, number(std::int64_t{-1})), du});
                }
            } else if (name == "chebyshevT") {
                if (isZero(n)) {
                    result = zero();
                } else {
                    const Expr nm1 = add({n, number(std::int64_t{-1})});
                    result = mul({n, func("chebyshevU", nm1, u), du});
                }
            } else if (name == "chebyshevU") {
                if (isZero(n)) {
                    result = zero();
                } else {
                    const Expr np1 = add({n, one()});
                    const Expr num = add({
                        mul({u, e}),
                        neg(mul({np1, func("chebyshevT", np1, u)}))});
                    const Expr den =
                        add({one(), neg(pow(u, number(std::int64_t{2})))});
                    result = mul({num, pow(den, number(std::int64_t{-1})), du});
                }
            } else if (name == "hermiteH") {
                if (isZero(n)) {
                    result = zero();
                } else {
                    const Expr nm1 = add({n, number(std::int64_t{-1})});
                    result = mul({number(std::int64_t{2}), n,
                                  func("hermiteH", nm1, u), du});
                }
            } else if (name == "laguerreL") {
                if (isZero(n)) {
                    result = zero();
                } else {
                    const Expr nm1 = add({n, number(std::int64_t{-1})});
                    const Expr num =
                        mul({n, add({e, neg(func("laguerreL", nm1, u))})});
                    result = mul({num, pow(u, number(std::int64_t{-1})), du});
                }
            } else if (name == "besselj" || name == "bessely" ||
                       name == "besselk") {
                const Expr np1 = add({n, one()});
                const Expr nextF = func(name, np1, u);
                if (isZero(n)) {
                    result = mul({neg(nextF), du});
                } else {
                    result = mul({
                        add({mul({n, pow(u, number(std::int64_t{-1})), e}),
                             neg(nextF)}),
                        du});
                }
            } else if (name == "besseli") {
                const Expr np1 = add({n, one()});
                const Expr nextF = func(name, np1, u);
                if (isZero(n)) {
                    result = mul({nextF, du});
                } else {
                    result = mul({
                        add({mul({n, pow(u, number(std::int64_t{-1})), e}),
                             nextF}),
                        du});
                }
            } else if (name == "polylog") {
                const Expr nm1 = add({n, number(std::int64_t{-1})});
                result = mul({
                    func("polylog", nm1, u),
                    pow(u, number(std::int64_t{-1})),
                    du});
            } else if (name == "bernoulliB" || name == "eulerE") {
                if (isZero(n)) {
                    result = zero();
                } else {
                    const Expr nm1 = add({n, number(std::int64_t{-1})});
                    result = mul({n, func(name, nm1, u), du});
                }
            } else {
                result = Expr();
            }
            break;
        }
        const Expr u = child(e, 0);
        const Expr du = diffRec(u, var, memo);
        if (du.isNull())
            break;
        if (isZero(du)) {
            result = zero();
            break;
        }
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
        else if (name == "gamma")
            result = mul({e, func("digamma", u), du});
        else if (name == "factorial") {
            const Expr up1 = add({u, one()});
            result = mul({e, func("digamma", up1), du});
        } else if (name == "lgamma" || name == "loggamma")
            result = mul({func("digamma", u), du});
        else if (name == "digamma" || name == "psi")
            result = mul({func("trigamma", u), du});
        else if (name == "airyAi")
            result = mul({func("airyAiPrime", u), du});
        else if (name == "airyAiPrime")
            result = mul({u, func("airyAi", u), du});
        else if (name == "airyBi")
            result = mul({func("airyBiPrime", u), du});
        else if (name == "airyBiPrime")
            result = mul({u, func("airyBi", u), du});
        else if (name == "ellipticK") {
            const Expr half = number(Rational(std::int64_t{1}, BigInt(2)));
            const Expr oneMinusU = add({one(), neg(u)});
            const Expr num = add({
                func("ellipticE", u),
                neg(mul({oneMinusU, e}))});
            result = mul({
                half, num,
                pow(u, number(std::int64_t{-1})),
                pow(oneMinusU, number(std::int64_t{-1})),
                du});
        } else if (name == "ellipticE") {
            const Expr half = number(Rational(std::int64_t{1}, BigInt(2)));
            const Expr num = add({e, neg(func("ellipticK", u))});
            result = mul({
                half, num,
                pow(u, number(std::int64_t{-1})),
                du});
        } else if (name == "F") {
            result = mul({func("dF", u), du});
        } else if (name == "dF") {
            result = mul({func("ddF", u), du});
        } else if (name == "F1") {
            result = mul({func("dF1", u), du});
        } else if (name == "dF1") {
            result = mul({func("ddF1", u), du});
        } else if (name == "F2") {
            result = mul({func("dF2", u), du});
        } else if (name == "dF2") {
            result = mul({func("ddF2", u), du});
        } else {
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
