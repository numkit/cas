#include <numkit/cas/ode/dsolve.hpp>

#include <numkit/cas/core/simplify.hpp>
#include <numkit/cas/core/symsolve.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>

#include <algorithm>
#include <cstdint>
#include <vector>

namespace numkit::cas {

namespace {

bool checkOdeBudget(const Ctx &c, Budget *budget)
{
    if (!budget)
        return true;
    return budget->step() && budget->recordArenaBytes(c.nodeCount() * 32);
}

bool mentionsSym(const Ctx &c, Expr e, Expr sym)
{
    if (e.isNull())
        return false;
    if (e == sym)
        return true;
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        if (mentionsSym(c, c.child(e, i), sym))
            return true;
    return false;
}

bool isZeroSimp(Ctx &c, Expr e)
{
    if (e.isNull())
        return false;
    if (c.isZero(e))
        return true;
    const Expr s = c.simplify(e);
    return !s.isNull() && c.isZero(s);
}

// Normalize a logarithm argument so log(-x) and log(x) match on positive/negative branches
// during symbolic integration, and simplify exp(a + c*log(u)) -> exp(a) * u^c.
Expr expOfIntegral(Ctx &c, Expr intA)
{
    const Expr expd = c.expand(intA);
    if (c.kind(expd) == NodeKind::Add) {
        std::vector<Expr> factors;
        std::vector<Expr> remAdd;
        for (std::size_t i = 0; i < c.childCount(expd); ++i) {
            const Expr t = c.child(expd, i);
            if (c.kind(t) == NodeKind::Func && c.funcName(t) == "log") {
                factors.push_back(c.child(t, 0));
            } else if (c.kind(t) == NodeKind::Mul && c.childCount(t) == 2 &&
                       c.kind(c.child(t, 0)) == NodeKind::Number &&
                       c.kind(c.child(t, 1)) == NodeKind::Func &&
                       c.funcName(c.child(t, 1)) == "log") {
                factors.push_back(
                    c.pow(c.child(c.child(t, 1), 0), c.child(t, 0)));
            } else {
                remAdd.push_back(t);
            }
        }
        if (!remAdd.empty())
            factors.push_back(c.func("exp", c.add(remAdd)));
        return c.simplify(factors.empty() ? c.one() : c.mul(factors));
    }
    return c.simplify(c.func("exp", intA));
}

bool verifyOde1(Ctx &c, Expr ySol, Expr rhs, Expr x, Expr y)
{
    if (ySol.isNull())
        return false;
    const Expr dy = c.diff(ySol, x);
    if (dy.isNull())
        return false;
    const Expr subRhs = c.subs(rhs, y, ySol);
    if (subRhs.isNull())
        return false;
    return isZeroSimp(c, c.add({dy, c.neg(subRhs)}));
}

bool verifyOde2(Ctx &c, Expr ySol, Expr a, Expr b, Expr d, Expr f, Expr x)
{
    if (ySol.isNull())
        return false;
    const Expr dy = c.diff(ySol, x);
    if (dy.isNull())
        return false;
    const Expr d2y = c.diff(dy, x);
    if (d2y.isNull())
        return false;
    const Expr lhs =
        c.add({c.mul({a, d2y}), c.mul({b, dy}), c.mul({d, ySol})});
    return isZeroSimp(c, c.add({lhs, c.neg(f)}));
}

// Split an expression into a linear combination of `x`-dependent basis atoms:
// each additive child is split into `(constFactor, xAtom)` where `constFactor`
// is independent of `x`.
void splitIntoBasisTerms(Ctx &c, Expr e, Expr x,
                         std::vector<std::pair<Expr, Expr>> &out)
{
    const Expr expd = c.expand(e);
    auto processTerm = [&](Expr t) {
        if (c.isZero(t))
            return;
        if (!mentionsSym(c, t, x)) {
            out.emplace_back(t, c.one());
            return;
        }
        if (c.kind(t) == NodeKind::Mul) {
            std::vector<Expr> constPart;
            std::vector<Expr> xPart;
            for (std::size_t i = 0; i < c.childCount(t); ++i) {
                const Expr f = c.child(t, i);
                if (mentionsSym(c, f, x))
                    xPart.push_back(f);
                else
                    constPart.push_back(f);
            }
            const Expr coef =
                constPart.empty() ? c.one() : c.simplify(c.mul(constPart));
            const Expr atom =
                xPart.empty() ? c.one() : c.simplify(c.mul(xPart));
            out.emplace_back(coef, atom);
            return;
        }
        out.emplace_back(c.one(), c.simplify(t));
    };

    if (c.kind(expd) == NodeKind::Add) {
        for (std::size_t i = 0; i < c.childCount(expd); ++i)
            processTerm(c.child(expd, i));
    } else {
        processTerm(expd);
    }
}

void addUniqueAtom(Ctx &c, std::vector<Expr> &atoms, Expr atom)
{
    if (atom.isNull() || c.isZero(atom))
        return;
    for (const Expr &existing : atoms) {
        if (existing == atom)
            return;
    }
    atoms.push_back(atom);
}

// Differential-closure Method of Undetermined Coefficients for
// L[y] = a*y'' + b*y' + d*y = f(x) (also supports 1st-order when a == 0).
bool tryUndeterminedCoeffs(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                           Budget *budget, Expr &ypOut)
{
    // Build the differential-closure basis from f(x), x*f(x), and x^2*f(x).
    std::vector<Expr> rawAtoms;
    const Expr seeds[3] = {
        f,
        c.mul({x, f}),
        c.mul({c.pow(x, c.number(std::int64_t{2})), f}),
    };

    for (const Expr &seed : seeds) {
        Expr cur = seed;
        for (int drv = 0; drv < 4; ++drv) {
            if (drv > 0)
                cur = c.diff(cur, x);
            std::vector<std::pair<Expr, Expr>> terms;
            splitIntoBasisTerms(c, cur, x, terms);
            for (const auto &kv : terms)
                addUniqueAtom(c, rawAtoms, kv.second);
            if (rawAtoms.size() > 16)
                return false; // not a D-finite poly-exp-trig forcing term
        }
    }

    auto applyL = [&](Expr phi) -> Expr {
        const Expr d1 = c.diff(phi, x);
        const Expr d2 = c.isZero(a) ? c.zero() : c.diff(d1, x);
        return c.simplify(
            c.add({c.mul({a, d2}), c.mul({b, d1}), c.mul({d, phi})}));
    };

    // Keep only non-kernel basis functions phi_j where L[phi_j] != 0.
    std::vector<Expr> phiBasis;
    std::vector<Expr> psiImages;
    std::vector<Expr> rowAtoms;

    std::vector<std::pair<Expr, Expr>> fTerms;
    splitIntoBasisTerms(c, f, x, fTerms);
    for (const auto &kv : fTerms)
        addUniqueAtom(c, rowAtoms, kv.second);

    for (const Expr &phi : rawAtoms) {
        const Expr psi = applyL(phi);
        if (psi.isNull() || isZeroSimp(c, psi))
            continue;
        phiBasis.push_back(phi);
        psiImages.push_back(psi);
        std::vector<std::pair<Expr, Expr>> psiTerms;
        splitIntoBasisTerms(c, psi, x, psiTerms);
        for (const auto &kv : psiTerms)
            addUniqueAtom(c, rowAtoms, kv.second);
    }

    if (phiBasis.empty() || rowAtoms.empty())
        return false;

    auto findAtomRow = [&](Expr atom) -> std::size_t {
        for (std::size_t r = 0; r < rowAtoms.size(); ++r)
            if (rowAtoms[r] == atom)
                return r;
        return rowAtoms.size();
    };

    std::vector<Expr> activePhi;
    std::vector<Expr> activePsi;
    for (std::size_t col = 0; col < phiBasis.size(); ++col) {
        activePhi.push_back(phiBasis[col]);
        activePsi.push_back(psiImages[col]);

        const std::size_t mRows = rowAtoms.size();
        const std::size_t nCols = activePhi.size();
        if (mRows < nCols)
            continue;

        SymMatrix M = SymMatrix::zeros(c, mRows, nCols);
        for (std::size_t j = 0; j < nCols; ++j) {
            std::vector<std::pair<Expr, Expr>> terms;
            splitIntoBasisTerms(c, activePsi[j], x, terms);
            for (const auto &kv : terms) {
                const std::size_t r = findAtomRow(kv.second);
                if (r < mRows)
                    M.at(r, j) = c.simplify(c.add({M.at(r, j), kv.first}));
            }
        }

        SymMatrix rhsVec = SymMatrix::zeros(c, mRows, 1);
        for (const auto &kv : fTerms) {
            const std::size_t r = findAtomRow(kv.second);
            if (r < mRows)
                rhsVec.at(r, 0) = c.simplify(c.add({rhsVec.at(r, 0), kv.first}));
        }

        const SymMatrix sol = linsolve(c, M, rhsVec, budget);
        if (!sol.empty()) {
            std::vector<Expr> ypTerms;
            for (std::size_t j = 0; j < nCols; ++j) {
                if (!c.isZero(sol.at(j, 0)))
                    ypTerms.push_back(c.mul({sol.at(j, 0), activePhi[j]}));
            }
            ypOut = ypTerms.empty() ? c.zero() : c.simplify(c.add(ypTerms));
            if (isZeroSimp(c, c.add({applyL(ypOut), c.neg(f)})))
                return true;
        }
    }

    return false;
}

// Try solving a linear 1st-order ODE: y' = A(x) * y + B(x).
bool tryLinearOde1(Ctx &c, Expr rhs, Expr x, Expr y, Expr C1, Budget *budget,
                   Expr &yOut)
{
    const Expr A = c.simplify(c.diff(rhs, y));
    if (A.isNull() || mentionsSym(c, A, y))
        return false;
    const Expr B = c.simplify(c.add({rhs, c.neg(c.mul({A, y}))}));
    if (B.isNull() || mentionsSym(c, B, y))
        return false;

    // Integrate A(x) dx
    const RationalIntegral intA = integrate(c, A, x, budget);
    if (!intA.proved())
        return false;

    const Expr expPos = expOfIntegral(c, intA.F);
    if (isZeroSimp(c, B)) {
        yOut = c.simplify(c.mul({C1, expPos}));
        return true;
    }

    const Expr expNeg = expOfIntegral(c, c.neg(intA.F));
    const Expr integrand = c.simplify(c.mul({B, expNeg}));
    const RationalIntegral intB = integrate(c, integrand, x, budget);
    if (intB.proved()) {
        yOut = c.simplify(c.mul({expPos, c.add({intB.F, C1})}));
        return true;
    }

    // Constant-coefficient 1st-order linear ODE y' - A*y = B(x) with
    // polynomial/exponential/trig forcing B(x) via undetermined coefficients.
    if (!mentionsSym(c, A, x)) {
        Expr yp;
        if (tryUndeterminedCoeffs(c, c.zero(), c.one(), c.neg(A), B, x, budget,
                                  yp)) {
            yOut = c.simplify(c.add({c.mul({C1, expPos}), yp}));
            return true;
        }
    }

    return false;
}

// Try solving a separable 1st-order ODE: y' = g(x) * h(y).
bool trySeparableOde1(Ctx &c, Expr rhs, Expr x, Expr y, Expr C1,
                      Budget *budget, Expr &yOut)
{
    const Expr factoredRhs = c.simplify(rhs);
    std::vector<Expr> xFactors;
    std::vector<Expr> yFactors;

    auto classifyFactor = [&](Expr f) -> bool {
        const bool hasX = mentionsSym(c, f, x);
        const bool hasY = mentionsSym(c, f, y);
        if (hasX && hasY)
            return false;
        if (hasY)
            yFactors.push_back(f);
        else
            xFactors.push_back(f);
        return true;
    };

    if (c.kind(factoredRhs) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(factoredRhs); ++i)
            if (!classifyFactor(c.child(factoredRhs, i)))
                return false;
    } else {
        if (!classifyFactor(factoredRhs))
            return false;
    }

    if (yFactors.empty())
        return false; // handled by quadrature

    const Expr gX = xFactors.empty() ? c.one() : c.mul(xFactors);
    const Expr hY = c.mul(yFactors);
    if (isZeroSimp(c, hY))
        return false;

    const Expr invHY = c.simplify(c.pow(hY, c.number(std::int64_t{-1})));
    const RationalIntegral intG = integrate(c, gX, x, budget);
    if (!intG.proved())
        return false;
    const RationalIntegral intH = integrate(c, invHY, y, budget);
    if (!intH.proved())
        return false;

    // Solve H(y) - (G(x) + C1) = 0 for y.
    const Expr implicitEq =
        c.add({intH.F, c.neg(intG.F), c.neg(C1)});
    const std::vector<Expr> sols = solveSymbolic(c, implicitEq, y, budget);
    for (const Expr &cand : sols) {
        if (verifyOde1(c, cand, rhs, x, y)) {
            yOut = cand;
            return true;
        }
    }
    return false;
}

// Try solving a Bernoulli 1st-order ODE: y' = A(x)*y + B(x)*y^n (n != 0, 1).
bool tryBernoulliOde1(Ctx &c, Expr rhs, Expr x, Expr y, Expr C1,
                      Budget *budget, Expr &yOut)
{
    const Expr expd = c.expand(rhs);
    if (c.kind(expd) != NodeKind::Add)
        return false;

    std::vector<Expr> linearTerms;
    std::vector<Expr> powerCoeffs;
    Rational nExp(0);
    bool hasPower = false;

    for (std::size_t i = 0; i < c.childCount(expd); ++i) {
        const Expr term = c.child(expd, i);
        // Extract power of y in `term`
        Rational pY(0);
        std::vector<Expr> xRest;
        bool validTerm = true;
        auto inspectFactor = [&](Expr f) {
            if (!mentionsSym(c, f, y)) {
                xRest.push_back(f);
            } else if (f == y) {
                pY += Rational(std::int64_t{1});
            } else if (c.kind(f) == NodeKind::Pow && c.child(f, 0) == y &&
                       c.kind(c.child(f, 1)) == NodeKind::Number) {
                pY += c.numberValue(c.child(f, 1));
            } else {
                validTerm = false;
            }
        };

        if (c.kind(term) == NodeKind::Mul) {
            for (std::size_t j = 0; j < c.childCount(term); ++j)
                inspectFactor(c.child(term, j));
        } else {
            inspectFactor(term);
        }
        if (!validTerm)
            return false;

        const Expr cof = xRest.empty() ? c.one() : c.mul(xRest);
        if (pY == Rational(std::int64_t{1})) {
            linearTerms.push_back(cof);
        } else if (!pY.isZero()) {
            if (!hasPower) {
                nExp = pY;
                hasPower = true;
            } else if (!(nExp == pY)) {
                return false;
            }
            powerCoeffs.push_back(cof);
        } else {
            return false;
        }
    }

    if (!hasPower || powerCoeffs.empty())
        return false;
    const Rational oneMinusN = Rational(std::int64_t{1}) - nExp;
    if (oneMinusN.isZero())
        return false;

    const Expr A = linearTerms.empty() ? c.zero() : c.simplify(c.add(linearTerms));
    const Expr B = c.simplify(c.add(powerCoeffs));

    // Substitute u = y^(1 - n): u' = (1 - n)*A(x)*u + (1 - n)*B(x)
    const Expr uSym = c.symbol("_ode_u");
    const Expr scale = c.number(oneMinusN);
    const Expr uRhs =
        c.add({c.mul({scale, A, uSym}), c.mul({scale, B})});
    Expr uSol;
    if (!tryLinearOde1(c, uRhs, x, uSym, C1, budget, uSol))
        return false;

    const Rational invOneMinusN = Rational(std::int64_t{1}) / oneMinusN;
    yOut = c.simplify(c.pow(uSol, c.number(invOneMinusN)));
    return true;
}

} // namespace

OdeResult dsolve1(Ctx &c, Expr rhs, Expr x, Expr y, Budget *budget)
{
    OdeResult out;
    if (rhs.isNull() || x.isNull() || y.isNull()) {
        out.reason = "null input expression";
        return out;
    }
    if (!checkOdeBudget(c, budget)) {
        out.reason = "budget exhausted";
        return out;
    }

    const Expr C1 = c.symbol("C1");

    // 1. Direct quadrature: y' = f(x)
    if (!mentionsSym(c, rhs, y)) {
        const RationalIntegral r = integrate(c, rhs, x, budget);
        if (r.proved()) {
            const Expr cand = c.simplify(c.add({r.F, C1}));
            if (verifyOde1(c, cand, rhs, x, y)) {
                out.status = OdeResult::Status::Proved;
                out.y = cand;
                return out;
            }
        }
    }

    // 2. Linear 1st-order ODE: y' = A(x)*y + B(x)
    {
        Expr cand;
        if (tryLinearOde1(c, rhs, x, y, C1, budget, cand) &&
            verifyOde1(c, cand, rhs, x, y)) {
            out.status = OdeResult::Status::Proved;
            out.y = cand;
            return out;
        }
    }

    // 3. Separable 1st-order ODE: y' = g(x) * h(y)
    {
        Expr cand;
        if (trySeparableOde1(c, rhs, x, y, C1, budget, cand) &&
            verifyOde1(c, cand, rhs, x, y)) {
            out.status = OdeResult::Status::Proved;
            out.y = cand;
            return out;
        }
    }

    // 4. Bernoulli 1st-order ODE: y' = A(x)*y + B(x)*y^n
    {
        Expr cand;
        if (tryBernoulliOde1(c, rhs, x, y, C1, budget, cand) &&
            verifyOde1(c, cand, rhs, x, y)) {
            out.status = OdeResult::Status::Proved;
            out.y = cand;
            return out;
        }
    }

    out.reason = "ODE outside supported 1st-order classes or uncertified";
    return out;
}

OdeResult dsolve1IVP(Ctx &c, Expr rhs, Expr x, Expr y, Expr x0, Expr y0,
                     Budget *budget)
{
    OdeResult gen = dsolve1(c, rhs, x, y, budget);
    if (!gen.proved())
        return gen;

    const Expr C1 = c.symbol("C1");
    const Expr atX0 = c.simplify(c.subs(gen.y, x, x0));
    const Expr icEq = c.add({atX0, c.neg(y0)});
    const std::vector<Expr> c1Vals = solveSymbolic(c, icEq, C1, budget);
    for (const Expr &cVal : c1Vals) {
        const Expr yPart = c.simplify(c.subs(gen.y, C1, cVal));
        const Expr checkIC = c.simplify(c.add({c.subs(yPart, x, x0), c.neg(y0)}));
        if (c.isZero(checkIC) && verifyOde1(c, yPart, rhs, x, y)) {
            OdeResult out;
            out.status = OdeResult::Status::Proved;
            out.y = yPart;
            return out;
        }
    }

    OdeResult fail;
    fail.reason = "unable to resolve initial condition y(x0) = y0";
    return fail;
}

// ============================================================================
// 2nd-Order Constant-Coefficient Linear ODE Solver
// ============================================================================

OdeResult dsolve2Linear(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                        Budget *budget)
{
    OdeResult out;
    if (a.isNull() || b.isNull() || d.isNull() || f.isNull() || x.isNull()) {
        out.reason = "null input expression";
        return out;
    }
    if (isZeroSimp(c, a) || mentionsSym(c, a, x) || mentionsSym(c, b, x) ||
        mentionsSym(c, d, x)) {
        out.reason = "coefficients a, b, d must be non-zero constants in x";
        return out;
    }
    if (!checkOdeBudget(c, budget)) {
        out.reason = "budget exhausted";
        return out;
    }

    const Expr C1 = c.symbol("C1");
    const Expr C2 = c.symbol("C2");
    const Expr two = c.number(std::int64_t{2});
    const Expr four = c.number(std::int64_t{4});
    const Expr twoA = c.mul({two, a});
    const Expr disc =
        c.simplify(c.add({c.pow(b, two), c.neg(c.mul({four, a, d}))}));

    Expr y1, y2;
    if (isZeroSimp(c, disc)) {
        // Critically damped: double root r = -b / (2*a)
        const Expr r = c.simplify(c.div(c.neg(b), twoA));
        y1 = c.simplify(c.func("exp", c.mul({r, x})));
        y2 = c.simplify(c.mul({x, y1}));
    } else if (c.kind(disc) == NodeKind::Number &&
               c.numberValue(disc).signum() < 0) {
        // Underdamped (complex conjugate roots alpha +- i*omega):
        // real fundamental basis exp(alpha*x)*cos(omega*x), exp(alpha*x)*sin(omega*x).
        const Expr alpha = c.simplify(c.div(c.neg(b), twoA));
        const Expr negDisc = c.neg(disc);
        const std::vector<Expr> wRoots = solveSymbolic(
            c, c.add({c.mul({four, c.pow(a, two), c.pow(x, two)}), c.neg(negDisc)}),
            x, budget);
        Expr omega = wRoots.empty()
                         ? c.simplify(c.div(
                               c.pow(negDisc, c.number(Rational(std::int64_t{1}, BigInt(2)))),
                               twoA))
                         : wRoots.back();
        const Expr env = c.simplify(c.func("exp", c.mul({alpha, x})));
        y1 = c.simplify(c.mul({env, c.func("cos", c.mul({omega, x}))}));
        y2 = c.simplify(c.mul({env, c.func("sin", c.mul({omega, x}))}));
    } else {
        // Overdamped (two distinct real/symbolic roots r1, r2)
        const Expr rSym = c.symbol("_ode_r");
        const Expr charEq =
            c.add({c.mul({a, c.pow(rSym, two)}), c.mul({b, rSym}), d});
        const std::vector<Expr> roots = solveSymbolic(c, charEq, rSym, budget);
        if (roots.size() < 2) {
            out.reason = "unable to solve characteristic equation";
            return out;
        }
        y1 = c.simplify(c.func("exp", c.mul({roots[0], x})));
        y2 = c.simplify(c.func("exp", c.mul({roots[1], x})));
    }

    const Expr yh = c.simplify(c.add({c.mul({C1, y1}), c.mul({C2, y2})}));
    if (isZeroSimp(c, f)) {
        if (verifyOde2(c, yh, a, b, d, f, x)) {
            out.status = OdeResult::Status::Proved;
            out.y = yh;
            return out;
        }
        out.reason = "homogeneous solution failed verification";
        return out;
    }

    // Particular solution y_p(x):
    // 1. Differential-closure Undetermined Coefficients via SymMatrix::linsolve.
    Expr yp;
    bool foundYp = tryUndeterminedCoeffs(c, a, b, d, f, x, budget, yp);

    // 2. Fallback: Variation of Parameters via Wronskian W = y1*y2' - y1'*y2.
    if (!foundYp) {
        const Expr dy1 = c.diff(y1, x);
        const Expr dy2 = c.diff(y2, x);
        const Expr W =
            c.simplify(c.add({c.mul({y1, dy2}), c.neg(c.mul({dy1, y2}))}));
        if (!isZeroSimp(c, W)) {
            const Expr aW = c.mul({a, W});
            const Expr int1 = c.simplify(c.neg(c.div(c.mul({y2, f}), aW)));
            const Expr int2 = c.simplify(c.div(c.mul({y1, f}), aW));
            const RationalIntegral u1 = integrate(c, int1, x, budget);
            const RationalIntegral u2 = integrate(c, int2, x, budget);
            if (u1.proved() && u2.proved()) {
                yp = c.simplify(
                    c.add({c.mul({u1.F, y1}), c.mul({u2.F, y2})}));
                foundYp = verifyOde2(c, yp, a, b, d, f, x);
            }
        }
    }

    if (!foundYp) {
        out.reason = "particular integral could not be determined or certified";
        return out;
    }

    const Expr yTotal = c.simplify(c.add({yh, yp}));
    if (verifyOde2(c, yTotal, a, b, d, f, x)) {
        out.status = OdeResult::Status::Proved;
        out.y = yTotal;
        return out;
    }

    out.reason = "combined ODE solution failed verification";
    return out;
}

OdeResult dsolve2LinearIVP(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                           Expr x0, Expr y0, Expr dy0, Budget *budget)
{
    OdeResult gen = dsolve2Linear(c, a, b, d, f, x, budget);
    if (!gen.proved())
        return gen;

    const Expr C1 = c.symbol("C1");
    const Expr C2 = c.symbol("C2");
    const Expr dyGen = c.diff(gen.y, x);

    const Expr yAt0 = c.simplify(c.subs(gen.y, x, x0));
    const Expr dyAt0 = c.simplify(c.subs(dyGen, x, x0));

    // Extract 2x2 linear system for (C1, C2):
    //   m00 * C1 + m01 * C2 + const0 = y0
    //   m10 * C1 + m11 * C2 + const1 = dy0
    const Expr m00 = c.simplify(c.diff(yAt0, C1));
    const Expr m01 = c.simplify(c.diff(yAt0, C2));
    const Expr const0 =
        c.simplify(c.subs(c.subs(yAt0, C1, c.zero()), C2, c.zero()));

    const Expr m10 = c.simplify(c.diff(dyAt0, C1));
    const Expr m11 = c.simplify(c.diff(dyAt0, C2));
    const Expr const1 =
        c.simplify(c.subs(c.subs(dyAt0, C1, c.zero()), C2, c.zero()));

    const SymMatrix M(2, 2, {m00, m01, m10, m11});
    const SymMatrix rhs(2, 1,
                        {c.simplify(c.add({y0, c.neg(const0)})),
                         c.simplify(c.add({dy0, c.neg(const1)}))});
    const SymMatrix sol = linsolve(c, M, rhs, budget);
    if (sol.empty()) {
        OdeResult fail;
        fail.reason = "singular Wronskian at initial point x0";
        return fail;
    }

    const Expr yIVP = c.simplify(
        c.subs(c.subs(gen.y, C1, sol.at(0, 0)), C2, sol.at(1, 0)));
    const Expr dyIVP = c.diff(yIVP, x);
    if (verifyOde2(c, yIVP, a, b, d, f, x) &&
        isZeroSimp(c, c.add({c.subs(yIVP, x, x0), c.neg(y0)})) &&
        isZeroSimp(c, c.add({c.subs(dyIVP, x, x0), c.neg(dy0)}))) {
        OdeResult out;
        out.status = OdeResult::Status::Proved;
        out.y = yIVP;
        return out;
    }

    OdeResult fail;
    fail.reason = "IVP solution failed verification";
    return fail;
}

} // namespace numkit::cas
