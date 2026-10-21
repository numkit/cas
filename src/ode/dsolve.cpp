#include <numkit/cas/ode/dsolve.hpp>

#include <numkit/cas/core/simplify.hpp>
#include <numkit/cas/core/symsolve.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/linalg/symmatrix.hpp>
#include <numkit/cas/poly/zassenhaus.hpp>

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
    if (s.isNull())
        return false;
    if (c.isZero(s))
        return true;
    const Expr expS = c.simplify(c.expand(c.expand(s)));
    if (!expS.isNull() && c.isZero(expS))
        return true;
    const Expr r = simplifyRationalExpr(c, s);
    if (!r.isNull()) {
        if (c.isZero(r))
            return true;
        const Expr expR = c.simplify(c.expand(c.expand(r)));
        if (!expR.isNull() && c.isZero(expR))
            return true;
    }
    return false;
}

// Normalize a logarithm argument so log(-x) and log(x) match on positive/negative branches
// during symbolic integration, and simplify exp(a + c*log(u)) -> exp(a) * u^c.
Expr expOfIntegral(Ctx &c, Expr intA)
{
    const Expr expd = c.expand(intA);
    std::vector<Expr> factors;
    std::vector<Expr> remAdd;
    auto processTerm = [&](Expr t) {
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
    };

    if (c.kind(expd) == NodeKind::Add) {
        for (std::size_t i = 0; i < c.childCount(expd); ++i)
            processTerm(c.child(expd, i));
    } else {
        processTerm(expd);
    }
    if (!remAdd.empty())
        factors.push_back(c.func("exp", c.add(remAdd)));
    return c.simplify(factors.empty() ? c.one() : c.mul(factors));
}

void splitRationalNumDen(Ctx &c, Expr e, Expr &numOut, Expr &denOut);

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
    if (isZeroSimp(c, c.add({dy, c.neg(subRhs)})))
        return true;

    Expr num, den;
    splitRationalNumDen(c, rhs, num, den);
    if (!num.isNull() && !den.isNull()) {
        const Expr subDen = c.expand(c.subs(den, y, ySol));
        if (!isZeroSimp(c, subDen)) {
            const Expr subNum = c.expand(c.subs(num, y, ySol));
            const Expr cross =
                c.expand(c.expand(c.add({c.mul({subDen, dy}), c.neg(subNum)})));
            if (isZeroSimp(c, cross))
                return true;
        }
    }
    return false;
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

// Try solving a homogeneous 1st-order ODE: y' = F(y / x) via y = u * x.
bool tryHomogeneousOde1(Ctx &c, Expr rhs, Expr x, Expr y, Expr C1,
                        Budget *budget, Expr &yOut)
{
    const Expr uSym = c.symbol("_ode_hom_u");
    Expr Fu = c.simplify(c.subs(rhs, y, c.mul({uSym, x})));
    if (Fu.isNull())
        return false;
    if (mentionsSym(c, Fu, x)) {
        const Expr ratFu = simplifyRationalExpr(c, Fu);
        if (!ratFu.isNull())
            Fu = ratFu;
    }
    if (mentionsSym(c, Fu, x))
        return false;

    Expr diffU = c.simplify(c.add({Fu, c.neg(uSym)}));
    if (const Expr ratDiff = simplifyRationalExpr(c, diffU); !ratDiff.isNull())
        diffU = ratDiff;
    if (isZeroSimp(c, diffU)) {
        yOut = c.simplify(c.mul({C1, x}));
        return verifyOde1(c, yOut, rhs, x, y);
    }

    // u' = (F(u) - u) / x
    const Expr uRhs = c.simplify(c.div(diffU, x));
    Expr uSol;
    if (trySeparableOde1(c, uRhs, x, uSym, C1, budget, uSol) ||
        tryLinearOde1(c, uRhs, x, uSym, C1, budget, uSol) ||
        tryBernoulliOde1(c, uRhs, x, uSym, C1, budget, uSol)) {
        const Expr cand = c.simplify(c.mul({uSol, x}));
        if (verifyOde1(c, cand, rhs, x, y)) {
            yOut = cand;
            return true;
        }
    }

    // Separable integration int du / (F(u) - u) = log(x) + C1, also trying
    // exponentiated algebraic forms exp(k * H(u)) = C1 * x^k.
    const Expr invDiffU = c.simplify(c.pow(diffU, c.number(std::int64_t{-1})));
    const RationalIntegral intU = integrate(c, invDiffU, uSym, budget);
    if (!intU.proved())
        return false;

    const std::int64_t kScales[] = {1, -1, 2, -2, 3, -3, 4, -4};
    for (std::int64_t k : kScales) {
        const Expr kExpr = c.number(k);
        const Expr lhsExp = expOfIntegral(c, c.mul({kExpr, intU.F}));
        const Expr rhsExp = c.mul({C1, c.pow(x, kExpr)});
        const Expr algEq = c.simplify(c.add({lhsExp, c.neg(rhsExp)}));
        const std::vector<Expr> sols = solveSymbolic(c, algEq, uSym, budget);
        for (const Expr &uCand : sols) {
            const Expr cand = c.simplify(c.mul({uCand, x}));
            if (verifyOde1(c, cand, rhs, x, y)) {
                yOut = cand;
                return true;
            }
        }
    }

    return false;
}

void splitRationalNumDen(Ctx &c, Expr e, Expr &numOut, Expr &denOut)
{
    Expr rat = simplifyRationalExpr(c, e);
    if (rat.isNull())
        rat = c.simplify(e);

    std::vector<Expr> numFactors;
    std::vector<Expr> denFactors;
    auto inspect = [&](Expr f) {
        if (c.kind(f) == NodeKind::Pow &&
            c.kind(c.child(f, 1)) == NodeKind::Number &&
            c.numberValue(c.child(f, 1)).signum() < 0) {
            const Rational posExp = -c.numberValue(c.child(f, 1));
            denFactors.push_back(c.pow(c.child(f, 0), c.number(posExp)));
        } else {
            numFactors.push_back(f);
        }
    };

    if (c.kind(rat) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(rat); ++i)
            inspect(c.child(rat, i));
    } else {
        inspect(rat);
    }

    numOut = numFactors.empty() ? c.one() : c.simplify(c.mul(numFactors));
    denOut = denFactors.empty() ? c.one() : c.simplify(c.mul(denFactors));
}

// Try solving an exact 1st-order ODE M(x, y)*dx + N(x, y)*dy = 0, or one
// admitting an integrating factor mu(x) or mu(y).
bool tryExactOde1(Ctx &c, Expr rhs, Expr x, Expr y, Expr C1, Budget *budget,
                  Expr &yOut)
{
    Expr num, den;
    splitRationalNumDen(c, rhs, num, den);
    if (num.isNull() || den.isNull() || isZeroSimp(c, den))
        return false;

    // y' = num / den  <=>  (-num)*dx + den*dy = 0
    Expr M = c.simplify(c.neg(num));
    Expr N = c.simplify(den);

    const Expr My = c.diff(M, y);
    const Expr Nx = c.diff(N, x);
    if (My.isNull() || Nx.isNull())
        return false;

    const Expr diffMN = c.simplify(c.add({My, c.neg(Nx)}));
    if (!isZeroSimp(c, diffMN)) {
        bool foundMu = false;
        // Try integrating factor mu(x): p(x) = (M_y - N_x) / N independent of y
        Expr px = simplifyRationalExpr(c, c.div(diffMN, N));
        if (px.isNull())
            px = c.simplify(c.div(diffMN, N));
        if (!px.isNull() && !mentionsSym(c, px, y)) {
            const RationalIntegral intP = integrate(c, px, x, budget);
            if (intP.proved()) {
                const Expr mu = expOfIntegral(c, intP.F);
                M = c.simplify(c.expand(c.mul({mu, M})));
                N = c.simplify(c.expand(c.mul({mu, N})));
                foundMu = isZeroSimp(c, c.add({c.diff(M, y), c.neg(c.diff(N, x))}));
            }
        }

        // Try integrating factor mu(y): q(y) = (N_x - M_y) / M independent of x
        if (!foundMu && !isZeroSimp(c, M)) {
            Expr qy = simplifyRationalExpr(c, c.div(c.neg(diffMN), M));
            if (qy.isNull())
                qy = c.simplify(c.div(c.neg(diffMN), M));
            if (!qy.isNull() && !mentionsSym(c, qy, x)) {
                const RationalIntegral intQ = integrate(c, qy, y, budget);
                if (intQ.proved()) {
                    const Expr mu = expOfIntegral(c, intQ.F);
                    M = c.simplify(c.expand(c.mul({mu, M})));
                    N = c.simplify(c.expand(c.mul({mu, N})));
                    foundMu =
                        isZeroSimp(c, c.add({c.diff(M, y), c.neg(c.diff(N, x))}));
                }
            }
        }

        if (!foundMu)
            return false;
    }

    // Reconstruct potential Phi(x, y) = int M(x, y) dx + int (N - d/dy int M dx) dy
    const RationalIntegral intMx = integrate(c, c.expand(M), x, budget);
    if (!intMx.proved())
        return false;

    Expr remY = c.simplify(c.expand(c.add({N, c.neg(c.diff(intMx.F, y))})));
    if (mentionsSym(c, remY, x)) {
        const Expr ratRem = simplifyRationalExpr(c, remY);
        if (!ratRem.isNull())
            remY = ratRem;
    }
    if (mentionsSym(c, remY, x))
        return false;

    const RationalIntegral intNy = integrate(c, remY, y, budget);
    if (!intNy.proved())
        return false;

    const Expr Phi = c.simplify(c.add({intMx.F, intNy.F}));
    const Expr implicitEq = c.add({Phi, c.neg(C1)});
    const std::vector<Expr> sols = solveSymbolic(c, implicitEq, y, budget);
    for (const Expr &cand : sols) {
        if (verifyOde1(c, cand, rhs, x, y)) {
            yOut = cand;
            return true;
        }
    }
    return false;
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

    // 5. Homogeneous 1st-order ODE: y' = F(y / x)
    {
        Expr cand;
        if (tryHomogeneousOde1(c, rhs, x, y, C1, budget, cand) &&
            verifyOde1(c, cand, rhs, x, y)) {
            out.status = OdeResult::Status::Proved;
            out.y = cand;
            return out;
        }
    }

    // 6. Exact 1st-order ODE / integrating factor mu(x) or mu(y)
    {
        Expr cand;
        if (tryExactOde1(c, rhs, x, y, C1, budget, cand) &&
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

// ============================================================================
// 2nd-Order Euler-Cauchy Equidimensional Linear ODE Solver
// ============================================================================

namespace {

bool verifyOde2EulerCauchy(Ctx &c, Expr ySol, Expr a, Expr b, Expr d, Expr f,
                           Expr x)
{
    if (ySol.isNull())
        return false;
    const Expr dy = c.diff(ySol, x);
    if (dy.isNull())
        return false;
    const Expr d2y = c.diff(dy, x);
    if (d2y.isNull())
        return false;
    const Expr x2 = c.pow(x, c.number(std::int64_t{2}));
    const Expr lhs =
        c.add({c.mul({a, x2, d2y}), c.mul({b, x, dy}), c.mul({d, ySol})});
    return isZeroSimp(c, c.add({lhs, c.neg(f)}));
}

} // namespace

OdeResult dsolve2EulerCauchy(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
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

    // Indicial equation for y = x^r:
    //   a * r * (r - 1) + b * r + d = a * r^2 + (b - a) * r + d = 0
    const Expr bInd = c.simplify(c.add({b, c.neg(a)}));
    const Expr disc =
        c.simplify(c.add({c.pow(bInd, two), c.neg(c.mul({four, a, d}))}));

    Expr y1, y2;
    if (isZeroSimp(c, disc)) {
        // Repeated indicial root r = (a - b) / (2*a)
        const Expr r = c.simplify(c.div(c.neg(bInd), twoA));
        y1 = c.simplify(c.pow(x, r));
        y2 = c.simplify(c.mul({y1, c.func("log", x)}));
    } else if (c.kind(disc) == NodeKind::Number &&
               c.numberValue(disc).signum() < 0) {
        // Complex-conjugate indicial roots alpha +- i*omega:
        // y1 = x^alpha * cos(omega * log(x)), y2 = x^alpha * sin(omega * log(x))
        const Expr alpha = c.simplify(c.div(c.neg(bInd), twoA));
        const Expr negDisc = c.neg(disc);
        const std::vector<Expr> wRoots = solveSymbolic(
            c, c.add({c.mul({four, c.pow(a, two), c.pow(x, two)}), c.neg(negDisc)}),
            x, budget);
        Expr omega = wRoots.empty()
                         ? c.simplify(c.div(
                               c.pow(negDisc, c.number(Rational(std::int64_t{1}, BigInt(2)))),
                               twoA))
                         : wRoots.back();
        const Expr env = c.simplify(c.pow(x, alpha));
        const Expr logX = c.func("log", x);
        y1 = c.simplify(c.mul({env, c.func("cos", c.mul({omega, logX}))}));
        y2 = c.simplify(c.mul({env, c.func("sin", c.mul({omega, logX}))}));
    } else {
        // Distinct real/symbolic indicial roots r1, r2
        const Expr rSym = c.symbol("_ode_ec_r");
        const Expr indEq =
            c.add({c.mul({a, c.pow(rSym, two)}), c.mul({bInd, rSym}), d});
        const std::vector<Expr> roots = solveSymbolic(c, indEq, rSym, budget);
        if (roots.size() < 2) {
            out.reason = "unable to solve Euler-Cauchy indicial equation";
            return out;
        }
        y1 = c.simplify(c.pow(x, roots[0]));
        y2 = c.simplify(c.pow(x, roots[1]));
    }

    const Expr yh = c.simplify(c.add({c.mul({C1, y1}), c.mul({C2, y2})}));
    if (isZeroSimp(c, f)) {
        if (verifyOde2EulerCauchy(c, yh, a, b, d, f, x)) {
            out.status = OdeResult::Status::Proved;
            out.y = yh;
            return out;
        }
        out.reason = "Euler-Cauchy homogeneous solution failed verification";
        return out;
    }

    // Particular solution y_p(x):
    // 1. Variation of Parameters with leading coefficient a * x^2:
    //    u1 = -int y2 * f / (a * x^2 * W) dx,  u2 = int y1 * f / (a * x^2 * W) dx
    Expr yp;
    bool foundYp = false;
    {
        const Expr dy1 = c.diff(y1, x);
        const Expr dy2 = c.diff(y2, x);
        const Expr W =
            c.simplify(c.add({c.mul({y1, dy2}), c.neg(c.mul({dy1, y2}))}));
        if (!isZeroSimp(c, W)) {
            const Expr ax2W =
                c.simplify(c.mul({a, c.pow(x, two), W}));
            const Expr int1 = c.simplify(c.neg(c.div(c.mul({y2, f}), ax2W)));
            const Expr int2 = c.simplify(c.div(c.mul({y1, f}), ax2W));
            const RationalIntegral u1 = integrate(c, int1, x, budget);
            const RationalIntegral u2 = integrate(c, int2, x, budget);
            if (u1.proved() && u2.proved()) {
                yp = c.simplify(
                    c.add({c.mul({u1.F, y1}), c.mul({u2.F, y2})}));
                foundYp = verifyOde2EulerCauchy(c, yp, a, b, d, f, x);
            }
        }
    }

    // 2. Fallback: x = exp(t) reduction to constant-coefficient ODE
    //    a * Y''(t) + (b - a) * Y'(t) + d * Y(t) = f(exp(t))
    if (!foundYp) {
        const Expr tSym = c.symbol("_ode_ec_t");
        const Expr ft = c.simplify(c.subs(f, x, c.func("exp", tSym)));
        Expr Yp;
        if (tryUndeterminedCoeffs(c, a, bInd, d, ft, tSym, budget, Yp)) {
            yp = c.simplify(c.subs(Yp, tSym, c.func("log", x)));
            foundYp = verifyOde2EulerCauchy(c, yp, a, b, d, f, x);
        }
    }

    if (!foundYp) {
        out.reason =
            "Euler-Cauchy particular integral could not be determined or certified";
        return out;
    }

    const Expr yTotal = c.simplify(c.add({yh, yp}));
    if (verifyOde2EulerCauchy(c, yTotal, a, b, d, f, x)) {
        out.status = OdeResult::Status::Proved;
        out.y = yTotal;
        return out;
    }

    out.reason = "combined Euler-Cauchy ODE solution failed verification";
    return out;
}

OdeResult dsolve2EulerCauchyIVP(Ctx &c, Expr a, Expr b, Expr d, Expr f, Expr x,
                                Expr x0, Expr y0, Expr dy0, Budget *budget)
{
    if (x0.isNull() || isZeroSimp(c, x0)) {
        OdeResult fail;
        fail.reason = "Euler-Cauchy initial point x0 must be non-zero";
        return fail;
    }

    OdeResult gen = dsolve2EulerCauchy(c, a, b, d, f, x, budget);
    if (!gen.proved())
        return gen;

    const Expr C1 = c.symbol("C1");
    const Expr C2 = c.symbol("C2");
    const Expr dyGen = c.diff(gen.y, x);

    const Expr yAt0 = c.simplify(c.subs(gen.y, x, x0));
    const Expr dyAt0 = c.simplify(c.subs(dyGen, x, x0));

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
    if (verifyOde2EulerCauchy(c, yIVP, a, b, d, f, x) &&
        isZeroSimp(c, c.add({c.subs(yIVP, x, x0), c.neg(y0)})) &&
        isZeroSimp(c, c.add({c.subs(dyIVP, x, x0), c.neg(dy0)}))) {
        OdeResult out;
        out.status = OdeResult::Status::Proved;
        out.y = yIVP;
        return out;
    }

    OdeResult fail;
    fail.reason = "Euler-Cauchy IVP solution failed verification";
    return fail;
}

// ============================================================================
// N-th Order Constant-Coefficient Linear ODE Solver
// ============================================================================

namespace {

bool verifyOdeN(Ctx &c, Expr ySol, const std::vector<Expr> &coeffs, Expr f,
                Expr x)
{
    if (ySol.isNull() || coeffs.size() < 2)
        return false;
    const std::size_t n = coeffs.size() - 1;
    std::vector<Expr> lhsTerms;
    Expr curDrv = ySol;
    for (std::size_t k = 0; k <= n; ++k) {
        if (k > 0) {
            curDrv = c.diff(curDrv, x);
            if (curDrv.isNull())
                return false;
        }
        if (!c.isZero(coeffs[k]))
            lhsTerms.push_back(c.mul({coeffs[k], curDrv}));
    }
    const Expr lhs = lhsTerms.empty() ? c.zero() : c.add(lhsTerms);
    return isZeroSimp(c, c.add({lhs, c.neg(f)}));
}

bool tryUndeterminedCoeffsN(Ctx &c, const std::vector<Expr> &coeffs, Expr f,
                            Expr x, Budget *budget, Expr &ypOut)
{
    const std::size_t n = coeffs.size() - 1;
    std::vector<Expr> rawAtoms;
    for (std::size_t k = 0; k <= n; ++k) {
        const Expr xk =
            (k == 0) ? c.one()
                     : c.pow(x, c.number(static_cast<std::int64_t>(k)));
        Expr cur = c.mul({xk, f});
        for (std::size_t drv = 0; drv < n + 2; ++drv) {
            if (drv > 0)
                cur = c.diff(cur, x);
            std::vector<std::pair<Expr, Expr>> terms;
            splitIntoBasisTerms(c, cur, x, terms);
            for (const auto &kv : terms)
                addUniqueAtom(c, rawAtoms, kv.second);
            if (rawAtoms.size() > 24)
                return false;
        }
    }

    auto applyL = [&](Expr phi) -> Expr {
        std::vector<Expr> terms;
        Expr curDrv = phi;
        for (std::size_t k = 0; k <= n; ++k) {
            if (k > 0)
                curDrv = c.diff(curDrv, x);
            if (!c.isZero(coeffs[k]))
                terms.push_back(c.mul({coeffs[k], curDrv}));
        }
        return terms.empty() ? c.zero() : c.simplify(c.add(terms));
    };

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
                rhsVec.at(r, 0) =
                    c.simplify(c.add({rhsVec.at(r, 0), kv.first}));
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

bool buildHomogeneousBasisN(Ctx &c, const std::vector<Expr> &coeffs, Expr x,
                            Budget *budget, std::vector<Expr> &basisOut)
{
    const std::size_t n = coeffs.size() - 1;
    basisOut.clear();

    // Check if all coefficients are rational numbers so we can factor P(lambda)
    // over Q with exact multiplicities via factorOverQ.
    bool allRational = true;
    std::vector<Rational> ratCoeffs(n + 1);
    for (std::size_t k = 0; k <= n; ++k) {
        const Expr ck = c.simplify(coeffs[k]);
        if (c.kind(ck) == NodeKind::Number) {
            ratCoeffs[k] = c.numberValue(ck);
        } else {
            allRational = false;
            break;
        }
    }

    if (allRational) {
        const UPoly charPoly(ratCoeffs);
        const std::vector<UPoly> rawFactors = factorOverQ(charPoly, budget);
        std::vector<std::pair<UPoly, std::size_t>> grouped;
        for (const UPoly &fac : rawFactors) {
            bool found = false;
            for (auto &gm : grouped) {
                if (gm.first == fac) {
                    gm.second += 1;
                    found = true;
                    break;
                }
            }
            if (!found)
                grouped.emplace_back(fac, 1);
        }

        std::size_t totalDeg = 0;
        bool supportedFactors = true;
        for (const auto &gm : grouped) {
            const int d = gm.first.deg();
            if (d != 1 && d != 2) {
                supportedFactors = false;
                break;
            }
            totalDeg += static_cast<std::size_t>(d) * gm.second;
        }

        if (supportedFactors && totalDeg == n) {
            const Expr two = c.number(std::int64_t{2});
            const Expr four = c.number(std::int64_t{4});
            for (const auto &gm : grouped) {
                const UPoly &fac = gm.first;
                const std::size_t mult = gm.second;
                if (fac.deg() == 1) {
                    // Monic linear factor: lambda + c0 = 0 => r = -c0
                    const Expr r = c.number(-fac.coeff(0));
                    const Expr expRx = c.simplify(c.func("exp", c.mul({r, x})));
                    for (std::size_t j = 0; j < mult; ++j) {
                        const Expr xj =
                            (j == 0)
                                ? c.one()
                                : c.pow(x, c.number(static_cast<std::int64_t>(j)));
                        basisOut.push_back(c.simplify(c.mul({xj, expRx})));
                    }
                } else if (fac.deg() == 2) {
                    // Monic quadratic factor: lambda^2 + p*lambda + q = 0
                    const Rational pRat = fac.coeff(1);
                    const Rational qRat = fac.coeff(0);
                    const Rational discRat =
                        pRat * pRat - Rational(std::int64_t{4}) * qRat;
                    const Expr pExpr = c.number(pRat);
                    const Expr qExpr = c.number(qRat);
                    if (discRat.signum() < 0) {
                        const Expr alpha =
                            c.number(-pRat / Rational(std::int64_t{2}));
                        const Expr negDisc = c.number(-discRat);
                        const std::vector<Expr> wRoots = solveSymbolic(
                            c,
                            c.add({c.mul({four, c.pow(x, two)}),
                                   c.neg(negDisc)}),
                            x, budget);
                        const Expr omega =
                            wRoots.empty()
                                ? c.simplify(c.div(
                                      c.pow(negDisc,
                                            c.number(Rational(std::int64_t{1},
                                                              BigInt(2)))),
                                      two))
                                : wRoots.back();
                        const Expr env =
                            c.simplify(c.func("exp", c.mul({alpha, x})));
                        const Expr cosWx = c.func("cos", c.mul({omega, x}));
                        const Expr sinWx = c.func("sin", c.mul({omega, x}));
                        for (std::size_t j = 0; j < mult; ++j) {
                            const Expr xj =
                                (j == 0)
                                    ? c.one()
                                    : c.pow(x, c.number(
                                                   static_cast<std::int64_t>(j)));
                            basisOut.push_back(
                                c.simplify(c.mul({xj, env, cosWx})));
                            basisOut.push_back(
                                c.simplify(c.mul({xj, env, sinWx})));
                        }
                    } else {
                        const Expr rSym = c.symbol("_ode_n_r");
                        const Expr quadEq = c.add(
                            {c.pow(rSym, two), c.mul({pExpr, rSym}), qExpr});
                        const std::vector<Expr> roots =
                            solveSymbolic(c, quadEq, rSym, budget);
                        if (roots.size() < 2) {
                            basisOut.clear();
                            break;
                        }
                        const Expr e1 =
                            c.simplify(c.func("exp", c.mul({roots[0], x})));
                        const Expr e2 =
                            c.simplify(c.func("exp", c.mul({roots[1], x})));
                        for (std::size_t j = 0; j < mult; ++j) {
                            const Expr xj =
                                (j == 0)
                                    ? c.one()
                                    : c.pow(x, c.number(
                                                   static_cast<std::int64_t>(j)));
                            basisOut.push_back(c.simplify(c.mul({xj, e1})));
                            basisOut.push_back(c.simplify(c.mul({xj, e2})));
                        }
                    }
                }
            }
            if (basisOut.size() == n)
                return true;
        }
    }

    // Symbolic / general fallback via solveSymbolic on P(r) = 0
    basisOut.clear();
    const Expr rSym = c.symbol("_ode_n_sym_r");
    std::vector<Expr> charTerms;
    for (std::size_t k = 0; k <= n; ++k) {
        const Expr rk =
            (k == 0) ? c.one()
                     : c.pow(rSym, c.number(static_cast<std::int64_t>(k)));
        charTerms.push_back(c.mul({coeffs[k], rk}));
    }
    const Expr charEq = c.add(charTerms);
    const std::vector<Expr> roots = solveSymbolic(c, charEq, rSym, budget);
    if (roots.empty())
        return false;

    // Determine algebraic multiplicity of each root by checking derivatives of charEq
    for (const Expr &r : roots) {
        std::size_t mult = 0;
        Expr drvEq = charEq;
        for (std::size_t m = 0; m < n; ++m) {
            if (m > 0)
                drvEq = c.diff(drvEq, rSym);
            if (isZeroSimp(c, c.subs(drvEq, rSym, r)))
                mult += 1;
            else
                break;
        }
        if (mult == 0)
            mult = 1;
        const Expr expRx = c.simplify(c.func("exp", c.mul({r, x})));
        for (std::size_t j = 0; j < mult && basisOut.size() < n; ++j) {
            const Expr xj =
                (j == 0) ? c.one()
                         : c.pow(x, c.number(static_cast<std::int64_t>(j)));
            basisOut.push_back(c.simplify(c.mul({xj, expRx})));
        }
    }

    return basisOut.size() == n;
}

SymMatrix buildCompanionMatrix(Ctx &c, const std::vector<Expr> &coeffs)
{
    const std::size_t n = coeffs.size() - 1;
    const Expr aN = coeffs[n];
    SymMatrix A = SymMatrix::zeros(c, n, n);
    for (std::size_t i = 0; i + 1 < n; ++i)
        A.at(i, i + 1) = c.one();
    for (std::size_t j = 0; j < n; ++j)
        A.at(n - 1, j) = c.simplify(c.neg(c.div(coeffs[j], aN)));
    return A;
}

} // namespace

OdeResult dsolveNLinear(Ctx &c, const std::vector<Expr> &coeffs, Expr f,
                        Expr x, Budget *budget)
{
    OdeResult out;
    if (coeffs.size() < 2 || f.isNull() || x.isNull()) {
        out.reason = "invalid N-th order ODE arguments";
        return out;
    }
    const std::size_t n = coeffs.size() - 1;
    for (const Expr &ck : coeffs) {
        if (ck.isNull() || mentionsSym(c, ck, x)) {
            out.reason = "coefficients must be non-null constants in x";
            return out;
        }
    }
    if (isZeroSimp(c, coeffs[n])) {
        out.reason = "leading coefficient coeffs[N] must be non-zero";
        return out;
    }
    if (!checkOdeBudget(c, budget)) {
        out.reason = "budget exhausted";
        return out;
    }

    if (n == 2) {
        OdeResult r2 =
            dsolve2Linear(c, coeffs[2], coeffs[1], coeffs[0], f, x, budget);
        if (r2.proved())
            return r2;
    }

    std::vector<Expr> basis;
    if (buildHomogeneousBasisN(c, coeffs, x, budget, basis) &&
        basis.size() == n) {
        std::vector<Expr> yhTerms;
        for (std::size_t i = 0; i < n; ++i) {
            const Expr Ci = c.symbol("C" + std::to_string(i + 1));
            yhTerms.push_back(c.mul({Ci, basis[i]}));
        }
        const Expr yh = c.simplify(c.add(yhTerms));

        if (isZeroSimp(c, f)) {
            if (verifyOdeN(c, yh, coeffs, f, x)) {
                out.status = OdeResult::Status::Proved;
                out.y = yh;
                return out;
            }
        } else {
            Expr yp;
            bool foundYp =
                tryUndeterminedCoeffsN(c, coeffs, f, x, budget, yp) &&
                verifyOdeN(c, yp, coeffs, f, x);

            // Fallback: Variation of Parameters via companion system
            if (!foundYp) {
                const SymMatrix A = buildCompanionMatrix(c, coeffs);
                std::vector<Expr> fVec(n, c.zero());
                fVec[n - 1] = c.simplify(c.div(f, coeffs[n]));
                const OdeSystemResult sysRes =
                    dsolveSystem1Linear(c, A, fVec, x, budget);
                if (sysRes.proved() && !sysRes.y.empty()) {
                    Expr candYp = sysRes.y[0];
                    for (std::size_t i = 0; i < n; ++i) {
                        candYp = c.subs(
                            candYp, c.symbol("C" + std::to_string(i + 1)),
                            c.zero());
                    }
                    candYp = c.simplify(candYp);
                    if (verifyOdeN(c, candYp, coeffs, f, x)) {
                        yp = candYp;
                        foundYp = true;
                    }
                }
            }

            if (foundYp) {
                const Expr yTotal = c.simplify(c.add({yh, yp}));
                if (verifyOdeN(c, yTotal, coeffs, f, x)) {
                    out.status = OdeResult::Status::Proved;
                    out.y = yTotal;
                    return out;
                }
            }
        }
    }

    // Full companion-matrix fallback
    {
        const SymMatrix A = buildCompanionMatrix(c, coeffs);
        std::vector<Expr> fVec(n, c.zero());
        fVec[n - 1] = c.simplify(c.div(f, coeffs[n]));
        const OdeSystemResult sysRes =
            dsolveSystem1Linear(c, A, fVec, x, budget);
        if (sysRes.proved() && !sysRes.y.empty() &&
            verifyOdeN(c, sysRes.y[0], coeffs, f, x)) {
            out.status = OdeResult::Status::Proved;
            out.y = sysRes.y[0];
            return out;
        }
    }

    out.reason =
        "N-th order constant-coefficient ODE could not be solved or certified";
    return out;
}

OdeResult dsolveNLinearIVP(Ctx &c, const std::vector<Expr> &coeffs, Expr f,
                           Expr x, Expr x0, const std::vector<Expr> &initVals,
                           Budget *budget)
{
    OdeResult out;
    if (coeffs.size() < 2 || x0.isNull() ||
        initVals.size() != coeffs.size() - 1) {
        out.reason = "invalid N-th order IVP arguments";
        return out;
    }
    const std::size_t n = coeffs.size() - 1;
    for (const Expr &iv : initVals) {
        if (iv.isNull()) {
            out.reason = "null initial condition value";
            return out;
        }
    }

    OdeResult gen = dsolveNLinear(c, coeffs, f, x, budget);
    if (!gen.proved())
        return gen;

    std::vector<Expr> cSyms(n);
    for (std::size_t j = 0; j < n; ++j)
        cSyms[j] = c.symbol("C" + std::to_string(j + 1));

    SymMatrix M = SymMatrix::zeros(c, n, n);
    SymMatrix rhs = SymMatrix::zeros(c, n, 1);

    Expr curDrv = gen.y;
    for (std::size_t k = 0; k < n; ++k) {
        if (k > 0)
            curDrv = c.diff(curDrv, x);
        const Expr drvAt0 = c.simplify(c.subs(curDrv, x, x0));
        Expr constPart = drvAt0;
        for (std::size_t j = 0; j < n; ++j) {
            M.at(k, j) = c.simplify(c.diff(drvAt0, cSyms[j]));
            constPart = c.subs(constPart, cSyms[j], c.zero());
        }
        constPart = c.simplify(constPart);
        rhs.at(k, 0) = c.simplify(c.add({initVals[k], c.neg(constPart)}));
    }

    const SymMatrix sol = linsolve(c, M, rhs, budget);
    if (sol.empty()) {
        out.reason = "singular Wronskian at initial point x0";
        return out;
    }

    Expr yIVP = gen.y;
    for (std::size_t j = 0; j < n; ++j)
        yIVP = c.subs(yIVP, cSyms[j], sol.at(j, 0));
    yIVP = c.simplify(yIVP);

    if (!verifyOdeN(c, yIVP, coeffs, f, x)) {
        out.reason = "N-th order IVP solution failed ODE certificate";
        return out;
    }

    Expr checkDrv = yIVP;
    for (std::size_t k = 0; k < n; ++k) {
        if (k > 0)
            checkDrv = c.diff(checkDrv, x);
        const Expr at0 = c.subs(checkDrv, x, x0);
        if (!isZeroSimp(c, c.add({at0, c.neg(initVals[k])}))) {
            out.reason = "N-th order IVP solution failed initial condition";
            return out;
        }
    }

    out.status = OdeResult::Status::Proved;
    out.y = yIVP;
    return out;
}

namespace {

bool verifyOdeSystem1Linear(Ctx &c, const std::vector<Expr> &ySol,
                            const SymMatrix &A, const std::vector<Expr> &f,
                            Expr x, Budget *budget)
{
    const std::size_t n = A.rows();
    if (ySol.size() != n || (!f.empty() && f.size() != n))
        return false;
    for (std::size_t i = 0; i < n; ++i) {
        if (!checkOdeBudget(c, budget) || ySol[i].isNull())
            return false;
        const Expr dyi = c.diff(ySol[i], x);
        if (dyi.isNull())
            return false;
        std::vector<Expr> rhsTerms;
        for (std::size_t j = 0; j < n; ++j) {
            if (!c.isZero(A.at(i, j)) && !c.isZero(ySol[j]))
                rhsTerms.push_back(c.mul({A.at(i, j), ySol[j]}));
        }
        if (!f.empty() && !f[i].isNull() && !c.isZero(f[i]))
            rhsTerms.push_back(f[i]);
        const Expr rhs = rhsTerms.empty() ? c.zero() : c.add(rhsTerms);
        const Expr residual = c.add({dyi, c.neg(rhs)});
        if (!isZeroSimp(c, residual)) {
            const Expr ratRes = simplifyRationalExpr(c, c.simplify(residual));
            if (ratRes.isNull() || !c.isZero(ratRes))
                return false;
        }
    }
    return true;
}

} // namespace

OdeSystemResult dsolveSystem1Linear(Ctx &c, const SymMatrix &A,
                                    const std::vector<Expr> &f, Expr x,
                                    Budget *budget)
{
    OdeSystemResult out;
    if (!A.isSquare() || A.empty() || x.isNull() ||
        c.kind(x) != NodeKind::Symbol) {
        out.reason = "invalid matrix or independent variable";
        return out;
    }
    const std::size_t n = A.rows();
    if (!f.empty() && f.size() != n) {
        out.reason = "forcing vector dimension mismatch";
        return out;
    }
    for (std::size_t r = 0; r < n; ++r) {
        for (std::size_t col = 0; col < n; ++col) {
            if (A.at(r, col).isNull() || mentionsSym(c, A.at(r, col), x)) {
                out.reason = "matrix A must have x-independent constant entries";
                return out;
            }
        }
    }

    const SymMatrix Phi = matrixExp(c, A, x, budget);
    if (Phi.empty()) {
        out.reason = "could not construct fundamental matrix exp(A*x)";
        return out;
    }

    std::vector<Expr> cVec(n);
    for (std::size_t i = 0; i < n; ++i)
        cVec[i] = c.symbol("C" + std::to_string(i + 1));

    const SymMatrix yHomMat = Phi.mul(c, SymMatrix::column(cVec));
    std::vector<Expr> ySol(n, c.zero());
    for (std::size_t i = 0; i < n; ++i)
        ySol[i] = simplify(c, yHomMat.at(i, 0), budget);

    bool hasForcing = false;
    for (const Expr &fi : f) {
        if (fi.isNull()) {
            out.reason = "null entry in forcing vector";
            return out;
        }
        if (!c.isZero(fi))
            hasForcing = true;
    }

    if (hasForcing) {
        // Variation of Parameters with Phi(x)^(-1) = exp(-A*x) = Phi(-x):
        // y_p(x) = Phi(x) * int Phi(-x) * f(x) dx
        const SymMatrix PhiInv = Phi.subs(c, x, c.neg(x));
        const SymMatrix integrandMat = PhiInv.mul(c, SymMatrix::column(f));
        SymMatrix intVec(n, 1, c.zero());
        for (std::size_t i = 0; i < n; ++i) {
            const Expr term = simplify(c, integrandMat.at(i, 0), budget);
            if (c.isZero(term))
                continue;
            const auto ant = integrate(c, term, x, budget);
            if (!ant.proved()) {
                out.reason = "could not integrate Variation of Parameters term";
                return out;
            }
            intVec.at(i, 0) = ant.F;
        }
        const SymMatrix ypMat = Phi.mul(c, intVec);
        for (std::size_t i = 0; i < n; ++i) {
            ySol[i] = simplify(c, c.add({ySol[i], ypMat.at(i, 0)}), budget);
        }
    }

    if (!verifyOdeSystem1Linear(c, ySol, A, f, x, budget)) {
        out.reason = "system ODE solution failed certificate verification";
        return out;
    }

    out.status = OdeSystemResult::Status::Proved;
    out.y = std::move(ySol);
    out.fundamental = Phi;
    return out;
}

OdeSystemResult dsolveSystem1Linear(Ctx &c, const SymMatrix &A, Expr x,
                                    Budget *budget)
{
    return dsolveSystem1Linear(c, A, {}, x, budget);
}

OdeSystemResult dsolveSystem1LinearIVP(Ctx &c, const SymMatrix &A,
                                       const std::vector<Expr> &f, Expr x,
                                       Expr x0, const std::vector<Expr> &y0,
                                       Budget *budget)
{
    OdeSystemResult out;
    if (!A.isSquare() || A.empty() || x.isNull() || x0.isNull() ||
        y0.size() != A.rows()) {
        out.reason = "invalid IVP arguments";
        return out;
    }
    const std::size_t n = A.rows();
    for (const Expr &yi0 : y0) {
        if (yi0.isNull()) {
            out.reason = "null initial value";
            return out;
        }
    }

    OdeSystemResult gen = dsolveSystem1Linear(c, A, f, x, budget);
    if (!gen.proved())
        return gen;

    // Extract particular solution y_p(x) by setting C1 = ... = Cn = 0
    std::vector<Expr> yp(n);
    for (std::size_t i = 0; i < n; ++i) {
        Expr e = gen.y[i];
        for (std::size_t j = 0; j < n; ++j)
            e = c.subs(e, c.symbol("C" + std::to_string(j + 1)), c.zero());
        yp[i] = simplify(c, e, budget);
    }

    // At x = x0: Phi(x0) * C + y_p(x0) = y0
    // Since Phi(x)^(-1) = Phi(-x), C = Phi(-x0) * (y0 - y_p(x0)) and
    // Phi(x) * C = Phi(x - x0) * (y0 - y_p(x0)).
    SymMatrix delta0(n, 1, c.zero());
    for (std::size_t i = 0; i < n; ++i) {
        const Expr ypAt0 = c.subs(yp[i], x, x0);
        delta0.at(i, 0) = simplify(c, c.add({y0[i], c.neg(ypAt0)}), budget);
    }

    const Expr shiftedX = c.add({x, c.neg(x0)});
    const SymMatrix PhiShifted = gen.fundamental.subs(c, x, shiftedX);
    const SymMatrix yHomIVP = PhiShifted.mul(c, delta0);

    std::vector<Expr> yIVP(n);
    for (std::size_t i = 0; i < n; ++i) {
        yIVP[i] = simplify(c, c.add({yHomIVP.at(i, 0), yp[i]}), budget);
    }

    if (!verifyOdeSystem1Linear(c, yIVP, A, f, x, budget)) {
        out.reason = "IVP system solution failed ODE certificate";
        return out;
    }
    for (std::size_t i = 0; i < n; ++i) {
        const Expr atX0 = c.subs(yIVP[i], x, x0);
        if (!isZeroSimp(c, c.add({atX0, c.neg(y0[i])}))) {
            out.reason = "IVP system solution failed initial condition at x0";
            return out;
        }
    }

    out.status = OdeSystemResult::Status::Proved;
    out.y = std::move(yIVP);
    out.fundamental = std::move(gen.fundamental);
    return out;
}

OdeSystemResult dsolveSystem1LinearIVP(Ctx &c, const SymMatrix &A, Expr x,
                                       Expr x0, const std::vector<Expr> &y0,
                                       Budget *budget)
{
    return dsolveSystem1LinearIVP(c, A, {}, x, x0, y0, budget);
}

} // namespace numkit::cas
