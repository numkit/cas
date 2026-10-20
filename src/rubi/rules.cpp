// rubi/rules.cpp — discrimination-tree traversal matcher (C2 step 2).
//
// Patterns linearize prefix-order into the trie; an edge carries the
// next term's (tag, value, ARITY) and the node for the term after
// it. matchAt(node, e) tries node's edges: a wildcard binds e's
// whole subtree and resumes at `next`; a structural edge requires
// the same tag and exact arity, then walks e's children through the
// chain. Reaching a leaf selects the rule. Step-2 scope: present
// matching only (no `_.` defaults, no AC normalization - exact
// canonical arity; rules with explicit `/` cannot match since the
// DAG canonicalizes division away - their step-3 matcher twin will
// handle that).
#include <numkit/cas/rubi/rules.hpp>
#include <numkit/cas/integrate/ratint.hpp>
#include <numkit/cas/integrate/verify.hpp>
#include <numkit/cas/poly/upoly.hpp>

#include <algorithm>
#include <array>
#include <functional>
#include <numeric>
#include <vector>

#include "rubi_tables_1111.inc"

namespace numkit::cas::rubi {

namespace {

bool exprMatchesTerm(const RuleTables &t, Ctx &c, Expr e,
                     std::int32_t tag, std::int32_t valId)
{
    switch (tag) {
    case kTagNum: {
        if (c.kind(e) != NodeKind::Number)
            return false;
        Rational r;
        return Rational::tryParse(r, t.str(valId)) &&
               c.numberValue(e) == r;
    }
    case kTagSym:
        return c.kind(e) == NodeKind::Symbol &&
               c.symbolName(e) == t.str(valId);
    case kTagHead:
        return c.kind(e) == NodeKind::Func &&
               c.funcName(e) == t.str(valId);
    case kTagOp: {
        // operators map onto Expr kinds; '/' canonicalizes away in
        // our DAG (a/b == a*b^-1), so patterns with explicit / are
        // matched by their canonicalized twin in step 3 - step 2
        // takes the exact kinds only.
        const char *op = t.str(valId);
        switch (c.kind(e)) {
        case NodeKind::Add: return op == std::string("+");
        case NodeKind::Mul: return op == std::string("*");
        case NodeKind::Pow: return op == std::string("^");
        default: return false;
        }
    }
    default:
        return false;
    }
}

const Binding *findBinding(const std::vector<Binding> &acc,
                           const std::string &name)
{
    for (const Binding &b : acc)
        if (b.name == name)
            return &b;
    return nullptr;
}

void upsertBinding(std::vector<Binding> &acc, const std::string &name,
                   Expr val)
{
    for (Binding &b : acc) {
        if (b.name == name) {
            b.value = val;
            return;
        }
    }
    acc.push_back(Binding{name, val});
}

using LeafCallback =
    std::function<bool(std::int32_t firstRule, const std::vector<Binding> &bnd)>;

// Prefix-trie walker with full backtracking over a pending-expression
// stack `work` (stored in reverse so `work.back()` is the next Expr
// to consume in prefix order; a null `Expr()` on `work` represents a
// synthesized default exponent `1` that may ONLY match an optional
// pattern variable `blank == "_."`, `opt == 1`). Calls `onLeaf`
// whenever `work` empties at a leaf node; stops and returns true as
// soon as `onLeaf` accepts.
bool matchStep(const RuleTables &t, Ctx &c, std::int32_t node,
               std::vector<Expr> &work, std::vector<Binding> &acc,
               const LeafCallback &onLeaf, bool inMul = false)
{
    if (work.empty()) {
        if (t.nodeRow(node, 3) != 0)
            return false; // pattern chain longer than expression
        const std::int32_t rule = t.nodeRow(node, 4);
        if (rule < 0)
            return false;
        return onLeaf(rule, acc);
    }

    const Expr e = work.back();
    const std::int32_t nEdges = t.nodeRow(node, 3);
    const std::int32_t first = t.nodeRow(node, 2);

    if (e.isNull()) {
        const Expr one = c.one();
        for (int ei = first; ei < first + nEdges; ++ei) {
            if (t.edgeRow(ei, 0) != kTagAny || !t.edgeRow(ei, 4))
                continue;
            const std::string vName = t.str(t.edgeRow(ei, 1));
            const Binding *existing = findBinding(acc, vName);
            if (!existing || !(existing->value == one))
                continue;
            work.pop_back();
            if (matchStep(t, c, t.edgeRow(ei, 2), work, acc, onLeaf, inMul))
                return true;
            work.push_back(e);
        }
        for (int ei = first; ei < first + nEdges; ++ei) {
            if (t.edgeRow(ei, 0) != kTagAny || !t.edgeRow(ei, 4))
                continue;
            const std::string vName = t.str(t.edgeRow(ei, 1));
            if (findBinding(acc, vName) != nullptr)
                continue;
            work.pop_back();
            acc.push_back(Binding{vName, one});
            if (matchStep(t, c, t.edgeRow(ei, 2), work, acc, onLeaf, inMul))
                return true;
            acc.pop_back();
            work.push_back(e);
        }
        return false;
    }

    // SPECIFICITY LADDER at every trie position:
    //   1. structural edges (exact tag/value, insertion order), with
    //      Mul factor permutation fallback (Orderless on Times);
    //   2a. optional-product synthesis (*[v_., w] with v := 1);
    //   2b. optional-sum synthesis (+[a_., w] with a := 0, inside Mul);
    //   2c. optional-power synthesis (^[w, m_.] with m := 1, inside Mul);
    //   3a. bound wildcard edges (non-linear pattern variable already
    //       in `acc` - an equality constraint, more specific than a
    //       fresh wildcard);
    //   3b. unbound wildcard edges (fresh pattern variable).
    for (int ei = first; ei < first + nEdges; ++ei) {
        const std::int32_t tag = t.edgeRow(ei, 0);
        if (tag == kTagAny)
            continue;
        const std::int32_t valId = t.edgeRow(ei, 1);
        const std::int32_t next = t.edgeRow(ei, 2);
        const std::int32_t arity = t.edgeRow(ei, 3);
        if (!exprMatchesTerm(t, c, e, tag, valId) ||
            static_cast<std::int32_t>(c.childCount(e)) != arity)
            continue;

        if (c.kind(e) == NodeKind::Mul && arity >= 2 && arity <= 4) {
            std::array<std::size_t, 4> perm = {{0, 1, 2, 3}};
            do {
                work.pop_back();
                for (std::int32_t ci = arity; ci > 0; --ci)
                    work.push_back(
                        c.child(e, perm[static_cast<std::size_t>(ci - 1)]));
                if (matchStep(t, c, next, work, acc, onLeaf, true))
                    return true;
                work.resize(work.size() - static_cast<std::size_t>(arity));
                work.push_back(e);
            } while (std::next_permutation(
                perm.begin(), perm.begin() + static_cast<std::size_t>(arity)));
        } else {
            work.pop_back();
            for (std::size_t ci = c.childCount(e); ci > 0; --ci)
                work.push_back(c.child(e, ci - 1));
            if (matchStep(t, c, next, work, acc, onLeaf, inMul))
                return true;
            work.resize(work.size() - c.childCount(e));
            work.push_back(e);
        }
    }

    if (c.kind(e) != NodeKind::Mul) {
        const Expr one = c.one();
        for (int ei = first; ei < first + nEdges; ++ei) {
            if (t.edgeRow(ei, 0) != kTagOp ||
                std::string(t.str(t.edgeRow(ei, 1))) != "*" ||
                t.edgeRow(ei, 3) != 2)
                continue;
            const std::int32_t next = t.edgeRow(ei, 2);
            const std::int32_t vFirst = t.nodeRow(next, 2);
            const std::int32_t vCount = t.nodeRow(next, 3);
            for (int ve = vFirst; ve < vFirst + vCount; ++ve) {
                if (t.edgeRow(ve, 0) != kTagAny || !t.edgeRow(ve, 4))
                    continue;
                const std::string vName = t.str(t.edgeRow(ve, 1));
                const std::int32_t afterV = t.edgeRow(ve, 2);
                const Binding *existing = findBinding(acc, vName);
                if (existing && !(existing->value == one))
                    continue;
                const std::size_t mark = acc.size();
                if (!existing)
                    acc.push_back(Binding{vName, one});
                if (matchStep(t, c, afterV, work, acc, onLeaf, inMul))
                    return true;
                acc.resize(mark);
            }
        }
    }

    if (inMul && c.kind(e) != NodeKind::Add && c.kind(e) != NodeKind::Number) {
        const Expr zero = c.zero();
        for (int ei = first; ei < first + nEdges; ++ei) {
            if (t.edgeRow(ei, 0) != kTagOp ||
                std::string(t.str(t.edgeRow(ei, 1))) != "+" ||
                t.edgeRow(ei, 3) != 2)
                continue;
            const std::int32_t next = t.edgeRow(ei, 2);
            const std::int32_t vFirst = t.nodeRow(next, 2);
            const std::int32_t vCount = t.nodeRow(next, 3);
            for (int ve = vFirst; ve < vFirst + vCount; ++ve) {
                if (t.edgeRow(ve, 0) != kTagAny || !t.edgeRow(ve, 4))
                    continue;
                const std::string vName = t.str(t.edgeRow(ve, 1));
                const std::int32_t afterV = t.edgeRow(ve, 2);
                const Binding *existing = findBinding(acc, vName);
                if (existing && !(existing->value == zero))
                    continue;
                const std::size_t mark = acc.size();
                if (!existing)
                    acc.push_back(Binding{vName, zero});
                if (matchStep(t, c, afterV, work, acc, onLeaf, inMul))
                    return true;
                acc.resize(mark);
            }
        }
    }

    if (inMul && c.kind(e) != NodeKind::Pow && c.kind(e) != NodeKind::Number) {
        for (int ei = first; ei < first + nEdges; ++ei) {
            if (t.edgeRow(ei, 0) != kTagOp ||
                std::string(t.str(t.edgeRow(ei, 1))) != "^" ||
                t.edgeRow(ei, 3) != 2)
                continue;
            work.pop_back();
            work.push_back(Expr());
            work.push_back(e);
            if (matchStep(t, c, t.edgeRow(ei, 2), work, acc, onLeaf, inMul))
                return true;
            work.pop_back();
            work.pop_back();
            work.push_back(e);
        }
    }

    for (int ei = first; ei < first + nEdges; ++ei) {
        if (t.edgeRow(ei, 0) != kTagAny)
            continue;
        const std::string vName = t.str(t.edgeRow(ei, 1));
        const Binding *existing = findBinding(acc, vName);
        if (!existing || !(existing->value == e))
            continue;
        work.pop_back();
        if (matchStep(t, c, t.edgeRow(ei, 2), work, acc, onLeaf, inMul))
            return true;
        work.push_back(e);
    }

    for (int ei = first; ei < first + nEdges; ++ei) {
        if (t.edgeRow(ei, 0) != kTagAny)
            continue;
        const std::string vName = t.str(t.edgeRow(ei, 1));
        if (findBinding(acc, vName) != nullptr)
            continue;
        work.pop_back();
        acc.push_back(Binding{vName, e});
        if (matchStep(t, c, t.edgeRow(ei, 2), work, acc, onLeaf, inMul))
            return true;
        acc.pop_back();
        work.push_back(e);
    }

    return false;
}

} // namespace

int matchFirst(const RuleTables &t, Ctx &c, Expr e,
               std::vector<Binding> &bindings)
{
    int matchedRule = -1;
    std::vector<Expr> work{e};
    std::vector<Binding> acc;
    matchStep(t, c, 0, work, acc,
              [&](std::int32_t rule, const std::vector<Binding> &bnd) {
                  matchedRule = rule;
                  bindings = bnd;
                  return true;
              });
    return matchedRule;
}

RuleTables sliceTables()
{
    // The generated arrays are file-static in the included .inc and
    // live in THIS translation unit - no extern declarations.
    RuleTables t;
    t.strings = kStrings;
    t.stringCount = &kStringCount;
    t.nodes = kNodes;
    t.edges = kEdges;
    t.repTerms = kRepTerms;
    t.condTerms = kCondTerms;
    t.rules = kRules;
    t.ruleCount = &kRuleCount;
    return t;
}

// ── Step 3a: rule execution with certification ────────────────

namespace {

bool mentionsVarRec(Ctx &c, Expr e, Expr var)
{
    if (e == var)
        return true;
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        if (mentionsVarRec(c, c.child(e, i), var))
            return true;
    return false;
}

} // namespace

namespace {

// Prefix-layout child addressing: child k of a term sits at
// childOff + (sum of the first k children's SUBTREE sizes); a
// subtree size is itself 1 + its children's sizes (induction on the
// same rule). Every consumer MUST go through child(), never
// childOff + k.
std::int32_t subtreeSize(const std::int32_t *terms, std::int32_t term);

std::int32_t childOf(const std::int32_t *terms, std::int32_t term, int k)
{
    const std::int32_t childOff = terms[term * 4 + 2];
    std::int32_t pos = childOff;
    for (int i = 0; i < k; ++i)
        pos += subtreeSize(terms, pos);
    return pos;
}

std::int32_t subtreeSize(const std::int32_t *terms, std::int32_t term)
{
    std::int32_t total = 1;
    const std::int32_t nkids = terms[term * 4 + 3];
    for (int i = 0; i < nkids; ++i)
        total += subtreeSize(terms, childOf(terms, term, i));
    return total;
}

constexpr int kMaxRubiDepth = 8;

Expr rubiApplyDepth(const RuleTables &t, Ctx &c, Expr e, Expr var, int depth);

bool evalCondition(const RuleTables &t, const std::int32_t *terms, Ctx &c,
                   Expr currentE, Expr var, const std::vector<Binding> &bnd,
                   std::int32_t term, int depth);

// Exact non-negative integer n-th root of a non-negative BigInt `m` (n >= 2).
bool nthRootExact(const BigInt &m, std::uint64_t n, BigInt &root)
{
    if (m.signum() < 0 || n < 2)
        return false;
    if (m.isZero() || m == BigInt(1)) {
        root = m;
        return true;
    }
    if (n == 2)
        return m.sqrtExact(root);
    BigInt lo(1), hi(2);
    while (BigInt::powUInt(hi, n) < m) {
        lo = hi;
        hi = hi * BigInt(2);
    }
    while (lo <= hi) {
        BigInt mid, rem;
        BigInt::divMod(lo + hi, BigInt(2), mid, rem);
        const BigInt p = BigInt::powUInt(mid, n);
        if (p == m) {
            root = mid;
            return true;
        }
        if (p < m)
            lo = mid + BigInt(1);
        else
            hi = mid - BigInt(1);
    }
    return false;
}

// Extract Numerator / Denominator (or Rubi's Numer / Denom) of a
// rational or rational-radical constant expression.
Expr extractNumerDenom(Ctx &c, Expr arg, bool isDenom)
{
    if (arg.isNull())
        return Expr();
    if (c.kind(arg) == NodeKind::Number) {
        const Rational &v = c.numberValue(arg);
        return isDenom ? c.number(Rational(v.den(), BigInt(1)))
                       : c.number(Rational(v.num(), BigInt(1)));
    }
    if (c.kind(arg) == NodeKind::Pow &&
        c.kind(c.child(arg, 0)) == NodeKind::Number &&
        c.kind(c.child(arg, 1)) == NodeKind::Number) {
        const Rational &v = c.numberValue(c.child(arg, 0));
        const Rational &e = c.numberValue(c.child(arg, 1));
        if (v.signum() <= 0)
            return Expr();
        if (e.signum() > 0) {
            const BigInt &part = isDenom ? v.den() : v.num();
            return c.pow(c.number(Rational(part, BigInt(1))), c.number(e));
        }
        const BigInt &part = isDenom ? v.num() : v.den();
        return c.pow(c.number(Rational(part, BigInt(1))), c.number(-e));
    }
    if (c.kind(arg) == NodeKind::Mul) {
        std::vector<Expr> parts;
        parts.reserve(c.childCount(arg));
        for (std::size_t i = 0; i < c.childCount(arg); ++i) {
            const Expr p = extractNumerDenom(c, c.child(arg, i), isDenom);
            if (p.isNull())
                return Expr();
            parts.push_back(p);
        }
        return c.mul(parts);
    }
    return isDenom ? c.one() : arg;
}

// Distribute factor `v` across an Add node `u` (or return `u * v`).
Expr distributeMul(Ctx &c, Expr u, Expr v)
{
    if (u.isNull() || v.isNull())
        return Expr();
    if (c.kind(u) == NodeKind::Add) {
        std::vector<Expr> parts;
        parts.reserve(c.childCount(u));
        for (std::size_t i = 0; i < c.childCount(u); ++i)
            parts.push_back(c.mul({v, c.child(u, i)}));
        return c.add(parts);
    }
    return c.mul({v, u});
}

// Base-B(x) expansion of polynomial P(x) times B(x)^r:
// writes P(x) = sum_k R_k(x) B(x)^k with deg(R_k) < deg(B), returning
// sum_k R_k(x) * BExpr^(r + k).
Expr expandPolyTimesBinomialPow(Ctx &c, const UPoly &P, const UPoly &B,
                                Expr BExpr, const Rational &r, Expr var)
{
    if (B.deg() < 1 || P.isZero())
        return c.zero();
    UPoly cur = P;
    Rational expK = r;
    std::vector<Expr> sumTerms;
    while (!cur.isZero()) {
        UPoly Q, R;
        UPoly::divMod(cur, B, Q, R);
        if (!R.isZero()) {
            for (std::size_t i = 0; i <= R.deg(); ++i) {
                if (R.coeff(i).isZero())
                    continue;
                Expr mono = c.number(R.coeff(i));
                if (i > 0) {
                    mono = c.mul(
                        {mono, c.pow(var, c.number(static_cast<std::int64_t>(i)))});
                }
                const Expr bPow = c.pow(BExpr, c.number(expK));
                if (bPow.isNull())
                    return Expr();
                sumTerms.push_back(c.mul({mono, bPow}));
            }
        }
        cur = Q;
        expK += Rational(std::int64_t{1});
    }
    return sumTerms.empty() ? c.zero() : c.add(sumTerms);
}

// Rubi's ExpandIntegrand[u, x]: expands polynomial products, base-B
// binomial products P(x)*(a+b*x^n)^r, and multi-factor rational
// functions over coprime binomial denominators.
Expr expandIntegrandExpr(Ctx &c, Expr u, Expr var)
{
    if (u.isNull())
        return Expr();
    if (c.kind(u) == NodeKind::Pow) {
        // Keep degree-2 positive powers on 1.1.2.1's reduction cascade;
        // expand other polynomial powers (e.g. (a + b*x^n)^p, n != 2).
        UPoly N, D;
        if (c.kind(c.child(u, 1)) == NodeKind::Number &&
            c.numberValue(c.child(u, 1)).den() == BigInt(1) &&
            c.numberValue(c.child(u, 1)).signum() > 0 &&
            toRational(c, c.child(u, 0), var, N, D) && D.isConst() &&
            N.deg() != 2) {
            const Expr ex = c.expand(u);
            return (ex == u) ? Expr() : ex;
        }
        return Expr();
    }
    if (c.kind(u) != NodeKind::Mul)
        return Expr();

    // Case 1: pure polynomial in var.
    UPoly N, D;
    if (toRational(c, u, var, N, D) && !D.isZero() && D.isConst()) {
        const UPoly P = N * UPoly(Rational(std::int64_t{1}) / D.coeff(0));
        const Expr ex = c.expand(toExpr(c, P, var));
        return (ex == u) ? Expr() : ex;
    }

    // Separate children of Mul into polynomial factors and non-polynomial
    // Pow(B_i(x), r_i) factors with polynomial bases B_i(x).
    struct BinomFactor
    {
        Expr baseExpr;
        UPoly basePoly;
        Rational exp;
    };
    UPoly polyProd(Rational(std::int64_t{1}));
    std::vector<BinomFactor> nonPoly;
    for (std::size_t i = 0; i < c.childCount(u); ++i) {
        const Expr ch = c.child(u, i);
        UPoly nCh, dCh;
        if (toRational(c, ch, var, nCh, dCh) && !dCh.isZero() && dCh.isConst()) {
            polyProd = polyProd * nCh *
                       UPoly(Rational(std::int64_t{1}) / dCh.coeff(0));
            continue;
        }
        if (c.kind(ch) == NodeKind::Pow &&
            c.kind(c.child(ch, 1)) == NodeKind::Number) {
            const Rational r = c.numberValue(c.child(ch, 1));
            UPoly nB, dB;
            if (toRational(c, c.child(ch, 0), var, nB, dB) && !dB.isZero() &&
                dB.isConst() && nB.deg() >= 1) {
                const UPoly B =
                    nB * UPoly(Rational(std::int64_t{1}) / dB.coeff(0));
                nonPoly.push_back({c.child(ch, 0), B, r});
                continue;
            }
        }
        return Expr();
    }

    // Case 2: P(x) * B(x)^r (single non-polynomial binomial power, r < 0 or fractional).
    if (nonPoly.size() == 1) {
        const BinomFactor &bf = nonPoly[0];
        const Expr ex = expandPolyTimesBinomialPow(
            c, polyProd, bf.basePoly, bf.baseExpr, bf.exp, var);
        return (ex.isNull() || ex == u) ? Expr() : ex;
    }

    // Case 3: P(x) * B_1(x)^r_1 * B_2(x)^r_2 ... where all but one have
    // negative integer exponents and at most one has fractional exponent:
    // if all r_i are negative integers, partial-fraction split via invMod!
    if (nonPoly.size() >= 2) {
        bool allNegInt = true;
        for (const BinomFactor &bf : nonPoly) {
            if (!(bf.exp.den() == BigInt(1)) || bf.exp.signum() >= 0) {
                allNegInt = false;
                break;
            }
        }
        if (allNegInt) {
            // Compute D_i = B_i^{|r_i|} for each factor.
            std::vector<UPoly> denFactors;
            UPoly totalDen(Rational(std::int64_t{1}));
            for (const BinomFactor &bf : nonPoly) {
                std::int64_t m = 0;
                if (!(-bf.exp.num()).fitsInt64(m) || m <= 0 || m > 12)
                    return Expr();
                UPoly di(Rational(std::int64_t{1}));
                for (std::int64_t k = 0; k < m; ++k)
                    di = di * bf.basePoly;
                denFactors.push_back(di);
                totalDen = totalDen * di;
            }
            UPoly quot, rem;
            UPoly::divMod(polyProd, totalDen, quot, rem);
            std::vector<Expr> pieces;
            if (!quot.isZero())
                pieces.push_back(c.expand(toExpr(c, quot, var)));

            UPoly curNum = rem;
            UPoly curDen = totalDen;
            for (std::size_t i = 0; i < nonPoly.size(); ++i) {
                const UPoly &Di = denFactors[i];
                UPoly otherDen, dummyRem;
                UPoly::divMod(curDen, Di, otherDen, dummyRem);
                UPoly numI;
                if (i + 1 == nonPoly.size()) {
                    numI = curNum;
                } else {
                    if (UPoly::gcd(otherDen, Di).deg() != 0)
                        return Expr(); // not coprime
                    const UPoly invOther = UPoly::invMod(otherDen, Di);
                    numI = (curNum * invOther) % Di;
                    UPoly nextNum, checkRem;
                    UPoly::divMod(curNum - numI * otherDen, Di, nextNum,
                                  checkRem);
                    curNum = nextNum;
                    curDen = otherDen;
                }
                if (!numI.isZero()) {
                    const Expr part = expandPolyTimesBinomialPow(
                        c, numI, nonPoly[i].basePoly, nonPoly[i].baseExpr,
                        nonPoly[i].exp, var);
                    if (part.isNull())
                        return Expr();
                    pieces.push_back(part);
                }
            }
            const Expr ex = pieces.empty() ? c.zero() : c.add(pieces);
            return (ex.isNull() || ex == u) ? Expr() : ex;
        }
    }
    return Expr();
}

// Evaluate a term forest (`t.repTerms` or `t.condTerms`) into an Expr,
// resolving bound pattern names and executing Rubi/Mathematica helper
// heads. Returns a null Expr for unsupported heads or invalid domain
// operations (honest decline).
Expr buildReplacement(const RuleTables &t, const std::int32_t *terms, Ctx &c,
                      Expr currentE, Expr var,
                      const std::vector<Binding> &bnd,
                      std::int32_t term, int depth)
{
    const std::int32_t tag = t.termRow(terms, term, 0);
    const std::int32_t valId = t.termRow(terms, term, 1);
    const std::int32_t nkids = t.termRow(terms, term, 3);
    switch (tag) {
    case kTagNum: {
        Rational r;
        if (!Rational::tryParse(r, t.str(valId)))
            return Expr();
        return c.number(r);
    }
    case kTagSym: {
        const std::string s = t.str(valId);
        for (const Binding &b : bnd)
            if (b.name == s)
                return b.value;
        if (c.kind(var) == NodeKind::Symbol && c.symbolName(var) == s)
            return var; // the integration variable itself
        return Expr(); // genuinely unbound
    }
    case kTagHead: {
        const std::string head = t.str(valId);
        if (nkids == 1 && (head == "Log" || head == "ArcTan" ||
                           head == "ArcTanh" || head == "ArcSinh" ||
                           head == "ArcCosh" || head == "ArcSin" ||
                           head == "ArcCos" || head == "Sin" ||
                           head == "Cos" || head == "Tan" ||
                           head == "Sinh" || head == "Cosh" ||
                           head == "Tanh")) {
            const Expr arg = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            if (arg.isNull())
                return Expr();
            if (head == "Log") return c.func("log", arg);
            if (head == "ArcTan") return c.func("atan", arg);
            if (head == "ArcTanh") return c.func("atanh", arg);
            if (head == "ArcSinh") return c.func("asinh", arg);
            if (head == "ArcCosh") return c.func("acosh", arg);
            if (head == "ArcSin") return c.func("asin", arg);
            if (head == "ArcCos") return c.func("acos", arg);
            if (head == "Sin") return c.func("sin", arg);
            if (head == "Cos") return c.func("cos", arg);
            if (head == "Tan") return c.func("tan", arg);
            if (head == "Sinh") return c.func("sinh", arg);
            if (head == "Cosh") return c.func("cosh", arg);
            return c.func("tanh", arg);
        }
        if (nkids == 1 && head == "Sqrt") {
            const Expr arg = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            if (arg.isNull())
                return Expr();
            if (c.kind(arg) == NodeKind::Number) {
                const Rational &v = c.numberValue(arg);
                if (v.signum() < 0)
                    return Expr();
                BigInt rn, rd;
                if (v.num().sqrtExact(rn) && v.den().sqrtExact(rd))
                    return c.number(Rational(rn, rd));
            }
            return c.pow(arg,
                         c.number(Rational(BigInt(1), BigInt(2))));
        }
        if (nkids == 1 && (head == "IntPart" || head == "FracPart" ||
                           head == "Simplify" || head == "Numerator" ||
                           head == "Numer" || head == "Denominator" ||
                           head == "Denom")) {
            const Expr arg = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            if (arg.isNull())
                return Expr();
            if (head == "Simplify")
                return arg;
            if (head == "Numerator" || head == "Numer")
                return extractNumerDenom(c, arg, false);
            if (head == "Denominator" || head == "Denom")
                return extractNumerDenom(c, arg, true);
            if (c.kind(arg) != NodeKind::Number)
                return Expr();
            const Rational &v = c.numberValue(arg);
            BigInt q, r;
            BigInt::divMod(v.num(), v.den(), q, r);
            if (head == "IntPart")
                return c.number(Rational(q, BigInt(1)));
            return c.number(Rational(r, v.den()));
        }
        if (nkids == 2 && head == "Simp") {
            return buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
        }
        if (nkids == 3 && head == "Dist") {
            const Expr factor = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr body = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            return distributeMul(c, body, factor);
        }
        if (nkids == 2 && (head == "With" || head == "Module")) {
            const std::int32_t listTerm = childOf(terms, term, 0);
            if (t.termRow(terms, listTerm, 0) != kTagOp ||
                std::string(t.str(t.termRow(terms, listTerm, 1))) != "list")
                return Expr();
            std::vector<Binding> localBnd = bnd;
            const std::int32_t nDecls = t.termRow(terms, listTerm, 3);
            for (int i = 0; i < nDecls; ++i) {
                const std::int32_t decl = childOf(terms, listTerm, i);
                if (t.termRow(terms, decl, 0) == kTagSym)
                    continue; // uninitialized Module variable
                if (t.termRow(terms, decl, 0) != kTagOp ||
                    std::string(t.str(t.termRow(terms, decl, 1))) != "bind" ||
                    t.termRow(terms, decl, 3) != 2)
                    return Expr();
                const std::int32_t lhs = childOf(terms, decl, 0);
                const std::int32_t rhs = childOf(terms, decl, 1);
                if (t.termRow(terms, lhs, 0) != kTagSym)
                    return Expr();
                const Expr val = buildReplacement(
                    t, terms, c, currentE, var, localBnd, rhs, depth);
                if (val.isNull())
                    return Expr();
                upsertBinding(localBnd, t.str(t.termRow(terms, lhs, 1)), val);
            }
            return buildReplacement(
                t, terms, c, currentE, var, localBnd, childOf(terms, term, 1),
                depth);
        }
        if (nkids == 3 && head == "Subst") {
            const Expr xSym = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            const Expr subExpr = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 2), depth);
            if (xSym.isNull() || !(xSym == var) || subExpr.isNull())
                return Expr();
            const Expr body = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            if (body.isNull())
                return Expr();
            return c.subs(body, var, subExpr);
        }
        if (nkids == 2 && head == "ReplaceAll") {
            const std::int32_t ruleTerm = childOf(terms, term, 1);
            if (t.termRow(terms, ruleTerm, 0) != kTagOp ||
                std::string(t.str(t.termRow(terms, ruleTerm, 1))) != "->" ||
                t.termRow(terms, ruleTerm, 3) != 2)
                return Expr();
            const Expr u = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr from = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, ruleTerm, 0),
                depth);
            const Expr to = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, ruleTerm, 1),
                depth);
            if (u.isNull() || from.isNull() || to.isNull())
                return Expr();
            return c.subs(u, from, to);
        }
        if (nkids == 3 && head == "SubstFor") {
            // SubstFor[x^k, Pq, x]: express polynomial Pq(x) = sum c_{j*k} x^{j*k}
            // as sum c_{j*k} x^j.
            const Expr powExpr = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr u = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            const Expr xArg = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 2), depth);
            if (powExpr.isNull() || u.isNull() || !(xArg == var))
                return Expr();
            std::int64_t k = 1;
            if (powExpr == var) {
                k = 1;
            } else if (c.kind(powExpr) == NodeKind::Pow &&
                       c.child(powExpr, 0) == var &&
                       c.kind(c.child(powExpr, 1)) == NodeKind::Number &&
                       c.numberValue(c.child(powExpr, 1)).den() == BigInt(1) &&
                       c.numberValue(c.child(powExpr, 1)).num().fitsInt64(k) &&
                       k >= 1) {
                // ok
            } else {
                return Expr();
            }
            UPoly N, D;
            if (!toRational(c, u, var, N, D) || !D.isConst() || D.isZero())
                return Expr();
            const std::size_t ku = static_cast<std::size_t>(k);
            std::vector<Rational> coeffs(N.deg() / ku + 1, Rational(0));
            for (std::size_t i = 0; i <= N.deg(); ++i) {
                if (N.coeff(i).isZero())
                    continue;
                if (i % ku != 0)
                    return Expr();
                coeffs[i / ku] = N.coeff(i) / D.coeff(0);
            }
            return toExpr(c, UPoly(coeffs), var);
        }
        if (nkids == 2 && (head == "Expon" || head == "Exponent")) {
            const Expr u = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr xArg = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            if (u.isNull() || xArg.isNull())
                return Expr();
            std::int64_t k = 1;
            if (!(xArg == var)) {
                if (c.kind(xArg) == NodeKind::Pow && c.child(xArg, 0) == var &&
                    c.kind(c.child(xArg, 1)) == NodeKind::Number &&
                    c.numberValue(c.child(xArg, 1)).den() == BigInt(1) &&
                    c.numberValue(c.child(xArg, 1)).num().fitsInt64(k) && k >= 1) {
                    // polynomial in x^k
                } else {
                    return Expr();
                }
            }
            UPoly N, D;
            if (!toRational(c, u, var, N, D) || !D.isConst() || D.isZero())
                return Expr();
            return c.number(static_cast<std::int64_t>(N.deg()) / k);
        }
        if (nkids == 3 && (head == "Coeff" || head == "Coefficient")) {
            const Expr u = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr xArg = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            const Expr kExpr = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 2), depth);
            if (u.isNull() || xArg.isNull() || kExpr.isNull() ||
                c.kind(kExpr) != NodeKind::Number)
                return Expr();
            std::int64_t ki = 0;
            const Rational &kv = c.numberValue(kExpr);
            if (!(kv.den() == BigInt(1)) || !kv.num().fitsInt64(ki) || ki < 0)
                return Expr();
            std::int64_t step = 1;
            if (!(xArg == var)) {
                if (c.kind(xArg) == NodeKind::Pow && c.child(xArg, 0) == var &&
                    c.kind(c.child(xArg, 1)) == NodeKind::Number &&
                    c.numberValue(c.child(xArg, 1)).den() == BigInt(1) &&
                    c.numberValue(c.child(xArg, 1)).num().fitsInt64(step) &&
                    step >= 1) {
                    // ok
                } else {
                    return Expr();
                }
            }
            UPoly N, D;
            if (!toRational(c, u, var, N, D) || !D.isConst() || D.isZero())
                return Expr();
            return c.number(
                N.coeff(static_cast<std::size_t>(ki * step)) / D.coeff(0));
        }
        if (nkids == 3 && (head == "PolynomialQuotient" ||
                           head == "PolynomialRemainder")) {
            const Expr u = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr v = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            const Expr xArg = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 2), depth);
            if (u.isNull() || v.isNull() || !(xArg == var))
                return Expr();
            UPoly Nu, Du, Nv, Dv;
            if (!toRational(c, u, var, Nu, Du) || !Du.isConst() || Du.isZero() ||
                !toRational(c, v, var, Nv, Dv) || !Dv.isConst() || Dv.isZero() ||
                Nv.isZero())
                return Expr();
            const UPoly Pu = Nu * UPoly(Rational(std::int64_t{1}) / Du.coeff(0));
            const UPoly Pv = Nv * UPoly(Rational(std::int64_t{1}) / Dv.coeff(0));
            UPoly Q, R;
            UPoly::divMod(Pu, Pv, Q, R);
            return toExpr(c, head == "PolynomialQuotient" ? Q : R, var);
        }
        if (nkids == 2 && head == "ExpandToSum") {
            const Expr u = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr xArg = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            if (u.isNull() || !(xArg == var))
                return Expr();
            return c.expand(u);
        }
        if ((nkids == 2 || nkids == 3) && head == "ExpandIntegrand") {
            if (nkids == 2) {
                const Expr u = buildReplacement(
                    t, terms, c, currentE, var, bnd, childOf(terms, term, 0),
                    depth);
                const Expr xArg = buildReplacement(
                    t, terms, c, currentE, var, bnd, childOf(terms, term, 1),
                    depth);
                if (u.isNull() || !(xArg == var))
                    return Expr();
                return expandIntegrandExpr(c, u, var);
            }
            const Expr v = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr u = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            const Expr xArg = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 2), depth);
            if (v.isNull() || u.isNull() || !(xArg == var))
                return Expr();
            const Expr exU = expandIntegrandExpr(c, u, var);
            if (exU.isNull())
                return Expr();
            return distributeMul(c, exU, v);
        }
        if (nkids == 2 && head == "Int") {
            if (depth >= kMaxRubiDepth)
                return Expr();
            const Expr integrand = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr iVar = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            if (integrand.isNull() || c.kind(iVar) != NodeKind::Symbol)
                return Expr();
            if (integrand == currentE && iVar == var)
                return Expr();
            return rubiApplyDepth(t, c, integrand, iVar, depth + 1);
        }
        if (nkids == 2 && head == "Rt") {
            // Rubi's Rt[q, n]: the REAL n-th root - the sign rides
            // along for odd n (Rt[-a, n] = -Rt[a, n]); even roots of
            // negative numbers are non-real and decline.
            const Expr q = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr n = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            if (q.isNull() || c.kind(q) != NodeKind::Number ||
                n.isNull() || c.kind(n) != NodeKind::Number)
                return Expr();
            const Rational &nv = c.numberValue(n);
            std::int64_t ni = 0;
            if (!(nv.den() == BigInt(1)) || !nv.num().fitsInt64(ni) || ni < 2)
                return Expr();
            const Rational v = c.numberValue(q);
            if (v.signum() < 0 && (ni % 2 == 0))
                return Expr();
            const Rational absV = v.signum() >= 0 ? v : -v;
            BigInt rn, rd;
            if (nthRootExact(absV.num(), static_cast<std::uint64_t>(ni), rn) &&
                nthRootExact(absV.den(), static_cast<std::uint64_t>(ni), rd)) {
                const Rational rExact(v.signum() >= 0 ? rn : -rn, rd);
                return c.number(rExact);
            }
            const Expr invN = c.number(Rational(BigInt(1), BigInt(ni)));
            if (v.signum() >= 0)
                return c.pow(c.number(v), invN);
            return c.neg(c.pow(c.number(-v), invN));
        }
        if (nkids == 2 && head == "RemoveContent") {
            const Expr u = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr xArg = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            if (u.isNull() || xArg.isNull() ||
                c.kind(xArg) != NodeKind::Symbol)
                return Expr();
            UPoly N, D;
            if (!toRational(c, u, xArg, N, D) || !D.isConst() ||
                N.isZero())
                return Expr();
            BigInt numGcd(0), denLcm(1);
            for (const Rational &q : N.coeffs()) {
                numGcd = BigInt::gcd(numGcd, q.num());
                denLcm = BigInt::lcm(denLcm, q.den());
            }
            const Rational content(numGcd, denLcm);
            if (content.isZero())
                return u;
            std::vector<Rational> prim;
            for (const Rational &q : N.coeffs())
                prim.push_back(q / content);
            return toExpr(c, UPoly(prim), xArg);
        }
        return Expr();
    }
    case kTagOp: {
        const std::string op = t.str(valId);
        if (nkids == 1 && op == "neg") {
            const Expr a = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            return a.isNull() ? Expr() : c.neg(a);
        }
        if (nkids != 2)
            return Expr();
        if (op == "/;") {
            if (!evalCondition(t, terms, c, currentE, var, bnd,
                               childOf(terms, term, 1), depth))
                return Expr();
            return buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
        }
        if (op == ";") {
            const std::int32_t stmt = childOf(terms, term, 0);
            std::vector<Binding> localBnd = bnd;
            if (t.termRow(terms, stmt, 0) == kTagOp &&
                std::string(t.str(t.termRow(terms, stmt, 1))) == "bind" &&
                t.termRow(terms, stmt, 3) == 2) {
                const std::int32_t lhs = childOf(terms, stmt, 0);
                const std::int32_t rhs = childOf(terms, stmt, 1);
                if (t.termRow(terms, lhs, 0) != kTagSym)
                    return Expr();
                const Expr val = buildReplacement(
                    t, terms, c, currentE, var, localBnd, rhs, depth);
                if (val.isNull())
                    return Expr();
                upsertBinding(localBnd, t.str(t.termRow(terms, lhs, 1)), val);
                return buildReplacement(t, terms, c, currentE, var, localBnd,
                                        childOf(terms, term, 1), depth);
            }
            return Expr();
        }
        const Expr a = buildReplacement(
            t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
        const Expr bb = buildReplacement(
            t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
        if (a.isNull() || bb.isNull())
            return Expr();
        if (op == "+")
            return c.add({a, bb});
        if (op == "-")
            return c.add({a, c.neg(bb)});
        if (op == "*")
            return c.mul({a, bb});
        if (op == "/") {
            if (c.isZero(bb))
                return Expr();
            return c.div(a, bb);
        }
        if (op == "^") {
            if (c.isZero(a) && c.kind(bb) == NodeKind::Number &&
                c.numberValue(bb).signum() <= 0)
                return Expr();
            if (c.kind(a) == NodeKind::Number &&
                c.numberValue(a).signum() < 0 &&
                c.kind(bb) == NodeKind::Number &&
                !(c.numberValue(bb).den() == BigInt(1)))
                return Expr();
            return c.pow(a, bb);
        }
        return Expr();
    }
    default:
        return Expr();
    }
}

bool termMentionsVar(const RuleTables &t, const std::int32_t *terms, Ctx &c,
                     Expr var, const std::vector<Binding> &bnd,
                     std::int32_t term)
{
    const std::int32_t tag = t.termRow(terms, term, 0);
    const std::int32_t valId = t.termRow(terms, term, 1);
    const std::int32_t nkids = t.termRow(terms, term, 3);
    if (tag == kTagSym) {
        const std::string s = t.str(valId);
        for (const Binding &b : bnd)
            if (b.name == s)
                return mentionsVarRec(c, b.value, var);
        return c.kind(var) == NodeKind::Symbol && c.symbolName(var) == s;
    }
    for (int i = 0; i < nkids; ++i)
        if (termMentionsVar(t, terms, c, var, bnd, childOf(terms, term, i)))
            return true;
    return false;
}

bool evalCondition(const RuleTables &t, const std::int32_t *terms, Ctx &c,
                   Expr currentE, Expr var, const std::vector<Binding> &bnd,
                   std::int32_t term, int depth)
{
    const std::int32_t tag = t.termRow(terms, term, 0);
    const std::int32_t valId = t.termRow(terms, term, 1);
    const std::int32_t nkids = t.termRow(terms, term, 3);
    if (tag == kTagOp) {
        const std::string op = t.str(valId);
        if ((op == "&&" || op == "||") && nkids == 2) {
            const bool l = evalCondition(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            if (op == "&&" && !l)
                return false;
            if (op == "||" && l)
                return true;
            return evalCondition(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
        }
        if ((op == "==" || op == "!=" || op == "<" || op == ">" ||
             op == "<=" || op == ">=") &&
            nkids == 2) {
            const Expr a = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
            const Expr b = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
            if (a.isNull() || b.isNull() || c.kind(a) != NodeKind::Number ||
                c.kind(b) != NodeKind::Number)
                return false;
            const Rational &va = c.numberValue(a);
            const Rational &vb = c.numberValue(b);
            if (op == "==") return va == vb;
            if (op == "!=") return !(va == vb);
            if (op == "<") return va < vb;
            if (op == ">") return va > vb;
            if (op == "<=") return va <= vb;
            return va >= vb;
        }
        return false;
    }
    if (tag != kTagHead || nkids < 1)
        return false;
    const std::string pred = t.str(valId);
    if (pred == "Not" && nkids == 1) {
        return !evalCondition(
            t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
    }
    if (pred == "FreeQ" && nkids == 2) {
        return !termMentionsVar(t, terms, c, var, bnd, childOf(terms, term, 0));
    }
    if (pred == "IntegersQ") {
        for (int i = 0; i < nkids; ++i) {
            const Expr a = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, i), depth);
            if (a.isNull() || c.kind(a) != NodeKind::Number ||
                !(c.numberValue(a).den() == BigInt(1)))
                return false;
        }
        return true;
    }
    if (pred == "LinearQ" && nkids == 2) {
        const Expr u = buildReplacement(
            t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
        const Expr xArg = buildReplacement(
            t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
        if (u.isNull() || !(xArg == var))
            return false;
        UPoly N, D;
        return toRational(c, u, var, N, D) && D.isConst() && !D.isZero() &&
               N.deg() == 1;
    }
    if ((pred == "PolyQ" || pred == "PolynomialQ") &&
        (nkids == 2 || nkids == 3)) {
        const Expr u = buildReplacement(
            t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
        const Expr xArg = buildReplacement(
            t, terms, c, currentE, var, bnd, childOf(terms, term, 1), depth);
        if (u.isNull() || xArg.isNull())
            return false;
        std::int64_t step = 1;
        if (!(xArg == var)) {
            if (c.kind(xArg) == NodeKind::Pow && c.child(xArg, 0) == var &&
                c.kind(c.child(xArg, 1)) == NodeKind::Number &&
                c.numberValue(c.child(xArg, 1)).den() == BigInt(1) &&
                c.numberValue(c.child(xArg, 1)).num().fitsInt64(step) &&
                step >= 1) {
                // polynomial in x^step
            } else {
                return false;
            }
        }
        UPoly N, D;
        if (!toRational(c, u, var, N, D) || !D.isConst() || D.isZero() ||
            N.deg() < 1)
            return false;
        const std::size_t su = static_cast<std::size_t>(step);
        for (std::size_t i = 0; i <= N.deg(); ++i)
            if (!N.coeff(i).isZero() && (i % su != 0))
                return false;
        if (nkids == 3) {
            const Expr dExpr = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, 2), depth);
            std::int64_t di = 0;
            if (dExpr.isNull() || c.kind(dExpr) != NodeKind::Number ||
                !(c.numberValue(dExpr).den() == BigInt(1)) ||
                !c.numberValue(dExpr).num().fitsInt64(di) || di < 0)
                return false;
            return N.deg() == static_cast<std::size_t>(di * step);
        }
        return true;
    }
    if (pred == "IntLinearQ" && nkids == 7) {
        const Expr em = buildReplacement(
            t, terms, c, currentE, var, bnd, childOf(terms, term, 4), depth);
        const Expr en = buildReplacement(
            t, terms, c, currentE, var, bnd, childOf(terms, term, 5), depth);
        if (em.isNull() || c.kind(em) != NodeKind::Number ||
            en.isNull() || c.kind(en) != NodeKind::Number)
            return false;
        const Rational m = c.numberValue(em);
        const Rational n = c.numberValue(en);
        const Rational zero(0);
        const auto isInt = [](const Rational &r) {
            return r.den() == BigInt(1);
        };
        if (isInt(m) && m > zero) return true;
        if (isInt(n) && n > zero) return true;
        if (isInt(m * Rational(3)) && isInt(n * Rational(3))) return true;
        if (isInt(m * Rational(4)) && isInt(n * Rational(4))) return true;
        if (isInt(m * Rational(2)) && isInt(n * Rational(6))) return true;
        if (isInt(m * Rational(6)) && isInt(n * Rational(2))) return true;
        if (isInt(m + n)) return true;
        return false;
    }
    if (pred == "IntBinomialQ" &&
        (nkids == 7 || nkids == 8 || nkids == 10)) {
        std::array<Rational, 10> v;
        for (int i = 0; i < nkids - 1; ++i) {
            const Expr ai = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, i), depth);
            if (ai.isNull() || c.kind(ai) != NodeKind::Number)
                return false;
            v[static_cast<std::size_t>(i)] = c.numberValue(ai);
        }
        const auto isInt = [](const Rational &r) {
            return r.den() == BigInt(1);
        };
        const Rational zero(0);
        if (nkids == 7) {
            // IntBinomialQ[a, b, c, n, m, p, x]
            const Rational &n = v[3], &m = v[4], &p = v[5];
            if (isInt(p) && p > zero) return true;
            if (isInt(n) && isInt(p * Rational(2))) return true;
            if (!n.isZero() && isInt((m + Rational(1)) / n + p)) return true;
            if ((n == Rational(2) || n == Rational(4)) &&
                isInt(m * Rational(2)) && isInt(p * Rational(4)))
                return true;
            if (n == Rational(2) && isInt(p * Rational(6)) &&
                (isInt(m) || isInt(m - p)))
                return true;
            return false;
        }
        if (nkids == 8) {
            // IntBinomialQ[a, b, c, d, n, p, q, x]
            const Rational &a = v[0], &b = v[1], &cVal = v[2], &d = v[3];
            const Rational &n = v[4], &p = v[5], &q = v[6];
            if (isInt(p) && isInt(q)) return true;
            if (isInt(p) && p > zero) return true;
            if (isInt(q) && q > zero) return true;
            if ((n == Rational(2) || n == Rational(4)) &&
                ((isInt(p) && isInt(q * Rational(4))) ||
                 (isInt(p * Rational(4)) && isInt(q))))
                return true;
            if (n == Rational(2) &&
                ((isInt(p * Rational(2)) && isInt(q * Rational(2))) ||
                 (isInt(p * Rational(3)) && isInt(q) &&
                  (b * cVal + Rational(3) * a * d).isZero()) ||
                 (isInt(p) && isInt(q * Rational(3)) &&
                  (Rational(3) * b * cVal + a * d).isZero())))
                return true;
            if (n == Rational(3) &&
                ((isInt(p + Rational(1, BigInt(3))) && isInt(q)) ||
                 (isInt(q + Rational(1, BigInt(3))) && isInt(p))))
                return true;
            if (n == Rational(3) &&
                ((isInt(p + Rational(2, BigInt(3))) && isInt(q)) ||
                 (isInt(q + Rational(2, BigInt(3))) && isInt(p))) &&
                (b * cVal + a * d).isZero())
                return true;
            return false;
        }
        // nkids == 10: IntBinomialQ[a, b, c, d, e, m, n, p, q, x]
        const Rational &m = v[5], &n = v[6], &p = v[7], &q = v[8];
        if (isInt(p) && isInt(q)) return true;
        if (isInt(p) && p > zero) return true;
        if (isInt(q) && q > zero) return true;
        if (n == Rational(2) &&
            ((isInt(m) && isInt(p * Rational(2)) && isInt(q * Rational(2))) ||
             (isInt(m * Rational(2)) && isInt(p) && isInt(q * Rational(2))) ||
             (isInt(m * Rational(2)) && isInt(p * Rational(2)) && isInt(q))))
            return true;
        if (n == Rational(4) &&
            ((isInt(m) && isInt(p) && isInt(q * Rational(2))) ||
             (isInt(m) && isInt(p * Rational(2)) && isInt(q))))
            return true;
        return false;
    }
    if (pred == "PosQ" || pred == "NegQ" || pred == "IntegerQ" ||
        pred == "FractionQ" || pred == "RationalQ") {
        if (nkids != 1)
            return false;
        const Expr a = buildReplacement(
            t, terms, c, currentE, var, bnd, childOf(terms, term, 0), depth);
        if (a.isNull() || c.kind(a) != NodeKind::Number)
            return false;
        const Rational &va = c.numberValue(a);
        if (pred == "PosQ") return va.signum() > 0;
        if (pred == "NegQ") return va.signum() < 0;
        if (pred == "IntegerQ") return va.den() == BigInt(1);
        if (pred == "FractionQ") return !(va.den() == BigInt(1));
        return true; // RationalQ
    }
    if (pred == "NeQ" || pred == "EqQ" || pred == "GtQ" || pred == "LtQ" ||
        pred == "GeQ" || pred == "LeQ" || pred == "IGtQ" || pred == "ILtQ" ||
        pred == "IGeQ" || pred == "ILeQ") {
        if (nkids < 2 || nkids > 3)
            return false;
        std::array<Rational, 3> vals;
        for (int i = 0; i < nkids; ++i) {
            const Expr ai = buildReplacement(
                t, terms, c, currentE, var, bnd, childOf(terms, term, i), depth);
            if (ai.isNull() || c.kind(ai) != NodeKind::Number)
                return false;
            vals[static_cast<std::size_t>(i)] = c.numberValue(ai);
        }
        const Rational &va = vals[0];
        const Rational &vb = vals[1];
        if (pred == "IGtQ" || pred == "ILtQ" ||
            pred == "IGeQ" || pred == "ILeQ") {
            if (nkids == 2) {
                if (!(va.den() == BigInt(1)))
                    return false;
                if (pred == "IGtQ") return va > vb;
                if (pred == "ILtQ") return va < vb;
                if (pred == "IGeQ") return va >= vb;
                return va <= vb;
            }
            if (!(vb.den() == BigInt(1)))
                return false;
            if (pred == "IGtQ") return va > vb && vb > vals[2];
            if (pred == "ILtQ") return va < vb && vb < vals[2];
            if (pred == "IGeQ") return va >= vb && vb >= vals[2];
            return va <= vb && vb <= vals[2];
        }
        auto cmpPair = [&](const Rational &x, const Rational &y) -> bool {
            if (pred == "EqQ") return x == y;
            if (pred == "NeQ") return !(x == y);
            if (pred == "GtQ") return x > y;
            if (pred == "LtQ") return x < y;
            if (pred == "GeQ") return x >= y;
            return x <= y; // LeQ
        };
        if (nkids == 2)
            return cmpPair(va, vb);
        return cmpPair(va, vb) && cmpPair(vb, vals[2]);
    }
    return false;
}

} // namespace

namespace {

// Factor a positive rational v^(exp) into canonical prime-base powers
// prod_i p_i^(k_i * exp) so that e.g. 4^(-1/2) -> 1/2 and (3/2)^(1/2) ->
// 2^(-1/2)*3^(1/2).
Expr factorRationalPower(Ctx &c, const Rational &v, const Rational &exp)
{
    if (v == Rational(std::int64_t{1}) || exp.isZero())
        return c.one();
    std::vector<Expr> parts;
    for (const auto &pk : BigInt::factorize(v.num())) {
        parts.push_back(
            c.pow(c.number(Rational(pk.first, BigInt(1))),
                  c.number(exp * Rational(static_cast<std::int64_t>(pk.second)))));
    }
    for (const auto &pk : BigInt::factorize(v.den())) {
        parts.push_back(
            c.pow(c.number(Rational(pk.first, BigInt(1))),
                  c.number(-exp * Rational(static_cast<std::int64_t>(pk.second)))));
    }
    return parts.empty() ? c.one() : c.mul(parts);
}

// Canonicalize radical powers Pow(base, p/q) across an algebraic
// expression: positive rational bases factor into prime bases, and
// polynomial bases P(x) in Q[var] factor out their positive rational
// content c > 0 as c^(p/q) * P_prim(x)^(p/q).
Expr normalizeRadicals(Ctx &c, Expr e, Expr var)
{
    if (e.isNull())
        return Expr();
    switch (c.kind(e)) {
    case NodeKind::Add: {
        std::vector<Expr> items;
        items.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            items.push_back(normalizeRadicals(c, c.child(e, i), var));
        return c.add(items);
    }
    case NodeKind::Mul: {
        std::vector<Expr> items;
        items.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            items.push_back(normalizeRadicals(c, c.child(e, i), var));
        return c.mul(items);
    }
    case NodeKind::Pow: {
        const Expr base = normalizeRadicals(c, c.child(e, 0), var);
        const Expr exp = c.child(e, 1);
        if (c.kind(exp) == NodeKind::Number) {
            const Rational &r = c.numberValue(exp);
            if (!(r.den() == BigInt(1))) {
                if (c.kind(base) == NodeKind::Number &&
                    c.numberValue(base).signum() > 0) {
                    return factorRationalPower(c, c.numberValue(base), r);
                }
                UPoly N, D;
                if (toRational(c, base, var, N, D) && !D.isZero() &&
                    D.isConst() && N.deg() >= 1) {
                    const UPoly P =
                        N * UPoly(Rational(std::int64_t{1}) / D.coeff(0));
                    BigInt numGcd(0), denLcm(1);
                    for (const Rational &q : P.coeffs()) {
                        numGcd = BigInt::gcd(numGcd, q.num());
                        denLcm = BigInt::lcm(denLcm, q.den());
                    }
                    const Rational content(numGcd, denLcm);
                    if (!content.isZero()) {
                        std::vector<Rational> primCoeffs;
                        primCoeffs.reserve(P.coeffs().size());
                        for (const Rational &q : P.coeffs())
                            primCoeffs.push_back(q / content);
                        const Expr primExpr =
                            toExpr(c, UPoly(primCoeffs), var);
                        return c.mul({factorRationalPower(c, content, r),
                                      c.pow(primExpr, exp)});
                    }
                }
            }
        }
        return c.pow(base, exp);
    }
    default:
        return e;
    }
}

// LCM of fractional exponent denominators in a product or power `q`
// (bounded to [2..12]; 0 when none or out of range).
std::int64_t radicalExponentLcm(const Ctx &c, Expr q)
{
    auto denomOf = [&](Expr node) -> std::int64_t {
        if (c.kind(node) != NodeKind::Pow ||
            c.kind(c.child(node, 1)) != NodeKind::Number)
            return 1;
        std::int64_t d = 1;
        if (!c.numberValue(c.child(node, 1)).den().fitsInt64(d) || d <= 0)
            return 0;
        return d;
    };
    std::int64_t L = 1;
    if (c.kind(q) == NodeKind::Pow) {
        L = denomOf(q);
    } else if (c.kind(q) == NodeKind::Mul) {
        for (std::size_t i = 0; i < c.childCount(q); ++i) {
            const std::int64_t d = denomOf(c.child(q, i));
            if (d <= 0)
                return 0;
            L = std::lcm(L, d);
            if (L > 12)
                return 0;
        }
    }
    return (L >= 2 && L <= 12) ? L : 0;
}

// Exact real sign (-1, +1, or 0 when zero/undefined/outside principal
// real domain) of a radical product `q` at `var = x0`.
int evalRadicalProductSign(Ctx &c, Expr e, const std::string &varName,
                           const Rational &x0)
{
    switch (c.kind(e)) {
    case NodeKind::Number:
        return c.numberValue(e).signum();
    case NodeKind::Symbol:
        return c.symbolName(e) == varName ? x0.signum() : 0;
    case NodeKind::Mul: {
        int s = 1;
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const int cs = evalRadicalProductSign(c, c.child(e, i), varName, x0);
            if (cs == 0)
                return 0;
            s *= cs;
        }
        return s;
    }
    case NodeKind::Pow: {
        if (c.kind(c.child(e, 1)) != NodeKind::Number)
            return 0;
        const Rational &exp = c.numberValue(c.child(e, 1));
        std::int64_t p = 0, q = 0;
        if (!exp.num().fitsInt64(p) || !exp.den().fitsInt64(q) || q <= 0)
            return 0;
        const int bs = evalRadicalProductSign(c, c.child(e, 0), varName, x0);
        if (bs == 0)
            return 0;
        if (q == 1)
            return (bs < 0 && (p % 2 != 0)) ? -1 : 1;
        return bs > 0 ? 1 : 0;
    }
    case NodeKind::Add: {
        Rational val;
        if (!c.evalExact(e, {{varName, x0}}, val))
            return 0;
        return val.signum();
    }
    default:
        return 0;
    }
}

bool collectSingleLinearRadical(Ctx &c, Expr e, Expr var, Expr &radBase,
                                std::int64_t &qLcm)
{
    if (c.kind(e) == NodeKind::Func)
        return false;
    if (c.kind(e) == NodeKind::Pow && mentionsVarRec(c, c.child(e, 0), var)) {
        if (c.kind(c.child(e, 1)) != NodeKind::Number)
            return false;
        const Rational &r = c.numberValue(c.child(e, 1));
        if (!(r.den() == BigInt(1))) {
            std::int64_t q = 0;
            if (!r.den().fitsInt64(q) || q < 2 || q > 12)
                return false;
            if (radBase.isNull())
                radBase = c.child(e, 0);
            else if (!(radBase == c.child(e, 0)))
                return false;
            qLcm = std::lcm(qLcm, q);
            if (qLcm > 12)
                return false;
            return true;
        }
    }
    for (std::size_t i = 0; i < c.childCount(e); ++i)
        if (!collectSingleLinearRadical(c, c.child(e, i), var, radBase, qLcm))
            return false;
    return true;
}

Expr substLinearRadical(Ctx &c, Expr e, Expr var, Expr radBase,
                        std::int64_t qLcm, Expr tSym, Expr xOfT)
{
    if (e == var)
        return xOfT;
    if (c.kind(e) == NodeKind::Pow && c.child(e, 0) == radBase &&
        c.kind(c.child(e, 1)) == NodeKind::Number) {
        const Rational &r = c.numberValue(c.child(e, 1));
        const Rational newExp = r * Rational(qLcm);
        return c.pow(tSym, c.number(newExp));
    }
    if (c.kind(e) == NodeKind::Add || c.kind(e) == NodeKind::Mul) {
        std::vector<Expr> kids;
        kids.reserve(c.childCount(e));
        for (std::size_t i = 0; i < c.childCount(e); ++i)
            kids.push_back(substLinearRadical(c, c.child(e, i), var, radBase,
                                              qLcm, tSym, xOfT));
        return c.kind(e) == NodeKind::Add ? c.add(kids) : c.mul(kids);
    }
    if (c.kind(e) == NodeKind::Pow) {
        return c.pow(
            substLinearRadical(c, c.child(e, 0), var, radBase, qLcm, tSym, xOfT),
            c.child(e, 1));
    }
    return e;
}

bool checkNormalizedCertificate(Ctx &c, Expr dF, Expr e, Expr var)
{
    if (dF.isNull() || e.isNull() || c.isZero(e))
        return false;
    if (dF == e)
        return true;

    UPoly n1, d1, n2, d2;
    if (toRational(c, dF, var, n1, d1) && toRational(c, e, var, n2, d2))
        return n1 * d2 == n2 * d1;

    const Expr invE = c.pow(e, c.number(std::int64_t{-1}));
    if (invE.isNull())
        return false;
    const Expr Q = distributeMul(c, dF, invE);
    UPoly nQ, dQ;
    if (toRational(c, Q, var, nQ, dQ) && !dQ.isZero())
        return nQ == dQ;

    const std::int64_t L = radicalExponentLcm(c, Q);
    if (L >= 2) {
        const Expr QL = c.pow(Q, c.number(L));
        UPoly nQL, dQL;
        if (toRational(c, QL, var, nQL, dQL) && !dQL.isZero() && nQL == dQL) {
            if (L % 2 != 0)
                return true;
            const std::string &varName = c.symbolName(var);
            const std::array<Rational, 10> kSignSamples = {{
                Rational(std::int64_t{0}),
                Rational(std::int64_t{1}, BigInt(8)),
                Rational(std::int64_t{1}, BigInt(2)),
                Rational(std::int64_t{5}, BigInt(4)),
                Rational(std::int64_t{3}),
                Rational(std::int64_t{16}),
                Rational(std::int64_t{-1}, BigInt(8)),
                Rational(std::int64_t{-1}, BigInt(2)),
                Rational(std::int64_t{-3}),
                Rational(std::int64_t{-16}),
            }};
            for (const Rational &x0 : kSignSamples) {
                const int s = evalRadicalProductSign(c, Q, varName, x0);
                if (s != 0)
                    return s > 0;
            }
        }
    }
    return false;
}

bool certificateHolds(Ctx &c, Expr F, Expr e, Expr var)
{
    if (F.isNull() || c.isZero(e))
        return false;

    const Expr dF = c.diff(F, var);
    if (dF.isNull())
        return false;
    if (checkNormalizedCertificate(c, dF, e, var))
        return true;

    const Expr dFNorm = normalizeRadicals(c, dF, var);
    const Expr eNorm = normalizeRadicals(c, e, var);
    if (checkNormalizedCertificate(c, dFNorm, eNorm, var))
        return true;

    // Single linear radical rationalizing substitution t = (c0 + c1*x)^(1/q):
    Expr radBase;
    std::int64_t qLcm = 1;
    if (collectSingleLinearRadical(c, dFNorm, var, radBase, qLcm) &&
        collectSingleLinearRadical(c, eNorm, var, radBase, qLcm) &&
        !radBase.isNull() && qLcm >= 2) {
        UPoly nB, dB;
        if (toRational(c, radBase, var, nB, dB) && dB.isConst() &&
            !dB.isZero() && nB.deg() == 1) {
            const Rational c0 = nB.coeff(0) / dB.coeff(0);
            const Rational c1 = nB.coeff(1) / dB.coeff(0);
            const Expr tSym = c.symbol("_t_rad");
            const Expr xOfT =
                c.mul({c.number(Rational(std::int64_t{1}) / c1),
                       c.add({c.pow(tSym, c.number(qLcm)), c.number(-c0)})});
            const Expr dFT = substLinearRadical(c, dFNorm, var, radBase, qLcm,
                                                tSym, xOfT);
            const Expr eT = substLinearRadical(c, eNorm, var, radBase, qLcm,
                                               tSym, xOfT);
            if (checkNormalizedCertificate(c, dFT, eT, tSym))
                return true;
        }
    }
    return false;
}

Expr rubiLinearityFallback(const RuleTables &t, Ctx &c, Expr e, Expr var,
                           int depth)
{
    if (depth >= kMaxRubiDepth)
        return Expr();
    Expr F;
    if (c.kind(e) == NodeKind::Number) {
        F = c.mul({e, var});
    } else if (e == var) {
        F = c.mul({c.number(Rational(std::int64_t{1}, BigInt(2))),
                   c.pow(var, c.number(std::int64_t{2}))});
    } else if (c.kind(e) == NodeKind::Mul &&
               c.kind(c.child(e, 0)) == NodeKind::Number) {
        std::vector<Expr> rest;
        for (std::size_t i = 1; i < c.childCount(e); ++i)
            rest.push_back(c.child(e, i));
        const Expr inner = rubiApplyDepth(t, c, c.mul(rest), var, depth + 1);
        if (inner.isNull())
            return Expr();
        F = c.mul({c.child(e, 0), inner});
    } else if (c.kind(e) == NodeKind::Add) {
        std::vector<Expr> pieces;
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const Expr p = rubiApplyDepth(t, c, c.child(e, i), var, depth + 1);
            if (p.isNull())
                return Expr();
            pieces.push_back(p);
        }
        F = c.add(pieces);
    } else {
        return Expr();
    }
    return certificateHolds(c, F, e, var) ? F : Expr();
}

Expr rubiApplyDepth(const RuleTables &t, Ctx &c, Expr e, Expr var, int depth)
{
    if (depth > kMaxRubiDepth)
        return Expr();
    // Rubi 9.1 constant-factor pull-out FIRST: canonical Mul sorts its
    // lone numeric factor at child(0), and pulling it out before trie
    // matching ensures (c*x)^m * (...) (where Ctx::pow distributed c^m
    // into a separate Number child) presents the exact factor count
    // the binomial rules expect.
    if (c.kind(e) == NodeKind::Mul && c.childCount(e) >= 2 &&
        c.kind(c.child(e, 0)) == NodeKind::Number) {
        std::vector<Expr> rest;
        rest.reserve(c.childCount(e) - 1);
        for (std::size_t i = 1; i < c.childCount(e); ++i)
            rest.push_back(c.child(e, i));
        const Expr inner = rubiApplyDepth(t, c, c.mul(rest), var, depth + 1);
        if (inner.isNull())
            return Expr();
        const Expr F = c.mul({c.child(e, 0), inner});
        return certificateHolds(c, F, e, var) ? F : Expr();
    }

    struct CandidateHit
    {
        std::int32_t rule;
        std::vector<Binding> bnd;
    };
    std::vector<CandidateHit> hits;
    std::vector<Expr> work{e};
    std::vector<Binding> acc;
    matchStep(
        t, c, 0, work, acc,
        [&](std::int32_t firstRule, const std::vector<Binding> &bnd) {
            for (std::int32_t rule = firstRule; rule >= 0;
                 rule = t.ruleRow(rule, 3)) {
                hits.push_back(CandidateHit{rule, bnd});
            }
            return false;
        });
    std::stable_sort(hits.begin(), hits.end(),
                     [](const CandidateHit &a, const CandidateHit &b) {
                         return a.rule < b.rule;
                     });
    for (const CandidateHit &h : hits) {
        const std::int32_t repOff = t.ruleRow(h.rule, 0);
        const std::int32_t condOff = t.ruleRow(h.rule, 1);
        if (condOff >= 0 &&
            !evalCondition(t, t.condTerms, c, e, var, h.bnd, condOff, depth))
            continue;
        const Expr F = buildReplacement(
            t, t.repTerms, c, e, var, h.bnd, repOff, depth);
        if (F.isNull())
            continue;
        if (certificateHolds(c, F, e, var))
            return F;
    }
    return rubiLinearityFallback(t, c, e, var, depth);
}

} // namespace

Expr rubiApply(const RuleTables &t, Ctx &c, Expr e, Expr var)
{
    return rubiApplyDepth(t, c, e, var, 0);
}

} // namespace numkit::cas::rubi
