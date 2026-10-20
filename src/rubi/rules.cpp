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

using LeafCallback =
    std::function<bool(std::int32_t firstRule, const std::vector<Binding> &bnd)>;

// Prefix-trie walker with full backtracking over a pending-expression
// stack `work` (stored in reverse so `work.back()` is the next Expr
// to consume in prefix order). Calls `onLeaf` whenever `work` empties
// at a leaf node; stops and returns true as soon as `onLeaf` accepts.
bool matchStep(const RuleTables &t, Ctx &c, std::int32_t node,
               std::vector<Expr> &work, std::vector<Binding> &acc,
               const LeafCallback &onLeaf)
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

    // SPECIFICITY LADDER at every trie position:
    //   1. structural edges (exact tag/value, insertion order), with
    //      binary Mul commutativity fallback;
    //   2. optional-product synthesis (*[v_., w] with v := 1);
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

        work.pop_back();
        for (std::size_t ci = c.childCount(e); ci > 0; --ci)
            work.push_back(c.child(e, ci - 1));
        if (matchStep(t, c, next, work, acc, onLeaf))
            return true;
        work.resize(work.size() - c.childCount(e));

        // Commutativity of binary Mul (Mathematica's Orderless on Times):
        // Rubi writes one-sided exponent conditions in 1.1.1.2 (e.g.
        // LtQ[m, -1], GtQ[n, 0]) relying on u*v == v*u.
        if (c.kind(e) == NodeKind::Mul && arity == 2 &&
            !(c.child(e, 0) == c.child(e, 1))) {
            work.push_back(c.child(e, 0));
            work.push_back(c.child(e, 1));
            if (matchStep(t, c, next, work, acc, onLeaf))
                return true;
            work.resize(work.size() - 2);
        }
        work.push_back(e);
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
                if (matchStep(t, c, afterV, work, acc, onLeaf))
                    return true;
                acc.resize(mark);
            }
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
        if (matchStep(t, c, t.edgeRow(ei, 2), work, acc, onLeaf))
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
        if (matchStep(t, c, t.edgeRow(ei, 2), work, acc, onLeaf))
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

// conditions live in their own forest with the SAME row layout
Expr buildReplacementCond(const RuleTables &t, Ctx &c,
                          const std::vector<Binding> &bnd, std::int32_t term);

constexpr int kMaxRubiDepth = 8;

Expr rubiApplyDepth(const RuleTables &t, Ctx &c, Expr e, Expr var, int depth);

// Evaluate a replacement term forest into an Expr, resolving the
// bound pattern names; heads (Log...), operators and rational
// literals rebuild through the canonical constructors. Returns a
// null Expr for anything outside the step-3a subset (Subst,
// Coefficient, bind, list, ...). An unbound symbol
// that names the rule's integration variable resolves to `var` -
// the x_-literals in patterns bind nothing by design.
Expr buildReplacement(const RuleTables &t, Ctx &c, Expr currentE, Expr var,
                      const std::vector<Binding> &bnd,
                      std::int32_t term, int depth)
{
    const std::int32_t tag = t.termRow(t.repTerms, term, 0);
    const std::int32_t valId = t.termRow(t.repTerms, term, 1);
    const std::int32_t childOff = t.termRow(t.repTerms, term, 2);
    const std::int32_t nkids = t.termRow(t.repTerms, term, 3);
    (void)childOff;
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
                           head == "ArcCos")) {
            const Expr arg = buildReplacement(
                t, c, currentE, var, bnd, childOf(t.repTerms, term, 0), depth);
            if (arg.isNull())
                return Expr();
            if (head == "Log") return c.func("log", arg);
            if (head == "ArcTan") return c.func("atan", arg);
            if (head == "ArcTanh") return c.func("atanh", arg);
            if (head == "ArcSinh") return c.func("asinh", arg);
            if (head == "ArcCosh") return c.func("acosh", arg);
            if (head == "ArcSin") return c.func("asin", arg);
            return c.func("acos", arg);
        }
        if (nkids == 1 && head == "Sqrt") {
            const Expr arg = buildReplacement(
                t, c, currentE, var, bnd, childOf(t.repTerms, term, 0), depth);
            if (arg.isNull())
                return Expr();
            return c.pow(arg,
                         c.number(Rational(BigInt(1), BigInt(2))));
        }
        if (nkids == 1 && (head == "IntPart" || head == "FracPart" ||
                           head == "Denominator" || head == "Simplify")) {
            const Expr arg = buildReplacement(
                t, c, currentE, var, bnd, childOf(t.repTerms, term, 0), depth);
            if (arg.isNull())
                return Expr();
            if (head == "Simplify")
                return arg;
            if (c.kind(arg) != NodeKind::Number)
                return Expr();
            const Rational &v = c.numberValue(arg);
            if (head == "Denominator")
                return c.number(Rational(v.den(), BigInt(1)));
            BigInt q, r;
            BigInt::divMod(v.num(), v.den(), q, r);
            if (head == "IntPart")
                return c.number(Rational(q, BigInt(1)));
            return c.number(Rational(r, v.den()));
        }
        if (nkids == 2 && head == "Simp") {
            return buildReplacement(
                t, c, currentE, var, bnd, childOf(t.repTerms, term, 0), depth);
        }
        if (nkids == 2 && head == "Int") {
            if (depth >= kMaxRubiDepth)
                return Expr();
            // Recursive rule application: Rubi cascades into a new
            // integral (e.g. 1/((a+b x)(c+d x)) -> Int[1/(a c +
            // b d x^2)] when b c+a d==0 - landing on the atan rule).
            // The inner answer carries its own certificate and the
            // OUTER gate re-checks the final assembled derivative,
            // so a bad cascade cannot slip through.
            const Expr integrand = buildReplacement(
                t, c, currentE, var, bnd, childOf(t.repTerms, term, 0), depth);
            const Expr iVar = buildReplacement(
                t, c, currentE, var, bnd, childOf(t.repTerms, term, 1), depth);
            if (integrand.isNull() || c.kind(iVar) != NodeKind::Symbol)
                return Expr();
            if (integrand == currentE && iVar == var)
                return Expr();
            return rubiApplyDepth(t, c, integrand, iVar, depth + 1);
        }
        if (nkids == 2 && head == "Rt") {
            // Rubi's Rt[q, n]: the REAL n-th root - the sign rides
            // along (Rt[-a, n] = -Rt[a, n]).
            const Expr q = buildReplacement(
                t, c, currentE, var, bnd, childOf(t.repTerms, term, 0), depth);
            const Expr n = buildReplacement(
                t, c, currentE, var, bnd, childOf(t.repTerms, term, 1), depth);
            if (q.isNull() || c.kind(q) != NodeKind::Number ||
                n.isNull() || c.kind(n) != NodeKind::Number)
                return Expr();
            const Rational &nv = c.numberValue(n);
            std::int64_t ni = 0;
            if (!(nv.den() == BigInt(1)) || !nv.num().fitsInt64(ni) || ni < 2)
                return Expr();
            const Rational v = c.numberValue(q);
            const Expr invN = c.number(Rational(BigInt(1), BigInt(ni)));
            if (v.signum() >= 0)
                return c.pow(c.number(v), invN);
            return c.neg(c.pow(c.number(-v), invN));
        }
        if (nkids == 2 && head == "RemoveContent") {
            // Rubi's RemoveContent[u, x]: strip the RATIONAL CONTENT
            // of u as a polynomial in x - u = content * primitive,
            // return the primitive (2+4x -> 1+2x; 2+3x stays - its
            // content is 1). This normalizes Log arguments.
            const Expr u = buildReplacement(
                t, c, currentE, var, bnd, childOf(t.repTerms, term, 0), depth);
            const Expr xArg = buildReplacement(
                t, c, currentE, var, bnd, childOf(t.repTerms, term, 1), depth);
            if (u.isNull() || xArg.isNull() ||
                c.kind(xArg) != NodeKind::Symbol)
                return Expr();
            UPoly N, D;
            if (!toRational(c, u, xArg, N, D) || !D.isConst() ||
                N.isZero())
                return Expr();
            // content = gcd(numerators) / lcm(denominators)
            BigInt numGcd(0), denLcm(1);
            for (const Rational &q : N.coeffs()) {
                numGcd = BigInt::gcd(numGcd, q.num());
                denLcm = BigInt::lcm(denLcm, q.den());
            }
            const Rational content(numGcd, denLcm);
            if (content.isZero())
                return u; // constant input: nothing to strip
            std::vector<Rational> prim;
            for (const Rational &q : N.coeffs())
                prim.push_back(q / content);
            return toExpr(c, UPoly(prim), xArg);
        }
        return Expr(); // other heads: step-3b remainder
    }
    case kTagOp: {
        const std::string op = t.str(valId);
        if (nkids == 1 && op == "neg") {
            const Expr a = buildReplacement(
                t, c, currentE, var, bnd, childOf(t.repTerms, term, 0), depth);
            return a.isNull() ? Expr() : c.neg(a);
        }
        if (nkids != 2)
            return Expr();
        const Expr a = buildReplacement(
            t, c, currentE, var, bnd, childOf(t.repTerms, term, 0), depth);
        const Expr bb = buildReplacement(
            t, c, currentE, var, bnd, childOf(t.repTerms, term, 1), depth);
        if (a.isNull() || bb.isNull())
            return Expr();
        if (op == "+")
            return c.add({a, bb});
        if (op == "-")
            return c.add({a, c.neg(bb)});
        if (op == "*")
            return c.mul({a, bb});
        if (op == "/")
            return c.div(a, bb);
        if (op == "^")
            return c.pow(a, bb);
        return Expr();
    }
    default:
        return Expr();
    }
}

// Step-3a condition evaluation: FreeQ[list, x], NeQ[a, r], EqQ.
// Returns false on UNKNOWN predicates (the rule then declines).
bool evalCondition(const RuleTables &t, Ctx &c, Expr var,
                   const std::vector<Binding> &bnd, std::int32_t term)
{
    const std::int32_t tag = t.termRow(t.condTerms, term, 0);
    const std::int32_t valId = t.termRow(t.condTerms, term, 1);
    const std::int32_t nkids = t.termRow(t.condTerms, term, 3);
    const std::int32_t *ct = t.condTerms;
    if (tag == kTagOp) {
        const std::string op = t.str(valId);
        if ((op == "&&" || op == "||") && nkids == 2) {
            const bool l = evalCondition(t, c, var, bnd, childOf(ct, term, 0));
            if (op == "&&" && !l)
                return false;
            if (op == "||" && l)
                return true;
            return evalCondition(t, c, var, bnd, childOf(ct, term, 1));
        }
        return false;
    }
    if (tag != kTagHead || nkids < 1)
        return false;
    const std::string pred = t.str(valId);
    if (pred == "Not" && nkids == 1) {
        return !evalCondition(t, c, var, bnd, childOf(ct, term, 0));
    }
    if (pred == "FreeQ" && nkids == 2) {
        // FreeQ[name-or-{names...}, x]: no bound value mentions x.
        // Rubi writes both FreeQ[m, x] and FreeQ[{a, b}, x].
        const std::int32_t lt = childOf(ct, term, 0);
        const std::int32_t ltTag = t.termRow(ct, lt, 0);
        const std::int32_t ltVal = t.termRow(ct, lt, 1);
        std::vector<std::string> names;
        if (ltTag == kTagSym) {
            names.push_back(t.str(ltVal));
        } else if (ltTag == kTagOp &&
                   std::string(t.str(ltVal)) == "list") {
            const std::int32_t ln = t.termRow(ct, lt, 3);
            for (int i = 0; i < ln; ++i) {
                const std::int32_t st = childOf(ct, lt, i);
                if (t.termRow(ct, st, 0) != kTagSym)
                    return false;
                names.push_back(t.str(t.termRow(ct, st, 1)));
            }
        } else {
            return false;
        }
        for (const std::string &nm : names)
            for (const Binding &b : bnd)
                if (b.name == nm && mentionsVarRec(c, b.value, var))
                    return false;
        return true;
    }
    if (pred == "IntegersQ") {
        for (int i = 0; i < nkids; ++i) {
            const Expr a = buildReplacementCond(t, c, bnd, childOf(ct, term, i));
            if (a.isNull() || c.kind(a) != NodeKind::Number ||
                !(c.numberValue(a).den() == BigInt(1)))
                return false;
        }
        return true;
    }
    if (pred == "IntLinearQ" && nkids == 7) {
        // Rubi 1.1.1.2 line 44: IntLinearQ[a,b,c,d,m,n,x]
        const Expr em = buildReplacementCond(t, c, bnd, childOf(ct, term, 4));
        const Expr en = buildReplacementCond(t, c, bnd, childOf(ct, term, 5));
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
        if (isInt(m + n)) return true; // covers ILtQ[m+n, -1] || IntegerQ[m+n] && RationalQ[m]
        return false;
    }
    if (pred == "PosQ" || pred == "NegQ" || pred == "IntegerQ" ||
        pred == "FractionQ" || pred == "RationalQ") {
        if (nkids != 1)
            return false;
        const Expr a = buildReplacementCond(t, c, bnd, childOf(ct, term, 0));
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
            const Expr ai = buildReplacementCond(t, c, bnd, childOf(ct, term, i));
            if (ai.isNull() || c.kind(ai) != NodeKind::Number)
                return false;
            vals[static_cast<std::size_t>(i)] = c.numberValue(ai);
        }
        const Rational &va = vals[0];
        const Rational &vb = vals[1];
        if (pred == "IGtQ" || pred == "ILtQ" ||
            pred == "IGeQ" || pred == "ILeQ") {
            if (nkids != 2 || !(va.den() == BigInt(1)))
                return false;
            if (pred == "IGtQ") return va > vb;
            if (pred == "ILtQ") return va < vb;
            if (pred == "IGeQ") return va >= vb;
            return va <= vb;
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

// conditions live in their own forest with the SAME row layout
// (buildReplacement reads repTerms rows; this mirrors it for
// kCondTerms)
Expr buildReplacementCond(const RuleTables &t, Ctx &c,
                          const std::vector<Binding> &bnd, std::int32_t term)
{
    // mirror of buildReplacement over kCondTerms
    const std::int32_t tag = t.termRow(t.condTerms, term, 0);
    const std::int32_t valId = t.termRow(t.condTerms, term, 1);
    const std::int32_t nkids = t.termRow(t.condTerms, term, 3);
    const std::int32_t *ct = t.condTerms;
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
        return Expr();
    }
    case kTagHead: {
        const std::string head = t.str(valId);
        if (nkids == 1 && (head == "IntPart" || head == "FracPart" ||
                           head == "Denominator" || head == "Simplify")) {
            const Expr arg =
                buildReplacementCond(t, c, bnd, childOf(ct, term, 0));
            if (arg.isNull())
                return Expr();
            if (head == "Simplify")
                return arg;
            if (c.kind(arg) != NodeKind::Number)
                return Expr();
            const Rational &v = c.numberValue(arg);
            if (head == "Denominator")
                return c.number(Rational(v.den(), BigInt(1)));
            BigInt q, r;
            BigInt::divMod(v.num(), v.den(), q, r);
            if (head == "IntPart")
                return c.number(Rational(q, BigInt(1)));
            return c.number(Rational(r, v.den()));
        }
        return Expr();
    }
    case kTagOp: {
        const std::string op = t.str(valId);
        if (nkids == 1 && op == "neg") {
            const Expr a = buildReplacementCond(t, c, bnd,
                                                childOf(ct, term, 0));
            return a.isNull() ? Expr() : c.neg(a);
        }
        if (nkids != 2)
            return Expr();
        const Expr a = buildReplacementCond(t, c, bnd, childOf(ct, term, 0));
        const Expr bb = buildReplacementCond(t, c, bnd, childOf(ct, term, 1));
        if (a.isNull() || bb.isNull())
            return Expr();
        if (op == "+")
            return c.add({a, bb});
        if (op == "*")
            return c.mul({a, bb});
        if (op == "-")
            return c.add({a, c.neg(bb)});
        if (op == "/")
            return c.div(a, bb);
        if (op == "^")
            return c.pow(a, bb);
        return Expr();
    }
    default:
        return Expr();
    }
}

} // namespace

namespace {

// Distribute `invE` across a top-level Add so like bases `(a+b*x^k)`
// in each additive term of `dF` merge their fractional exponents with
// `invE` inside `Ctx::makeMul`.
Expr distributeMul(Ctx &c, Expr dF, Expr invE)
{
    if (c.kind(dF) != NodeKind::Add)
        return c.mul({dF, invE});
    std::vector<Expr> terms;
    terms.reserve(c.childCount(dF));
    for (std::size_t i = 0; i < c.childCount(dF); ++i)
        terms.push_back(c.mul({c.child(dF, i), invE}));
    return c.add(terms);
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
        // Fractional power p/q: principal real root requires base > 0
        // and is always strictly positive.
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

// Certified derivative check on the assembled antiderivative F:
// unlike ratint (where Tier-1 checks the pre-assembly piece table),
// rubiApply differentiates the final Expr F itself via c.diff(F, var):
//  - Grade 1a (structural): dF == e (exact DAG node identity);
//  - Grade 1b (polynomial): dF and e in Q(var) -> cross-multiply;
//  - Grade 1c (quotient in Q(var)): distribute(dF * e^-1) == 1 in Q(var)
//    (certifies fractional-power reduction cascades where like bases
//    merge to integer exponents);
//  - Grade 1d (algebraic radical quotient): Q = dF * e^-1 has Q^L == 1
//    in Q(var) and exact principal-branch sign +1 on the real domain.
bool certificateHolds(Ctx &c, Expr F, Expr e, Expr var)
{
    if (F.isNull() || c.isZero(e))
        return false;

    const Expr dF = c.diff(F, var);
    if (dF.isNull())
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

// Mirrors of Rubi's utility-tier identities (upstream implements
// them as helper code, not table rules; so do we): 9.1's constant
// rule Int[a_,x] := a*x, OneIdentity linear monomial x -> x^2/2,
// constant-factor pull-out Int[a_*u_,x] := a*Int[u,x], plus IntSum's
// additivity over sums. They fire only after every table rule has
// declined, and the assembled answer passes the same certificate as
// a rule's replacement.
Expr rubiLinearityFallback(const RuleTables &t, Ctx &c, Expr e, Expr var,
                           int depth)
{
    if (depth >= kMaxRubiDepth)
        return Expr();
    Expr F;
    if (c.kind(e) == NodeKind::Number) {
        // Rubi 9.1: Int[a_, x_Symbol] := a*x /; FreeQ[a, x] - a bare
        // Number is free of var by construction.
        F = c.mul({e, var});
    } else if (e == var) {
        // OneIdentity elision for x_^m_. at m = 1: bare integration
        // variable integrates to 1/2*x^2 (and c*x lands here via the
        // constant-factor pull-out below).
        F = c.mul({c.number(Rational(std::int64_t{1}, BigInt(2))),
                   c.pow(var, c.number(std::int64_t{2}))});
    } else if (c.kind(e) == NodeKind::Mul &&
               c.kind(c.child(e, 0)) == NodeKind::Number) {
        // Rubi 9.1: Int[a_*u_, x_Symbol] := a*Int[u, x] /; FreeQ[a, x].
        // The canonical Mul sorts its lone numeric factor first.
        std::vector<Expr> rest;
        for (std::size_t i = 1; i < c.childCount(e); ++i)
            rest.push_back(c.child(e, i));
        const Expr inner = rubiApplyDepth(t, c, c.mul(rest), var, depth + 1);
        if (inner.isNull())
            return Expr();
        F = c.mul({c.child(e, 0), inner});
    } else if (c.kind(e) == NodeKind::Add) {
        // Rubi's IntSum: Int[u_+v_+...] := Int[u]+Int[v]+... - every
        // term must integrate or the whole sum declines (honesty).
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
    Expr answer;
    std::vector<Expr> work{e};
    std::vector<Binding> acc;
    const bool found = matchStep(
        t, c, 0, work, acc,
        [&](std::int32_t firstRule, const std::vector<Binding> &bnd) {
            // Rubi's IDENTICAL-PATTERN sign variants share one trie
            // leaf and try in chain (file) order; if the entire leaf
            // chain declines, returning false backtracks the trie walk
            // to the next matching pattern branch.
            for (std::int32_t rule = firstRule; rule >= 0;
                  rule = t.ruleRow(rule, 3)) {
                const std::int32_t repOff = t.ruleRow(rule, 0);
                const std::int32_t condOff = t.ruleRow(rule, 1);
                if (condOff >= 0 && !evalCondition(t, c, var, bnd, condOff))
                    continue;
                const Expr F =
                    buildReplacement(t, c, e, var, bnd, repOff, depth);
                if (F.isNull())
                    continue;
                if (certificateHolds(c, F, e, var)) {
                    answer = F;
                    return true;
                }
            }
            return false;
        });
    if (found)
        return answer;
    return rubiLinearityFallback(t, c, e, var, depth);
}

} // namespace

Expr rubiApply(const RuleTables &t, Ctx &c, Expr e, Expr var)
{
    return rubiApplyDepth(t, c, e, var, 0);
}

} // namespace numkit::cas::rubi
