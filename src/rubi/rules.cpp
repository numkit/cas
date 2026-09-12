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
#include <numkit/cas/poly/upoly.hpp>

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

// Returns the trie position after e's pattern-subtree, or -1.
// Bindings from successful branches stay in `acc`; on failure the
// caller retries other edges (the pushed bindings of a failed branch
// are dropped by retrying from `acc.size()` snapshot).
std::int32_t matchAt(const RuleTables &t, Ctx &c, std::int32_t node,
                     Expr e, std::vector<Binding> &acc);

// Optional-product default synthesis (Mathematica's `_.`): the
// pattern *[v_., w] against an expression WITHOUT a Mul node means
// the coefficient folded away - v := 1 and w must match the bare
// expression itself. Covers the canonicalizer's 1*x = x (so
// (2 + x)^4 reaches the (a + b x)^m rule with b := 1).
std::int32_t tryOptionalProduct(const RuleTables &t, Ctx &c,
                                std::int32_t node, Expr e,
                                std::vector<Binding> &acc)
{
    if (c.kind(e) == NodeKind::Mul)
        return -1; // a real Mul goes through the structural branch
    const std::int32_t nEdges = t.nodeRow(node, 3);
    const std::int32_t first = t.nodeRow(node, 2);
    for (int ei = first; ei < first + nEdges; ++ei) {
        const std::int32_t valId = t.edgeRow(ei, 1);
        const std::int32_t next = t.edgeRow(ei, 2);
        const std::int32_t arity = t.edgeRow(ei, 3);
        if (t.edgeRow(ei, 0) != kTagOp ||
            std::string(t.str(valId)) != "*" || arity != 2)
            continue;
        // The OPTIONAL flag lives on the CHILD wildcard v_., not on
        // the * term itself; the factor position (child 1) may carry
        // MULTIPLE edge alternatives from different rules sharing
        // this prefix - delegate the choice to the general matcher,
        // whose edge order already encodes specificity.
        const std::int32_t vEdge = t.nodeRow(next, 2);
        bool hasOpt = false;
        std::int32_t afterV = -1;
        std::string vName;
        for (int ve = t.nodeRow(next, 2);
             ve < t.nodeRow(next, 2) + t.nodeRow(next, 3); ++ve) {
            if (t.edgeRow(ve, 0) == kTagAny && t.edgeRow(ve, 4)) {
                hasOpt = true;
                afterV = t.edgeRow(ve, 2);
                vName = t.str(t.edgeRow(ve, 1));
                break;
            }
        }
        if (!hasOpt)
            continue;
        const std::size_t mark = acc.size();
        acc.push_back(Binding{vName, c.number(std::int64_t{1})});
        // w matches the bare expression; the position after w IS the
        // position after the whole *[v_., w] subtree (w is its last
        // term), so the matcher's return value continues the chain.
        const std::int32_t res = matchAt(t, c, afterV, e, acc);
        if (res >= 0)
            return res;
        acc.resize(mark);
    }
    return -1;
}

std::int32_t matchAt(const RuleTables &t, Ctx &c, std::int32_t node,
                     Expr e, std::vector<Binding> &acc)
{
    const std::int32_t nEdges = t.nodeRow(node, 3);
    const std::int32_t first = t.nodeRow(node, 2);
    // SPECIFICITY LADDER at every trie position:
    //   1. structural edges (exact tag/value, insertion order);
    //   2. optional-product synthesis (a folded 1*x reading - still
    //      structural, but with a synthesized default, so it sits
    //      BELOW the direct structural edges: firing it inside pass
    //      1's edge loop let it jump ahead of later structural edges
    //      like a literal Symbol x);
    //   3. wildcard edges (match everything - always last).
    for (int ei = first; ei < first + nEdges; ++ei) {
        if (t.edgeRow(ei, 0) == kTagAny)
            continue;
        const std::size_t mark = acc.size();
        const std::int32_t next = t.edgeRow(ei, 2);
        if (exprMatchesTerm(t, c, e, t.edgeRow(ei, 0), t.edgeRow(ei, 1)) &&
            static_cast<std::int32_t>(c.childCount(e)) ==
                t.edgeRow(ei, 3)) {
            std::int32_t cur = next;
            bool ok = true;
            for (std::size_t ci = 0; ci < c.childCount(e); ++ci) {
                cur = matchAt(t, c, cur, c.child(e, ci), acc);
                if (cur < 0) {
                    ok = false;
                    break;
                }
            }
            if (ok)
                return cur;
            acc.resize(mark); // drop the failed branch's bindings
        }
    }
    {
        const std::int32_t opt = tryOptionalProduct(t, c, node, e, acc);
        if (opt >= 0)
            return opt;
    }
    for (int ei = first; ei < first + nEdges; ++ei) {
        if (t.edgeRow(ei, 0) != kTagAny)
            continue;
        // A wildcard consumes the whole subtree. Multiple wildcard
        // edges at one node are different pattern NAMES; the trie
        // merges continuations only for equal (tag, value), so the
        // first edge commits (pre-existing step-3 semantics - the
        // rule-level specificity sort put the winning name first).
        acc.push_back(Binding{t.str(t.edgeRow(ei, 1)), e});
        return t.edgeRow(ei, 2);
    }
    return -1;
}

} // namespace

int matchFirst(const RuleTables &t, Ctx &c, Expr e,
               std::vector<Binding> &bindings)
{
    // The root node's edges hold the alternatives for the FIRST
    // pattern term; a completed chain lands on a leaf carrying the
    // rule id.
    struct Walk
    {
        const RuleTables &t;
        Ctx &c;
        std::vector<Binding> acc;

        // The chain starts by consuming e against the root's edges,
        // exactly like matchAt but from the root.
        std::int32_t run(std::int32_t node, Expr ex)
        {
            return matchAt(t, c, node, ex, acc);
        }
    } w{t, c, {}};

    const std::int32_t end = w.run(0, e);
    if (end < 0)
        return -1;
    // `end` is the trie position after the last consumed term: a
    // LEAF (no edges) whose rule slot names the winner.
    if (t.nodeRow(end, 3) != 0)
        return -1; // pattern chain shorter than the expression
    const std::int32_t rule = t.nodeRow(end, 4);
    if (rule < 0)
        return -1;
    bindings = std::move(w.acc);
    return rule;
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

// Evaluate a replacement term forest into an Expr, resolving the
// bound pattern names; heads (Log...), operators and rational
// literals rebuild through the canonical constructors. Returns a
// null Expr for anything outside the step-3a subset (Subst, Int,
// Coefficient, RemoveContent, bind, list, ...). An unbound symbol
// that names the rule's integration variable resolves to `var` -
// the x_-literals in patterns bind nothing by design.
Expr buildReplacement(const RuleTables &t, Ctx &c, Expr var,
                      const std::vector<Binding> &bnd,
                      std::int32_t term)
{
    const std::int32_t tag = t.termRow(t.repTerms, term, 0);
    const std::int32_t valId = t.termRow(t.repTerms, term, 1);
    const std::int32_t childOff = t.termRow(t.repTerms, term, 2);
    const std::int32_t nkids = t.termRow(t.repTerms, term, 3);
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
        if (nkids == 1 && head == "Log") {
            const Expr arg =
                buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 0));
            if (arg.isNull())
                return Expr();
            return c.func("log", arg);
        }
        if (nkids == 1 && head == "ArcTan") {
            const Expr arg =
                buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 0));
            if (arg.isNull())
                return Expr();
            return c.func("atan", arg);
        }
        if (nkids == 1 && head == "Sqrt") {
            const Expr arg =
                buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 0));
            if (arg.isNull())
                return Expr();
            return c.pow(arg,
                         c.number(Rational(BigInt(1), BigInt(2))));
        }
        if (nkids == 2 && head == "Int") {
            // Recursive rule application: Rubi cascades into a new
            // integral (e.g. 1/((a+b x)(c+d x)) -> Int[1/(a c +
            // b d x^2)] when b c+a d==0 - landing on the atan rule).
            // The inner answer carries its own certificate and the
            // OUTER gate re-checks the final assembled derivative,
            // so a bad cascade cannot slip through.
            const Expr integrand =
                buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 0));
            const Expr iVar =
                buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 1));
            if (integrand.isNull() || c.kind(iVar) != NodeKind::Symbol)
                return Expr();
            return rubiApply(t, c, integrand, iVar);
        }
        if (nkids == 2 && head == "Rt") {
            // Rubi's Rt[q, n]: the REAL n-th root - the sign rides
            // along (Rt[-a, 2] = -Rt[a, 2]). Step scope: n == 2.
            const Expr q =
                buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 0));
            const Expr n =
                buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 1));
            if (q.isNull() || c.kind(q) != NodeKind::Number ||
                c.kind(n) != NodeKind::Number ||
                !(c.numberValue(n) == Rational(std::int64_t{2})))
                return Expr();
            const Rational v = c.numberValue(q);
            if (v.signum() >= 0)
                return c.pow(c.number(v),
                             c.number(Rational(BigInt(1), BigInt(2))));
            return c.neg(c.pow(c.number(-v),
                               c.number(Rational(BigInt(1), BigInt(2)))));
        }
        if (nkids == 2 && head == "RemoveContent") {
            // Rubi's RemoveContent[u, x]: strip the RATIONAL CONTENT
            // of u as a polynomial in x - u = content * primitive,
            // return the primitive (2+4x -> 1+2x; 2+3x stays - its
            // content is 1). This normalizes Log arguments.
            const Expr u =
                buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 0));
            const Expr xArg =
                buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 1));
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
            const Expr a =
                buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 0));
            return a.isNull() ? Expr() : c.neg(a);
        }
        if (nkids != 2)
            return Expr();
        const Expr a =
            buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 0));
        const Expr bb =
            buildReplacement(t, c, var, bnd, childOf(t.repTerms, term, 1));
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
    if (tag != kTagHead || nkids < 1 || nkids > 2)
        return false; // unary PosQ/NegQ and binary predicates alike
    const std::string pred = t.str(valId);
    if (pred == "FreeQ") {
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
    if (pred == "NeQ" || pred == "EqQ" || pred == "GtQ" || pred == "LtQ" ||
        pred == "PosQ" || pred == "NegQ" || pred == "IntegerQ") {
        // numeric comparisons over the bound values; PosQ/NegQ/IntegerQ
        // take one argument (compare against zero / denominator one)
        const Expr a = buildReplacementCond(t, c, bnd, childOf(ct, term, 0));
        if (a.isNull() || c.kind(a) != NodeKind::Number) {
            return false;
        }
        const Rational va = c.numberValue(a);
        if (pred == "PosQ") {
            return va.signum() > 0;
        }
        if (pred == "NegQ")
            return va.signum() < 0;
        if (pred == "IntegerQ")
            return va.den() == BigInt(1);
        const Expr bb = buildReplacementCond(t, c, bnd, childOf(ct, term, 1));
        if (bb.isNull() || c.kind(bb) != NodeKind::Number)
            return false;
        const Rational vb = c.numberValue(bb);
        if (pred == "EqQ")
            return va == vb;
        if (pred == "NeQ")
            return !(va == vb);
        if (pred == "GtQ")
            return va > vb;
        return va < vb; // LtQ
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

// Tier-1 certificate, two grades: POLYNOMIAL when both sides are
// rational in var (cross-multiplied in Q(var) - node identity is too
// weak: d(log(1+2x)/4) is (1/2)(1+2x)^-1, structurally unlike
// 1/(2+4x) yet equal); STRUCTURAL fallback when they are not rational
// (fractional powers of the variable), where exact node identity is
// the strongest available check.
bool certificateHolds(Ctx &c, Expr F, Expr e, Expr var)
{
    UPoly n1, d1, n2, d2;
    const bool rational = toRational(c, c.diff(F, var), var, n1, d1) &&
                          toRational(c, e, var, n2, d2);
    if (rational)
        return n1 * d2 == n2 * d1;
    return c.diff(F, var) == e;
}

// Mirrors of Rubi's utility-tier identities (upstream implements
// them as helper code, not table rules; so do we): 9.1's constant
// rule Int[a_,x] := a*x and constant-factor pull-out Int[a_*u_,x] :=
// a*Int[u,x], plus IntSum's additivity over sums. They fire only
// after every table rule has declined, and the assembled answer
// passes the same certificate as a rule's replacement.
Expr rubiLinearityFallback(const RuleTables &t, Ctx &c, Expr e, Expr var)
{
    Expr F;
    if (c.kind(e) == NodeKind::Number) {
        // Rubi 9.1: Int[a_, x_Symbol] := a*x /; FreeQ[a, x] - a bare
        // Number is free of var by construction.
        F = c.mul({e, var});
    } else if (c.kind(e) == NodeKind::Mul &&
               c.kind(c.child(e, 0)) == NodeKind::Number) {
        // Rubi 9.1: Int[a_*u_, x_Symbol] := a*Int[u, x] /; FreeQ[a, x].
        // The canonical Mul sorts its lone numeric factor first.
        std::vector<Expr> rest;
        for (std::size_t i = 1; i < c.childCount(e); ++i)
            rest.push_back(c.child(e, i));
        const Expr inner = rubiApply(t, c, c.mul(rest), var);
        if (inner.isNull())
            return Expr();
        F = c.mul({c.child(e, 0), inner});
    } else if (c.kind(e) == NodeKind::Add) {
        // Rubi's IntSum: Int[u_+v_+...] := Int[u]+Int[v]+... - every
        // term must integrate or the whole sum declines (honesty).
        std::vector<Expr> pieces;
        for (std::size_t i = 0; i < c.childCount(e); ++i) {
            const Expr p = rubiApply(t, c, c.child(e, i), var);
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

} // namespace

Expr rubiApply(const RuleTables &t, Ctx &c, Expr e, Expr var)
{
    std::vector<Binding> bnd;
    int rule = matchFirst(t, c, e, bnd);
    if (rule < 0) {
        return rubiLinearityFallback(t, c, e, var);
    }
    // Rubi's IDENTICAL-PATTERN sign variants share one trie leaf and
    // try in chain (file) order: a declined condition falls through
    // to the twin.
    for (; rule >= 0; rule = t.ruleRow(rule, 3)) {
        const std::int32_t repOff = t.ruleRow(rule, 0);
        const std::int32_t condOff = t.ruleRow(rule, 1);
        if (condOff >= 0 && !evalCondition(t, c, var, bnd, condOff))
            continue; // condition declines - try the chain twin
        const Expr F = buildReplacement(t, c, var, bnd, repOff);
        if (F.isNull())
            continue; // replacement outside the subset - next twin
        if (certificateHolds(c, F, e, var))
            return F;
        // certificate rejected - try the chain twin
    }
    return rubiLinearityFallback(t, c, e, var);
}

} // namespace numkit::cas::rubi
