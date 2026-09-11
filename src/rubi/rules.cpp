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
        const std::int32_t opt = t.edgeRow(ei, 4);
        if (t.edgeRow(ei, 0) != kTagOp ||
            std::string(t.str(valId)) != "*" || arity != 2 || !opt)
            continue;
        // Child 0 must be the optional wildcard v_., child 1 the
        // factor (a symbol like x, or a wildcard like u_).
        const std::int32_t vEdge = t.nodeRow(next, 2);
        if (t.nodeRow(next, 3) != 1 || t.edgeRow(vEdge, 0) != kTagAny ||
            !t.edgeRow(vEdge, 4))
            continue;
        const std::int32_t afterV = t.edgeRow(vEdge, 2);
        const std::int32_t wEdge = t.nodeRow(afterV, 2);
        if (t.nodeRow(afterV, 3) != 1)
            continue;
        // Position after the whole *[v_., w] subtree.
        const std::int32_t afterW = t.edgeRow(wEdge, 2);
        const std::size_t mark = acc.size();
        acc.push_back(Binding{t.str(t.edgeRow(vEdge, 1)),
                              c.number(std::int64_t{1})});
        const std::int32_t res =
            matchAt(t, c, afterV, e, acc); // w matches the bare expr
        if (res >= 0)
            return afterW;
        acc.resize(mark);
    }
    return -1;
}

std::int32_t matchAt(const RuleTables &t, Ctx &c, std::int32_t node,
                     Expr e, std::vector<Binding> &acc)
{
    const std::int32_t nEdges = t.nodeRow(node, 3);
    const std::int32_t first = t.nodeRow(node, 2);
    for (int ei = first; ei < first + nEdges; ++ei) {
        const std::int32_t tag = t.edgeRow(ei, 0);
        const std::int32_t valId = t.edgeRow(ei, 1);
        const std::int32_t next = t.edgeRow(ei, 2);
        const std::int32_t arity = t.edgeRow(ei, 3);
        const std::size_t mark = acc.size();
        if (tag == kTagAny) {
            acc.push_back(Binding{t.str(valId), e});
            return next;
        }
        if (!exprMatchesTerm(t, c, e, tag, valId)) {
            // Fall through to the optional-product synthesis below;
            // a structural mismatch here might be a folded 1*x.
            const std::int32_t opt = tryOptionalProduct(t, c, node, e, acc);
            if (opt >= 0)
                return opt;
            continue;
        }
        if (static_cast<std::int32_t>(c.childCount(e)) != arity) {
            const std::int32_t opt = tryOptionalProduct(t, c, node, e, acc);
            if (opt >= 0)
                return opt;
            continue; // exact-arity step-2 semantics
        }
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
// Coefficient, RemoveContent, bind, list, ...).
Expr buildReplacement(const RuleTables &t, Ctx &c,
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
        return Expr(); // unbound symbol (should not happen)
    }
    case kTagHead: {
        if (nkids != 1 || std::string(t.str(valId)) != "Log")
            return Expr(); // step-3a: Log only
        const Expr arg =
            buildReplacement(t, c, bnd, childOf(t.repTerms, term, 0));
        if (arg.isNull())
            return Expr();
        return c.func("log", arg);
    }
    case kTagOp: {
        const std::string op = t.str(valId);
        if (nkids == 1 && op == "neg") {
            const Expr a =
                buildReplacement(t, c, bnd, childOf(t.repTerms, term, 0));
            return a.isNull() ? Expr() : c.neg(a);
        }
        if (nkids != 2)
            return Expr();
        const Expr a =
            buildReplacement(t, c, bnd, childOf(t.repTerms, term, 0));
        const Expr bb =
            buildReplacement(t, c, bnd, childOf(t.repTerms, term, 1));
        if (a.isNull() || bb.isNull())
            return Expr();
        if (op == "+")
            return c.add({a, bb});
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
    if (tag != kTagHead || nkids != 2)
        return false;
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
    if (pred == "NeQ" || pred == "EqQ") {
        // compare a bound value against a rational literal
        const Expr a = buildReplacementCond(t, c, bnd, childOf(ct, term, 0));
        const Expr bb = buildReplacementCond(t, c, bnd, childOf(ct, term, 1));
        if (a.isNull() || bb.isNull())
            return false;
        if (c.kind(a) != NodeKind::Number || c.kind(bb) != NodeKind::Number)
            return false;
        const bool eq = c.numberValue(a) == c.numberValue(bb);
        return pred == "EqQ" ? eq : !eq;
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

Expr rubiApply(const RuleTables &t, Ctx &c, Expr e, Expr var)
{
    std::vector<Binding> bnd;
    const int rule = matchFirst(t, c, e, bnd);
    if (rule < 0)
        return Expr();
    const std::int32_t repOff = t.ruleRow(rule, 0);
    const std::int32_t condOff = t.ruleRow(rule, 1);
    if (condOff >= 0 && !evalCondition(t, c, var, bnd, condOff))
        return Expr(); // condition declines the rule
    const Expr F = buildReplacement(t, c, bnd, repOff);
    if (F.isNull())
        return Expr(); // replacement outside the step-3a subset
    // Tier-1 certificate reused verbatim: the rule's answer is only
    // real if it differentiates back to the integrand.
    if (c.diff(F, var) != e)
        return Expr();
    return F;
}

} // namespace numkit::cas::rubi
