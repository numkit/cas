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
        if (!exprMatchesTerm(t, c, e, tag, valId))
            continue;
        if (static_cast<std::int32_t>(c.childCount(e)) != arity)
            continue; // exact-arity step-2 semantics
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

} // namespace numkit::cas::rubi
