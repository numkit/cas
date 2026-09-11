// rubi/rules.hpp — flat-table Rubi rule matcher (C2 step 2).
//
// The generated tables (a committed .inc, built offline by
// tools/rubi_parse.py + tools/rubi_codegen.py) hold a discrimination
// tree over the serialized rule patterns plus term forests for the
// replacements and conditions. This header defines the table view
// and the traversal matcher.
//
// STEP-2 SCOPE (deliberate): PRESENT matching only - a wildcard
// binds an actual subtree; optional blanks (`m_.` defaults) do not
// synthesize their default values yet, and condition evaluation is
// not implemented. matchFirst returns the rule id and the bindings;
// what the caller does with them (and full pattern semantics,
// step 3) come later.
#pragma once

#include <numkit/cas/core/expr.hpp>

#include <cstdint>
#include <string>
#include <vector>

namespace numkit::cas::rubi {

// Term tags - mirror tools/rubi_codegen.py.
enum Tag : std::uint8_t {
    kTagAny = 0,  // pattern variable (wildcard)
    kTagOp = 1,   // arithmetic/logic operator by string id
    kTagHead = 2, // function head by string id
    kTagNum = 3,  // rational literal (string form, parsed on load)
    kTagSym = 4,  // free symbol by string id
};

// A flat table set. The default instance points at the generated
// slice; custom sets can be loaded from the arrays directly.
struct RuleTables
{
    const char *const *strings = nullptr;
    const std::int32_t *stringCount = nullptr;
    // nodes: tag, valId, firstEdge, nEdges, ruleId (-1 = inner)
    const std::int32_t *nodes = nullptr;
    // edges: tag, valId, next, arity, optional - arity is the
    // pattern-term child count (exact-arity matching), optional=1
    // marks an `_.` blank eligible for default synthesis
    const std::int32_t *edges = nullptr;
    // terms: tag, valId, childOff, childCount
    const std::int32_t *repTerms = nullptr;
    const std::int32_t *condTerms = nullptr;
    // rules: repTermOff, condTermOff (-1 = none), patternLeafNode,
    // nextRuleWithSamePattern (-1 = end of chain) - Rubi's identical-
    // pattern sign variants try in chain (file) order
    const std::int32_t *rules = nullptr;
    const std::int32_t *ruleCount = nullptr;

    const char *str(std::int32_t id) const
    {
        return strings[id];
    }
    std::int32_t nodeRow(std::int32_t n, int col) const
    {
        return nodes[n * 5 + col];
    }
    std::int32_t edgeRow(std::int32_t e, int col) const
    {
        return edges[e * 5 + col];
    }
    std::int32_t termRow(const std::int32_t *table, std::int32_t t,
                         int col) const
    {
        return table[t * 4 + col];
    }
    std::int32_t ruleRow(std::int32_t r, int col) const
    {
        return rules[r * 4 + col];
    }
};

// The committed generated slice (currently 1.1.1.1 (a+b x)^m).
RuleTables sliceTables();

// Apply the FIRST matching rule of the slice to e and return its
// replacement with the bindings substituted. STEP-3A SCOPE:
//  - replacements execute over the bound names plus rational
//    literals and the Log head;
//  - conditions: FreeQ[name-list, var], NeQ[expr, rational] and
//    EqQ evaluate; anything else declines the rule (honest null);
//  - the answer is CERTIFIED by the caller-grade check dF/dvar == e
//    (the Tier-1 gate of the core, reused verbatim) - a rule answer
//    is only returned when it differentiates back to the integrand.
// Returns a null Expr when no rule matches, conditions fail, or the
// certificate rejects the result.
Expr rubiApply(const RuleTables &t, Ctx &c, Expr e, Expr var);

// One wildcard binding: the pattern variable name (from the string
// table at generation time, recorded per rule) and the matched Expr.
struct Binding
{
    std::string name;
    Expr value;
};

// Match `e` against the tables' patterns, depth-first along the
// trie. Returns the rule id or -1; `bindings` receives the wildcard
// assignments of the FIRST matching rule (table order = rule order
// in the source file, which is Rubi's precedence by construction).
int matchFirst(const RuleTables &t, Ctx &c, Expr e,
               std::vector<Binding> &bindings);

} // namespace numkit::cas::rubi
