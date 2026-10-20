#!/usr/bin/env python3
"""Codegen: Rubi rule IR (rubi_parse JSON) -> flat C++ tables.

C2 step 2. The generated data is a DISCRIMINATION TREE over the
serialized patterns plus term tables for replacements/conditions:

- pattern terms serialize prefix-order; trie nodes match a term by
  (tag, value) or by the wildcard tag (pattern_var);
- edges are flat arrays grouped contiguously per node;
- replacement/condition terms carry (childOffset, childCount) so the
  runtime can walk them without recursion into the generator;
- operators, heads and symbols share one string table.

The output is COMMITTED to the repository ("generated - do not
edit") so builds stay Python-free; regeneration is an explicit
tools invocation:

    python tools/rubi_parse.py <rules.m> rules.json
    python tools/rubi_codegen.py rules.json rubi_tables.inc
"""

from fractions import Fraction
import json
import sys

# tag ids - must match include/numkit/cas/rubi/rules.hpp
TAG_ANY = 0      # pattern_var wildcard
TAG_OP = 1       # {op: ...}
TAG_HEAD = 2     # {head: ...}
TAG_NUM = 3      # {num: ...}
TAG_SYM = 4      # {sym: ...}


def term_tag(node):
    """(tag, value-string) of an IR node; a wildcard carries its
    VARIABLE NAME (the matcher binds subtrees under that name)."""
    if "pattern_var" in node:
        return TAG_ANY, node["pattern_var"]
    if "op" in node:
        return TAG_OP, node["op"]
    if "head" in node:
        return TAG_HEAD, node["head"]
    if "num" in node:
        return TAG_NUM, node["num"]
    if "sym" in node:
        return TAG_SYM, node["sym"]
    raise ValueError(f"unknown IR node {node}")


def prefix_terms(node):
    """Prefix-order IR subtree list."""
    out = [node]
    for arg in node.get("args", []):
        out.extend(prefix_terms(arg))
    return out


def fmt_frac(f):
    return (f"{f.numerator}/{f.denominator}"
            if f.denominator != 1 else str(f.numerator))


def has_opt_var(node):
    return any("pattern_var" in c and c.get("blank") == "_."
               for c in node.get("args", []))


def flatten_mul(node):
    if node.get("op") != "*":
        return node
    flat = []
    for a in node["args"]:
        if a.get("op") == "*" and not has_opt_var(a):
            flat.extend(a["args"])
        else:
            flat.append(a)
    return {"op": "*", "args": flat}


def make_pow(base, exp):
    """Canonicalize (u^r)^n -> u^(r*n) and (u*v)^n -> u^n*v^n for
    integer n, mirroring Ctx::pow (src/core/expr.cpp)."""
    if (base.get("op") == "^" and "num" in base["args"][1]
            and "num" in exp):
        n = Fraction(exp["num"])
        if n.denominator == 1:
            r = Fraction(base["args"][1]["num"])
            return {"op": "^", "args": [base["args"][0],
                                        {"num": fmt_frac(r * n)}]}
    if (base.get("op") == "*" and not has_opt_var(base)
            and "num" in exp and Fraction(exp["num"]).denominator == 1):
        return flatten_mul({"op": "*",
                            "args": [make_pow(f, exp) for f in base["args"]]})
    return {"op": "^", "args": [base, exp]}


def rewrite_div(node):
    """Canonicalize a PATTERN into the shapes the expression DAG
    actually builds:
        neg[num]        ->  num (-r)
        / [num, num]    ->  num (p/q)
        Sqrt[u]         ->  ^ [u, 1/2]
        ^ [^[u, r], n]  ->  ^ [u, r*n]  (integer n, numeric r)
        / [1, d]        ->  ^ [d, -1]   (distributed over * factors)
        / [a, b]        ->  * [a, ^ [b, -1]]
        * [*[a, b], c]  ->  * [a, b, c] (flattened unless inner * is v_.*w)
    Children are rewritten recursively. REPLACEMENTS keep their
    spelling (the replacement builder evaluates / through div)."""
    if "args" not in node:
        return node
    args = [rewrite_div(a) for a in node["args"]]
    if node.get("op") == "neg" and len(args) == 1 and "num" in args[0]:
        return {"num": fmt_frac(-Fraction(args[0]["num"]))}
    if node.get("head") == "Sqrt" and len(args) == 1:
        return make_pow(args[0], {"num": "1/2"})
    if node.get("op") == "^" and len(args) == 2:
        return make_pow(args[0], args[1])
    if node.get("op") == "/":
        num, den = args
        if "num" in num and "num" in den:
            return {"num": fmt_frac(
                Fraction(num["num"]) / Fraction(den["num"]))}
        if num.get("num") == "1":
            return make_pow(den, {"num": "-1"})
        return flatten_mul({"op": "*",
                            "args": [num, make_pow(den, {"num": "-1"})]})
    out = dict(node)
    out["args"] = args
    if out.get("op") == "*":
        return flatten_mul(out)
    return out


def subtree_sizes(terms):
    """sizes[i] = number of terms in the subtree rooted at terms[i]
    (prefix layout: children follow immediately, sequentially)."""
    sizes = [1] * len(terms)
    for i in range(len(terms) - 1, -1, -1):
        total = 1
        off = i + 1
        for _ in terms[i].get("args", []):
            total += sizes[off]
            off += sizes[off]
        sizes[i] = total
    return sizes


def child_offsets(terms):
    """(childOff, childCount) rows: child k of node i sits at
    i + 1 + sum(sizes of previous children)."""
    sizes = subtree_sizes(terms)
    rows = []
    for i, t in enumerate(terms):
        args = t.get("args", [])
        kids = len(args)
        off = i + 1
        first = off if kids else 0
        # verify contiguity (sanity): each child starts where the
        # previous child's subtree ends
        rows.append([first, kids])
    return rows


class Codegen:
    def __init__(self, rules):
        self.rules = rules
        self.strings = []
        self.string_ids = {}

    def sid(self, s):
        if s not in self.string_ids:
            self.string_ids[s] = len(self.strings)
            self.strings.append(s)
        return self.string_ids[s]

    def emit(self):
        # ---- specificity ordering ----
        # Mathematica dispatches rules by pattern specificity, not by
        # file order: (a_.+b_.*x_)^m_ must beat x_^m_. on non-bare
        # bases. A computable approximation for the trie: the more
        # STRUCTURAL (non-wildcard) terms a pattern's prefix
        # serialization carries, the more specific it is; stable
        # sort keeps the file order among equals (Rubi lists the
        # x-forms before the u-forms, which is the right tie-break).
        # Canonical-twin rewrite of the patterns: division must go,
        # or /-rules could never match the DAG (see rewrite_div).
        self.rules = [dict(r, pattern=rewrite_div(r["pattern"]))
                      for r in self.rules]

        def spec_norm(t, var):
            if "args" not in t:
                return t
            op = t.get("op")
            args = [spec_norm(a, var) for a in t["args"]]
            # Strip optional coefficient wrapper *[c_., w] -> w so
            # (c_.*x) has the same structural specificity as bare x.
            if (op == "*" and len(args) == 2
                    and "pattern_var" in args[0]
                    and args[0].get("blank") == "_."):
                return args[1]
            # Collapse monomial wildcard power ^[x_, m_|m_.] -> x_ so
            # x_, x_^m_., x_^m_, and (c_.*x_)^m_. share the same
            # structural rank and preserve Rubi's intra-file rule order.
            if (op == "^" and len(args) == 2
                    and args[0].get("pattern_var") == var
                    and "pattern_var" in args[1]):
                return args[0]
            return dict(t, args=args)

        def specificity(rule):
            var = rule.get("var")
            terms = prefix_terms(spec_norm(rule["pattern"], var))
            non_any = sum(
                1 for t in terms
                if term_tag(t)[0] != TAG_ANY or t.get("pattern_var") == var
            )
            has_var = sum(1 for t in terms if t.get("pattern_var") == var)
            return (non_any, has_var)

        self.rules.sort(key=specificity, reverse=True)

        # ---- pattern trie ----
        nodes = [[0, -1, 0, 0, -1]]  # tag, valId, firstEdge, nEdges, rule
        edges = []  # tag, valId, next, arity, optional(blank `_.`)
        node_edges = {0: []}
        rule_leaves = []
        for rid, rule in enumerate(self.rules):
            node = 0
            for t in prefix_terms(rule["pattern"]):
                tag, val = term_tag(t)
                # A pattern variable NAMED like the rule's integration
                # variable (x_ in Int[..., x_Symbol]) is Rubi's way of
                # writing the LITERAL variable - x_ must not swallow
                # arbitrary subtrees (it grabbed whole Adds through
                # the optional-product delegation otherwise). Encode
                # it as a Symbol edge; plain wildcards (u_, m_, ...)
                # stay kTagAny.
                if tag == TAG_ANY and t.get("pattern_var") == rule.get("var"):
                    tag = TAG_SYM
                    val = t["pattern_var"]
                vid = self.sid(val) if val else -1
                arity = len(t.get("args", []))
                opt = 1 if ("pattern_var" in t and t.get("blank") == "_.") else 0
                nxt = None
                for e in node_edges[node]:
                    et, ev, en, ea, eo = edges[e]
                    if et == tag and ev == vid and ea == arity and eo == opt:
                        nxt = en
                        break
                if nxt is None:
                    edges.append((tag, vid, len(nodes), arity, opt))
                    node_edges[node].append(len(edges) - 1)
                    nxt = len(nodes)
                    nodes.append([tag, vid, 0, 0, -1])
                    node_edges[nxt] = []
                node = nxt
            rule_leaves.append(node)
            # The leaf carries the FIRST rule of its chain (identical
            # patterns overwrite otherwise and the earlier twins -
            # e.g. the PosQ variant before NegQ - become unreachable;
            # the chain's next column walks the rest).
            if nodes[node][4] == -1:
                nodes[node][4] = rid
        # flatten: REORDER the edges contiguously per node (depth-
        # first interleaved insertion leaves them mixed) and set the
        # nodes' firstEdge/nEdges accordingly.
        flat_edges = []
        # rules sharing one trie leaf (identical patterns), in chain
        # order: leaf -> [rid, rid, ...]; each rule row's column 3
        # points to the NEXT rule of the chain (-1 = end)
        leaf_rules = {}
        off = 0
        for i, nd in enumerate(nodes):
            nd[2] = off
            nd[3] = len(node_edges[i])
            for e in node_edges[i]:
                flat_edges.append(edges[e])
            off += nd[3]
        edges = flat_edges

        # ---- rule rows: leaf node + replacement/condition terms ----
        rep_terms = []
        cond_terms = []
        rule_rows = []
        for rid, rule in enumerate(self.rules):
            rts = prefix_terms(rule["replacement"])
            rep_off = len(rep_terms)
            # childOff must be GLOBAL (absolute index into the whole
            # term table) - the runtime indexes terms by rule offset
            # plus nothing else.
            for t, (co, cn) in zip(rts, child_offsets(rts)):
                tag, val = term_tag(t)
                rep_terms.append((tag, self.sid(val) if val else -1,
                                  rep_off + co, cn))
            if rule["conditions"]:
                cts = prefix_terms(rule["conditions"])
                cond_off = len(cond_terms)
                for t, (co, cn) in zip(cts, child_offsets(cts)):
                    tag, val = term_tag(t)
                    cond_terms.append((tag, self.sid(val) if val else -1,
                                       cond_off + co, cn))
            else:
                cond_off = -1
            node = rule_leaves[rid]
            rule_rows.append([rep_off, cond_off, node, -1])
            # IDENTICAL patterns from different rules (Rubi's
            # sign-variant twins) share ONE leaf; chain them in
            # stable (file) order so condition fallback works.
            leaf_rules.setdefault(node, []).append(rid)

        def rows_int(name, rows):
            body = ",\n".join("    " + ", ".join(str(v) for v in r)
                              for r in rows) or "    0"
            return f"static const int32_t {name}[] = {{\n{body},\n}};\n"

        def esc(s):
            return s.replace("\\", "\\\\").replace('"', '\\"')

        out = []
        out.append("// GENERATED by tools/rubi_codegen.py - do not edit.")
        out.append(f"// rules: {len(self.rules)}, trie nodes: {len(nodes)},"
                   f" edges: {len(edges)}")
        out.append("")
        strs = ",\n".join(f'    "{esc(s)}"' for s in self.strings) or '    ""'
        out.append(f"static const char *const kStrings[] = {{\n{strs},\n}};")
        out.append(f"static const int32_t kStringCount = "
                   f"{len(self.strings)};")
        out.append("")
        out.append(rows_int("kNodes", nodes))
        out.append(rows_int("kEdges", edges))
        out.append(rows_int("kRepTerms", rep_terms))
        out.append(rows_int("kCondTerms", cond_terms))
        # link the leaf chains: column 3 = next rule with the SAME
        # pattern (identical leaf), stable file order
        for chain in leaf_rules.values():
            for k in range(len(chain) - 1):
                rule_rows[chain[k]][3] = chain[k + 1]
        out.append(rows_int("kRules", rule_rows))
        out.append(f"static const int32_t kRuleCount = {len(rule_rows)};")
        return "\n".join(out) + "\n", len(nodes), len(edges)


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 1
    rules = json.load(open(sys.argv[1], encoding="utf-8"))
    gen = Codegen(rules)
    text, n_nodes, n_edges = gen.emit()
    open(sys.argv[2], "w", encoding="utf-8", newline="\n").write(text)
    print(f"{len(rules)} rules -> {sys.argv[2]} "
          f"({n_nodes} trie nodes, {n_edges} edges)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
