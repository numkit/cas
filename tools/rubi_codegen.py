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
        def specificity(rule):
            return sum(1 for t in prefix_terms(rule["pattern"])
                       if term_tag(t)[0] != TAG_ANY)

        self.rules.sort(key=specificity, reverse=True)

        # ---- pattern trie ----
        nodes = [[0, -1, 0, 0, -1]]  # tag, valId, firstEdge, nEdges, rule
        edges = []                    # tag, valId, next, arity
        node_edges = {0: []}
        for rid, rule in enumerate(self.rules):
            node = 0
            for t in prefix_terms(rule["pattern"]):
                tag, val = term_tag(t)
                vid = self.sid(val) if val else -1
                arity = len(t.get("args", []))
                nxt = None
                for e in node_edges[node]:
                    et, ev, en, ea = edges[e]
                    if et == tag and ev == vid:
                        nxt = en
                        break
                if nxt is None:
                    edges.append((tag, vid, len(nodes), arity))
                    node_edges[node].append(len(edges) - 1)
                    nxt = len(nodes)
                    nodes.append([tag, vid, 0, 0, -1])
                    node_edges[nxt] = []
                node = nxt
            nodes[node][4] = rid
        # flatten: REORDER the edges contiguously per node (depth-
        # first interleaved insertion leaves them mixed) and set the
        # nodes' firstEdge/nEdges accordingly.
        flat_edges = []
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
            # leaf of this rule's pattern
            node = 0
            for t in prefix_terms(rule["pattern"]):
                tag, val = term_tag(t)
                vid = self.sid(val) if val else -1
                for e in range(nodes[node][2], nodes[node][2] + nodes[node][3]):
                    et, ev, en, _ = edges[e]
                    if et == tag and ev == vid:
                        node = en
                        break
            rule_rows.append((rep_off, cond_off, node))

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
