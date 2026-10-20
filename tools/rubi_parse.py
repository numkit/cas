#!/usr/bin/env python3
"""Parse a Rubi rule file (.m) into a JSON intermediate representation.

C2 step 1 toolchain: an OFFLINE build-stage script (Python, like the
corpus generator - the library itself stays dependency-free). The
parser understands the subset of Mathematica notation that the rule
files use:

    Int[pattern, x_Symbol] := replacement /; conditions

- patterns carry blanks with optional defaults:  x_   m_.   b_.*x
- the replacement is a plain expression over the bound names plus
  Rubi/Mathematica helper heads (Log, Subst, Coefficient, ...);
- conditions are conjunctions of predicates over the bound names
  (FreeQ, NeQ, LinearQ, ...).

The IR (one JSON object per rule) keeps the three parts as nested
lists, deliberately NOT interpreting pattern semantics - that is the
matcher's business (C2 step 3). Comments (* ... *) are dropped.

Usage:
    python tools/rubi_parse.py <rules.m> [out.json]
"""

import json
import re
import sys

TOKEN_RE = re.compile(r"""
    \s+                       # whitespace (skipped)
  | \(\*.*?\*\)               # comment (skipped, non-greedy)
  | :=                        # rule separator
  | /;                        # condition separator
  | ->                        # Mathematica Rule arrow (e.g. ReplaceAll)
  | \\\[[A-Za-z]+]            # Mathematica long name, e.g. \[Star]
  | [A-Za-z$][A-Za-z0-9$]*    # symbol
  | \d+(?:\.\d+)?\.?          # number (incl. trailing dot typo 2.)
  | ==|!=|<=|>=               # two-char comparisons
  | [-+*/^,.()\[\]{}<>!=&_|=;] # punctuation/operators (one char each)
""", re.VERBOSE | re.DOTALL)


# Long-name aliases: \[Star] and friends are Mathematica's ASCII
# spellings of operators; map them onto the plain characters.
LONG_NAME = {
    "\\[Star]": "*",
    "\\[Slash]": "/",
    "\\[Caret]": "^",
    "\\[Times]": "*",
    "\\[Divide]": "/",
    "\\[Plus]": "+",
    "\\[Minus]": "-",
}


def tokenize(src):
    toks = []
    pos = 0
    while pos < len(src):
        m = TOKEN_RE.match(src, pos)
        if not m:
            raise SyntaxError(f"lex error at offset {pos}: {src[pos:pos+20]!r}")
        pos = m.end()
        text = m.group(0)
        if text.strip() == "" or text.startswith("(*"):
            continue
        toks.append(LONG_NAME.get(text, text))
    return toks


class Parser:
    """Recursive-descent parser over the token stream.

    Grammar (a faithful subset for the rule files):
        file    := rule*
        rule    := 'Int' '[' expr ',' var ']' ':=' expr ('/;' cond)?
        var     := SYMBOL '_' 'Symbol'
        expr    := term (op term)*          left-assoc + - * /
        op precedence handled by climbing: ^ binds tighter, right-assoc
        term    := NUMBER | SYMBOL BLANK? | SYMBOL '[' args ']'
                   | '(' expr ')' | '{' args '}' | '-' term
        BLANK   := '_' '.'?
    """

    def __init__(self, toks):
        self.toks = toks
        self.i = 0

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def next(self):
        t = self.peek()
        self.i += 1
        return t

    def expect(self, t):
        got = self.next()
        if got != t:
            raise SyntaxError(f"expected {t!r}, got {got!r}")

    def parse_file(self):
        rules = []
        while self.peek() is not None:
            if self.peek() == "Int":
                rules.append(self.parse_rule())
            else:
                self.next()  # skip anything between rules
        return rules

    def parse_rule(self):
        self.expect("Int")
        self.expect("[")
        pattern = self.parse_expr()
        self.expect(",")
        var = self.parse_var()
        self.expect("]")
        self.expect(":=")
        replacement = self.parse_expr()
        conditions = []
        # A rule-level condition surfaces as a /; node wrapping the
        # whole replacement (Mathematica's Condition head); nested
        # conditions inside Int[...] stay embedded in the tree.
        if isinstance(replacement, dict) and replacement.get("op") == "/;":
            conditions = replacement["args"][1]
            replacement = replacement["args"][0]
        return {"pattern": pattern, "var": var,
                "replacement": replacement, "conditions": conditions}

    def parse_var(self):
        name = self.next()
        self.expect("_")
        sym = self.next()  # 'Symbol'
        assert sym == "Symbol", f"expected Symbol, got {sym!r}"
        return name

    def parse_conditions(self):
        # '&&'/'||' are already part of the expression grammar (they
        # bind loosest), so a condition is just an expression.
        return self.parse_expr()

    # ---- expression parser (precedence climbing) ----
    # loosest: || then &&, then + -, then * /, then ^ (right assoc),
    # then unary -, atoms (with optional blank markers). The boolean
    # levels exist for conditions; they never collide with the
    # arithmetic ones.

    def parse_expr(self):
        node = self.parse_semi()
        # Condition head INSIDE expressions: Rubi writes nested
        # Int[..., x] /; cond, x] replacements.
        if self.peek() == "/;":
            self.next()
            return {"op": "/;", "args": [node, self.parse_expr()]}
        return node

    def parse_semi(self):
        node = self.parse_bind()
        while self.peek() == ";":
            self.next()
            node = {"op": ";", "args": [node, self.parse_bind()]}
        return node

    def parse_bind(self):
        node = self.parse_or()
        # local bindings inside With[{q = ...}] bodies or Rule x -> v
        if self.peek() == "=":
            self.next()
            return {"op": "bind", "args": [node, self.parse_bind()]}
        if self.peek() == "->":
            self.next()
            return {"op": "->", "args": [node, self.parse_bind()]}
        return node

    def parse_or(self):
        node = self.parse_and()
        while self.peek() == "|":
            self.next()
            self.expect("|")
            node = {"op": "||", "args": [node, self.parse_and()]}
        return node

    def parse_and(self):
        node = self.parse_cmp()
        while self.peek() == "&":
            self.next()
            self.expect("&")
            node = {"op": "&&", "args": [node, self.parse_cmp()]}
        return node

    def parse_cmp(self):
        node = self.parse_sum()
        while self.peek() in ("==", "!=", "<", ">", "<=", ">="):
            op = self.next()
            node = {"op": op, "args": [node, self.parse_sum()]}
        return node

    def parse_sum(self):
        node = self.parse_product()
        while self.peek() in ("+", "-"):
            op = self.next()
            rhs = self.parse_product()
            node = {"op": op, "args": [node, rhs]}
        return node

    def parse_product(self):
        node = self.parse_power()
        while self.peek() in ("*", "/", "("):
            if self.peek() == "(":
                rhs = self.parse_power()
                node = {"op": "*", "args": [node, rhs]}
            else:
                op = self.next()
                rhs = self.parse_power()
                node = {"op": op, "args": [node, rhs]}
        return node

    def parse_power(self):
        base = self.parse_atom()
        if self.peek() == "^":
            self.next()
            exp = self.parse_power()  # right associative
            return {"op": "^", "args": [base, exp]}
        return base

    def parse_atom(self):
        t = self.peek()
        if t == "-":
            self.next()
            return {"op": "neg", "args": [self.parse_atom()]}
        if t == "(":
            self.next()
            e = self.parse_expr()
            self.expect(")")
            return e
        if t == "{":
            self.next()
            args = []
            if self.peek() != "}":
                args.append(self.parse_expr())
                while self.peek() == ",":
                    self.next()
                    args.append(self.parse_expr())
            self.expect("}")
            return {"op": "list", "args": args}
        m = re.fullmatch(r"\d+(?:\.\d+)?\.?", t or "")
        if m:
            self.next()
            return {"num": t[:-1] if t.endswith(".") else t}
        if t is not None and re.fullmatch(r"[A-Za-z$][A-Za-z0-9$]*", t):
            self.next()
            name = t
            blank = None
            if self.peek() == "_":
                self.next()
                blank = "_"          # required blank
                if self.peek() == ".":
                    self.next()
                    blank = "_."     # optional (default) blank
            if self.peek() == "[":
                self.next()
                args = []
                if self.peek() != "]":
                    args.append(self.parse_expr())
                    while self.peek() == ",":
                        self.next()
                        args.append(self.parse_expr())
                self.expect("]")
                return {"head": name, "args": args}
            if blank is not None:
                return {"pattern_var": name, "blank": blank}
            return {"sym": name}
        raise SyntaxError(f"unexpected token {t!r} at {self.i}")


def parse_file(path):
    src = open(path, encoding="utf-8", errors="replace").read()
    return Parser(tokenize(src)).parse_file()


# Exact load order from upstream Rubi.m for 1.1 Binomial products.
_RUBI_1_1_ORDER = [
    "1.1.1.1", "1.1.1.2", "1.1.1.3", "1.1.1.4",
    "1.1.2.1", "1.1.2.2", "1.1.2.3", "1.1.2.4", "1.1.2.5",
    "1.1.2.6", "1.1.2.7", "1.1.2.8", "1.1.2.9",
    "1.1.3.1", "1.1.3.2", "1.1.3.3", "1.1.3.4", "1.1.3.5", "1.1.3.6",
    "1.1.4.1", "1.1.4.2", "1.1.4.3",
    "1.1.1.7", "1.1.1.6", "1.1.1.5",
    "1.1.2.11", "1.1.2.10", "1.1.2.14", "1.1.2.13", "1.1.2.12",
    "1.1.3.8", "1.1.3.7",
    "1.1.4.4",
]
_RUBI_1_1_RANK = {sec: i for i, sec in enumerate(_RUBI_1_1_ORDER)}


def _section_sort_key(path):
    import os
    base = os.path.basename(path)
    sec = base.split(" ", 1)[0]
    if sec in _RUBI_1_1_RANK:
        return (0, [_RUBI_1_1_RANK[sec]], base)
    is_px = " P(x) " in base
    parts = [int(p) if p.isdigit() else 999 for p in sec.split(".")]
    return (1 if is_px else 0, parts, base)


def parse_path(path):
    import glob
    import os
    if os.path.isdir(path):
        files = glob.glob(os.path.join(path, "**", "*.m"), recursive=True)
        files.sort(key=_section_sort_key)
        rules = []
        for f in files:
            rules.extend(parse_file(f))
        return rules
    return parse_file(path)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 1
    rules = parse_path(sys.argv[1])
    out = json.dumps(rules, indent=1)
    if len(sys.argv) > 2:
        open(sys.argv[2], "w", encoding="utf-8", newline="\n").write(out + "\n")
        print(f"{len(rules)} rules -> {sys.argv[2]}")
    else:
        print(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
