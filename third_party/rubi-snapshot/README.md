# Rubi rule snapshot (C2 step 1)

Pinned extracts from the Rubi rule base (MIT, see LICENSE;
(c) 2018 Rule-Based-Integration Organization) used as the parser
development corpus. Full upstream:
https://github.com/RuleBasedIntegration/Rubi

Slices: full section `1.1 Binomial products` (`1.1.1 Linear` 7 files,
`1.1.2 Quadratic` 14 files, `1.1.3 General` 8 files, `1.1.4 Improper`
4 files) — 33 active `.m` files, 1365 rules total (compiled into
6365 trie nodes / 6364 edges in `src/rubi/rubi_tables_1111.inc`).

Coverage of tools/rubi_parse.py over the FULL upstream tree
(221 .m files): 165 files / 5501 rules parse into the JSON IR;
the remaining classes are catalogued in
notes/c1-algebraic-layer.md (item 24).
