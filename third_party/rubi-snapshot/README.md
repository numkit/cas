# Rubi rule snapshot (C2 step 1)

Pinned extracts from the Rubi rule base (MIT, see LICENSE;
(c) 2018 Rule-Based-Integration Organization) used as the parser
development corpus. Full upstream:
https://github.com/RuleBasedIntegration/Rubi

Slices: 1.1.1.1 (a+b x)^m (5 rules), 1.1.1.2 (a+b x)^m (c+d x)^n
(40 rules), 1.1.2.1 (a+b x^2)^p (33 rules) - 78 rules total, the
committed matcher corpus.

Coverage of tools/rubi_parse.py over the FULL upstream tree
(221 .m files): 165 files / 5501 rules parse into the JSON IR;
the remaining classes are catalogued in
notes/c1-algebraic-layer.md (item 24).
