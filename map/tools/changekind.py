#!/usr/bin/env python3
"""Heuristic kind of a source-level statement change 72fead1 -> 61d870d.

usage: changekind.py NAMES.tsv DECLS72.tsv DECLS61.tsv OUT.tsv
Kinds (computed, heuristic; 'substantive' needs a reading):
  cosmetic      only `.1`<->`.val`, binder notation, whitespace, renamed referenced constants
                (token replaced by a token, same count), or local variable renames
  drop-inst     only instance binders `[...]` removed (statement at least as strong; usually cosmetic)
  add-inst      only instance binders added (weaker in principle; usually cosmetic)
  substantive   anything else: hypotheses/conclusions/types changed
"""
import difflib, re, sys

TOK = re.compile(r"\[[^\[\]]*\]|[\w'₀-₉!?.]+|\S")
names, p72, p61, out = sys.argv[1:5]


def load(p):
    d = {}
    for l in open(p, encoding="utf-8"):
        if l[0] != "#":
            c = l.rstrip("\n").split("\t"); d.setdefault(c[0], c[4])
    return d


d72, d61 = load(p72), load(p61)


def kind(a, b):
    ta, tb = TOK.findall(a), TOK.findall(b)
    ops = [o for o in difflib.SequenceMatcher(None, ta, tb, autojunk=False).get_opcodes() if o[0] != "equal"]
    if not ops:
        return "cosmetic", ""
    dels = [t for o in ops for t in ta[o[1]:o[2]]]
    ins = [t for o in ops for t in tb[o[3]:o[4]]]
    inst = lambda ts: ts and all(t.startswith("[") and t.endswith("]") for t in ts)
    if not ins and inst(dels):
        return "drop-inst", " ".join(dels)
    if not dels and inst(ins):
        return "add-inst", " ".join(ins)
    cos = {".1", ".val", "1", "val", "fun", "↦", "{", "}", "|", "(", ")", "=>"}
    if all(o[0] == "replace" and (o[2] - o[1]) == (o[4] - o[3]) for o in ops):
        # token-for-token: identifier renames or projection spelling
        pairs = [(x, y) for o in ops for x, y in zip(ta[o[1]:o[2]], tb[o[3]:o[4]])]
        if all(re.match(r"^[\w'.₀-₉]+$", x) and re.match(r"^[\w'.₀-₉]+$", y) for x, y in pairs):
            return "cosmetic", "; ".join(f"{x}->{y}" for x, y in sorted(set(pairs)))[:300]
    if set(dels) | set(ins) <= cos:
        return "cosmetic", ""
    desc = " / ".join(f"-[{' '.join(ta[o[1]:o[2]])}] +[{' '.join(tb[o[3]:o[4]])}]" for o in ops[:4])
    return "substantive", desc[:400]


with open(out, "w") as o:
    o.write("# name\tkind\tdetail\n")
    for l in open(names, encoding="utf-8"):
        c = l.split("\t")
        if c[0][0] == "#" or c[3] != "changed":
            continue
        k, det = kind(d72[c[0]], d61[c[0]])
        o.write(f"{c[0]}\t{k}\t{det}\n")
