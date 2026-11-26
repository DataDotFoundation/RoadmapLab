#!/usr/bin/env python3
"""Classify each cited name: present at 72fead1, at 61d870d, statement drift, liveness from riemannHypothesis.

usage: classify.py CITES.tsv DECLS72.tsv DECLS61.tsv CORPUS_DUMP.tsv CORPUS_DEPS.tsv OUT_NAMES.tsv
Per distinct cited name:
  in72      source-level declaration found at 72fead1 (y/n)
  in61      in the elaborated corpus condensed@61d870d (y/n)  [authoritative]
  drift     same | changed | renamed:<new> | removed | moved-same (same statement, other file) | ?  (source-level)
  live      y/n: in the dependency closure of `riemannHypothesis` at 61d870d (n/a if absent)
  file72, file61
"""
import collections, sys

cites, d72p, d61p, dump, deps, out = sys.argv[1:7]


def load_decls(p):
    by, stm = {}, collections.defaultdict(list)
    for l in open(p, encoding="utf-8"):
        if l[0] == "#":
            continue
        n, k, f, ln, s = l.rstrip("\n").split("\t")
        by.setdefault(n, (k, f, ln, s))
        stm[s].append(n)
    return by, stm


d72, _ = load_decls(d72p)
d61, s61 = load_decls(d61p)

names = sorted({l.split("\t")[4].strip() for l in open(cites, encoding="utf-8") if l[0] != "#" and l.split("\t")[4].strip()})
want = set(names)

corpus, mod = set(), {}
for l in open(dump, encoding="utf-8"):
    if l[0] == "#":
        continue
    c = l.split("\t", 3)
    nm = c[1].split("::", 1)[-1]
    corpus.add(nm)
    mod.setdefault(nm, c[0])

# dependency closure from riemannHypothesis
adj = {}
for l in open(deps, encoding="utf-8"):
    if l[0] == "#":
        continue
    c = l.rstrip("\n").split("\t")
    adj[c[1].split("::", 1)[-1]] = [x.split("::", 1)[-1] for x in c[2:]]
roots = [n for n in adj if n == "riemannHypothesis" or n.endswith(".riemannHypothesis")]
seen, st = set(roots), list(roots)
while st:
    x = st.pop()
    for y in adj.get(x, ()):
        if y not in seen:
            seen.add(y); st.append(y)
# structures: a structure is live if any of its projections/constructor is
for n in list(seen):
    if "." in n:
        seen.add(n.rsplit(".", 1)[0])
print(f"roots {roots}; closure {len(seen)}", file=sys.stderr)

with open(out, "w") as o:
    o.write("# name\tin72\tin61\tdrift\tlive\tfile72\tfile61\n")
    for n in names:
        a, b = d72.get(n), d61.get(n)
        in61 = n in corpus
        if a and b:
            drift = "same" if a[3] == b[3] else "changed"
            if drift == "same" and a[1] != b[1]:
                drift = "moved-same"
        elif a and not in61:
            cand = [m for m in s61.get(a[3], []) if m not in d72 and len(a[3]) > 25]
            drift = f"renamed:{cand[0]}" if len(cand) == 1 else "removed"
        elif in61 and not a:
            drift = "?"  # not found at 72 by source parser (generated or parser miss)
        elif in61 and a and not b:
            drift = "same?"  # in corpus, source parser missed at 61
        else:
            drift = "absent"
        live = ("y" if n in seen else "n") if in61 else "n/a"
        o.write("\t".join([n, "y" if a else "n", "y" if in61 else "n", drift, live,
                           a[1] if a else "", (b[1] if b else mod.get(n, ""))]) + "\n")
