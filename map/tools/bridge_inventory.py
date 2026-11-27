#!/usr/bin/env python3
"""Per-file inventory and per-roadmap / per-area tables for the bridges of bridges.py.

usage: bridge_inventory.py CORPUS_DIR LIVE.txt CITES.tsv OUT_DIR
CITES.tsv is RoadmapLab's map/cites.tsv (roadmap, section, title, file at 72fead1, declaration).
Writes OUT_DIR/inventory.md and appends the roadmap and area tables to OUT_DIR/metrics.md (computed).
"""
import collections, re, sys

corpus, livef, citesf, O = sys.argv[1:5]
rows = [l.rstrip("\n").split("\t") for l in open(f"{O}/bridges.tsv", encoding="utf-8") if l[0] != "#"]
own = collections.defaultdict(set)
for l in open(citesf, encoding="utf-8"):
    if l[0] == "#":
        continue
    r, s, t, f, d = (l.rstrip("\n").split("\t") + [""] * 5)[:5]
    if f:
        own[f.replace(".lean", "").replace("/", ".")].add(r)
by = collections.defaultdict(list)
for r in rows:
    if r[3] == "y":
        by[r[1]].append(r)
TAG = ("*Tag:* computed (bridges.py, bridge_graph.py, bridge_inventory.py) at corpus `condensed@61d870d`; owners read "
       "from the RoadmapLab correspondence map at `72fead1`.\n\n")
agg = collections.defaultdict(lambda: [0, 0, 0])
with open(f"{O}/inventory.md", "w", encoding="utf-8") as o:
    o.write("# Inventory: lines of reasoning between theta lifts and number fields (condensed proof @ 61d870d)\n\n" + TAG)
    o.write("One row per source file with live bridges. A bridge is a declaration that directly uses a theta-lift "
            "construction and substantive number-field arithmetic (definitions in metrics.md). Sorted by weight (line "
            "spans: a price tag, not content). Owner: the TauCetiRoadmap ShortGRH roadmaps whose sections cite the file "
            "(empty for files added after 72fead1).\n\n")
    o.write("| file (src/) | bridges | lines | arithmetic kinds | Θ used | TauCetiRoadmap owner(s) |\n|---|---|---|---|---|---|\n")
    for m, rs in sorted(by.items(), key=lambda x: -sum(int(r[2]) for r in x[1])):
        ks = collections.Counter(k for r in rs for k in r[4].split(",") if k in ("L_values", "hecke_characters"))
        th = collections.Counter(t.rsplit(".", 1)[-1] for r in rs for t in r[5].split(","))
        ow = sorted(own.get(m, set()))
        lines = sum(int(r[2]) for r in rs)
        for rm in ow or ["—"]:
            a = agg[rm]; a[0] += 1; a[1] += len(rs); a[2] += lines
        o.write(f"| `{m.replace('.', '/')}.lean` | {len(rs)} | {lines} | "
                f"{', '.join(f'{k} {n}' for k, n in ks.items()) or '—'} | {', '.join(t for t, _ in th.most_common(3))} | "
                f"{'; '.join(ow) or '—'} |\n")
    o.write(f"\nFiles: {len(by)}.\n")
live = set(x.strip() for x in open(livef, encoding="utf-8"))
span = collections.Counter()
for l in open(f"{corpus}/types.tsv", encoding="utf-8"):
    if l[0] == "#":
        continue
    c = l.rstrip("\n").split("\t")
    n = c[1].split("::", 1)[-1]
    if n in live and c[5] and c[6] and not re.search(r"_proof_|_simp_|match_", n):
        for k in (2, 3):
            span[".".join(c[0].split(".")[:k])] += int(c[6]) - int(c[5]) + 1
with open(f"{O}/metrics.md", "a", encoding="utf-8") as o:
    o.write("\n## By TauCetiRoadmap roadmap (files with live bridges, by the roadmap that cites them)\n\n"
            "| roadmap | files | bridges | lines |\n|---|---|---|---|\n")
    for rm, a in sorted(agg.items(), key=lambda x: -x[1][2]):
        o.write(f"| {rm} | {a[0]} | {a[1]} | {a[2]:,} |\n")
    o.write("\n## Whole areas (live line spans of every declaration in the area, bridges or not)\n\n"
            "These are upper bounds for what a reformulation could replace, not estimates of savings.\n\n"
            "| area | live lines |\n|---|---|\n")
    for k in ["New.Determinant", "New.Determinant.AuxiliaryForms", "New.Determinant.Exchange", "New.Determinant.Chain",
              "New.OneLift", "Lib.Weil", "Lib.SiegelWeil", "New.UpperBound"]:
        o.write(f"| `{k}` | {span[k]:,} |\n")
for rm, a in sorted(agg.items(), key=lambda x: -x[1][2])[:10]:
    print(rm, a)
