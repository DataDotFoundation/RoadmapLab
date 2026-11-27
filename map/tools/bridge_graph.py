#!/usr/bin/env python3
"""Graph metrics for the bridges of bridges.py: lines of reasoning, depth from the root, fan-in.

usage: bridge_graph.py CORPUS_DIR LIVE.txt BRIDGES.tsv OUT_DIR
- A *line of reasoning* is a connected component of the graph whose vertices are the live bridges,
  with an edge when one bridge directly depends on another; its weight is the sum of line spans.
- *Depth*: the BFS distance from `riemannHypothesis` along direct dependencies.
- *Fan-in*: the number of live project declarations that directly use the bridge.
Appends to OUT_DIR/metrics.md and writes OUT_DIR/lines.tsv (stdlib only; computed).
"""
import collections, sys

corpus, livef, bridgesf, out = sys.argv[1:5]
live = set(x.strip() for x in open(livef, encoding="utf-8"))
rows = [l.rstrip("\n").split("\t") for l in open(bridgesf, encoding="utf-8") if l[0] != "#"]
B = {r[0]: r for r in rows if r[3] == "y"}
adj, rev = collections.defaultdict(set), collections.defaultdict(set)
for l in open(f"{corpus}/deps.tsv", encoding="utf-8"):
    if l[0] == "#":
        continue
    c = l.rstrip("\n").split("\t")
    n = c[1].split("::", 1)[-1]
    if n not in live:
        continue
    for x in c[2:]:
        x = x.split("::", 1)[-1]
        adj[n].add(x)
        if x in B and n.startswith("New."):
            rev[x].add(n)
# depth from the root
depth, q = {"riemannHypothesis": 0}, collections.deque(["riemannHypothesis"])
while q:
    u = q.popleft()
    for v in adj.get(u, ()):
        if v not in depth:
            depth[v] = depth[u] + 1
            q.append(v)
# components among bridges
und = collections.defaultdict(set)
for b in B:
    for v in adj.get(b, ()):
        if v in B:
            und[b].add(v); und[v].add(b)
seen, comps = set(), []
for b in B:
    if b in seen:
        continue
    comp, st = [], [b]
    seen.add(b)
    while st:
        u = st.pop(); comp.append(u)
        for v in und[u]:
            if v not in seen:
                seen.add(v); st.append(v)
    comps.append(comp)
comps.sort(key=lambda c: -sum(int(B[x][2]) for x in c))
with open(f"{out}/lines.tsv", "w", encoding="utf-8") as o:
    o.write("# line\tbridges\tlines\tmin_depth\tmain_directories\tkinds\texample\n")
    for i, c in enumerate(comps, 1):
        dirs = collections.Counter(".".join(B[x][1].split(".")[:3]) for x in c)
        kinds = collections.Counter(k for x in c for k in B[x][4].split(","))
        ex = max(c, key=lambda x: len(rev[x]))
        o.write(f"L{i}\t{len(c)}\t{sum(int(B[x][2]) for x in c)}\t{min((depth[x] for x in c if x in depth), default="-")}\t"
                f"{', '.join(d for d, _ in dirs.most_common(3))}\t{', '.join(f'{k}:{n}' for k, n in kinds.most_common())}\t{ex}\n")
unreached = [b for b in B if b not in depth]
ds = sorted(depth[b] for b in B if b in depth)
fan = sorted(((len(rev[b]), b) for b in B), reverse=True)
with open(f"{out}/metrics.md", "a", encoding="utf-8") as o:
    o.write("\n## Weighted-graph metrics (live bridges)\n\n")
    o.write(f"- Lines of reasoning (connected components of bridges): **{len(comps)}**; the largest has "
            f"{len(comps[0])} bridges ({sum(int(B[x][2]) for x in comps[0]):,} lines); singletons: "
            f"{sum(1 for c in comps if len(c) == 1)}. Full list: `lines.tsv`.\n")
    o.write(f"- Depth from `riemannHypothesis` (BFS over direct dependencies of live declarations): min {ds[0]}, median "
            f"{ds[len(ds)//2]}, max {ds[-1]}, over {len(ds)} bridges; {len(unreached)} live bridges are not reached by this BFS "
            f"(live in the Librarian closure, which also follows structure projections and instances, but not along "
            f"direct-dependency edges from the root) and are excluded from the depth statistics.\n")
    o.write(f"- Fan-in (live users): median {sorted(f for f, _ in fan)[len(fan)//2]}; top: "
            + ", ".join(f"`{b}` ({f})" for f, b in fan[:5]) + ".\n")
    arith = [b for b in B if set(B[b][4].split(",")) & {"L_values", "hecke_characters"}]
    o.write(f"- *Arithmetic* bridges (using L-values or Hecke characters, not only places/adeles/conductors, which "
            f"the adelic groups carry structurally): **{len(arith)}** ({sum(int(B[b][2]) for b in arith):,} lines).\n")
print(len(comps), ds[len(ds)//2])
