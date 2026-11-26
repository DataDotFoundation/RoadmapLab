#!/usr/bin/env python3
"""Replacement candidates at condensed@61d870d for names removed since 72fead1 (= condensed@686902a).

usage: replace.py STALENESS.tsv OUT.tsv
For each removed/renamed row of the Librarian's staleness TSV:
  hash      61d870d declarations with the same statement fingerprint (types.tsv hash) as the old one
  short     61d870d declarations with the same last name component (other namespace)
  absorbed  surviving direct consumers at 686902a (project declarations that used the name), with liveness at 61d870d
  why       removal kind from the PR title: inline | drop-direction | conjunction | doc-ref | method | unused | rename | ?
Computed; candidates, not verdicts.
"""
import collections, os, re, sys

C = os.path.join(os.environ.get("LIBRARIAN_STATE", os.path.expanduser("~/work/Librarian/state")), "corpora")
R = os.path.join(os.environ.get("LIBRARIAN_STATE", os.path.expanduser("~/work/Librarian/state")), "reports")
stale, out = sys.argv[1:3]
AUX = re.compile(r"\._proof_|\._simp_|\.eq_\d|\.congr_simp|\.match_|\._unfold|\.proof_\d|::|\._eq|\.induct")


def types(c):
    h, by = {}, collections.defaultdict(list)
    for l in open(f"{C}/{c}/types.tsv", encoding="utf-8"):
        if l[0] == "#":
            continue
        m = l.rstrip("\n").split("\t")
        n = m[1].split("::", 1)[-1]
        # a fingerprint identifies a statement only for theorems with a non-trivial type (short def types collide)
        key = m[3] if (m[2] == "theorem" and int(m[4] or 0) > 120) else f"{m[3]}:{n}"
        h[n] = key
        by[key].append(n)
    return h, by


h72, _ = types("condensed@686902a")
h61, by61 = types("condensed@61d870d")
short61 = collections.defaultdict(list)
for n in h61:
    if not AUX.search(n):
        short61[n.rsplit(".", 1)[-1]].append(n)
live = set(l.strip() for l in open(f"{R}/live-61d870d.txt", encoding="utf-8"))

rows = [l.rstrip("\n").split("\t") for l in open(stale, encoding="utf-8") if l[0] != "#"]
gone = {r[1] for r in rows if r[2] in ("removed", "renamed")}
users = collections.defaultdict(set)
users_all = collections.defaultdict(set)
for l in open(f"{C}/condensed@686902a/deps.tsv", encoding="utf-8"):
    if l[0] == "#":
        continue
    c = l.rstrip("\n").split("\t")
    u = c[1].split("::", 1)[-1]
    base = AUX.split(u)[0].rstrip(".")
    for x in c[2:]:
        x = x.split("::", 1)[-1]
        if base != x and not AUX.search(x):
            users_all[x].add(base)
            if x in gone:
                users[x].add(base)


def why(t):
    t = t.split("(merge")[0].lower()
    for k, pat in (("inline", r"inline"), ("drop-direction", r"direction"), ("conjunction", r"conjunction"),
                   ("doc-ref", r"^pr #\d+ doc|drop references"), ("unused", r"unused"), ("word-only", r"as a word"),
                   ("method", r"refactor|prove|construct|replace|reuse|use ")):
        if re.search(pat, t):
            return k
    return "?"


with open(out, "w") as o:
    o.write("# roadmap\tname\tclass\twhy\thash\tshort\tabsorbed\tupstream\n")
    seen = set()
    for r in rows:
        if r[2] not in ("removed", "renamed"):
            continue
        n = r[1]
        hh = [m for m in by61.get(h72.get(n, "-"), []) if m != n and not AUX.search(m)][:3]
        sh = [m for m in short61.get(n.rsplit(".", 1)[-1], []) if m != n][:3]
        # nearest surviving consumers: walk up through consumers that also vanished
        ab, frontier, vis, depth = set(), set(users.get(n, ())), {n}, 0
        while frontier and not ab and depth < 6:
            ab = {u for u in frontier if u in h61}
            vis |= frontier
            frontier = {v for u in frontier if u not in h61 for v in users_all.get(u, ()) if v not in vis}
            depth += 1
        ab = sorted(ab)
        ab = [f"{u}{'' if u in live else '(dead)'}" for u in ab][:4]
        if not ab and n not in users_all:
            ab = ["(no consumer at 72fead1)"]
        cls = r[2] + (":" + r[3] if r[3] else "")
        o.write("\t".join([r[0], n, cls, why(r[5]) if r[2] == "removed" else "rename",
                           ",".join(hh), ",".join(sh), ",".join(ab), r[5][:160]]) + "\n")
