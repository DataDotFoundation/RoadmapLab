#!/usr/bin/env python3
"""Build the per-name and per-section correspondence TSVs for ShortGRH at condensed@61d870d.

usage: final.py WORKDIR OUTDIR
Inputs (WORKDIR, a scratch directory with the outputs of the other tools): cites.tsv, my-kinds.txt, replace.tsv, live-72fead1.txt,
substantive-judged.tsv, plumbing-judged.tsv (optional); Librarian staleness TSV and live-61d870d.txt.
Outputs: OUTDIR/shortgrh-61d870d-names.tsv, OUTDIR/shortgrh-61d870d.tsv (sections), and a summary on stdout.
"""
import collections, os, sys

W, O = sys.argv[1:3]
L = os.path.join(os.environ.get("LIBRARIAN_STATE", os.path.expanduser("~/work/Librarian/state")), "reports")


def tsv(p):
    if not os.path.exists(p):
        return []
    return [l.rstrip("\n").split("\t") for l in open(p, encoding="utf-8") if l.strip() and l[0] != "#"]


stale = {(r[0], r[1]): r for r in tsv(f"{L}/shortgrh-staleness-61d870d.tsv")}
live61 = set(l.strip() for l in open(f"{L}/live-61d870d.txt", encoding="utf-8"))
live72 = set(l.strip() for l in open(f"{W}/live-72fead1.txt", encoding="utf-8"))
kinds = {r[0]: r[1] for r in tsv(f"{W}/my-kinds.txt")}
judged = {}
for f in ("plumbing-judged.tsv", "substantive-judged.tsv", "manual-judged.tsv"):
    for r in tsv(f"{W}/{f}"):
        if len(r) >= 2:
            judged[r[0]] = (r[1].strip().lower(), r[2] if len(r) > 2 else "", r[3] if len(r) > 3 else "")
repl = {(r[0], r[1]): r for r in tsv(f"{W}/replace.tsv")}


def eff(rm, n):
    """effective class of a cited name, and a note"""
    s = stale.get((rm, n))
    if not s:
        return None, ""
    cls = s[2]
    if cls == "aux":
        return None, ""
    if cls == "renamed":
        new = s[3].strip("`→ ")
        if n in judged:
            v = judged[n][0]
            return ("removed" if v == "removed" else ("renamed" if v == "same-meaning" else v)), f"→ {new}: {judged[n][2][:120]}"
        return "renamed?", f"→ {new} (skeleton-equal, unchecked)"
    if cls == "removed":
        r = repl.get((rm, n), [""] * 8)
        why, hh, sh, ab = r[3], r[4], r[5], r[6]
        if n not in live72:
            return "removed-offroute", f"dead at 72fead1; {s[5][:90]}"
        if hh:
            return "renamed", hh.split(",")[0] + " (same statement hash)"
        if why == "conjunction":
            return "removed-split", f"conjunction of existing lemmas; consumers {ab}"
        if why == "drop-direction":
            return "removed-weakened", f"one direction dropped; {s[5][:90]}"
        if ab and "no consumer" not in ab:
            return "removed-absorbed", f"[{why}] into {ab}; {s[5][:90]}"
        return "removed", f"[{why}] {s[5][:110]}"
    # same or changed
    if n in judged:
        v = judged[n][0]
        v = {"same-meaning": "same-meaning", "stronger": "stronger", "weaker": "weaker",
             "incomparable": "incomparable", "vacuous-risk": "incomparable"}.get(v, v)
        return v, judged[n][2][:140]
    k = kinds.get(n)
    if cls == "changed" or k in ("drop-inst", "add-inst", "cosmetic"):
        if k in ("drop-inst", "add-inst", "cosmetic") or k is None:
            return "same-meaning", f"{k or 'elaboration-only'} change"
        return "changed-unjudged", ""
    if k == "substantive":
        return "changed-unjudged", ""
    return "same", ""


cites = collections.OrderedDict()
titles = {}
for r in tsv(f"{W}/cites.tsv"):
    rm, sec, title, f, d = (r + [""] * 5)[:5]
    titles[(rm, sec)] = (title, f)
    cites.setdefault((rm, sec), [])
    if d:
        cites[(rm, sec)].append(d)

names_out = open(f"{O}/shortgrh-61d870d-names.tsv", "w")
names_out.write("# roadmap\tsection\tname\tclass_librarian\teffective\tlive72\tlive61\tnote\n")
sec_out = open(f"{O}/shortgrh-61d870d.tsv", "w")
sec_out.write("# roadmap\tsection\ttitle\tfile72\tn_names\tmatch\tlive61\tchanged\tvanished\troute_change\toffroute\tdetail\n")
summary = collections.defaultdict(collections.Counter)
for (rm, sec), ds in cites.items():
    title, f = titles[(rm, sec)]
    effs = []
    for d in dict.fromkeys(ds):
        e, note = eff(rm, d)
        if e is None:
            continue
        s = stale[(rm, d)]
        effs.append((d, e, note))
        names_out.write("\t".join([rm, sec, d, s[2], e, "y" if d in live72 else "n",
                                   "y" if d in live61 else ("-" if e.startswith("removed") else "n"), note]) + "\n")
    E = [e for _, e, _ in effs]
    if sec == "S":
        match = "target(see matcher)"
    elif not E:
        match = "nocite"
    else:
        rem = [e for e in E if e.startswith("removed")]
        keep = [e for e in E if not e.startswith("removed")]
        if rem and not keep:
            match = "none"  # every cited name vanished; 'detail' points to the absorbing consumer
        elif rem:
            match = "partial"
        elif "weaker" in E or "removed-weakened" in E:
            match = "weaker"
        elif "incomparable" in E:
            match = "partial"
        elif "stronger" in E:
            match = "stronger"
        elif "changed-unjudged" in E or "renamed?" in E:
            match = "changed?"
        else:
            match = "same"
    surv = [d for d, e, _ in effs if not e.startswith("removed") and e != "renamed"]
    lv = "y" if surv and all(d in live61 for d in surv) else ("n/a" if not surv else "partly")
    chg = sum(e in ("stronger", "weaker", "incomparable", "changed-unjudged") for e in E)
    van = sum(e.startswith("removed") for e in E)
    rc = sum(e.startswith("removed") and e != "removed-offroute" for e in E)
    off = sum(e == "removed-offroute" for e in E)
    det = "; ".join(f"{d.split('.')[-1]}:{e}" for d, e, _ in effs if e not in ("same", "same-meaning"))[:400]
    sec_out.write("\t".join(map(str, [rm, sec, title, f, len(effs), match, lv, chg, van, rc, off, det])) + "\n")
    if sec != "S":
        summary[rm][match] += 1
        summary[rm]["sections"] += 1
        summary[rm]["route_change"] += rc > 0
        summary[rm]["offroute"] += off > 0

print("roadmap\tsections\tsame\tstronger\tweaker\tpartial\tnone\tchanged?\tnocite\tsec_with_route_change\tsec_with_offroute")
for rm, c in sorted(summary.items()):
    print("\t".join([rm] + [str(c[k]) for k in ("sections", "same", "stronger", "weaker", "partial", "none", "changed?", "nocite", "route_change", "offroute")]))
