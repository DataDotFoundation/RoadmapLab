#!/usr/bin/env python3
"""Daily drift watch: declarations cited by the ShortGRH roadmaps that are missing from upstream.

usage: watch.py ROADMAP_SHORTGRH_DIR UPSTREAM_SRC_DIR OUT_DIR [--src72 GRH_SRC_AT_72FEAD1]
                [--baseline PREV.json] [--meta KEY=VALUE ...]

The roadmaps cite `[ShortProof]`, grh-lean at `72fead1` (upstream's root commit, folder `grh/src`).
Upstream (leanprover-community/riemann-hypothesis) has moved on; this reports which cited names no
longer resolve at upstream head.

Steps (stdlib only, source level, approximate):
  1. `map/tools/citations.py` extracts every declaration cited per roadmap section
     (the `[ShortProof], file (decls)` line at the end of each section).
  2. `map/tools/leandecls.py` extracts every declaration of a source tree.
  3. A cited name resolves in a tree if it is a full name there, or a dotted suffix of one.
  4. With --src72, every missing name is classed:
       drift  resolves at 72fead1, missing at head: upstream removed or renamed it;
       noise  missing at both: an extractor artefact (`Main`, notation) or a name that is not a
              declaration of [ShortProof] at all (worth a look: a possible roadmap typo).
Writes OUT_DIR/latest.md and OUT_DIR/latest.json. With --baseline, the report also lists the change
since the previous run. Exit status: 0, or 3 if there are drift names that were not in the baseline
(the workflow uses this to open or update an issue).
"""
import json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.join(HERE, "..", "map", "tools")


def run(tool, *args):
    subprocess.run([sys.executable, "-I", os.path.join(TOOLS, tool), *args], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def read_tsv(p):
    with open(p, encoding="utf-8") as f:
        return [l.rstrip("\n").split("\t") for l in f if not l.startswith("#")]


def names_of(src, t, tag):
    p = os.path.join(t, f"decls-{tag}.tsv")
    run("leandecls.py", src, p)
    full = {r[0] for r in read_tsv(p) if r and r[0]}
    suffixes = set()
    for n in full:
        parts = n.split(".")
        for k in range(1, len(parts)):
            suffixes.add(".".join(parts[k:]))
    return full | suffixes


def pop_opt(args, flag, multi=False):
    vals = []
    while flag in args:
        i = args.index(flag)
        vals.append(args[i + 1])
        del args[i:i + 2]
    return vals if multi else (vals[0] if vals else None)


def main():
    args = sys.argv[1:]
    base = pop_opt(args, "--baseline")
    src72 = pop_opt(args, "--src72")
    meta = dict(kv.split("=", 1) for kv in pop_opt(args, "--meta", multi=True))
    roadmaps, src, out = args[:3]
    os.makedirs(out, exist_ok=True)
    with tempfile.TemporaryDirectory() as t:
        cites = os.path.join(t, "cites.tsv")
        run("citations.py", roadmaps, cites)
        head = names_of(src, t, "head")
        old = names_of(src72, t, "72") if src72 else None
        miss, total = {}, 0
        for r in read_tsv(cites):
            if len(r) < 5 or not r[4]:
                continue
            rm, sec, _title, _file, name = r[:5]
            total += 1
            if name not in head:
                miss.setdefault(name, set()).add(f"{rm} §{sec}")
    cls = {}
    for n in miss:
        cls[n] = "missing" if old is None else ("drift" if n in old else "noise")
    cur = {k: {"class": cls[k], "sections": sorted(v)} for k, v in sorted(miss.items())}
    prev = {}
    if base and os.path.isfile(base):
        prev = json.load(open(base, encoding="utf-8")).get("missing", {})
    new = {k: v for k, v in cur.items() if k not in prev}
    fixed = sorted(k for k in prev if k not in cur)
    drift = {k: v for k, v in cur.items() if v["class"] in ("drift", "missing")}
    noise = {k: v for k, v in cur.items() if v["class"] == "noise"}
    new_drift = {k: v for k, v in new.items() if v["class"] in ("drift", "missing")}
    json.dump({"meta": meta, "cited": total, "missing": cur}, open(os.path.join(out, "latest.json"), "w",
              encoding="utf-8"), indent=1, ensure_ascii=False)
    with open(os.path.join(out, "latest.md"), "w", encoding="utf-8") as o:
        o.write("# ShortGRH citation drift\n\n")
        if meta:
            o.write(" · ".join(f"{k}: `{v}`" for k, v in meta.items()) + "\n\n")
        o.write(f"{total} citations. {len(drift)} cited names no longer resolve at upstream head"
                + (f" (present at `72fead1`); {len(noise)} do not resolve at `72fead1` either." if old is not None
                   else ".") + " Source level and approximate: a resolving name may still have changed its"
                " statement; see the correspondence map for the elaborated comparison.\n\n")
        if base:
            o.write(f"## Since the previous run: {len(new_drift)} newly missing, {len(fixed)} newly resolved\n\n")
            for k, v in new_drift.items():
                o.write(f"- `{k}`: {', '.join(v['sections'])}\n")
            for k in fixed:
                o.write(f"- resolved again: `{k}`\n")
            o.write("\n")
        o.write("## Missing at upstream head\n\n")
        by_rm = {}
        for k, v in drift.items():
            for s in v["sections"]:
                by_rm.setdefault(s.split(" §")[0], []).append((s.split(" §")[1], k))
        for rm in sorted(by_rm):
            o.write(f"### {rm} ({len(by_rm[rm])})\n\n")
            for sec, k in sorted(by_rm[rm], key=lambda x: ([int(p) if p.isdigit() else 0 for p in x[0].split(".")], x[1])):
                o.write(f"- §{sec} `{k}`\n")
            o.write("\n")
        if noise:
            o.write("## Not a declaration at `72fead1` either (extractor noise or a possible roadmap typo)\n\n")
            for k, v in noise.items():
                o.write(f"- `{k}`: {', '.join(v['sections'][:4])}{' …' if len(v['sections']) > 4 else ''}\n")
    print(f"cited={total} drift={len(drift)} noise={len(noise)} new_drift={len(new_drift)} fixed={len(fixed)}")
    sys.exit(3 if (base and new_drift) else 0)


if __name__ == "__main__":
    main()
