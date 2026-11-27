#!/usr/bin/env python3
"""Lines of reasoning between theta lifts and number fields, on the weighted dependency graph.

usage: bridges.py CORPUS_DIR LIVE.txt OUT_DIR
CORPUS_DIR is a MeaningLib/Librarian corpus (types.tsv: module, name, kind, hash, length, line,
end_line; deps.tsv: module, name, direct dependencies, type and value). LIVE.txt is the closure of
`riemannHypothesis`, one name per line.

Definitions (all by name and module, i.e. grep-level; computed):
  Θ   theta-lift constructions: project definitions whose last name component is in THETA_STEMS and
      whose module lies in THETA_MODULES (Weil representation, Siegel–Weil, theta lifts of the
      chain, one lift, upper bound, spanning). Abelian-variety theta functions are excluded.
  N   number-field constants, classed by KINDS (regexes over full names).
  bridge   a project declaration whose direct dependencies contain at least one Θ constant and at
           least one N constant: one step of reasoning that uses a theta lift and number-field
           arithmetic together.
  weight   the declaration's source line span (end_line − line + 1).
Writes OUT_DIR/bridges.tsv and OUT_DIR/metrics.md (stdlib only).
"""
import collections, os, re, sys

corpus, livef, out = sys.argv[1:4]
os.makedirs(out, exist_ok=True)
THETA_MODULES = re.compile(r"^(Lib\.Weil|Lib\.SiegelWeil|Lib\.DiscreteSeries\.Theta|New\.Determinant|New\.OneLift|New\.UpperBound|New\.Spanning|New\.Derivatives)")
THETA_STEMS = {"lift", "thetaLift", "IsThetaLift", "pairTheta", "pairThetaKernel", "pairThetaKer", "thetaKernel",
               "thetaKernelY", "thetaKernelPairing", "ThetaKernel", "thetaLarge", "thetaSmall", "thetaIntegral",
               "equalRankThetaRatio", "modTransposedLift", "pointLift", "pointTransposedLift", "periodLift",
               "formLift", "triangleLift", "trivialLift", "singleLift", "liftDeterminant", "chainDeterminant",
               "thetaOnRealData", "lineTheta", "lagrangianTheta", "θ",
               # theta kernels and the chain of lifts (added on RH-Dual's review)
               "modKernel", "modLift", "liftKernel", "gridKernel", "columnLineKernel", "rowLineKernel",
               "lowerChain", "lowerChainAtLevel", "Θ", "transposedChain", "transposedMove", "liftMove"}
KINDS = [
    ("places", re.compile(r"InfinitePlace|New\.FinPlace|ClosurePlace|IsPlaceOver|HeightOneSpectrum|LevelPlaces|ramifiedPlaces|PlaceAboveLevel|New\.IsSplit")),
    ("L_values", re.compile(r"lValue|LFunction|\.L$|LSeries|zetaFunction|dedekindZeta|lValueProd")),
    ("hecke_characters", re.compile(r"HeckeChar|SplitTameChar|TameChar|\.character$|New\.chiK|quadTwist|New\.QZChar|AutChar\.[a-z]")),
    ("conductors_ideals_classgroups", re.compile(r"ClassGroup|absNorm|New\.Modulus|ResidueRing|Ideal\.span|IsDedekindDomain\.|\.Nm$|normQ")),
    ("adeles", re.compile(r"New\.𝔸|FiniteAdeleRing|AdeleRing|New\.LocProd|toAdele|New\.SemilocalField")),
    ("field_invariants", re.compile(r"NumberField\.(discr|classNumber|Units|regulator|RingOfIntegers\.[a-z])|New\.QuadField\.[a-z]|discriminant")),
]
# Typeclass plumbing (NumberField E, CMType E, WeilData E, group types) is NOT counted: it occurs in every
# theta-lift type and says nothing about which number-field arithmetic a step uses.
AUX = re.compile(r"\._proof_|\._simp_|\.match_|\.eq_\d|congr_simp|::|\._unfold|\.proof_\d|\._aux")

types, span, module = {}, {}, {}
for l in open(f"{corpus}/types.tsv", encoding="utf-8"):
    if l[0] == "#":
        continue
    c = l.rstrip("\n").split("\t")
    n = c[1].split("::", 1)[-1]
    module[n], types[n] = c[0], c[2]
    if c[5] and c[6]:
        span[n] = int(c[6]) - int(c[5]) + 1
live = set(x.strip() for x in open(livef, encoding="utf-8"))
theta = {n for n, k in types.items() if k in ("def", "opaque", "abbrev", "inductive", "structure")
         and THETA_MODULES.match(module.get(n, "")) and n.rsplit(".", 1)[-1] in THETA_STEMS and not AUX.search(n)}

def kinds_of(names):
    ks = collections.defaultdict(set)
    for x in names:
        for k, rx in KINDS:
            if rx.search(x):
                ks[k].add(x)
    return ks

rows = []
for l in open(f"{corpus}/deps.tsv", encoding="utf-8"):
    if l[0] == "#":
        continue
    c = l.rstrip("\n").split("\t")
    n = c[1].split("::", 1)[-1]
    if AUX.search(n) or not (n.startswith("New.") or n.startswith("_root_")):
        continue
    ds = {x.split("::", 1)[-1] for x in c[2:]}
    th = ds & theta
    if not th:
        continue
    ks = kinds_of(ds)
    if not ks:
        continue
    rows.append((n, module.get(n, c[0]), span.get(n, 0), n in live, sorted(ks), sorted(th),
                 "Matrix.det" in ds, {k: sorted(v)[:3] for k, v in ks.items()}))

with open(f"{out}/bridges.tsv", "w", encoding="utf-8") as o:
    o.write("# name\tmodule\tlines\tlive\tkinds\ttheta_constants\tuses_det\texample_nf_constants\n")
    for r in sorted(rows, key=lambda r: (r[1], r[0])):
        o.write("\t".join([r[0], r[1], str(r[2]), "y" if r[3] else "n", ",".join(r[4]), ",".join(r[5]),
                           "y" if r[6] else "n", "; ".join(f"{k}:{'|'.join(v)}" for k, v in r[7].items())]) + "\n")

# metrics
live_proj = [n for n in live if n.startswith("New.") and not AUX.search(n)]
live_lines = sum(span.get(n, 0) for n in live_proj)
def agg(sel):
    return len(sel), sum(r[2] for r in sel)
allb, liveb = rows, [r for r in rows if r[3]]
by_dir = collections.defaultdict(list)
for r in liveb:
    by_dir[".".join(r[1].split(".")[:2])].append(r)
by_kind = collections.Counter(k for r in liveb for k in r[4])
lines_kind = collections.Counter()
for r in liveb:
    for k in r[4]:
        lines_kind[k] += r[2]
theta_live = [n for n in theta if n in live]
with open(f"{out}/metrics.md", "w", encoding="utf-8") as o:
    o.write("# Theta lifts ↔ number fields: metrics (computed)\n\n")
    o.write("*Tag:* computed (bridges.py, bridge_graph.py) at corpus `condensed@61d870d` (Librarian, built with MeaningLib's "
            "extractor from leanprover-community/riemann-hypothesis `61d870d`, Lean v4.37.0-rc1, Mathlib `31ce06e`); live set = "
            "the Librarian's closure of `riemannHypothesis` at that corpus (`live-61d870d.txt`); owners read from the "
            "RoadmapLab correspondence map (ShortGRH at `72fead1`). All matching is grep-level, over names and modules. "
            "Line spans are a price tag (the proof as written, detours included), not a measure of content.\n\n")
    o.write(f"- Θ (theta-lift constructions, by name and module): **{len(theta)}**, of which live **{len(theta_live)}**.\n")
    o.write(f"- Bridges (direct use of a Θ constant and a number-field constant): **{agg(allb)[0]}**, live **{agg(liveb)[0]}** ({agg(liveb)[1]:,} lines).\n")
    o.write(f"- Live project declarations: {len(live_proj):,} ({live_lines:,} lines); bridge share of live lines: **{100*agg(liveb)[1]/max(1,live_lines):.1f}%**.\n")
    o.write(f"- Bridges also using `Matrix.det`: **{sum(r[6] for r in liveb)}** ({sum(r[2] for r in liveb if r[6]):,} lines).\n\n")
    o.write("## By number-field kind (live bridges; a bridge may have several kinds)\n\n| kind | bridges | lines |\n|---|---|---|\n")
    for k, _ in KINDS:
        o.write(f"| {k} | {by_kind[k]} | {lines_kind[k]:,} |\n")
    o.write("\n## By directory (live bridges)\n\n| directory | bridges | lines | with det |\n|---|---|---|---|\n")
    for d, rs in sorted(by_dir.items(), key=lambda x: -sum(r[2] for r in x[1])):
        o.write(f"| `{d}` | {len(rs)} | {sum(r[2] for r in rs):,} | {sum(r[6] for r in rs)} |\n")
    o.write("\n## Θ used by the most bridges\n\n| Θ constant | live bridges |\n|---|---|\n")
    cnt = collections.Counter(t for r in liveb for t in r[5])
    for t, c in cnt.most_common(15):
        o.write(f"| `{t}` | {c} |\n")
print(f"theta={len(theta)} live={len(theta_live)} bridges={len(allb)} live_bridges={len(liveb)} lines={agg(liveb)[1]}")
