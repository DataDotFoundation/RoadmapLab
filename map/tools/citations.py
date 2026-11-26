#!/usr/bin/env python3
"""Extract per-section [ShortProof] citations from the ShortGRH roadmaps.

usage: citations.py SHORTGRH_DIR OUT.tsv
Rows: roadmap, section number, section title, file (as cited, normalized to .lean), declaration.
A section with no [ShortProof] line gets one row with empty file/declaration.
Suggested.lean targets are emitted with section 'S' and the target name as title.
"""
import os, re, sys

H = re.compile(r"^(#{2,4})\s+(?:(\d+(?:\.\d+)*)\s+)?(.*)$")
TICK = re.compile(r"`([^`]+)`")
SUGG = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:theorem|lemma|def|abbrev|structure|class|instance|noncomputable def)\s+([^\s:({\[]+)")


def norm_file(f):
    f = f.strip().rstrip(",;")
    if f.startswith("src/"):
        f = f[4:]
    if f.startswith("grh/src/"):
        f = f[8:]
    return f if f.endswith(".lean") else f + ".lean"


def blocks(lines):
    """Yield (secnum, title, [ShortProof] text) for each numbered ### section."""
    sec, title, buf, grab = None, None, [], False
    out = []
    for l in lines:
        m = H.match(l)
        if m:
            if sec is not None:
                out.append((sec, title, " ".join(buf)))
            if m.group(2) and len(m.group(1)) >= 3:
                sec, title, buf, grab = m.group(2), m.group(3).strip(), [], False
            else:
                sec, title, buf, grab = None, None, [], False
            continue
        if sec is None:
            continue
        if l.startswith("[ShortProof]"):
            grab = True
        if grab:
            if not l.strip():
                grab = False
            else:
                buf.append(l.strip())
    if sec is not None:
        out.append((sec, title, " ".join(buf)))
    return out


def main(d, out):
    rows = []
    for rm in sorted(os.listdir(d)):
        p = os.path.join(d, rm, "README.md")
        if not os.path.isfile(p):
            continue
        for sec, title, txt in blocks(open(p, encoding="utf-8").read().split("\n")):
            cur, n = "", 0
            for t in TICK.findall(txt):
                if "/" in t and " " not in t:
                    cur = norm_file(t); continue
                if " " in t or not re.match(r"^[@A-Za-z_𝔸-𝔾]", t):
                    continue
                rows.append((rm, sec, title, cur, t.lstrip("@")))
                n += 1
            if n == 0:
                rows.append((rm, sec, title, cur, ""))
        s = os.path.join(d, rm, "Suggested.lean")
        if os.path.isfile(s):
            for l in open(s, encoding="utf-8"):
                m = SUGG.match(l)
                if m:
                    rows.append((rm, "S", m.group(1), "", ""))
    with open(out, "w") as o:
        o.write("# roadmap\tsection\ttitle\tfile\tdecl\n")
        for r in rows:
            o.write("\t".join(r) + "\n")
    print(f"{len(rows)} rows", file=sys.stderr)


if __name__ == "__main__":
    main(*sys.argv[1:3])
