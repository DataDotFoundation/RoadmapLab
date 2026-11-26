#!/usr/bin/env python3
"""Source-level declaration extractor for a Lean 4 tree (approximate, stdlib only).

usage: leandecls.py SRC_ROOT OUT.tsv
Writes: name, kind, file (relative), line, normalized statement (text from the declaration keyword
up to the first top-level `:=`, ` where`, or `|` line; comments stripped; whitespace collapsed; the
name itself replaced by `_` so a rename with an identical statement can be detected).
Namespaces: tracks `namespace X` / `section` / `end`; a name starting with `_root_.` escapes.
Structure/class fields are emitted as `S.field` (kind `field`); inductive constructors as `I.c`.
"""
import os, re, sys

KW = r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|noncomputable def|irreducible_def)"
MODS = r"(?:(?:@\[[^\]]*\]\s*)|(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
DECL = re.compile(r"^" + MODS + r"(theorem|lemma|def|abbrev|instance|structure|class inductive|class|inductive|opaque|axiom|irreducible_def)\b\s*([^\s:({\[]*)")
NS = re.compile(r"^namespace\s+(\S+)")
SEC = re.compile(r"^(?:noncomputable\s+)?section\b\s*(\S*)")
END = re.compile(r"^end\b\s*(\S*)")
FIELD = re.compile(r"^\s{2,}(?:\(\s*)?([A-Za-z_][\w'₀-₉!?]*)\s*(?:[:({\[]|::)")
CTOR = re.compile(r"^\s*\|\s*([A-Za-z_][\w'₀-₉!?]*)")


def strip_comments(text):
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(text[i]); i += 1
    return "".join(out)


def stmt_of(lines, k, short):
    buf = []
    for j in range(k, min(k + 80, len(lines))):
        l = lines[j]
        if j > k and (DECL.match(l) or l.startswith("end ") or l.startswith("namespace ")):
            break
        cut = None
        for pat in (r":=", r"\bwhere\b"):
            m = re.search(pat, l)
            if m and (cut is None or m.start() < cut):
                cut = m.start()
        if cut is not None:
            buf.append(l[:cut]); break
        if j > k and re.match(r"^\s*\|", l):
            break
        buf.append(l)
    s = " ".join(" ".join(buf).split())
    if short:
        s = s.replace(short, "_", 1)
    return s


def walk(root):
    for d, _, fs in os.walk(root):
        for f in sorted(fs):
            if f.endswith(".lean"):
                yield os.path.join(d, f)


def main(root, out):
    rows = []
    for p in walk(root):
        rel = os.path.relpath(p, root)
        lines = strip_comments(open(p, encoding="utf-8").read()).split("\n")
        stack = []  # (kind, name)
        cur = None  # ("structure"/"inductive", fullname) while inside body
        for k, l in enumerate(lines):
            m = NS.match(l)
            if m:
                # `namespace A.B` opens two scopes (closed by `end B` then `end A`, or `end A.B`)
                for part in m.group(1).replace("«", "").replace("»", "").split("."):
                    stack.append(("ns", part))
                cur = None; continue
            m = SEC.match(l)
            if m and not l.startswith("section_"):
                stack.append(("sec", m.group(1))); cur = None; continue
            m = END.match(l)
            if m and l.split()[0] == "end":
                k = len(m.group(1).split(".")) if m.group(1) else 1
                for _ in range(k):
                    if stack:
                        stack.pop()
                cur = None; continue
            m = DECL.match(l)
            if m:
                kind, nm = m.group(1), m.group(2)
                if not nm or nm in ("where",):
                    cur = None; continue
                prefix = ".".join(x for t, n in stack if t == "ns" for x in [n])
                nm = nm.replace("«", "").replace("»", "")
                full = nm[len("_root_."):] if nm.startswith("_root_.") else (prefix + "." + nm if prefix else nm)
                short = nm.split(".")[-1]
                rows.append((full, kind.split()[-1], rel, k + 1, stmt_of(lines, k, nm)))
                cur = (kind, full) if kind in ("structure", "class", "inductive", "class inductive") else None
                continue
            if cur and l.strip():
                if not l.startswith(" ") and not l.startswith("|"):
                    cur = None; continue
                if cur[0] in ("structure", "class"):
                    f = FIELD.match(l)
                    if f and f.group(1) not in ("extends", "mk", "where", "deriving") and l.startswith("  ") and not l.startswith("    "):
                        rows.append((cur[1] + "." + f.group(1), "field", rel, k + 1, " ".join(l.split())))
                else:
                    c = CTOR.match(l)
                    if c:
                        rows.append((cur[1] + "." + c.group(1), "ctor", rel, k + 1, " ".join(l.split())))
    with open(out, "w") as o:
        o.write("# name\tkind\tfile\tline\tstatement\n")
        for r in rows:
            o.write("\t".join(str(x).replace("\t", " ") for x in r) + "\n")
    print(f"{len(rows)} declarations from {root}", file=sys.stderr)


if __name__ == "__main__":
    main(*sys.argv[1:3])
