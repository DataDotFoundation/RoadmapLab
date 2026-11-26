#!/usr/bin/env python3
"""Textual identity check: ported targets in a certificate file vs the roadmap's Suggested.lean.

usage: check_text.py SUGGESTED.lean CERT.lean
Blocks in CERT.lean between `-- BEGIN DEFS` / `-- END DEFS` must equal the roadmap's text from the
first `section` to its matching `end` (whitespace-normalised).
Blocks `-- BEGIN TARGET k NAME` / `-- END TARGET k` hold `def Target_k : Prop := ∀ BINDERS, CONCL`;
the roadmap's `theorem NAME BINDERS : CONCL := by sorry` must give the same BINDERS and CONCL.
The only adaptation allowed is that one (theorem signature -> ∀-proposition) and the docstring.
Exit status 0 iff every block matches. Computed; stdlib only.
"""
import re, sys

sug, cert = (open(p, encoding="utf-8").read() for p in sys.argv[1:3])
norm = lambda s: " ".join(s.split())
ok = True


def strip_doc(s):
    return re.sub(r"/--.*?-/", "", s, flags=re.S)


def top_colon(s):
    """index of the first ':' at bracket depth 0 (the signature's result colon)"""
    depth, last = 0, -1
    for i, c in enumerate(s):
        if c in "([{⦃":
            depth += 1
        elif c in ")]}⦄":
            depth -= 1
        elif c == ":" and depth == 0 and s[i + 1:i + 2] not in ("=",):
            return i
    return last


# definitions block
m = re.search(r"-- BEGIN DEFS\n(.*?)-- END DEFS", cert, re.S)
if m:
    r = re.search(r"\n(section Remainder\n.*?\nend Remainder)\n", sug, re.S)
    same = r and norm(strip_doc(r.group(1))) == norm(strip_doc(m.group(1)))
    print(f"DEFS: {'identical' if same else 'DIFFERENT'}")
    ok &= bool(same)

for m in re.finditer(r"-- BEGIN TARGET (\S+) (\S+)\n(.*?)-- END TARGET \1", cert, re.S):
    k, name, body = m.groups()
    body = strip_doc(body)
    b = re.search(r"def Target_\S+ : Prop :=\s*∀(.*)", body, re.S).group(1)
    r = re.search(r"theorem " + re.escape(name) + r"\b(.*?):=\s*by\s+sorry", sug, re.S)
    if not r:
        print(f"TARGET {k} {name}: not found in roadmap"); ok = False; continue
    sig = r.group(1)
    i = top_colon(sig)
    binders, concl = sig[:i], sig[i + 1:]
    # in the port the binders end at the top-level ',' before the conclusion
    j, depth = -1, 0
    for t, c in enumerate(b):
        if c in "([{⦃":
            depth += 1
        elif c in ")]}⦄":
            depth -= 1
        elif c == "," and depth == 0:
            j = t
            break
    pb, pc = b[:j], b[j + 1:]
    same = norm(binders) == norm(pb) and norm(concl) == norm(pc)
    print(f"TARGET {k} {name}: {'identical' if same else 'DIFFERENT'}")
    if not same:
        print("  roadmap:", norm(binders), "|", norm(concl))
        print("  port   :", norm(pb), "|", norm(pc))
    ok &= same

sys.exit(0 if ok else 1)
