#!/usr/bin/env python3
"""Text check: `-- BEGIN OLD NAME` ... `-- END OLD` blocks of a certificate file vs the declaration
`lemma NAME` (up to `:= by`) in a 72fead1 source file. Whitespace-normalised; allowed adaptations
are listed in ADAPT (pin drift only). usage: check_text72.py SRC72_FILE CERT.lean ; exit 0 iff all match."""
import re, sys
ADAPT = [("schwartzBruhat HasLeftInv", "schwartzBruhat {y | HasLeftInv y}")]
src, cert = (open(p, encoding="utf-8").read() for p in sys.argv[1:3])
norm = lambda s: " ".join(s.split())
ok = True
for m in re.finditer(r"-- BEGIN OLD (\S+)\n(.*?)-- END OLD", cert, re.S):
    name, body = m.groups()
    r = re.search(r"\nlemma " + re.escape(name) + r" .*?:= by", src, re.S)
    old = norm(r.group(0)) if r else ""
    used = []
    for a, b in ADAPT:
        if a in old:
            old = old.replace(a, b); used.append(a)
    same = bool(r) and old == norm(body)
    print(f"{name}: {'identical' if same else 'DIFFERENT'}{' (adapted: ' + '; '.join(used) + ')' if used and same else ''}")
    ok &= same
sys.exit(0 if ok else 1)
