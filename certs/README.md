# Certificates against the proof

These files are proved in the environment of the upstream proof, leanprover-community/riemann-hypothesis at `61d870d08d5f6f5cc12f31fe40f5689024ea15ab` (Lean v4.37.0-rc1, Mathlib `31ce06e`, TauCeti `6d810e5`). The proof's own build is far too large for free CI, so reproduce them locally.

```bash
git clone https://github.com/leanprover-community/riemann-hypothesis.git rh
cd rh && git checkout 61d870d08d5f6f5cc12f31fe40f5689024ea15ab
lake exe cache get              # the proof's published build cache; see its CACHE.md
lake build --no-build           # should report every target up to date
mkdir -p src/RoadmapLab && cp /path/to/RoadmapLab/certs/*.lean src/RoadmapLab/
lake env lean src/RoadmapLab/OneSided.lean    # no output = no errors, no warnings
lake env lean src/RoadmapLab/Exchange.lean
```

To check the axioms, add a file containing `import RoadmapLab.OneSided` and `#print axioms TauCetiRoadmap.ShortGRH.OneSidedPrimeSumBoundsAndAdmissibleData.target_02_iff`, and so on. First compile each certificate to an `.olean`, with `lake env lean -o .lake/build/lib/lean/RoadmapLab/OneSided.olean src/RoadmapLab/OneSided.lean`. Every certificate here depends only on `propext`, `Classical.choice` and `Quot.sound`.

Text identity. Each ported statement sits between `BEGIN`/`END` markers.
- `python3 -I map/tools/check_text.py <roadmap Suggested.lean> certs/OneSided.lean` compares OneSided against the roadmap's text. The only adaptation is `theorem … : concl := by sorry` ↦ `def Target_k : Prop := ∀ …, concl`.
- `python3 -I map/tools/check_text72.py <72fead1 TheoremForPartners.lean> certs/Exchange.lean` compares Exchange against the `72fead1` source. It allows one listed pin adaptation, a predicate used as a `Set`.

Cross-version meaning (computed). A certificate proves the roadmap's statement at the proof's pins (Mathlib `31ce06e`), while the roadmap is written at its own pins (Mathlib `1b1ccf4`). For OneSided, the roadmap's `Suggested.lean` was compiled verbatim at both pins, and the full closure of its 8 roots through definitions was fingerprinted with proofs erased.
- All 8 roots fingerprint identically, as do 3,066 of the 3,088 shared constants.
- The remaining 22 differ only in representation: the `enorm` → `eNorm` rename, repackaged order instances, and `fixF` moved to core.

So the port means the same at both pins. The check was run with MeaningLib's fingerprinting tools.

A `lake comparator` package of the OneSided certificates, with the roadmap file taken verbatim as the challenge, is in [DataDotFoundation/RH-Dual](https://github.com/DataDotFoundation/RH-Dual), `roadmap-certs/`.

| file | roadmap | sections | kind |
|---|---|---|---|
| `OneSided.lean` | OneSidedPrimeSumBoundsAndAdmissibleData | 0.1 (=), 0.2 (↔), 6.2 (c) (↔), 6.3 (←) | 2 |
| `Exchange.lean` | DeterminantsOfThetaLiftChains | 3.4 (↔), 3.8 (a)–(b) (←, four lemmas) | 2 |
