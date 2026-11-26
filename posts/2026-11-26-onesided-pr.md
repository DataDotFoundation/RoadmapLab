---
kind: pr
repo: TauCetiProject/TauCetiRoadmap
base: main
branch: onesided-constant-forms
title: OneSidedPrimeSumBoundsAndAdmissibleData: the constant forms of 0.2 and 6.2 (c), with citations of the continuation
patch: posts/patches/onesided.patch
label_comment: awaiting-review
---
This updates two citations in OneSidedPrimeSumBounds to the current upstream proof and adds two remarks; no statement changes, so open implementation PRs are unaffected.
<!-- OBSERVATION (checklist): your chosen opening line. "open implementation PRs are unaffected" concerns a venue (TauCeti PRs) with no cited overlap proof; it is supported by reading their bodies (they target the existing statements). Your words, your call. -->

<!-- roadmap-summary -->
**What this revision changes.** Two new remarks:
- §0.2 records that the one-sided criterion is equivalent to its form with a constant in the hypothesis, `R_{q₀}^{(d)}(x) ≤ A·x^{β−1}`.
- §6.2 (c) records that the one-sided bound is equivalent to the same bound with a constant factor.

Both sections now also cite, next to [ShortProof] at `72fead1`, the declaration that proves them in the continuation of [ShortProof], [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis), at commit `61d870d`. The [ShortProof] reference names that repository.

**Why the change is made.** In the continuation, both results carry the constant. This came with upstream [PR #5627](https://github.com/leanprover-community/riemann-hypothesis/pull/5627), "carry the leading constant through Landau's criterion" (commit `f2201365d2d`).
- `New.LFunction_ne_zero_of_primeRemainder_le` now assumes `∃ A, ∀ᶠ x, R ≤ A·x^{β−1}`.
- `New.eventually_primeRemainder_le_rpow` was replaced by `New.eventually_primeRemainder_le_mul_rpow`, with the constant `128φ(q₀) + 32`.

The remarks let a reader use either form. <!-- OBSERVATION (checklist): no overlap proof between this claim and §6.3 implementations is cited; keep only if you phrase it as your own reading. -->

**What the roadmap keeps.** Every statement, every section number and `Suggested.lean`, unchanged. The criterion keeps its hypothesis `R ≤ x^{β−1}`, and the bound keeps `R ≤ y^{−1/2+ε}`. Both forms are proved equivalent below.
<!-- /roadmap-summary -->

This is a revision confined to `TauCetiRoadmap/ShortGRH/OneSidedPrimeSumBoundsAndAdmissibleData/README.md`.

**§0.2, the one-sided criterion.** A new paragraph after the statement:
- The hypothesis may equally be `R_{q₀}^{(d)}(x) ≤ A·x^{β−1}` for some real `A`.
- The two statements are equivalent: for `β < β′ < Re ρ`, eventually `A·x^{β−1} ≤ x^{β′−1}`.
- The citation line adds [`New.LFunction_ne_zero_of_primeRemainder_le`](https://github.com/leanprover-community/riemann-hypothesis/blob/61d870d08d5f6f5cc12f31fe40f5689024ea15ab/src/New/Reduction/Zeros/Criterion.lean#L41) at `61d870d`, the form with a constant.

**§6.2 (c), the one-sided bound.** A new paragraph after (a)–(c):
- (c) is equivalent to `R_{q₀}(y) ≤ C·y^{−1/2+ε}` for some `C`. Apply that bound with `ε/2` and use `C·y^{−ε/2} ≤ 1` for large `y`.
- The citation line adds [`New.eventually_primeRemainder_le_mul_rpow`](https://github.com/leanprover-community/riemann-hypothesis/blob/61d870d08d5f6f5cc12f31fe40f5689024ea15ab/src/New/Reduction/OneSidedBound.lean#L210), which proves (c) with `C = 128φ(q₀) + 32`.

**References.** The [ShortProof] entry gains one sentence naming its continuation and the commit cited in 0.2 and 6.2.

No section, layer, target or headline theorem is added, removed or renumbered. No supplier is added or dropped. `Suggested.lean` is untouched.
<!-- OBSERVATION (checklist): no overlap proof between this claim and the TauCeti implementation PRs is cited; keep only if you phrase it as your own reading. -->
Open implementation work on §§0.2 and 6.2 targets the existing statements, which do not change.

**Verification.** Both equivalences are proved in Lean, against the continuation at `61d870d`.
- The roadmap's definitions of `R_q` (0.1) and its `Suggested.lean` targets are taken verbatim, and the roadmap's `primeRemainder` is proved equal to the continuation's `New.primeRemainder`.
- The certificates are `target_02_iff` (↔ with `New.LFunction_ne_zero_of_primeRemainder_le`) and `target_62_iff` (↔ with `New.eventually_primeRemainder_le_mul_rpow`). They use the standard axioms only.
- To check: `<one command per certificate, from RH-Dual's roadmap-certs comparator package, once published>`.
- The statements were checked to mean the same at the roadmap's Mathlib pin and at the edition's: the 8 roadmap declarations elaborate to identical terms in both (compared by fingerprint, with proofs erased and binder names ignored); 22 of the ~3,000 constants they depend on changed representation between the pins (field renames, repackaged instances), and 25 more are reached in only one version, each examined individually but not machine-checked across versions. Report: `https://github.com/DataDotFoundation/RoadmapLab/blob/main/reports/crossversion-OneSided.md`.
<!-- OBSERVATION (checklist): the report link becomes valid only once the RoadmapLab repo is pushed with reports/crossversion-OneSided.md; until then the evidence is in a non-public path. Do not write "machine-verified across versions". -->

**Possible follow-up for the author.** Restate §0.2 with the constant in its hypothesis, as the continuation does. That is the stronger form of the theorem (the equivalence is `target_02_iff`).
<!-- OBSERVATION (checklist): no overlap proof between this claim and the TauCeti implementation PRs is cited; keep only if you phrase it as your own reading. -->
It is left out here because it would change a statement that implementation PRs build against.

<!-- depends-on -->
**Depends on** (suppliers still open; they merge first): none.
<!-- /depends-on -->

AI-prepared with Claude Opus 5.5 (Anthropic): it surveyed the roadmap against the upstream proof, drafted the remarks and wrote the Lean certificates; I selected the changes and read the diff and the certificates. <!-- user: adjust to the work actually done; add any other models used by the sessions whose work you rely on (e.g. the comparator package) -->
