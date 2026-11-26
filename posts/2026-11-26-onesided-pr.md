---
kind: pr
repo: TauCetiProject/TauCetiRoadmap
base: main
branch: onesided-constant-forms
title: OneSidedPrimeSumBoundsAndAdmissibleData: constant forms of 0.2 and 6.2 (c), citing the continuation of [ShortProof]
patch: posts/patches/onesided.patch
label_comment: awaiting-review
---
This updates two citations in OneSidedPrimeSumBounds to the current upstream proof and adds two remarks; no statement changes, so open implementation PRs are unaffected.
<!-- OBSERVATION (checklist): your chosen opening line. "open implementation PRs are unaffected" concerns the TauCeti PRs, a venue with no cited overlap proof; it is supported by reading their bodies (they target the existing statements). "updates two citations" is accurate as "adds": the [ShortProof] lines are unchanged, and the rehearsal predicts the AI pass will flag it; a version that matches the head: "This adds two remarks to OneSidedPrimeSumBoundsAndAdmissibleData, each citing the current upstream proof; no statement changes, so open implementation PRs are unaffected." Your words, your call. -->

<!-- roadmap-summary -->
**What this revision changes.** §0.2 gains a remark: the one-sided criterion is equivalent to its form with a constant in the hypothesis, `R_{q₀}^{(d)}(x) ≤ A·x^{β−1}` for some `A`. §6.2 (c) gains a remark: the one-sided bound is equivalent to the same bound with a constant factor. Each remark cites the declaration that proves the constant form in the continuation of [ShortProof] at commit `61d870d`, and the [ShortProof] reference now says what that continuation is.

**Why the change is made.** Since upstream [PR #5627](https://github.com/leanprover-community/riemann-hypothesis/pull/5627) ("carry the leading constant through Landau's criterion"), the proof states both results with the constant (`New.LFunction_ne_zero_of_primeRemainder_le`, `New.eventually_primeRemainder_le_mul_rpow`, with `C = 128φ(q₀) + 32`). The remarks record that the roadmap's forms and the proof's forms are interchangeable.

**What the roadmap keeps.** Every statement, every `[ShortProof], path (declaration)` line, every section number, and `Suggested.lean`.
<!-- /roadmap-summary -->

A revision confined to `TauCetiRoadmap/ShortGRH/OneSidedPrimeSumBoundsAndAdmissibleData/README.md` (+15 −1). No section, target or supplier is added, removed or renumbered.

Should §0.2 instead be restated with the constant in its hypothesis, as the proof now has it? That is the stronger form of the theorem; I left it out because it changes a statement.

<!-- depends-on -->
**Depends on** (suppliers still open; they merge first): none.
<!-- /depends-on -->

AI-prepared with Claude Opus 5.5 (Anthropic): it compared the roadmap with the upstream proof, drafted the remarks, and proved both equivalences in Lean against the proof at `61d870d`. I selected the change and read the diff. <!-- user: adjust to the work actually done. The Lean certificates are not public yet: link them (RH-Dual roadmap-certs) once published, or drop "proved both equivalences in Lean". -->
