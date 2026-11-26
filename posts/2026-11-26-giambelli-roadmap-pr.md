---
kind: pr
repo: TauCetiProject/TauCetiRoadmap
base: main
branch: giambelli-theta-grids
title: GiambelliAndThetaLiftGrids: Giambelli's identity, Frobenius coordinates and the grids of the chain of lifts
patch: posts/patches/giambelli.patch
label_comment: awaiting-review
cert1:
---
TODO-USER: read the roadmap and this description carefully and rewrite them in your own words; resolve the TODO-USER line in the README (Lean Pool status in 2.2); push the branch to your fork, run RoadmapLab's cert1 workflow on it and paste the run URL into `cert1:` above; then delete this line.

<!-- roadmap-summary -->
**What this roadmap builds.** Frobenius coordinates and the Durfee rank of a Young diagram; the hook formula and Giambelli's identity `s_λ = det(s_{(a_i|b_j)})` for Tau Ceti's `diagramSchurPoly` and `schurPoly`, consuming Tau Ceti's Jacobi–Trudi and dual Jacobi–Trudi identities; the vanishing of `[p_μ] s_λ` for `ℓ(μ) < d(λ)` and the hook values at a single power sum, from Tau Ceti's Murnaghan–Nakayama rule. Layer 3 states, as theorems to prove, a dictionary for the monotone paths through two grids of DeterminantsOfThetaLiftChains §5.1: enclosed squares form a Young diagram in the `m × m` box, the diagonal node is its Durfee rank, and orders of the `m²` turns are standard tableaux of shape `(m^m)`.

**Where it sits.** It consumes Tau Ceti's Schur polynomials and Mathlib's `YoungDiagram`, and reads DeterminantsOfThetaLiftChains §§3.11, 3.12, 4.4, 5.1, 5.9 without restating them. The geometric Giambelli formula stays with TensorProductCombinatorics §6.4, which is cited. A formalization of Giambelli's identity against Tau Ceti's Schur polynomials is under review at Lean Pool ([LeanPool/lean-pool#1038](https://github.com/LeanPool/lean-pool/pull/1038)).

**What it does not claim.** The shorter formal proof does not use Giambelli's identity, and the roadmap claims no shortening of it; Layer 3 is a dictionary for reading the grids. A research question about amplitudes on the grid and a first Plücker test (`m = 2`) is kept in a final section marked as a roadmap for a roadmap, not to be implemented.
<!-- /roadmap-summary -->

A new roadmap directory `TauCetiRoadmap/GiambelliAndThetaLiftGrids/` (`README.md`, `Suggested.lean`, `metadata.toml` with topic `math.CO`); no other file changes. `Suggested.lean` states the Durfee rank, the Frobenius coordinates and the properties of 1.1, and elaborates at the pinned Mathlib with only `sorry` warnings.

<!-- depends-on -->
**Depends on** (suppliers still open; they merge first): none.
<!-- /depends-on -->

AI-prepared with Claude Opus 5.5 (Anthropic): it wrote the roadmap following my research direction, checked the cited declarations against the pinned Mathlib and Tau Ceti and against the shorter formal proof at `72fead1`, and checked that `Suggested.lean` elaborates. The site was found by AI. I selected the scope and read the roadmap. <!-- user: adjust to the work actually done -->
