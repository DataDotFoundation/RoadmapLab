import Mathlib

/-!
# Giambelli's identity, Frobenius coordinates and the grids of the chain of lifts: target signatures

This file is not the roadmap. The definitive document for this folder is `README.md`; the forms
below are suggestions, not an exhaustive checklist.

It states the Durfee rank and the Frobenius coordinates of a Young diagram (README 1.1) on
Mathlib's `YoungDiagram`, with the headline properties of 1.1 as `sorry`'d targets. Giambelli's
identity (2.2) is stated against Tau Ceti's `diagramSchurPoly` and `schurPoly`; a formalization of it,
with the hook formula (2.1), is merged in Lean Pool (LeanPool/lean-pool#1038, `fb336fb`), so its
signatures are not repeated here. Layer 3 is stated on the paths of TauCetiRoadmap's DeterminantsOfThetaLiftChains
§5.1, which have no signature at the pins, so nothing of it is stated here.
-/

namespace Roadmaps.GiambelliAndThetaLiftGrids

open Finset

/-- The Durfee rank `d(μ)` (1.1): the number of `i` with `(i, i) ∈ μ`, the side of the largest
square in `μ`. -/
def durfeeRank (μ : YoungDiagram) : ℕ :=
  ((range (μ.rowLen 0 + 1)).filter fun i ↦ (i, i) ∈ μ).card

/-- The arm coordinate `a_i = λ_i − i − 1` (1.1), meaningful for `i < durfeeRank μ`. -/
def frobeniusArm (μ : YoungDiagram) (i : ℕ) : ℕ := μ.rowLen i - (i + 1)

/-- The leg coordinate `b_i = λ′_i − i − 1` (1.1), meaningful for `i < durfeeRank μ`. -/
def frobeniusLeg (μ : YoungDiagram) (i : ℕ) : ℕ := μ.colLen i - (i + 1)

/-- 1.1 (b): `|λ| = Σ_{i<d} (a_i + b_i + 1)`. -/
theorem card_cells_eq_sum_frobenius (μ : YoungDiagram) :
    μ.cells.card = ∑ i ∈ range (durfeeRank μ), (frobeniusArm μ i + frobeniusLeg μ i + 1) := by
  sorry

/-- 1.1 (c): the conjugate has the same Durfee rank and exchanged coordinates. -/
theorem durfeeRank_transpose (μ : YoungDiagram) : durfeeRank μ.transpose = durfeeRank μ := by
  sorry

theorem frobeniusArm_transpose (μ : YoungDiagram) (i : ℕ) :
    frobeniusArm μ.transpose i = frobeniusLeg μ i := by
  sorry

/-- 1.1 (d), injectivity: a Young diagram is determined by its Durfee rank and its Frobenius
coordinates. -/
theorem eq_of_frobenius_eq {μ ν : YoungDiagram} (hd : durfeeRank μ = durfeeRank ν)
    (ha : ∀ i < durfeeRank μ, frobeniusArm μ i = frobeniusArm ν i)
    (hb : ∀ i < durfeeRank μ, frobeniusLeg μ i = frobeniusLeg ν i) : μ = ν := by
  sorry

end Roadmaps.GiambelliAndThetaLiftGrids
