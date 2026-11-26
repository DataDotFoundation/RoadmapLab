import New.Determinant.Exchange.TheoremForPartners

/-!
# ShortGRH `DeterminantsOfThetaLiftChains` §§3.4, 3.8: the 72fead1 statements hold at 61d870d

The roadmap cites, in §3.4 and §3.8, five lemmas of `New/Determinant/Exchange/TheoremForPartners.lean`
as they stood at grh-lean `72fead1`. Upstream PR #7266 (`0ea5c74`, "prove the value of the equal-rank
theta ratio directly on H ⊕ X") generalised four of them from the space `W` (or `stdSpace E m`, `J`) to
any `X` with an adapted splitting of `H ⊕ X`, and respelled the fifth.

Each theorem below has as its statement the **72fead1 text, verbatim** (checked by `check_text72.py`
between the `BEGIN`/`END` markers, against `72fead1:grh/src/New/Determinant/Exchange/
TheoremForPartners.lean`), in the same `variable` context, with one adaptation to the Mathlib pin
(a predicate used as a `Set`: `schwartzBruhat HasLeftInv` ↦ `schwartzBruhat {y | HasLeftInv y}`, as
upstream itself rewrote it), and is proved at `61d870d` from the route's
declaration by specialising `X := W`, `p := Unit`, `A := removePlanes Unit W`. So the old forms the
roadmap cites are corollaries of the route's (kind ←).

Owner: RoadmapLab. Nothing here is posted anywhere.
-/

noncomputable section

namespace RoadmapLab.Exchange72

open New New.Exchange

section ExchangeCore

open Matrix MeasureTheory NumberField Fintype Fock CoordChange Weil Seesaw

variable {E : Type} [Field E] [CMType E] [WeilData E] {n r b : Type} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r] [Fintype b] [DecidableEq b] {s : n → ℤˣ} {t : r → ℤˣ} {u : b → ℤˣ}

-- BEGIN OLD thetaLarge_eq_smul_of_areMatched
lemma thetaLarge_eq_smul_of_areMatched (W : Space E n s) (V : Space E r t) (U : Space E b u)
    (σ : b ⊕ r ≃ n) (h_even : 2 ∣ card n) {μ : InfinitePlace E → ℤ} {𝔠 : SplitTameChar E μ}
    {v : PairFock E s t} {y : PairFock E s u} (hv : IsSchwartzVector v) (hy : IsSchwartzVector y)
    {c : ℂ}
    (h_std : ∀ z : Matrix b n (LocProd 𝔠.ramifiedPlaces), IsIntMatrix SemilocalField.O z →
      thetaLarge W V 𝔠 v (stdRowDatum σ 𝔠.semilocalChar z) = c • thetaSmall W U 𝔠 y
        (stdColDatum 𝔠.semilocalChar z))
    {Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ} {Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ}
    (hΨ : IsLocallyConstant Ψ) (hΦΨ : AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ) :
    Ψ ∈ schwartzBruhat {y | HasLeftInv y} ∧ thetaLarge W V 𝔠 v Φ = c • thetaSmall W U 𝔠 y Ψ := by
-- END OLD
  exact New.Exchange.thetaLarge_eq_smul_of_areMatched W V U σ h_even hv hy h_std hΨ hΦΨ

-- BEGIN OLD exists_rowColExchangeIdentity_of_even_rank
lemma exists_rowColExchangeIdentity_of_even_rank (W : Space E n s) (U : Space E b u)
    (μ : InfinitePlace E → ℤ) (V : Space E r t) (σ : b ⊕ r ≃ n)
    {z : PairFock E (hyperbolicSigns Unit ⊕ᵥ s) (hyperbolicSigns Unit ⊕ᵥ s)} {y : PairFock E s u}
    (hz : IsSchwartzVector z) (hy : IsSchwartzVector y)
    (h_signs : negCount u + negCount s = card b + negCount t) (h_even : 2 ∣ card n) :
    ∃ v : PairFock E s t, RowColExchangeIdentity W V U μ σ v y
      fun 𝔠 : SplitTameChar E μ ↦ equalRankThetaRatio (hyperbolicSum Unit W) 𝔠 z := by
-- END OLD
  exact New.Exchange.exists_rowColExchangeIdentity_of_even_rank W U μ V σ W (removePlanes Unit W)
    hz hy h_signs h_even (by simp)

-- BEGIN OLD exchange_of_matches
lemma exchange_of_matches (W : Space E n s) (U : Space E b u) (μ : InfinitePlace E → ℤ)
    (V : Space E r t) (σ : b ⊕ r ≃ n)
    {z : PairFock E (hyperbolicSigns Unit ⊕ᵥ s) (hyperbolicSigns Unit ⊕ᵥ s)} {y : PairFock E u s}
    (hz : IsSchwartzVector z) (hy : IsSchwartzVector y)
    (h_signs : negCount s = negCount t + negCount u) (h_even : 2 ∣ card n) :
    ∃ (C : ℝ) (v : PairFock E s t), IsSchwartzVector v ∧ ∀ 𝔠 : SplitTameChar E μ,
      let γ : AutChar E := rankTwist 𝔠.character⁻¹ n
      ∃ c : ℂ,
        -- (a) the modulus of the constant
        C * ‖c‖ ^ 2 =
          lValueProdInt 𝔠 (card r - card n / 2) * equalRankThetaRatio (hyperbolicSum Unit W) 𝔠 z ∧
        -- (b) the identity of theta integrals, for all matched functions
        ∀ (Φ : Matrix r n (LocProd 𝔠.ramifiedPlaces) → ℂ)
          (Ψ : Matrix n b (LocProd 𝔠.ramifiedPlaces) → ℂ),
          IsLocallyConstant Ψ → AreMatched SemilocalField.O σ 𝔠.semilocalChar Φ Ψ → ∀ g : G E s,
          thetaIntegral W V γ 1 (localDatum W V v Φ 𝔠.readsAt) g =
            c * ∫ h : G E u, pairTheta U W γ γ (localDatum U W y Ψ 𝔠.readsAt) (h, g)
              ∂U.quotMeasure := by
-- END OLD
  exact New.Exchange.exchange_of_matches W U μ V σ W (removePlanes Unit W) hz hy h_signs h_even
    (by simp)

end ExchangeCore

section EqualRankValue

open MeasureTheory NumberField Fintype Space Equiv Fock MixedModel Heisenberg OrthogonalSum

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n] [DecidableEq n] {s : n → ℤˣ}

variable {m : Type} [Fintype m] [DecidableEq m]

-- BEGIN OLD exists_equalRankThetaRatio_ne_zero
lemma exists_equalRankThetaRatio_ne_zero (μ : InfinitePlace E → ℤ) {k : ℕ}
    (hm : card m = 2 * k) (hμ : ∀ w : InfinitePlace E, k ≤ μ w) (𝔠 : SplitTameChar E μ) :
    ∃ v : PairFock E (Sum.elim (hyperbolicSigns Unit) 1) (Sum.elim (hyperbolicSigns Unit) 1),
      IsSchwartzVector v ∧ equalRankThetaRatio (hyperbolicSum Unit (stdSpace E m)) 𝔠 v ≠ 0 := by
-- END OLD
  exact New.Exchange.exists_equalRankThetaRatio_ne_zero (m := m) μ hm hμ (stdSpace E m)
    (by simp [hm]) 𝔠

-- BEGIN OLD exists_equalRankThetaRatio_sq_eq
lemma exists_equalRankThetaRatio_sq_eq (μ : InfinitePlace E → ℤ) {k : ℕ} (hm : card m = 2 * k)
    (J : Space E m 1)
    {v : PairFock E (Sum.elim (hyperbolicSigns Unit) (1 : m → ℤˣ))
      (Sum.elim (hyperbolicSigns Unit) (1 : m → ℤˣ))}
    (hv : IsSchwartzVector v) :
    ∃ D : ℝ, ∀ 𝔠 : SplitTameChar E μ, equalRankThetaRatio (hyperbolicSum Unit J) 𝔠 v ^ 2 = D := by
-- END OLD
  exact New.Exchange.exists_equalRankThetaRatio_sq_eq μ hm J J (removePlanes Unit J) (by simp) hv

end EqualRankValue

end RoadmapLab.Exchange72
