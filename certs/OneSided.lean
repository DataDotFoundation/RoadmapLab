import New.Reduction.OneSidedBound

/-!
# Pilot step 2: certified revision of ShortGRH `OneSidedPrimeSumBoundsAndAdmissibleData`

The definitions and the three `sorry`'d targets of TauCetiRoadmap
`ShortGRH/OneSidedPrimeSumBoundsAndAdmissibleData/Suggested.lean` (roadmap commit `87991688`, Lean
v4.36.0-rc2, Mathlib `1b1ccf4`) are ported here, textually, into the environment of the proof at
upstream `61d870d` (Lean v4.37.0-rc1, Mathlib `31ce06e`, TauCeti `6d810e5`). The text of every block
between `BEGIN`/`END` markers is checked against the roadmap by `check_text.py` (RoadmapLab), the
only adaptation being `theorem NAME binders : concl := by sorry` ↦ `def Target_k : Prop := ∀ binders,
concl`.

* `primeRemainder_eq`: the roadmap's `R_q` is the route's `New.primeRemainder`.
* **Cert 2, §0.2 (↔).** `target_02_iff`: the roadmap's one-sided criterion is equivalent to the route's
  `New.LFunction_ne_zero_of_primeRemainder_le`, whose bound carries a constant `A` since upstream
  PR #5627 (`f2201365d2d`).
* **Cert 2, §6.2 (c) (↔).** `target_62_iff`: the roadmap's one-sided bound is equivalent to the
  route's `New.eventually_primeRemainder_le_mul_rpow` (constant `128 φ(q₀) + 32`, same PR).
* **Cert 2, §6.3 (←).** `target_63_of_criterion`: the conditional passage to the half-plane follows
  from the route's criterion, by the argument the route inlines in `New.grh`; it has no standalone
  counterpart at `61d870d`.

Owner: RoadmapLab. Nothing here is posted anywhere.
-/

namespace TauCetiRoadmap.ShortGRH.OneSidedPrimeSumBoundsAndAdmissibleData

open ArithmeticFunction Filter

-- BEGIN DEFS
section Remainder

variable (d : ℕ) [Fact d.Prime] (q : ℕ)

/-- The weight `λ_q` of 0.1: `λ_q(n) = Λ(n)·(1 − χ_K(n))` if `n ≡ 1 (mod q)` and `0` otherwise,
with `χ_K = (·/d)` the Legendre symbol of the prime `d`. -/
noncomputable def primeWeight (n : ℕ) : ℝ :=
  if (n : ZMod q) = 1 then Λ n * (1 - (legendreSym d n : ℝ)) else 0

/-- The function `E_ψ` of 0.1 for a Dirichlet character `ψ`: its L-function if `ψ` is not
principal, and the entire continuation of `(s − 1)·L(s, ψ)` if it is. -/
noncomputable def entireLFunction {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  open Classical in if ψ = 1 then DirichletCharacter.LFunctionTrivChar₁ N else ψ.LFunction

/-- The product `ψ·χ_K` of 0.1, a Dirichlet character modulo `q·d`. -/
noncomputable def quadraticTwist {q : ℕ} (ψ : DirichletCharacter ℂ q) :
    DirichletCharacter ℂ (q * d) :=
  DirichletCharacter.changeLevel (Dvd.intro d rfl) ψ *
    DirichletCharacter.changeLevel (Dvd.intro_left q rfl)
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))

variable [NeZero q]

/-- The function `G_q` of 0.1:
`G_q(s) = φ(q)⁻¹·(Σ_ψ (E′_{ψχ_K}/E_{ψχ_K}(s) − E′_ψ/E_ψ(s)) − 1)`, the sum over all Dirichlet
characters `ψ` modulo `q`. -/
noncomputable def logDerivMean (s : ℂ) : ℂ :=
  haveI : NeZero (q * d) := ⟨Nat.mul_ne_zero (NeZero.ne q) (Fact.out : d.Prime).ne_zero⟩
  (∑ ψ : DirichletCharacter ℂ q,
    (logDeriv (entireLFunction (quadraticTwist d ψ)) s - logDeriv (entireLFunction ψ) s) - 1) /
      (Nat.totient q : ℂ)

/-- The remainder `R_q` of 0.1:
`R_q(y) = Σ_{1 ≤ n ≤ y} λ_q(n)·(1/n − 1/y) − (log y)/φ(q) − c_q` with `c_q = Re G_q(1)`. -/
noncomputable def primeRemainder (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, primeWeight d q n * (1 / (n : ℝ) - 1 / y) -
    Real.log y / (Nat.totient q : ℝ) - (logDerivMean d q 1).re

end Remainder
-- END DEFS

set_option linter.unusedVariables false

-- BEGIN TARGET 02 LFunction_ne_zero_of_primeRemainder_le
/-- Roadmap 0.2, `LFunction_ne_zero_of_primeRemainder_le`. -/
def Target_02 : Prop :=
  ∀ {q₀ : ℕ} [NeZero q₀] (hq₀ : 8 ∣ q₀) {d₀ : ℕ}
    (hd₀ : d₀ % 8 = 7) (hd₀q₀ : d₀.Coprime q₀) {β : ℝ} (hβ : 1 / 2 < β)
    (h : ∀ (d : ℕ) [Fact d.Prime], d ≡ d₀ [MOD q₀] →
      ∀ᶠ x : ℝ in atTop, primeRemainder d q₀ x ≤ x ^ (β - 1))
    (ψ : DirichletCharacter ℂ q₀) {ρ : ℂ} (hρ : ρ ≠ 1) (hβρ : β < ρ.re),
    ψ.LFunction ρ ≠ 0
-- END TARGET 02

-- BEGIN TARGET 62 eventually_primeRemainder_le_rpow
/-- Roadmap 6.2 (c), `eventually_primeRemainder_le_rpow`. -/
def Target_62 : Prop :=
  ∀ {q₀ : ℕ} [NeZero q₀] (hq₀ : 18480 ∣ q₀) {d : ℕ}
    [Fact d.Prime] (hd : d ≡ q₀ / 2 - 1 [MOD q₀]) {ε : ℝ} (hε : 0 < ε),
    ∀ᶠ y : ℝ in atTop, primeRemainder d q₀ y ≤ y ^ (-1 / 2 + ε)
-- END TARGET 62

-- BEGIN TARGET 63 LFunction_ne_zero_of_forall_primeRemainder_le
/-- Roadmap 6.3 (conditional), `LFunction_ne_zero_of_forall_primeRemainder_le`. -/
def Target_63 : Prop :=
  ∀ {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 / 2 < s.re) (hs₁ : s ≠ 1)
    (h : ∀ (d : ℕ) [Fact d.Prime], d ≡ 9240 * N - 1 [MOD 18480 * N] → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ y : ℝ in atTop, primeRemainder d (18480 * N) y ≤ y ^ (-1 / 2 + ε)),
    χ.LFunction s ≠ 0
-- END TARGET 63

set_option linter.unusedVariables true

/-! ## The roadmap's remainder is the route's -/

section Bridge

variable (d : ℕ) [Fact d.Prime] (q : ℕ)

theorem primeWeight_eq (n : ℕ) : primeWeight d q n = New.lambdaKResidueClass d q n := by
  unfold primeWeight New.lambdaKResidueClass
  rw [New.chiK_eq_legendreSym]
  by_cases h : (n : ZMod q) = 1
  · simp [h, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator]
  · simp [h, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator]

theorem entireLFunction_eq {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) :
    entireLFunction ψ = New.entireL ψ := by
  unfold entireLFunction New.entireL
  by_cases h : ψ = 1 <;> simp [h]

theorem quadraticTwist_eq {q : ℕ} (ψ : DirichletCharacter ℂ q) :
    quadraticTwist d ψ = New.quadTwist ψ d := by
  unfold quadraticTwist New.quadTwist New.chiK
  congr 2

variable [NeZero q]

theorem logDerivMean_eq (s : ℂ) : logDerivMean d q s = New.logDerivMean d q s := by
  unfold logDerivMean New.logDerivMean
  simp only [entireLFunction_eq, quadraticTwist_eq]

theorem primeRemainder_eq (y : ℝ) : primeRemainder d q y = New.primeRemainder d q y := by
  unfold primeRemainder New.primeRemainder New.lambdaKSum
  rw [logDerivMean_eq]
  have h_sum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, primeWeight d q n * (1 / (n : ℝ) - 1 / y) =
      (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, New.lambdaKResidueClass d q n / n * (n : ℝ) ^ 0) / y ^ 0 -
        (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, New.lambdaKResidueClass d q n / n * (n : ℝ) ^ 1) / y ^ 1 := by
    rw [pow_zero, div_one, pow_one, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn0 : (n : ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : n ≠ 0)
    rw [primeWeight_eq]
    field_simp
  rw [h_sum]

end Bridge

/-! ## Cert 2, §0.2: the one-sided criterion (↔) -/

/-- A constant can be traded for a slightly larger exponent: if `R ≤ A x^{β-1}` eventually and
`β < β'`, then `R ≤ x^{β'-1}` eventually. -/
theorem eventually_le_rpow_of_le_mul_rpow {R : ℝ → ℝ} {A β β' : ℝ} (hββ' : β < β')
    (h : ∀ᶠ x : ℝ in atTop, R x ≤ A * x ^ (β - 1)) :
    ∀ᶠ x : ℝ in atTop, R x ≤ x ^ (β' - 1) := by
  have h_grow : Tendsto (fun x : ℝ ↦ x ^ (β' - β)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  filter_upwards [h, h_grow.eventually_ge_atTop A, eventually_gt_atTop 0] with x hx hA hx0
  calc R x ≤ A * x ^ (β - 1) := hx
    _ ≤ x ^ (β' - β) * x ^ (β - 1) := by gcongr
    _ = x ^ (β' - 1) := by rw [← Real.rpow_add hx0]; ring_nf

theorem target_02_iff : Target_02 ↔ type_of% @New.LFunction_ne_zero_of_primeRemainder_le := by
  constructor
  · -- The roadmap's criterion implies the route's: absorb `A` into an exponent between `β` and `re ρ`.
    intro h q₀ _ hq₀ d₀ hd₀ hd₀q₀ β hβ h_bound ψ ρ hρ hβρ
    obtain ⟨β', hββ', hβ'ρ⟩ := exists_between hβρ
    refine h hq₀ hd₀ hd₀q₀ (hβ.trans hββ') (fun d _ hd ↦ ?_) ψ hρ hβ'ρ
    obtain ⟨A, hA⟩ := h_bound ⟨d, Fact.out⟩ hd
    refine eventually_le_rpow_of_le_mul_rpow (A := A) hββ' ?_
    simpa only [primeRemainder_eq] using hA
  · -- The route's criterion implies the roadmap's: take `A = 1`.
    intro h q₀ _ hq₀ d₀ hd₀ hd₀q₀ β hβ h_bound ψ ρ hρ hβρ
    refine h hq₀ hd₀ hd₀q₀ hβ (fun d hd ↦ ⟨1, ?_⟩) ψ hρ hβρ
    simpa only [one_mul, primeRemainder_eq] using h_bound d hd

/-! ## Cert 2, §6.2 (c): the one-sided bound (↔) -/

theorem target_62_iff : Target_62 ↔ type_of% @New.eventually_primeRemainder_le_mul_rpow := by
  constructor
  · -- The roadmap's bound implies the route's, since `128 φ(q₀) + 32 ≥ 1`.
    intro h q₀ _ hq₀ d _ hd ε hε
    have hC : (1 : ℝ) ≤ 128 * q₀.totient + 32 := by
      have : (0 : ℝ) ≤ q₀.totient := Nat.cast_nonneg _
      linarith
    filter_upwards [h hq₀ hd hε, eventually_gt_atTop 0] with y hy hy0
    rw [← primeRemainder_eq]
    calc primeRemainder d q₀ y ≤ y ^ (-1 / 2 + ε) := hy
      _ = 1 * y ^ (-1 / 2 + ε) := (one_mul _).symm
      _ ≤ (128 * q₀.totient + 32) * y ^ (-1 / 2 + ε) := by gcongr
  · -- The route's bound implies the roadmap's: apply it with `ε / 2` and absorb the constant.
    intro h q₀ _ hq₀ d _ hd ε hε
    have h' := h hq₀ hd (half_pos hε)
    have key := eventually_le_rpow_of_le_mul_rpow (R := fun y ↦ primeRemainder d q₀ y)
      (A := 128 * q₀.totient + 32) (β := 1 / 2 + ε / 2) (β' := 1 / 2 + ε)
      (by linarith) (by
        filter_upwards [h'] with y hy
        rw [primeRemainder_eq]
        convert hy using 3
        ring)
    filter_upwards [key] with y hy
    convert hy using 2
    ring

/-! ## Cert 2, §6.3: the conditional passage to the half-plane (←, from the route's criterion) -/

/-- The roadmap's 6.3 follows from the route's criterion, with the argument that `New.grh` inlines:
pass to the character modulo `18480 N` induced by `χ`, with `d₀ = 9240 N − 1`. -/
theorem target_63_of_criterion (hcrit : type_of% @New.LFunction_ne_zero_of_primeRemainder_le) :
    Target_63 := by
  intro N _ χ s hs hs₁ h
  obtain ⟨β, hβ, hβs⟩ : ∃ β : ℝ, 1 / 2 < β ∧ β < s.re := exists_between hs
  have hN : 0 < N := NeZero.pos N
  have hd₀_cop : (9240 * N - 1).Coprime (18480 * N) := by
    have h_two : (9240 * N - 1).Coprime 2 := (Nat.odd_iff.2 (by omega)).coprime_two_right
    have h_eq : 18480 * N = 2 * ((9240 * N - 1) + 1) := by omega
    rw [h_eq]
    exact h_two.mul_right (Nat.coprime_comm.1 (Nat.coprime_self_add_left.2 (Nat.coprime_one_left _)))
  have h_bound (d : Nat.Primes) (hd : (d : ℕ) ≡ 9240 * N - 1 [MOD 18480 * N]) :
      ∃ A : ℝ, ∀ᶠ x : ℝ in atTop, New.primeRemainder d (18480 * N) x ≤ A * x ^ (β - 1) := by
    refine ⟨1, ?_⟩
    filter_upwards [h d hd (β - 1 / 2) (by linarith)] with x hx
    rw [← primeRemainder_eq, one_mul]
    convert hx using 2
    ring
  have h_ind : (χ.changeLevel (dvd_mul_left N 18480)).LFunction s ≠ 0 :=
    hcrit (by omega) (by omega) hd₀_cop hβ h_bound _ hs₁ hβs
  rw [DirichletCharacter.LFunction_changeLevel _ χ (Or.inr hs₁)] at h_ind
  exact left_ne_zero_of_mul h_ind

/-- Recorded for the note: Target 6.3 is also a consequence of the route's unconditional theorem,
which makes that proof uninformative as a correspondence. -/
theorem target_63 : Target_63 :=
  target_63_of_criterion New.LFunction_ne_zero_of_primeRemainder_le

end TauCetiRoadmap.ShortGRH.OneSidedPrimeSumBoundsAndAdmissibleData
