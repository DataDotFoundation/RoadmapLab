import New.Determinant.AuxiliaryForms.GridPaths

/-!
# The squares enclosed by a two-grid path form a Young diagram

Against the upstream definitions `New.GridPath`, `New.TwoGridPath`, `New.TwoGridPath.squares`
and `New.TwoGridPath.Turn` (riemann-hypothesis @ 7c4ccbd). The orientation is the standard one:
`Γ.squares` is a lower set of `ℕ × ℕ` under the componentwise order, no reflection needed.
-/

namespace New

open Finset

namespace GridPath

variable {a₀ b₀ a b : ℕ}

/-- The squares of one half are closed downwards, within the rows the path passes. -/
theorem squares_down_closed (p : GridPath a₀ b₀ a b) {i j i' j' : ℕ}
    (h : (i, j) ∈ p.squares) (hi : i' ≤ i) (hb : b ≤ j') (hj : j' ≤ j) :
    (i', j') ∈ p.squares := by
  induction p generalizing i j j' with
  | nil => simp [squares] at h
  | @down a b p ih =>
    simp only [squares, mem_union, mem_product, mem_range, mem_singleton] at h ⊢
    rcases h with h | ⟨h1, h2⟩
    · obtain ⟨hia, hbj, -⟩ := bounds_of_mem_squares h
      by_cases hj' : b + 1 ≤ j'
      · exact .inl (ih h hi hj' hj)
      · right; constructor <;> omega
    · right; constructor <;> omega
  | right p ih => exact ih h hi hb hj

/-- A path is determined by its squares (for fixed endpoints). -/
theorem eq_of_squares_eq (p q : GridPath a₀ b₀ a b) (h : p.squares = q.squares) : p = q := by
  induction p with
  | nil =>
    cases q with
    | nil => rfl
    | down q => have := q.le_and_le; omega
    | right q => have := q.le_and_le; omega
  | @down a b p ih =>
    cases q with
    | nil => have := p.le_and_le; omega
    | down q =>
      congr 1
      apply ih
      ext ⟨i, j⟩
      have hp := fun h' => (bounds_of_mem_squares (p := p) (s := (i, j)) h')
      have hq := fun h' => (bounds_of_mem_squares (p := q) (s := (i, j)) h')
      have := congrArg (fun S => (i, j) ∈ S) h
      simp only [squares, mem_union, mem_product, mem_range, mem_singleton, eq_iff_iff] at this
      constructor
      · intro hm
        have := (this.mp (.inl hm))
        rcases this with h' | ⟨-, h'⟩
        · exact h'
        · have := (hp hm).2.1; omega
      · intro hm
        have := (this.mpr (.inl hm))
        rcases this with h' | ⟨-, h'⟩
        · exact h'
        · have := (hq hm).2.1; omega
    | @right a' _ q =>
      have hm : (a', b) ∈ (GridPath.down p).squares := by simp [squares]
      rw [h] at hm
      have := (bounds_of_mem_squares (p := q) hm).1
      omega
  | @right a b p ih =>
    cases q with
    | nil => have := p.le_and_le; omega
    | down q =>
      have hm : (a, b) ∈ (GridPath.down q).squares := by simp [squares]
      rw [← h] at hm
      have := (bounds_of_mem_squares (p := p) hm).1
      omega
    | right q => exact congrArg GridPath.right (ih q h)

end GridPath

namespace TwoGridPath

variable {m : ℕ}

/-- (a) The squares of a two-grid path form a lower set: explicit form. -/
theorem squares_down_closed (Γ : TwoGridPath m) {i j i' j' : ℕ} (h : (i, j) ∈ Γ.squares)
    (hi : i' ≤ i) (hj : j' ≤ j) : (i', j') ∈ Γ.squares := by
  rw [mem_squares] at h ⊢
  rcases h with ⟨h1, h2⟩ | h | h
  · exact .inl ⟨by simp; omega, by simp; omega⟩
  · obtain ⟨hia, hlj, -⟩ := GridPath.bounds_of_mem_squares h
    by_cases hj' : Γ.diagonalIndex ≤ j'
    · exact .inr (.inl (GridPath.squares_down_closed _ h hi hj' hj))
    · exact .inl ⟨by simp; omega, by simp; omega⟩
  · simp only [Prod.swap_prod_mk] at h ⊢
    obtain ⟨hja, hli, -⟩ := GridPath.bounds_of_mem_squares h
    by_cases hi' : Γ.diagonalIndex ≤ i'
    · exact .inr (.inr (GridPath.squares_down_closed _ h hj hi' hi))
    · exact .inl ⟨by omega, by omega⟩

/-- (a) The squares of a two-grid path form a lower set of `ℕ × ℕ` (componentwise order). -/
theorem isLowerSet_squares (Γ : TwoGridPath m) : IsLowerSet (Γ.squares : Set (ℕ × ℕ)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ ⟨hi, hj⟩ h
  exact Γ.squares_down_closed h hi hj

/-- (b) The diagonal squares are exactly the `(i, i)` with `i < Γ.diagonalIndex`. -/
theorem diag_mem_squares_iff (Γ : TwoGridPath m) (i : ℕ) :
    (i, i) ∈ Γ.squares ↔ i < Γ.diagonalIndex := by
  rw [mem_squares]
  constructor
  · rintro (⟨h, -⟩ | h | h)
    · exact h
    · exact (GridPath.bounds_of_mem_squares h).1
    · exact (GridPath.bounds_of_mem_squares h).1
  · intro h; exact .inl ⟨h, h⟩

/-- (b) Durfee rank: `Γ.diagonalIndex` is the number of diagonal squares of `Γ.squares`. -/
theorem diagonalIndex_eq_card (Γ : TwoGridPath m) :
    Γ.diagonalIndex = #((range m).filter fun i => (i, i) ∈ Γ.squares) := by
  have : (range m).filter (fun i => (i, i) ∈ Γ.squares) = range Γ.diagonalIndex := by
    ext i
    simp only [mem_filter, mem_range, diag_mem_squares_iff]
    have := Γ.diagonalIndex_le
    omega
  rw [this, card_range]

example : (first m).diagonalIndex = 0 := rfl
example : (last m).diagonalIndex = m := rfl

/-- (c) A turn at `s` is at an addable corner of `Γ.squares`: `s` is not a square of `Γ`,
every `t ≤ s` other than `s` is, and inserting `s` keeps a lower set. -/
theorem Turn.addable {Γ Γ' : TwoGridPath m} {s : ℕ × ℕ} (h_turn : Γ.Turn s Γ') :
    s ∉ Γ.squares ∧ (∀ t, t ≤ s → t ≠ s → t ∈ Γ.squares) ∧
      IsLowerSet ((insert s Γ.squares : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  obtain ⟨hs, h_eq⟩ := h_turn.squares_eq
  have hlow : IsLowerSet ((insert s Γ.squares : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) :=
    h_eq ▸ Γ'.isLowerSet_squares
  refine ⟨hs, fun t hts hne => ?_, hlow⟩
  have : t ∈ ((insert s Γ.squares : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) :=
    hlow hts (by simp)
  simpa [hne] using this

lemma mem_half_false_iff (Γ : TwoGridPath m) (s : ℕ × ℕ) :
    s ∈ (Γ.half false).squares ↔ s ∈ Γ.squares ∧ Γ.diagonalIndex ≤ s.2 := by
  rw [mem_squares]
  constructor
  · intro h; exact ⟨.inr (.inl h), (GridPath.bounds_of_mem_squares h).2.1⟩
  · rintro ⟨⟨-, h⟩ | h | h, hl⟩
    · omega
    · exact h
    · have := (GridPath.bounds_of_mem_squares h).1; simp at this; omega

lemma mem_half_true_iff (Γ : TwoGridPath m) (s : ℕ × ℕ) :
    s ∈ (Γ.half true).squares ↔ s.swap ∈ Γ.squares ∧ Γ.diagonalIndex ≤ s.2 := by
  rw [mem_squares]
  constructor
  · intro h; exact ⟨.inr (.inr (by simpa using h)), (GridPath.bounds_of_mem_squares h).2.1⟩
  · rintro ⟨⟨h, -⟩ | h | h, hl⟩
    · simp at h; omega
    · have := (GridPath.bounds_of_mem_squares h).1; simp at this; omega
    · simpa using h

/-- (d) A two-grid path is determined by its squares. -/
theorem squares_injective : Function.Injective (squares : TwoGridPath m → Finset (ℕ × ℕ)) := by
  intro Γ Γ' h
  have hl : Γ.diagonalIndex = Γ'.diagonalIndex := by
    rw [diagonalIndex_eq_card, diagonalIndex_eq_card, h]
  obtain ⟨l, f⟩ := Γ
  obtain ⟨l', f'⟩ := Γ'
  obtain rfl : l = l' := hl
  congr 1
  funext z
  apply GridPath.eq_of_squares_eq
  ext s
  cases z
  · have h1 := mem_half_false_iff ⟨l, f⟩ s
    have h2 := mem_half_false_iff ⟨l, f'⟩ s
    simp only at h1 h2
    rw [h1, h2, h]
  · have h1 := mem_half_true_iff ⟨l, f⟩ s
    have h2 := mem_half_true_iff ⟨l, f'⟩ s
    simp only at h1 h2
    rw [h1, h2, h]

end TwoGridPath

end New

#print axioms New.TwoGridPath.squares_down_closed
#print axioms New.TwoGridPath.isLowerSet_squares
#print axioms New.TwoGridPath.diag_mem_squares_iff
#print axioms New.TwoGridPath.diagonalIndex_eq_card
#print axioms New.TwoGridPath.Turn.addable
#print axioms New.TwoGridPath.squares_injective
