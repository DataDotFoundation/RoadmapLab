import New.Determinant.AuxiliaryForms.GridPaths

/-!
# Turns of a two-grid path are exactly the addable corners of its squares

Against the upstream definitions `New.GridPath`, `New.TwoGridPath`, `New.TwoGridPath.squares`
and `New.TwoGridPath.Turn` (riemann-hypothesis @ 7c4ccbd).

`Turn.addable` (copied from `GridDiagram.lean`) says a turn sits at an addable corner of
`Γ.squares`. New here is the converse, `TwoGridPath.exists_turn_of_addable`, and the iff
`TwoGridPath.exists_turn_iff_addable`. The core is the one-grid lemma
`GridPath.exists_corner_of_addable`: a path whose squares have an addable corner at `(i, j)`
factors as `q.down.right.append r` with `q` ending at `(i, j + 1)`.
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

/-- A path to `(a, b)` below the start row, whose square `(a - 1, b)` is present (when `a > 0`),
ends with a step down. -/
theorem exists_eq_down_of_mem (p : GridPath a₀ b₀ a b) (hb : b < b₀)
    (hprev : ∀ i, i + 1 = a → (i, b) ∈ p.squares) :
    ∃ q : GridPath a₀ b₀ a (b + 1), p = q.down := by
  cases p with
  | nil => omega
  | down q => exact ⟨q, rfl⟩
  | @right a' _ p' =>
    have h := hprev a' rfl
    simp only [squares] at h
    exact absurd (bounds_of_mem_squares h).1 (lt_irrefl _)

/-- One grid: if `(i, j)` is an addable corner of the squares of `p` (inside the box of `p`),
then `p` comes down to `(i, j)` and leaves it to the right. -/
theorem exists_corner_of_addable (p : GridPath a₀ b₀ a b) {i j : ℕ} (hi : i < a) (hbj : b ≤ j)
    (hj : j < b₀) (hs : (i, j) ∉ p.squares) (hleft : ∀ i', i' < i → (i', j) ∈ p.squares)
    (hbelow : b < j → (i, j - 1) ∈ p.squares) :
    ∃ (q : GridPath a₀ b₀ i (j + 1)) (r : GridPath (i + 1) j a b),
      p = q.down.right.append r := by
  induction p with
  | nil => omega
  | @down a b p ih =>
    have hjb : b ≠ j := by
      rintro rfl; exact hs (by simp [squares, hi])
    simp only [squares, mem_union, mem_product, mem_range, mem_singleton] at hs hleft hbelow
    obtain ⟨q, r, rfl⟩ := ih hi (by omega) (fun h => hs (.inl h))
      (fun i' hi' => (hleft i' hi').resolve_right (by rintro ⟨-, h⟩; omega))
      (fun h => (hbelow (by omega)).resolve_right (by rintro ⟨-, h'⟩; omega))
    exact ⟨q, r.down, rfl⟩
  | @right a b p ih =>
    simp only [squares] at hs hleft hbelow
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · obtain ⟨q, r, rfl⟩ := ih hi hbj hs hleft hbelow
      exact ⟨q, r.right, rfl⟩
    · obtain rfl : j = b := by
        by_contra hne
        have := (bounds_of_mem_squares (hbelow (by omega))).1
        omega
      obtain ⟨q, rfl⟩ := exists_eq_down_of_mem p hj (fun i' hi' => hleft i' (by omega))
      exact ⟨q, nil, rfl⟩

end GridPath

namespace TwoGridPath

variable {m : ℕ}

/-! Copied from `GridDiagram.lean`. -/

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

/-- The converse of `Turn.addable`, predecessor form: if `s` lies in the box, is not a square of
`Γ`, and every `t ≤ s` other than `s` is, then `Γ` has a turn at `s`. -/
theorem exists_turn_of_forall_lt (Γ : TwoGridPath m) {s : ℕ × ℕ}
    (hs_box : s ∈ range m ×ˢ range m) (hs : s ∉ Γ.squares)
    (hlt : ∀ t, t ≤ s → t ≠ s → t ∈ Γ.squares) : ∃ Γ', Γ.Turn s Γ' := by
  obtain ⟨x, y⟩ := s
  simp only [mem_product, mem_range] at hs_box
  have hl := diag_mem_squares_iff Γ
  -- the diagonal node `(l, l)` is a square below any corner `(x, y)` with `l ≤ x, y`, `x ≠ y`
  have hdiag : ¬ (Γ.diagonalIndex ≤ x ∧ Γ.diagonalIndex ≤ y ∧ x ≠ y) := by
    rintro ⟨h1, h2, h3⟩
    have := hlt (Γ.diagonalIndex, Γ.diagonalIndex) ⟨h1, h2⟩ (by simp [Prod.ext_iff]; omega)
    exact absurd ((hl _).mp this) (lt_irrefl _)
  have hblock : ¬ (x < Γ.diagonalIndex ∧ y < Γ.diagonalIndex) := fun h =>
    hs (mem_squares.mpr (.inl h))
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · -- `x < y`: a corner of `half false` at `(x, y)`
    have hly : Γ.diagonalIndex ≤ y := by omega
    have hxl : x < Γ.diagonalIndex := by omega
    obtain ⟨q, r, h⟩ := GridPath.exists_corner_of_addable (Γ.half false) hxl hly hs_box.2
      (fun h => hs ((mem_half_false_iff Γ _).mp h).1)
      (fun i' hi' => (mem_half_false_iff Γ _).mpr
        ⟨hlt (i', y) ⟨hi'.le, le_rfl⟩ (by simp [Prod.ext_iff]; omega), hly⟩)
      (fun h => (mem_half_false_iff Γ _).mpr
        ⟨hlt (x, y - 1) ⟨le_rfl, by omega⟩ (by simp [Prod.ext_iff]; omega), by simp; omega⟩)
    exact ⟨_, Turn.inner Γ false q r h⟩
  · -- `x = y`: the diagonal turn, at `(l, l)`
    have hxl : Γ.diagonalIndex ≤ x := by omega
    have hlx : x = Γ.diagonalIndex := by
      by_contra h
      have := hlt (Γ.diagonalIndex, Γ.diagonalIndex) ⟨hxl, hxl⟩ (by simp [Prod.ext_iff]; omega)
      exact absurd ((hl _).mp this) (lt_irrefl _)
    obtain ⟨l, half⟩ := Γ
    change x = l at hlx
    subst hlx
    have hd : ∀ z, ∃ q : GridPath 0 m x (x + 1), half z = q.down := by
      intro z
      refine GridPath.exists_eq_down_of_mem _ hs_box.1 fun i hi => ?_
      cases z
      · exact (mem_half_false_iff ⟨x, half⟩ (i, x)).mpr
          ⟨hlt (i, x) ⟨by omega, le_rfl⟩ (by simp [Prod.ext_iff]; omega), le_rfl⟩
      · exact (mem_half_true_iff ⟨x, half⟩ (i, x)).mpr
          ⟨hlt (x, i) ⟨le_rfl, by omega⟩ (by simp [Prod.ext_iff]; omega), le_rfl⟩
    choose q hq using hd
    obtain rfl : half = fun z => (q z).down := funext hq
    exact ⟨_, Turn.diagonal q⟩
  · -- `y < x`: a corner of `half true` at `(y, x)`
    have hlx : Γ.diagonalIndex ≤ x := by omega
    have hyl : y < Γ.diagonalIndex := by omega
    obtain ⟨q, r, h⟩ := GridPath.exists_corner_of_addable (Γ.half true) hyl hlx hs_box.1
      (fun h => hs ((mem_half_true_iff Γ _).mp h).1)
      (fun i' hi' => (mem_half_true_iff Γ _).mpr
        ⟨hlt (x, i') ⟨le_rfl, hi'.le⟩ (by simp [Prod.ext_iff]; omega), hlx⟩)
      (fun h => (mem_half_true_iff Γ _).mpr
        ⟨hlt (x - 1, y) ⟨by omega, le_rfl⟩ (by simp [Prod.ext_iff]; omega), by simp; omega⟩)
    exact ⟨_, Turn.inner Γ true q r h⟩

/-- The converse of `Turn.addable`: every addable corner `s` of `Γ.squares` in the box (that is,
`s ∉ Γ.squares` and `insert s Γ.squares` is still a lower set) is the node of a turn. -/
theorem exists_turn_of_addable (Γ : TwoGridPath m) {s : ℕ × ℕ}
    (hs_box : s ∈ range m ×ˢ range m) (hs : s ∉ Γ.squares)
    (hlow : IsLowerSet ((insert s Γ.squares : Finset (ℕ × ℕ)) : Set (ℕ × ℕ))) :
    ∃ Γ', Γ.Turn s Γ' := by
  refine Γ.exists_turn_of_forall_lt hs_box hs fun t hts hne => ?_
  have : t ∈ ((insert s Γ.squares : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := hlow hts (by simp)
  simpa [hne] using this

/-- Turns of `Γ` are exactly the addable corners of `Γ.squares` in the box. -/
theorem exists_turn_iff_addable (Γ : TwoGridPath m) (s : ℕ × ℕ) :
    (∃ Γ', Γ.Turn s Γ') ↔ s ∈ range m ×ˢ range m ∧ s ∉ Γ.squares ∧
      IsLowerSet ((insert s Γ.squares : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  constructor
  · rintro ⟨Γ', h⟩
    exact ⟨h.mem_product, h.addable.1, h.addable.2.2⟩
  · rintro ⟨hb, hs, hlow⟩
    exact Γ.exists_turn_of_addable hb hs hlow

/-- The same iff, predecessor form. -/
theorem exists_turn_iff_forall_lt (Γ : TwoGridPath m) (s : ℕ × ℕ) :
    (∃ Γ', Γ.Turn s Γ') ↔ s ∈ range m ×ˢ range m ∧ s ∉ Γ.squares ∧
      ∀ t, t ≤ s → t ≠ s → t ∈ Γ.squares := by
  constructor
  · rintro ⟨Γ', h⟩
    exact ⟨h.mem_product, h.addable.1, h.addable.2.1⟩
  · rintro ⟨hb, hs, hlt⟩
    exact Γ.exists_turn_of_forall_lt hb hs hlt

end TwoGridPath

end New

#print axioms New.GridPath.exists_corner_of_addable
#print axioms New.TwoGridPath.exists_turn_of_forall_lt
#print axioms New.TwoGridPath.exists_turn_of_addable
#print axioms New.TwoGridPath.exists_turn_iff_addable
#print axioms New.TwoGridPath.exists_turn_iff_forall_lt
