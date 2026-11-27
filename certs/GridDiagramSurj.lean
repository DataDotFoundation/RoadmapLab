import New.Determinant.AuxiliaryForms.GridPaths

/-!
# Two-grid paths and Young diagrams in the box: the dictionary is a bijection

Parts (a)-(d) are copied from `GridDiagram.lean` (lower set, Durfee rank, turns, injectivity).
New here: (e) `TwoGridPath.exists_squares_eq`, every lower set of `ℕ × ℕ` inside
`range m ×ˢ range m` is `Γ.squares` for some `Γ`, via the one-grid lemma
`GridPath.exists_of_squares`; and (f) `TwoGridPath.toDiagram_bijective`.

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

/-! ## Surjectivity: every Young diagram in the box comes from a two-grid path -/

namespace GridPath

/-- Steps to the right add no squares. -/
theorem exists_extend_right {a₀ b₀ r b : ℕ} (p : GridPath a₀ b₀ r b) (k : ℕ) :
    ∃ q : GridPath a₀ b₀ (r + k) b, q.squares = p.squares := by
  induction k with
  | zero => exact ⟨p, rfl⟩
  | succ k ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨q.right, by simp [squares, hq]⟩

/-- One grid: a finite set `T` of squares lying in the box `i < a`, `b ≤ j < b₀`, closed
downwards within that box, is the set of squares of a path from `(0, b₀)` to `(a, b)`. -/
theorem exists_of_squares (b₀ : ℕ) : ∀ (n b a : ℕ), b₀ = b + n → ∀ T : Finset (ℕ × ℕ),
    (∀ s ∈ T, s.1 < a ∧ b ≤ s.2 ∧ s.2 < b₀) →
    (∀ i j i' j', (i, j) ∈ T → i' ≤ i → b ≤ j' → j' ≤ j → (i', j') ∈ T) →
    ∃ p : GridPath 0 b₀ a b, p.squares = T := by
  intro n
  induction n with
  | zero =>
    intro b a hb T hT _
    simp only [Nat.add_zero] at hb
    subst hb
    refine ⟨row b₀ a, ?_⟩
    rw [squares_row]
    ext s
    simp only [Finset.notMem_empty, false_iff]
    intro hs
    have := hT s hs
    omega
  | succ n ih =>
    intro b a hb T hT hdown
    classical
    have hex : ∃ i, (i, b) ∉ T := ⟨a, fun h => by have := hT _ h; simp at this⟩
    obtain ⟨r, hra, hr⟩ : ∃ r, r ≤ a ∧ ∀ i, (i, b) ∈ T ↔ i < r := by
      refine ⟨Nat.find hex, Nat.find_min' hex (fun h => by have := hT _ h; simp at this),
        fun i => ⟨fun h => ?_, fun h => not_not.mp (Nat.find_min hex h)⟩⟩
      by_contra hc
      exact Nat.find_spec hex (hdown i b _ b h (by omega) le_rfl le_rfl)
    obtain ⟨p', hp'⟩ := ih (b + 1) r (by omega) (T.filter fun s => b + 1 ≤ s.2)
      (by
        rintro ⟨i, j⟩ hs
        simp only [mem_filter] at hs
        have h1 := hT _ hs.1
        refine ⟨(hr i).mp (hdown i j i b hs.1 le_rfl le_rfl (by simp at hs; omega)), hs.2, h1.2.2⟩)
      (by
        intro i j i' j' h hi hj' hj
        simp only [mem_filter] at h ⊢
        exact ⟨hdown i j i' j' h.1 hi (by omega) hj, hj'⟩)
    obtain ⟨k, rfl⟩ : ∃ k, a = r + k := ⟨a - r, by omega⟩
    obtain ⟨q, hq⟩ := exists_extend_right p'.down k
    refine ⟨q, ?_⟩
    rw [hq]
    simp only [squares, hp']
    ext ⟨i, j⟩
    simp only [mem_union, mem_filter, mem_product, mem_range, mem_singleton]
    constructor
    · rintro (⟨h, -⟩ | ⟨hi, rfl⟩)
      · exact h
      · exact (hr i).mpr hi
    · intro h
      by_cases hj : b + 1 ≤ j
      · exact .inl ⟨h, hj⟩
      · have := (hT _ h).2.1
        obtain rfl : j = b := by simp at this; omega
        exact .inr ⟨(hr i).mp h, rfl⟩

end GridPath

namespace TwoGridPath

variable {m : ℕ}

/-- (e) Surjectivity: every lower set of `ℕ × ℕ` inside the box `range m ×ˢ range m` is the set
of squares of a two-grid path. -/
theorem exists_squares_eq (S : Finset (ℕ × ℕ)) (hS : S ⊆ range m ×ˢ range m)
    (hlow : IsLowerSet (S : Set (ℕ × ℕ))) : ∃ Γ : TwoGridPath m, Γ.squares = S := by
  classical
  have hbox : ∀ s ∈ S, s.1 < m ∧ s.2 < m := fun s hs => by
    have := hS hs; simp only [mem_product, mem_range] at this; exact this
  have hdc : ∀ i j i' j', (i, j) ∈ S → i' ≤ i → j' ≤ j → (i', j') ∈ S :=
    fun i j i' j' h hi hj => hlow (show ((i', j') : ℕ × ℕ) ≤ (i, j) from ⟨hi, hj⟩) h
  -- the Durfee rank
  have hex : ∃ i, (i, i) ∉ S := ⟨m, fun h => by have := hbox _ h; simp at this⟩
  obtain ⟨l, hlm, hl⟩ : ∃ l, l ≤ m ∧ ∀ i, (i, i) ∈ S ↔ i < l := by
    refine ⟨Nat.find hex, Nat.find_min' hex (fun h => by have := hbox _ h; simp at this),
      fun i => ⟨fun h => ?_, fun h => not_not.mp (Nat.find_min hex h)⟩⟩
    by_contra hc
    exact Nat.find_spec hex (hdc i i _ _ h (by omega) (by omega))
  -- a square off the `l × l` block has one index below `l`
  have hoff : ∀ i j, (i, j) ∈ S → l ≤ j → i < l := by
    intro i j h hj
    by_contra hc
    exact absurd ((hl l).mp (hdc i j l l h (by omega) hj)) (lt_irrefl l)
  have hoff' : ∀ i j, (i, j) ∈ S → l ≤ i → j < l := by
    intro i j h hi
    by_contra hc
    exact absurd ((hl l).mp (hdc i j l l h hi (by omega))) (lt_irrefl l)
  obtain ⟨pf, hpf⟩ := GridPath.exists_of_squares m (m - l) l l (by omega)
    (S.filter fun s => l ≤ s.2)
    (by
      rintro ⟨i, j⟩ hs
      simp only [mem_filter] at hs
      exact ⟨hoff i j hs.1 hs.2, hs.2, (hbox _ hs.1).2⟩)
    (by
      intro i j i' j' h hi hj' hj
      simp only [mem_filter] at h ⊢
      exact ⟨hdc i j i' j' h.1 hi hj, hj'⟩)
  obtain ⟨pt, hpt⟩ := GridPath.exists_of_squares m (m - l) l l (by omega)
    ((S.filter fun s => l ≤ s.1).image Prod.swap)
    (by
      rintro ⟨i, j⟩ hs
      simp only [mem_image, mem_filter, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq] at hs
      obtain ⟨a, b, ⟨h, hab⟩, rfl, rfl⟩ := hs
      exact ⟨hoff' a b h hab, hab, (hbox _ h).1⟩)
    (by
      intro i j i' j' h hi hj' hj
      simp only [mem_image, mem_filter, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq] at h ⊢
      obtain ⟨a, b, ⟨h, hab⟩, rfl, rfl⟩ := h
      exact ⟨j', i', ⟨hdc a b j' i' h hj hi, hj'⟩, rfl, rfl⟩)
  refine ⟨⟨l, fun z => match z with | false => pf | true => pt⟩, ?_⟩
  ext ⟨i, j⟩
  rw [mem_squares]
  show (i < l ∧ j < l) ∨ (i, j) ∈ pf.squares ∨ (j, i) ∈ pt.squares ↔ _
  rw [hpf, hpt]
  simp only [mem_image, mem_filter, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
  constructor
  · rintro (⟨hi, hj⟩ | ⟨h, -⟩ | ⟨a, b, ⟨h, -⟩, rfl, rfl⟩)
    · have := (hl (max i j)).mpr (by omega)
      exact hdc _ _ i j this (by omega) (by omega)
    · exact h
    · exact h
  · intro h
    by_cases hj : l ≤ j
    · exact .inr (.inl ⟨h, hj⟩)
    by_cases hi : l ≤ i
    · exact .inr (.inr ⟨i, j, ⟨h, hi⟩, rfl, rfl⟩)
    · exact .inl ⟨by omega, by omega⟩

/-- The lower sets of `ℕ × ℕ` inside the `m × m` box (Young diagrams in the box). -/
abbrev BoxDiagram (m : ℕ) : Type :=
  {S : Finset (ℕ × ℕ) // S ⊆ range m ×ˢ range m ∧ IsLowerSet (S : Set (ℕ × ℕ))}

/-- The dictionary: a two-grid path goes to its set of squares, a Young diagram in the box. -/
def toDiagram (Γ : TwoGridPath m) : BoxDiagram m :=
  ⟨Γ.squares, Γ.squares_subset, Γ.isLowerSet_squares⟩

/-- (f) The dictionary is a bijection between two-grid paths and Young diagrams in the box. -/
theorem toDiagram_bijective : Function.Bijective (toDiagram : TwoGridPath m → BoxDiagram m) := by
  refine ⟨fun Γ Γ' h => squares_injective (congrArg Subtype.val h), fun ⟨S, hS, hlow⟩ => ?_⟩
  obtain ⟨Γ, hΓ⟩ := exists_squares_eq S hS hlow
  exact ⟨Γ, Subtype.ext hΓ⟩

end TwoGridPath

end New

#print axioms New.TwoGridPath.squares_injective
#print axioms New.GridPath.exists_of_squares
#print axioms New.TwoGridPath.exists_squares_eq
#print axioms New.TwoGridPath.toDiagram_bijective
