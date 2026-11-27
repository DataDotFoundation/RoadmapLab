# Roadmap: Giambelli's identity, Frobenius coordinates and the grids of the chain of lifts

**Summary.** This roadmap builds the Frobenius coordinates of a Young diagram, and Giambelli's identity for Tau Ceti's Schur polynomials:
`s_λ = det(s_{(a_i|b_j)})_{1≤i,j≤d}`, where `d` is the Durfee rank of `λ` and `(a_1,…,a_d | b_1,…,b_d)` its Frobenius coordinates. With them come the hook formula for `s_{(a|b)}` and the vanishing of the power-sum coefficients `[p_μ] s_λ` when `ℓ(μ) < d(λ)`.

It then states, as theorems, a dictionary between Young diagrams and the monotone paths through two square grids along which the shorter Lean proof of the Riemann hypothesis for Dirichlet L-functions moves forms. For a grid of side `m`:
- the squares enclosed by a path form a Young diagram in the `m × m` box;
- the node at which the path meets the diagonal is its Durfee rank;
- an order of the `m²` turns is a standard Young tableau of rectangular shape `(m^m)`.

It builds on:
- Tau Ceti's Schur polynomials: Jacobi–Trudi, dual Jacobi–Trudi, Murnaghan–Nakayama;
- Mathlib's `YoungDiagram`;
- DeterminantsOfThetaLiftChains §5.1, where the paths and their turns are defined.

It cites TensorProductCombinatorics §6.4 for the geometric Giambelli formula of Schubert calculus, which it does not restate.

Layer 1 sets up Durfee rank and Frobenius coordinates. Layer 2 proves the hook formula and Giambelli's identity, and their power-sum consequence. Layer 3 proves the grid dictionary. The last section is a roadmap for a roadmap. It records a research question about amplitudes attached to the paths and a first Plücker test, and **is not to be implemented**.

## Conventions

- **Young diagrams** are Mathlib's `YoungDiagram`, with cells `(i, j)` (row `i`, column `j`), row lengths `λ_i = μ.rowLen i` and column lengths `λ′_j = μ.colLen j`, indices from `0`. `μ.transpose` is the conjugate diagram.
- **Durfee rank** `d(λ)` is the number of `i` with `(i, i) ∈ λ`, the side of the largest square in `λ`.
- **Frobenius coordinates.** For `i < d(λ)`, `a_i = λ_i − i − 1` and `b_i = λ′_i − i − 1`. So `a_0 > a_1 > ⋯ ≥ 0` and `b_0 > b_1 > ⋯ ≥ 0`, and `(a|b)` denotes the diagram with these coordinates. The hook `(a|b)` with one coordinate each has row lengths `a + 1, 1, …, 1` (`b` ones).
- **Schur polynomials** are Tau Ceti's `diagramSchurPoly N R μ` (alphabet `Fin N`) and `schurPoly σ R μ` (partitions, any finite alphabet), with `hsymmInt` and `esymmInt` the complete and elementary symmetric polynomials of integer degree, zero in negative degree.
- **Grids.** The paths, their halves, their turns and the set `Γ.squares ⊆ [0,m) × [0,m)` of the squares enclosed by a path are those of DeterminantsOfThetaLiftChains §5.1. That roadmap is the specification; [ShortProof] names them `New.TwoGridPath`, `New.TwoGridPath.Turn` and `New.TwoGridPath.squares`.
- **Other roadmaps.** DeterminantsOfThetaLiftChains, TensorProductCombinatorics and OneSidedPrimeSumBoundsAndAdmissibleData are roadmaps of [TauCetiProject/TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap) (the first and the last in its family `ShortGRH`), cited by section number at its branch `main`.
- **Labels.** Every section carries one of:
  - **source-verified**: stated as in a cited formal or published source, re-read;
  - **classical consequence**: a standard consequence of material that exists;
  - **proposed dictionary**: a correspondence this roadmap proposes, stated here as a theorem to prove;
  - **open test**: a question, only in the last section.

## Layer 1: Durfee rank and Frobenius coordinates

### 1.1 Durfee rank and Frobenius coordinates

*Label:* classical consequence.

Define `durfeeRank`, and the arm and leg coordinates `a_i`, `b_i` for `i < d(λ)`, as in the Conventions. Prove:

(a) the coordinates are strictly decreasing and nonnegative;
(b) `|λ| = Σ_{i<d} (a_i + b_i + 1)`;
(c) the Durfee rank of `λ′` is that of `λ`, and `λ′` has coordinates `(b|a)`;
(d) `λ ↦ (d(λ), a, b)` is a bijection from Young diagrams onto triples of an integer `d ≥ 0` and two strictly decreasing sequences of `d` nonnegative integers;
(e) for each `d`, the diagrams of Durfee rank `d` inside the `m × m` box correspond to pairs of diagrams in the `d × (m − d)` box. The square is removed, and what remains to the right of it and below it are the two pieces. In particular the number of diagrams in the box with Durfee rank `d` is `C(m, d)²`.

*Check:* `λ = (4, 3, 1)` has `d = 2` and coordinates `(3, 1 | 2, 0)`; its conjugate `(3, 2, 2, 1)` has `(2, 0 | 3, 1)`.

*Needs:* Mathlib `YoungDiagram`, `YoungDiagram.transpose`, `YoungDiagram.rowLen`, `YoungDiagram.colLen`.

## Layer 2: Giambelli's identity

### 2.1 Hook Schur polynomials

*Label:* classical consequence.

Prove the hook formula `s_{(a|b)} = Σ_{r=0}^{a} (−1)^r h_{a−r} e_{b+1+r}` for `diagramSchurPoly N R` and for `schurPoly σ R`, over any commutative ring. It is the expansion of the Jacobi–Trudi determinant of the hook along its first row, after the dual Jacobi–Trudi identity for the column. Prove also that `s_{(a|b)} = 0` when `N < b + 1`, for the alphabet `Fin N`.

*Needs:* Tau Ceti `diagramSchurPoly_eq_det_hsymmInt`, `diagramSchurPoly_eq_det_esymmInt`, `schurPoly_eq_det_hsymmInt`, `schurPoly_eq_det_esymmInt`, `det_hsymmInt_eq_det_esymmInt`.

### 2.2 Giambelli's identity

*Label:* classical consequence; source-verified for the formalization below.

Prove `diagramSchurPoly N R λ = det (diagramSchurPoly N R (a_i | b_j))_{i,j<d(λ)}`, and the same for `schurPoly σ R`.
- The proof multiplies the Jacobi–Trudi matrix of size `ℓ(λ)` on the right by the unitriangular matrix `((−1)^{j+k} e_{k−j})`. The rows below the Durfee square then reduce to a block whose determinant is `±1`, and the remaining `d × d` block has the hook entries of 2.1.
- The same argument proves the identity for any pair of symbols `h`, `e` vanishing in negative degree, with `h_0 = e_0 = 1` and `H(X)E(−X) = 1`.
- Prove that general form too, since it covers the specialisations used in 2.3.

A formalization against Tau Ceti's `diagramSchurPoly` and `schurPoly` is merged in Lean Pool ([LeanPool/lean-pool#1038](https://github.com/LeanPool/lean-pool/pull/1038), merge commit `fb336fb`). Its declarations are [`Giambelli.diagramSchurPoly_eq_det_hook`](https://github.com/LeanPool/lean-pool/blob/fb336fb85bca1f6669c9b13fc334467a29530b89/LeanPool/Giambelli/Schur.lean#L160), [`Giambelli.schurPoly_eq_det_hook`](https://github.com/LeanPool/lean-pool/blob/fb336fb85bca1f6669c9b13fc334467a29530b89/LeanPool/Giambelli/Schur.lean#L173), [`Giambelli.giambelli_jt'`](https://github.com/LeanPool/lean-pool/blob/fb336fb85bca1f6669c9b13fc334467a29530b89/LeanPool/Giambelli/Basic.lean#L541) and [`Giambelli.diagramSchurPoly_hookDiagram`](https://github.com/LeanPool/lean-pool/blob/fb336fb85bca1f6669c9b13fc334467a29530b89/LeanPool/Giambelli/Schur.lean#L147).

*Check:* for `λ = (2, 2) = (1, 0 | 1, 0)`, Giambelli gives `s_{22} = s_{(1|1)} s_{(0|0)} − s_{(1|0)} s_{(0|1)} = s_{211} s_1 − s_2 s_{11}`.

*Needs:* 1.1, 2.1.

### 2.3 Power-sum coefficients and Durfee rank

*Label:* classical consequence.

Over `ℚ`, write `s_λ = Σ_μ [p_μ] s_λ · p_μ` in power sums.

(a) Prove that `[p_μ] s_λ = 0` when `ℓ(μ) < d(λ)`. By 2.2, `s_λ` is a sum of products of `d(λ)` hook Schur polynomials, each of positive degree, and each `p_μ` term of a product of `d` homogeneous symmetric functions of positive degree involves at least `d` power sums.
(b) Prove that for `|λ| = k ≥ 1`, `k · [p_{(k)}] s_λ` is `(−1)^b` if `λ` is the hook `(a|b)` with `a + b + 1 = k`, and `0` otherwise. Equivalently, under the specialisation `p_k = k`, `p_j = 0` for `j ≠ k`, `s_λ` takes these values.

*Needs:* 2.2; Tau Ceti `psum_mul_diagramSchurPoly`, `psum_mul_schurPoly` (Murnaghan–Nakayama).

## Layer 3: The grids of the chain of lifts

### 3.1 The squares enclosed by a path form a Young diagram

*Label:* proposed dictionary.

Let `Γ` range over the paths through the two grids of side `m` of DeterminantsOfThetaLiftChains §5.1, and write `Γ.squares` for the squares it encloses. Fix the orientation that makes `Γ.squares` contain `(i, j)` together with every `(i′, j′)` with `i′ ≤ i`, `j′ ≤ j`. Prove:

(a) `Γ.squares` is the set of cells of a Young diagram `λ(Γ)` in the `m × m` box;
(b) `Γ ↦ λ(Γ)` is a bijection from the paths onto the Young diagrams in the box;
(c) the index `l` of the node `(l, l)` at which `Γ` meets the diagonal is `d(λ(Γ))`;
(d) under (b), the two halves of `Γ`, the part recorded in the grid of the `Y` and the part recorded, with exchanged indices, in the grid of the `Ỹ`, correspond to the two pieces of `λ(Γ)` outside its Durfee square (1.1 (e)).

The first path, through `(0, 0)`, gives the empty diagram. The last, through `(m, m)`, gives the full box. Both counts are `Σ_l C(m, l)² = C(2m, m)`.

*Needs:* 1.1; DeterminantsOfThetaLiftChains §5.1 (the paths, their halves, `squares`, and that the last path encloses the whole box).

*Status:* (a), (c) and the injectivity half of (b) are **proved in Lean** against [ShortProof]'s continuation at commit `7c4ccbd`, on its own `New.TwoGridPath`, with no restatement of its definitions ([`certs/GridDiagram.lean`](https://github.com/DataDotFoundation/RoadmapLab/blob/main/certs/GridDiagram.lean); axioms `propext`, `Classical.choice`, `Quot.sound`):
- `New.TwoGridPath.isLowerSet_squares`: the squares form a lower set in the plain componentwise order, so no reflection is needed;
- `New.TwoGridPath.diag_mem_squares_iff`: `(i, i) ∈ Γ.squares ↔ i < Γ.diagonalIndex`;
- `New.TwoGridPath.diagonalIndex_eq_card`: the diagonal index is the Durfee rank;
- `New.TwoGridPath.squares_injective`: a path is determined by its squares.

The surjectivity half of (b) is also **proved in Lean** ([`certs/GridDiagramSurj.lean`](https://github.com/DataDotFoundation/RoadmapLab/blob/main/certs/GridDiagramSurj.lean)):
- `New.TwoGridPath.exists_squares_eq`: every lower set in the `m × m` box is the set of squares of a path;
- `New.TwoGridPath.toDiagram_bijective`: paths ↔ Young diagrams in the box.

(b) is therefore proved in full. (d) remains a target.

### 3.2 Turns add one cell; sweeps are standard tableaux

*Label:* source-verified for (a), classical consequence for (b).

(a) A turn from `Γ` to `Γ′` at `s` adds the single cell `s` to `λ(Γ)`, and `s ∉ λ(Γ)` (DeterminantsOfThetaLiftChains §5.1; [ShortProof] `New.TwoGridPath.Turn.squares_eq`). Prove that, under 3.1, the cells that can be added by a turn are exactly the addable corners of `λ(Γ)` in the box.

*Status of (a):* one direction is **proved in Lean**, as `New.TwoGridPath.Turn.addable` ([`certs/GridDiagram.lean`](https://github.com/DataDotFoundation/RoadmapLab/blob/main/certs/GridDiagram.lean)): a turn at `s` adds `s`, every cell strictly below `s` is already enclosed, and the result is a lower set, so every turn adds an addable corner. The converse is also **proved** ([`certs/GridDiagramTurns.lean`](https://github.com/DataDotFoundation/RoadmapLab/blob/main/certs/GridDiagramTurns.lean)): `New.TwoGridPath.exists_turn_iff_addable` says a turn at `s` exists iff `s` is an addable corner of `Γ.squares` in the box. So the turns are exactly the covering relations of the poset of Young diagrams in the box, and (a) is proved.

(b) Prove that a sequence of turns from the first path to the last is the same as a standard Young tableau of shape `(m^m)`: the cell added at step `t` gets the label `t`. Their number is the hook length formula's `(m²)! / ∏_{i,j<m} (i + j + 1)`.

*Needs:* 3.1; DeterminantsOfThetaLiftChains §5.1.

### 3.3 What the exchange identities attach to cells

*Label:* source-verified. No target is owned here.

The theta-lift side of the grid is DeterminantsOfThetaLiftChains' and is not restated:
- the finite square law (§3.11);
- the one-square identity, up then down against down then up (§3.12);
- the transfer of period data from the first path to the last (§5.9).

For the reader of 3.1–3.2, three facts in the language of cells (read, [ShortProof] at `72fead1`):
- The identity attached to a turn at a cell is a **scalar** relation, `Σ Ψ′L′ = (κ/c) Σ ΨL` over matched finite data. `|c|²` is a product of Hecke L-values up to a constant, and `κ` may vanish. It is not a bijection of paths, and there is no positive growth rule.
- A turn on the diagonal also involves a finite Fourier transform and a line reversal.
- Composing all `m²` turns multiplies the absolute values by `∏_{i,j<m} turnRatio(i, j)`, up to a constant and a power of the norm of the conductor. This is a product over the cells of the full box. It is distinct from the triangular product in the factorisation of the norm of the chain (DeterminantsOfThetaLiftChains §4.4), which is not a product over the box.

The Gram determinant `det(Θ*Θ)` of a lift is a squared norm. It is positive when the lift is injective, and it is a sum of squared minors, not a single minor.

*Needs:* DeterminantsOfThetaLiftChains §§3.11, 3.12, 4.4, 5.9.

## Downstream consumers

None on the route of the proof. The shorter formal proof neither states nor uses Giambelli's identity, Frobenius coordinates or hook Schur polynomials, and none of its determinants is a Schur-function determinant of Jacobi–Trudi type. This roadmap makes no claim that Giambelli's identity shortens or replaces any step of that proof. Layer 3 is a dictionary for reading the grids, not a step of the proof.

## Scope and ownership

### Owned here

1.1; 2.1–2.3; 3.1, 3.2 (b), and the corner statement of 3.2 (a).

### Not owned here

- Jacobi–Trudi, dual Jacobi–Trudi, Murnaghan–Nakayama: Tau Ceti.
- Young diagrams: Mathlib.
- The geometric Giambelli formula of Schubert calculus: TensorProductCombinatorics §6.4.
- The paths through the two grids, their turns and squares, the square law, the one-square identity, the norm of the chain and the transfer of period data: DeterminantsOfThetaLiftChains §§3.11, 3.12, 4.4, 5.1, 5.3, 5.9.

## Exact supplier contracts

### From Tau Ceti

`TauCeti.diagramSchurPoly`, `TauCeti.schurPoly`, `hsymmInt`, `esymmInt`, `diagramSchurPoly_eq_det_hsymmInt`, `diagramSchurPoly_eq_det_esymmInt`, `schurPoly_eq_det_hsymmInt`, `schurPoly_eq_det_esymmInt`, `det_hsymmInt_eq_det_esymmInt`, `psum_mul_diagramSchurPoly`, `psum_mul_schurPoly` (`TauCeti/RingTheory/MvPolynomial/Symmetric/Schur/`).

### From Mathlib

`YoungDiagram`, `YoungDiagram.rowLen`, `YoungDiagram.colLen`, `YoungDiagram.transpose`, `Matrix.det`.

### From DeterminantsOfThetaLiftChains

§5.1 (the paths through two grids of side `m`, their halves, the diagonal index, `squares`, turns, and the first and last paths), and §§3.11, 3.12, 4.4, 5.9 for 3.3, cited only.

### From TensorProductCombinatorics

§6.4, cited only.

## A roadmap for a roadmap: amplitudes on the grid and a Plücker test

**Do not implement this section.** It records a research question that motivated the roadmap. A future roadmap may take it up once the finite tests below have an answer. Every statement here is a **proposed dictionary** or an **open test**, not a target.

- **Amplitudes.** Seek normalised scalar amplitudes `τ_λ(ϑ)` attached to the boundary paths `λ = λ(Γ)` of 3.1. They would need a common ambient space, compatible choices of the matched data, and a vacuum `τ_∅ = 1`. The question is whether `τ_λ = det(τ_{(a_i|b_j)})` in Frobenius coordinates, as in 2.2.
- **First test, `m = 2`.** The smallest non-hook case is the unnormalised relation `τ_{(2,2)} τ_∅ = τ_{(2,1)} τ_{(1)} − τ_{(2)} τ_{(1,1)}`.
  - It involves six amplitudes, all of which must be identified first.
  - A scalar exchange at one cell (3.3) does not by itself give an additive relation. Amplitudes that are sections of different lines need canonical identifications before they can be added.
  - Vanishing of `κ`, the sum over matched data, and the Fourier transform on diagonal turns may each obstruct the relation.
  - A negative answer is useful.
- **If the test succeeds**: whether the `τ` family is a decomposable wedge (a point of a Grassmannian), and whether its pairing recovers the Gram determinant of 3.3.
- **If it fails**: a weaker formulation, on determinant lines or with weighted paths.
- **Deformed Schur functions as inputs.** Dehaye (2008, §8.1, Proposition 8.1) proves a Giambelli formula for a deformation of Schur functions in Macdonald's ninth variation. Its determinant has Frobenius-coordinate entries `Γ(R − b_j)/Γ(R + a_i + 1) · 1/(a_i! b_j! (1 + a_i + b_j))`. Row and column factors separate from a Cauchy kernel, which is the pairing of monomials on `[0, 1]`. (Quoted from the paper and confirmed by its author.)
  Dehaye (2011) studies the operator `exp(Σ_{n≥1} n ∂_{p_n} ∂_{p̃_n})` coupling two alphabets. Its role relative to the Cauchy kernel and to paired theta sectors is an open question.
- **Limit shapes.** Plancherel growth, the Vershik–Kerov–Logan–Shepp curve and Airy (Tracy–Widom) scaling at the edge suggest questions about long sweeps of the grid (3.2). None of these features has been shown in the grids.
- **The size of the grid.** The proof takes grids of side `m ≍ √x` at the cut-off `x`, in its admissible data, and its main inequality compares `m · totalRemainder` with `f · a · (log b)^5`. Which constraints prevent a larger `m` is a question for the proof's own roadmaps (OneSidedPrimeSumBoundsAndAdmissibleData). Nothing here explains the exponent, and no local (per-cell) form of the global error bounds is claimed.

## Provenance

This roadmap was written by an AI model (Claude Opus 5.5, Anthropic), following a research direction set by Paul-Olivier Dehaye.
- The formal results it cites are their authors': Tau Ceti; Mathlib; the authors of the shorter formal proof ([ShortProof]); and the Lean Pool formalization cited in 2.2.
- Every section carries a label from the Conventions.
- [ShortProof] was read at commit `72fead1`. The cited declarations are unchanged at `61d870d` of its continuation, leanprover-community/riemann-hypothesis.

## References

- [ShortProof] The shorter Lean formalization of the Riemann hypothesis for Dirichlet L-functions: the folder `grh` of github.com/lsernau/grh-lean at commit `72fead1`; paths are relative to its directory `src/`. Its continuation is the branch `main` of github.com/leanprover-community/riemann-hypothesis.
- G. Z. Giambelli, *Alcune proprietà delle funzioni simmetriche caratteristiche*, Atti Torino 38 (1903); I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford (1995), Chapter I (Giambelli's formula; the ninth variation of Schur functions): 2.1, 2.2, the last section.
- R. P. Stanley, *Enumerative Combinatorics* Vol. 2, Cambridge (1999), Chapter 7 (Murnaghan–Nakayama rule; hook length formula): 2.3, 3.2.
- P.-O. Dehaye, *Joint moments of derivatives of characteristic polynomials*, Algebra & Number Theory 2 (2008), 31–68, §8: the last section.
- P.-O. Dehaye, *On an identity due to Bump and Diaconis, and Tracy and Widom*, Canad. Math. Bull. 54 (2011), 255–269: the last section.
- [LeanPool/lean-pool#1038](https://github.com/LeanPool/lean-pool/pull/1038), *Add Giambelli: Giambelli's identity for Schur polynomials*, merged as `fb336fb` (`LeanPool/Giambelli/Basic.lean`, `LeanPool/Giambelli/Schur.lean`): 2.2.
