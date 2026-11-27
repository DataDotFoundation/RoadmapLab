# Roadmap: the theta lifts of the shorter proof as one Giambelli determinant — assessment and motivation

**Summary.** The shorter Lean proof of the Riemann hypothesis for Dirichlet L-functions ([ShortProof]) moves automorphic forms along a chain of theta lifts between unitary groups. At each step it ties them to the arithmetic of a CM field: places, Hecke characters, conductors, adeles and L-values. This roadmap asks whether all of those lifts can be expressed as **one Giambelli determinant**: a determinant of hook amplitudes, indexed by the Frobenius coordinates of the diagram that the grids of the chain sweep out (GiambelliAndThetaLiftGrids, Layer 3).

The roadmap is in two parts, in this order:
1. **An assessment.** It inventories every line of reasoning in the proof that uses a theta lift together with number-field arithmetic, and measures it with metrics defined directly from names and the dependency graph (grep-level, reproducible). The inventory and the metrics are published on RH-Dual.
2. **Motivation**, in four parts:
   - what a single determinant could save, in proof lines;
   - an argument from elegance and symmetry;
   - an argument about an elementary proof;
   - a perspective on the RH-related roadmaps published on Tau Ceti.

It builds on GiambelliAndThetaLiftGrids, and on the TauCetiRoadmap roadmaps that own the lifts: DeterminantsOfThetaLiftChains, NormsOfThetaLiftsAndExchangeIdentities, WeilRepresentationsOnBanachSpacesOfData, SiegelWeilAndRallisFormulasOnUnitaryGroups and ThetaLiftChainsAndTheSeesawIdentity.

**Status.** No step of the proof is known to be a Giambelli determinant today. The proof neither states nor uses Giambelli's identity, and none of its determinants is of Jacobi–Trudi type (RH-Dual, *giambelli-sites*). This roadmap therefore has **no formalization target yet**. Its targets are the assessment, which is reproducible, and a sequence of **open tests** that would have to pass before a formalization roadmap could be written. Every claim carries a label: **computed**, **source-verified**, **proposed dictionary**, **open test** or **inferred**.

## Conventions

- **The proof** is [ShortProof] as continued at leanprover-community/riemann-hypothesis. The assessment is computed at commit `61d870d` on the elaborated corpus `condensed@61d870d` (types, line spans, direct dependencies) and the closure of `riemannHypothesis` there.
- **Θ, the theta-lift constructions**: the 41 project definitions whose last name component is a theta-lift construction and whose module is in the Weil-representation, Siegel–Weil, chain, one-lift, upper-bound, spanning or derivative areas. Examples: `New.Space.θ`, `New.Space.lift`, `New.pairTheta`, `New.pairThetaKer`, `New.Exchange.thetaLarge`, `New.Exchange.thetaSmall`, `New.DescentPair.thetaLift`, `New.Data.singleLift`, `New.Data.triangleLift`, `New.Exchange.modTransposedLift`; the theta kernels `New.modKernel`, `New.Data.liftKernel`, `New.Data.gridKernel`; and the chain of lifts itself, `New.Data.lowerChain` and `New.Data.Θ`. Theta functions of abelian varieties (`CMLattice`, `ThetaTori`) are excluded.
- **Number-field arithmetic**: constants of six kinds, matched by name.
  - places (`InfinitePlace`, `New.FinPlace`, `ClosurePlace`, `IsPlaceOver`, …);
  - L-values (`lValueProd`, `LFunction`, …);
  - Hecke characters (`SplitTameChar`, `.character`, `quadTwist`, …);
  - conductors, ideals and class groups (`New.Modulus`, `ResidueRing`, `absNorm`, `ClassGroup`, …);
  - adeles (`New.𝔸`, `New.LocProd`, …);
  - field invariants (`NumberField.discr`, …).

  Typeclass plumbing (`NumberField E`, `CMType E`, `WeilData E`) is not counted: it occurs in every type of the theory and says nothing about which arithmetic a step uses.
- **A bridge** is a project declaration whose direct dependencies (statement and proof) contain a Θ constant and a number-field constant: one step of reasoning that uses a theta lift and number-field arithmetic together. An *arithmetic bridge* uses L-values or Hecke characters, not only places, adeles or conductors (which the adelic groups carry structurally).
- **The weighted graph**: vertices are the live declarations, an edge goes from a declaration to each direct dependency, and the weight of a vertex is its source line span. A *line of reasoning* is a connected component of the subgraph of live bridges.
- **Giambelli determinant**: `det(τ_{(a_i|b_j)})_{i,j<d}` in Frobenius coordinates, as in GiambelliAndThetaLiftGrids 2.2. Tau Ceti's Schur polynomials are the model case. GiambelliAndThetaLiftGrids is a roadmap of RoadmapLab; the others named here are roadmaps of TauCetiProject/TauCetiRoadmap, cited by section at its `main`.

## Part I: Assessment

### 1. The inventory of lines of reasoning

*Label:* computed.

The full inventory lists every bridge (758 bridges, 741 live). It gives one row per source file, with its bridges, weight, arithmetic kinds, the Θ constructions it uses, and the TauCetiRoadmap roadmap that cites the file. It is published on RH-Dual:
- inventory: [`inventory.md`](https://github.com/DataDotFoundation/RH-Dual/blob/b82c85314437c7e427b4f68e85ca0c080762bc2a/bridge/links/theta-numberfields/inventory.md);
- one row per bridge: [`bridges.tsv`](https://github.com/DataDotFoundation/RH-Dual/blob/b82c85314437c7e427b4f68e85ca0c080762bc2a/bridge/links/theta-numberfields/bridges.tsv);
- the lines of reasoning: [`lines.tsv`](https://github.com/DataDotFoundation/RH-Dual/blob/b82c85314437c7e427b4f68e85ca0c080762bc2a/bridge/links/theta-numberfields/lines.tsv);
- the generators, rerunnable at any corpus (Python ≥ 3.12): [`bridges.py`](https://github.com/DataDotFoundation/RH-Dual/blob/b82c85314437c7e427b4f68e85ca0c080762bc2a/bridge/links/theta-numberfields/bridges.py), [`bridge_graph.py`](https://github.com/DataDotFoundation/RH-Dual/blob/b82c85314437c7e427b4f68e85ca0c080762bc2a/bridge/links/theta-numberfields/bridge_graph.py), [`bridge_inventory.py`](https://github.com/DataDotFoundation/RH-Dual/blob/b82c85314437c7e427b4f68e85ca0c080762bc2a/bridge/links/theta-numberfields/bridge_inventory.py);
- summary and provenance: [`README.md`](https://github.com/DataDotFoundation/RH-Dual/blob/b82c85314437c7e427b4f68e85ca0c080762bc2a/bridge/links/theta-numberfields/README.md).

The heaviest files are in the exchange identity and the norms of single lifts:
- `New/OneLift/HeckeValues/TwistedValueHeights.lean` (11 bridges, 759 lines);
- `New/Determinant/Exchange/LargeTriple.lean` (20, 580);
- `New/Determinant/Exchange/TheoremForPartners.lean` (16, 553);
- `New/Determinant/Exchange/OneSquare.lean` (17, 463);
- `New/UpperBound/Divisibility/ValuationAtNonSplitPrimes.lean` (14, 451);
- `New/UpperBound/Seesaw/UnfoldingStages.lean` (12, 442).

### 2. Metrics

*Label:* computed (definitions above; full tables on RH-Dual, [`metrics.md`](https://github.com/DataDotFoundation/RH-Dual/blob/b82c85314437c7e427b4f68e85ca0c080762bc2a/bridge/links/theta-numberfields/metrics.md)).

| metric | value |
|---|---|
| Θ constructions (all live) | 41 |
| bridges / live bridges | 758 / 741 |
| weight of live bridges | 18,445 lines, **6.3%** of the 294,471 live lines of the proof |
| arithmetic bridges (L-values or Hecke characters) | 322 (9,111 lines) |
| bridges using L-values | 71 (2,731 lines) |
| bridges also using `Matrix.det` | 82 (3,271 lines) |
| lines of reasoning (components of the bridge graph) | 4; **one of them holds 731 of the 741 bridges** (18,357 lines); the reading as "one line of reasoning" is inferred |
| depth from `riemannHypothesis` (BFS; 12 bridges unreached by direct edges, excluded) | min 5, median 15, max 30 |
| fan-in (live direct users), top | `New.pairTheta` 102, `New.modKernel` 93, `New.Space.jetSeries` 69, `New.modKernelStdSpace` 61, `New.Data.liftKernel` 55 |

By area, the live bridges are in:
- `New/Determinant`: 235 bridges, 5,856 lines, 31 with `det`;
- `New/OneLift`: 130, 4,255;
- `Lib/Weil`: 170, 2,939;
- `New/UpperBound`: 113, 2,703;
- `Lib/SiegelWeil`: 59, 1,807;
- elsewhere: 34, of which 10 (190 lines) in `New/Reduction`, through the chain of lifts `lowerChain`.

No bridge lies in the analytic part of the proof (`Lib/Analytic`, the zero-free regions and the prime sums).

The single giant component is the assessment's main structural fact. All of the proof's reasoning that ties theta lifts to number-field arithmetic is one connected web, joined through a few hubs (`pairTheta`, `modKernel`, `Space.jetSeries`, `liftKernel`), not a collection of independent arguments. That is a necessary condition for a single determinant, not evidence for one.

## Part II: Motivation

### 3. Proof line savings

*Labels:* computed (the bounds); inferred (the expectation).

Upper bounds, as live line spans:
- all bridges: 18,445;
- the bridges that already involve a determinant: 3,271;
- the whole chain machinery `New/Determinant`: 13,759, of which:
  - `New/Determinant/AuxiliaryForms`, the two grids and the transfer of period data: 5,277;
  - `New/Determinant/Exchange`, the exchange identity: 5,434;
  - `New/Determinant/Chain`, the norm of the chain and its determinants: 2,023.

These bound what a reformulation could replace; they are not estimates of a saving. With what is known today, the expected saving is **zero**: there is no Jacobi–Trudi or Giambelli determinant in the proof to rewrite (RH-Dual, *giambelli-sites*: 0 of 11 candidate sites).

A saving would require the open tests of §7 to pass. If they did, the transfer of period data through the `m²` turns would become one determinant identity (DeterminantsOfThetaLiftChains §5.9; [ShortProof] `New.Data.exists_transfersPeriods_first_last`), together with its cell-by-cell bookkeeping. The order of magnitude at stake is then the 5–11 thousand lines of `AuxiliaryForms` and `Exchange`, not the whole proof.

### 4. Elegance: more symmetry on the lifts

*Labels:* source-verified (the grid facts); proposed dictionary (the symmetries).

**What the proof does today.** It moves forms along monotone paths through two grids reflected in the diagonal, one cell per turn (DeterminantsOfThetaLiftChains §5.1; GiambelliAndThetaLiftGrids 3.1–3.2). The half of a path in the grid of the `Ỹ` is recorded with its indices exchanged.

**What a Giambelli form would add.** A Giambelli determinant carries three symmetries the cell-by-cell proof does not exhibit:
- conjugation `λ ↦ λ′`, which exchanges the arm and leg coordinates `(a|b) ↦ (b|a)`. It is proposed to match the reflection of the two grids in the diagonal, the grid of the `Y` against the grid of the `Ỹ`;
- invariance under row and column operations, so that one could choose which hooks to use, rather than following one path;
- the reduction of the whole sweep to the `d` hooks on the diagonal. Here `d` is the Durfee rank, which is the node at which the path meets the diagonal.

The proof treats diagonal turns separately, with a finite Fourier transform and a line reversal (DeterminantsOfThetaLiftChains §5.9). In a Giambelli form, those would be the steps that create the hooks.

**On the question of [RoadmapLab#7](https://github.com/DataDotFoundation/RoadmapLab/issues/7).** The dictionary gives Durfee rank `m` and area `m²` on the last path for every `m`, so it does **not** explain why the proof takes `m ≍ √x`. That choice is imposed in the admissible data (OneSidedPrimeSumBoundsAndAdmissibleData §3.7: `m` is the least power of `2` with `m ≥ √x`). It enters through the main inequality `m · totalRemainder ≤ f · a · (log b)^5`. An explanation of the exponent would need an estimate in which `x` controls the *area* of the swept diagram, and none is known (open test §7.4). The expected bearing on [riemann-hypothesis#6836](https://github.com/leanprover-community/riemann-hypothesis/issues/6836) is recorded in GiambelliAndThetaLiftGrids (open test).

### 5. Towards an elementary proof

*Labels:* inferred; lit for the cited negative.

Giambelli's identity is a polynomial identity: it holds for any pair of symbols `h`, `e` with `H(X)E(−X) = 1`, over any commutative ring (GiambelliAndThetaLiftGrids 2.2). If the arithmetic transfers along the chain were a determinant identity in such symbols, that part of the proof would become algebra, with positivity and size estimates left on either side.

What it would not touch must be stated as clearly:
- **Analytic inputs.** The proof's analytic inputs need more than Chebyshev strength. The remainder bound needs `(log y)^{−B}` for every `B`, and the primes in short windows must lie in progressions `≡ 1 mod M^k`, uniformly in the modulus. A Diamond–Erdős finite-weight replacement fails (RH-Dual, *ED audit*, a precise negative).
- **L-values.** The 71 bridges using L-values (2,731 lines) are where Hecke L-values enter the lifts: squared norms of lifts as L-values, and the Rallis inner product. These are arithmetic, not combinatorics. A determinant form would have to carry them as the entries `τ_{(a|b)}`, not remove them.

So the most a Giambelli form could offer an elementary proof is an elementary *combinatorial skeleton* for the chain, with the analytic and L-value content isolated in the hook amplitudes. That would be a real clarification of where the arithmetic power lies. It is not an elementary proof.

### 6. Perspective on the RH-related roadmaps on Tau Ceti

*Labels:* computed (weights); read (implementation status, from Tau Ceti PRs linking each section).

The bridges belong to ShortGRH roadmaps of TauCetiRoadmap, by the roadmap that cites their file:

| roadmap | files | bridges | lines | open implementation PRs (sections) |
|---|---|---|---|---|
| DeterminantsOfThetaLiftChains | 30 | 277 | 6,764 | 3 of 36 |
| NormsOfThetaLiftsAndExchangeIdentities | 22 | 141 | 4,478 | 0 of 39 |
| WeilRepresentationsOnBanachSpacesOfData | 28 | 170 | 2,939 | 0 of 62 |
| SiegelWeilAndRallisFormulasOnUnitaryGroups | 9 | 58 | 1,748 | 0 of 38 |
| ThetaLiftChainsAndTheSeesawIdentity | 12 | 73 | 1,620 | 0 of 46 |
| CompositeThetaLiftsAndShortForms | 6 | 40 | 1,083 | 1 of 47 |
| DivisibilityOfThetaDerivatives | 5 | 18 | 455 | 0 of 34 |
| CongruencesOfTwistedThetaLifts | 3 | 10 | 250 | 1 of 41 |
| SecondMomentsOfPoincareSeries | 1 | 4 | 226 | 4 of 44 |
| OneSidedPrimeSumBoundsAndAdmissibleData | 3 | 10 | 190 | 8 of 26 |

Three observations:
- The roadmaps a determinant reformulation would touch have almost no implementation in progress. The implementation activity on ShortGRH is in the analytic roadmaps. ZeroFreeRegionsAndPrimesInShortWindows holds **no** bridges. OneSidedPrimeSumBoundsAndAdmissibleData holds 10 small ones, where the chain of lifts enters its target lattice (§5.1), its normalised Poincaré maps (§5.2) and its main inequality (§6.1, `New.star_inequality`), and its open implementation PRs are on §§0.1, 0.2, 2.2–2.3, 3.6–3.7, 4.2 and 6.2, not on those steps. A reformulation would not disrupt open work.
- The other family, RiemannHypothesisForDirichletLFunctions (the original export), states the same theta machinery in nine roadmaps, among them ThetaKernelsForUnitaryDualPairs, SeesawForThetaChains, RowTowerAndRallisIdentities, ThetaChainsOnDefiniteUnitaryGroups and LocalGainOfThetaChains. A Giambelli form found for the condensed proof would be a candidate there too. The assessment here is computed for the condensed proof only.
- The geometric Giambelli formula of Schubert calculus is TensorProductCombinatorics §6.4. A determinant of hook amplitudes would sit between it and the arithmetic, in GiambelliAndThetaLiftGrids.

## Two goals

A Giambelli reduction of the theta lifts could serve two different goals, and every task and result below is tagged with the goal it bears on.

- **(L) Compression.** Fewer lines in the proof: a determinant identity replacing cell-by-cell bookkeeping. It is measured by the line spans of Part I and of §3.
- **(U) Understanding.** The proxy is proximity to an Erdős-like argument: an elementary, counting or divisibility-style argument in the spirit of Erdős's proof of Bertrand's postulate. The effect of each result on (U) is recorded as **open**.

| task | goal | result | effect on (L) | effect on (U) |
|---|---|---|---|---|
| R0 Toeplitz moduli | L, U | positive (read) | none by itself | open |
| T1 classify the determinants | L | negative (no Jacobi–Trudi determinant) | L ≈ 0 at the chain-norm level | open |
| T2 explicit symbol, Schur test | L, U | negative for m ≥ 3 | L ≈ 0 | open |
| T3 Toeplitz → Giambelli in Lean | L, U | positive (proved) | none until the proof has such a determinant | open |
| T4 amplitudes, `m = 2` Plücker | U | not run (premise failed) | — | open |
| T5 coverage, exponent | L, U | not run | — | open |
| T6 shape of the turn ratios | L, U | negative (none of separable / content / Hankel) | L ≈ 0 | open |
| D1 grids are Young diagrams (Lean) | U | positive (proved) | none | open |

RH-Dual's earlier finding that Giambelli would shorten 0 of 11 candidate sites (*giambelli-sites*) also reads as L ≈ 0.

## Implementation status

Upstream is pinned at `7c4ccbd`. Each result gives its label, the exact declaration or script with a permalink, and what it means for this roadmap's claim.

**R0. The chain moduli are Toeplitz.**
- *Label:* read (upstream lemma).
- *Source:* [`New.Data.quotientRatio`](https://github.com/leanprover-community/riemann-hypothesis/blob/7c4ccbd64d02774b0a5b40a5f923f5b7a18e8abc/src/New/Determinant/Chain/Moduli.lean#L287) and [`New.Data.quotientRatio_add_eq_lRatioProd`](https://github.com/leanprover-community/riemann-hypothesis/blob/7c4ccbd64d02774b0a5b40a5f923f5b7a18e8abc/src/New/Determinant/Chain/Moduli.lean#L290). `quotientRatio i (i+n)` depends only on `n`, because the lift characters form a geometric progression. Write `C_n` for it.
- *Meaning:* the moduli have the shape a Jacobi–Trudi symbol needs.

**R1. The moduli enter the chain norm as a product, not as a determinant.**
- *Label:* read.
- *Source:* [`New.Data.exists_inner_weightedChain_eq`](https://github.com/leanprover-community/riemann-hypothesis/blob/7c4ccbd64d02774b0a5b40a5f923f5b7a18e8abc/src/New/Determinant/Chain/NormOfChain.lean#L168). The norm carries `∏_{0<i<j≤m} quotientRatio i j = ∏_n C_n^{m−n}`, up to a constant and a power of the norm of the conductor.
- *Meaning:* there is no determinant of the moduli for Giambelli to rewrite.

**T1. No Jacobi–Trudi determinant among the determinant bridges.**
- *Label:* computed and read (RH-Dual).
- *Source:* [report](https://github.com/DataDotFoundation/RH-Dual/blob/c845d86abf0499eec4267a64faa42e91325a5243/bridge/links/toeplitz-symbol/README.md), [classification](https://github.com/DataDotFoundation/RH-Dual/blob/c845d86abf0499eec4267a64faa42e91325a5243/bridge/links/toeplitz-symbol/det-bridges-7c4ccbd.tsv), [script](https://github.com/DataDotFoundation/RH-Dual/blob/c845d86abf0499eec4267a64faa42e91325a5243/bridge/scripts/classify_det_bridges.py).
- *Result:* `quotientRatio` is used only as the product over pairs, or as the modulus of a single square. The 82 bridges that take a determinant split as follows:

  | class | bridges |
  |---|---|
  | determinant of a group element, residue matrix or diagonal block, fed to a character or norm (`χ(det g)`) | 45 |
  | minors of a variable matrix (highest-weight polynomials `∏ det^c`) | 5 |
  | structural determinant algebra | 4 |
  | a Gram matrix, used for invertibility | 1 |
  | no determinant in their own source | 27 |
  | Jacobi–Trudi type `det(C_{λ_i−i+j})` | **0** |

- *Meaning:* the direct route is closed at the chain-norm level.

**T2. The explicit symbol and the Schur test.**
- *Label:* read, proved and computed (RH-Dual).
- *Source:* [report](https://github.com/DataDotFoundation/RH-Dual/blob/c845d86abf0499eec4267a64faa42e91325a5243/bridge/links/toeplitz-symbol/README.md), [Lean](https://github.com/DataDotFoundation/RH-Dual/blob/c845d86abf0499eec4267a64faa42e91325a5243/bridge/links/toeplitz-symbol/ToeplitzSymbol.lean), [script](https://github.com/DataDotFoundation/RH-Dual/blob/c845d86abf0499eec4267a64faa42e91325a5243/bridge/scripts/toeplitz_symbol_check.py).
- *Result:*
  - `C_n(ϑ) = ∏_{z=1}^{t} ‖L^{MQ}(z, (ν_n ϑ^n)^{−1})‖ / ‖L^M(z, ν_n^{−1})‖`, with `ν_n = (υ^{−Δ} χ_M)^n`.
  - Normalisation is free: the proof uses the moduli only up to `f ↦ K · N(Q)^a · f` (proved).
  - `c_0 ≠ 1` in general (proved).
  - The symbol is two-sided as defined and one-sided as used (proved).
  - `P_m = ∏ C_n^{m−n}` is a single Schur function only for `m = 2` (`P_2 = s_{(1)}`); `P_3 = s_4 + 2s_{31} + s_{22} + s_{211}`, and `P_4`, `P_5` have 33 and 510 terms (computed, exact).
  - There is no form `C_n = g(a+n)/g(n)` (inferred).
- *Meaning:* the product of the moduli is not a principal specialisation of one Schur function, so Giambelli does not reduce it.

**T3. Toeplitz to Giambelli, in Lean.**
- *Label:* proved (RMTlib; `lake build --wfail`; axioms `propext`, `Classical.choice`, `Quot.sound`).
- *Source:* [`RMT.Symmetric.Giambelli.giambelli_toeplitz`](https://github.com/DataDotFoundation/RMTlib/blob/c2c73a6d6c95fb610f96ea31ffb15af374738057/RMTlib/Symmetric/Giambelli.lean#L583): for `c : ℕ → R` with `c 0 = 1`, `det(c_{λ_i−i+j})_{i,j<n} = det(jt (symbolOf c) (hookShape (frobA λ i) (frobB λ j)))_{i,j<d(λ)}`. It rests on [`hePair_dualSymbol`](https://github.com/DataDotFoundation/RMTlib/blob/c2c73a6d6c95fb610f96ea31ffb15af374738057/RMTlib/Symmetric/Giambelli.lean#L555), [`giambelli_jt'`](https://github.com/DataDotFoundation/RMTlib/blob/c2c73a6d6c95fb610f96ea31ffb15af374738057/RMTlib/Symmetric/Giambelli.lean#L538) and [`jt_hook`](https://github.com/DataDotFoundation/RMTlib/blob/c2c73a6d6c95fb610f96ea31ffb15af374738057/RMTlib/Symmetric/Giambelli.lean#L526). Documentation: [docs/giambelli.md](https://github.com/DataDotFoundation/RMTlib/blob/c2c73a6d6c95fb610f96ea31ffb15af374738057/docs/giambelli.md).
- *Meaning:* the algebra is ready. It applies to the proof only where the proof has a Toeplitz determinant, and T1 found none.

**T6. The turn ratios have no Giambelli shape.**
- *Goal:* L, U.
- *Label:* proved, computed and read (RH-Dual#269).
- *Source:* [report](https://github.com/DataDotFoundation/RH-Dual/blob/8eb12cf9f71e4d524a3c8343abab1acad37a363d/bridge/links/turn-ratio-shape/README.md), [Lean](https://github.com/DataDotFoundation/RH-Dual/blob/8eb12cf9f71e4d524a3c8343abab1acad37a363d/bridge/links/turn-ratio-shape/TurnRatioShape.lean), [script](https://github.com/DataDotFoundation/RH-Dual/blob/8eb12cf9f71e4d524a3c8343abab1acad37a363d/bridge/scripts/turn_ratio_shape.py).
- *Result:*
  - `turnRatio i j = G(i+j, j+1)`, with `G(s, n)(ϑ) = ∏_{z≤t} ‖L^{MQ}(z, (ν_s ϑ^n)^{−1})‖ / ‖L^M(z, ν_s^{−1})‖` (proved). The character depends on the antidiagonal `i + j`, the twist on the column.
  - The normalisation the proof allows is per cell, not uniform (read).
  - For every nontrivial twist the ratio is **neither** separable `A(i)B(j)`, **nor** of content type `f(j − i)`, **nor** Hankel `g(i + j)` (computed, in the free model with the L-values as independent symbols, `m ≤ 6`).
  - At the trivial twist every turn ratio is `1` (proved).
  - The product over the cells of a diagram `λ` is `|λ|` distinct L-products over a denominator indexed by the antidiagonal profile, not a hook-content product.
- *Meaning:* the period transfer along the grid is not a Schur-function evaluation, so Giambelli cannot act on it as stated.

**D1. The grids are Young diagrams, in Lean.**
- *Goal:* U.
- *Label:* proved in Lean against upstream `7c4ccbd` ([`certs/GridDiagram.lean`](https://github.com/DataDotFoundation/RoadmapLab/blob/main/certs/GridDiagram.lean), 195 lines; [`certs/GridDiagramSurj.lean`](https://github.com/DataDotFoundation/RoadmapLab/blob/main/certs/GridDiagramSurj.lean), 355 lines).
- *Result:* on upstream's own `New.TwoGridPath`, the squares a path encloses form a lower set; the diagonal index is their Durfee rank; a turn adds an addable corner; and paths are in bijection with the Young diagrams in the box (`New.TwoGridPath.toDiagram_bijective`; GiambelliAndThetaLiftGrids 3.1–3.2).
- *Meaning:* the combinatorial skeleton of the chain of lifts is, provably, Young-diagram combinatorics. It does not change any number in the proof (L: none). It is the precondition for any Giambelli formulation of the grid.

**T4, T5.**
- *Label:* not run.
- *Reason:* their premise, a determinant structure from T1/T2, failed. Any amplitudes `τ_λ` would have to come from elsewhere: the turn ratios, which are not Hankel (RH-Dual, `condensed-twin-audit.md`), or the 5 minor-polynomial bridges of T1.

**What this shows and does not show.**
- It shows that neither arithmetic datum along the chain has a Giambelli shape. The chain moduli are Toeplitz but enter only as a product (R1, T1, T2), and the turn ratios are neither Toeplitz, Hankel nor separable (T6). Compression by this route is **L ≈ 0**. Separately, the grids themselves are provably Young-diagram combinatorics (D1).
- It does not show that no determinant form of the theta lifts exists. Amplitudes built from other data (7.1) remain untested, and the effect on understanding (U) is open.

## Part III: Open tests (a roadmap for a roadmap; do not implement)

**Do not implement this part.** Each test must pass before a formalization roadmap can be written.

7.1 **Amplitudes.** Define scalar amplitudes `τ_λ` on the boundary paths of the grid, with a common ambient space and `τ_∅ = 1` (GiambelliAndThetaLiftGrids, last section).
7.2 **The `m = 2` Plücker relation.** `τ_{(2,2)} τ_∅ = τ_{(2,1)} τ_{(1)} − τ_{(2)} τ_{(1,1)}`, with the six actual theta-lift quantities named on both sides. This is the worked `2 × 2` example asked for in RoadmapLab#7. A negative answer is useful.
7.3 **Coverage.** If 7.2 holds, how many of the 741 bridges become entries `τ_{(a|b)}` or row and column operations? This is measured with the published metrics, rerun on the reformulated proof.
7.4 **The exponent.** An estimate in which the cut-off `x` controls the area of the swept diagram, or a proof that none exists within the proof's admissible data.

## Scope and ownership

### Owned here

The assessment (Part I) and the open tests (Part III).

### Not owned here

- The theta lifts, the grids and the exchange identities: DeterminantsOfThetaLiftChains and the TauCetiRoadmap roadmaps in §6.
- Giambelli's identity, Frobenius coordinates and the grid dictionary: GiambelliAndThetaLiftGrids.
- The published inventory and metrics: RH-Dual.

## Provenance

This roadmap was written by an AI model (Claude Opus 5.5, Anthropic), on Paul-Olivier Dehaye's instruction and following his research direction. The site was found by AI.
- The metrics were computed by RoadmapLab and are published on RH-Dual.
- The formal results cited are those of the authors of [ShortProof] and of Tau Ceti.
- No claim is made that Giambelli's identity shortens the proof.

## References

- [ShortProof] The shorter Lean formalization of the Riemann hypothesis for Dirichlet L-functions: the folder `grh` of github.com/lsernau/grh-lean at commit `72fead1`; continued at github.com/leanprover-community/riemann-hypothesis (assessment at commit `61d870d`).
- RH-Dual (github.com/DataDotFoundation/RH-Dual): the Toeplitz-symbol report (`bridge/links/toeplitz-symbol/`, RH-Dual#268 at `c845d86`); *giambelli-sites* (`bridge/links/giambelli-sites.md`); the ED audit (the Erdős → Diamond–Erdős lane, a precise negative); the theta ↔ number-field inventory and metrics, `bridge/links/theta-numberfields/` at commit `b82c853` ([RH-Dual#267](https://github.com/DataDotFoundation/RH-Dual/pull/267)).
- GiambelliAndThetaLiftGrids (this repository, `Roadmaps/GiambelliAndThetaLiftGrids`).
- RMTlib (github.com/DataDotFoundation/RMTlib): `RMTlib/Symmetric/Giambelli.lean` and `docs/giambelli.md` at `c2c73a6`.
- TauCetiProject/TauCetiRoadmap: the ShortGRH roadmaps in §6; RiemannHypothesisForDirichletLFunctions; TensorProductCombinatorics §6.4.
