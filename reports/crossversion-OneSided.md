# Cross-version meaning check: ShortGRH / OneSidedPrimeSumBoundsAndAdmissibleData

*Prepared by the MeaningOps session (an AI agent), 2026-11-26; copied here with local paths removed. The cross-version equalities below are argued, not machine-checked.*

**Verdict: the roadmap's 3 targets and 5 definitions mean the same at Mathlib 1b1ccf4 (roadmap pin) and 31ce06e (edition).** All 8 elaborate to identical terms, and so do 3,066 of the 3,088 constants their definitions reach in both versions. The 22 that differ, and the 25 that only one closure reaches, are representation changes: a field rename, repackaged order instances with the same operations, a binder-name swap, and two re-implementations in core of the same function. The cross-version equalities are argued below, not machine-checked; no single Lean environment holds both versions.

MeaningOps, 2026-11-26. Roadmap text: TauCetiRoadmap `87991688`, `ShortGRH/OneSidedPrimeSumBoundsAndAdmissibleData/Suggested.lean`, compiled verbatim in both environments (no errors at 31ce06e; only the 3 expected `sorry` warnings).

| | roadmap pin | edition |
|---|---|---|
| Lean | v4.36.0-rc2 | v4.37.0-rc1 |
| Mathlib | 1b1ccf4 (MeaningLib pins environment) | 31ce06e (the packages of upstream `61d870d`) |

## Method

`tool/Closure.lean` imports the roadmap module and starts from every constant in the roadmap's namespace (8 roots). It follows each constant's type, the value of every def, opaque and instance, the constructors of every inductive and the inductive of every constructor and recursor. A theorem contributes its statement only (proof irrelevance), and every proof subterm inside a type or value is replaced by `□` (`Meta.isProof`) before fingerprinting and before following constants, so a reworked proof never counts as a change. Each constant gets FNV-1a-64 plus the length of its full canonical form: uncapped, binder names dropped, universe parameters renamed in order, independent of the toolchain. Constants that differ were pretty-printed with `pp.explicit` in both environments and diffed (`OneSided.ppdiff.txt`, with `enorm→eNorm` and `nnnorm→nnNorm` normalised).

## Counts

| | constants |
|---|---|
| closure at 1b1ccf4 / 31ce06e | 3,099 / 3,102 |
| in both, identical (type and value) | **3,066** |
| in both, differ | 22 |
| reached on one side only | 11 / 14 |
| roots (5 defs, 3 targets) | **8/8 identical** |

## The constants that differ, and why the meaning is unchanged

| Constant(s) | Change | Why the meaning is the same |
|---|---|---|
| `ENorm.enorm` → `ENorm.eNorm`, `NNNorm.nnnorm` → `NNNorm.nnNorm`; hence `ContinuousENorm.mk`, `ESeminormedAddMonoid.mk`, `NNNorm.toENorm`, `egauge`, `MeasureTheory.HasFiniteIntegral`, `eLpNorm'`, `eLpNormEssSup` | structure field renamed | after the renaming, the diff is empty for every one of them |
| `WithTop.instSupSet` | `if ⊤∈S then ⊤ else if BddAbove S then sSup S else ⊤` became `if ⊤∈S ∨ ¬BddAbove S then ⊤ else sSup S` | the same case split |
| `ENNReal.instCompleteLinearOrder` and `_aux_1/4/7/10/13/16/22/26` | `sSup`/`sInf` now packaged as `SupSet`/`InfSet` instances; the partial order is taken through the `inf` side of the lattice rather than the `sup` side | `≤` on ENNReal is identical in both (`ENNReal.instLE`, `instPartialOrder` same). In a complete lattice, `sSup`/`sInf` are the least upper and greatest lower bounds and are forced by `≤`, so the values agree. The two parent paths reach the same partial order |
| `WithTop.lattice`, `GaloisCoinsertion.liftLattice` | lattice rebuilt via `SemilatticeSup.mk` from the `inf` side's order; in `liftLattice` the binders `l`,`u` swap names | the same `sup`, `inf` and order; the types agree up to binder names |
| `Nonneg.conditionallyCompleteLinearOrder._aux_1/_3` (`sSup`/`sInf` on `Set.Ici a`) | guard `s.Nonempty ∧ BddAbove s ∧ …` became `∃ x, IsLUB s x`, with the LUB chosen | they agree on every set: on ∅ both return `a`; on unbounded sets both return the default; otherwise both return the supremum. The edition reaches it only through NNReal → ENNReal, where it is applied to bounded sets |
| `WellFounded.fixF`, `WellFounded.FixGraph(.mk)`, `Acc.rec` (only 1b1ccf4) | `fixF` was `Acc.rec`; it is now the unique element of `FixGraph`, chosen | the same function: both satisfy `fixF_eq`, and that equation determines the function. It is reached only through `Nat.find`, i.e. `Nat.instInfSet` |
| `List.utf8Encode`, `List.toByteArray*`, `ByteArray.*` (only 1b1ccf4) | builds `⟨#[…]⟩` directly instead of `toByteArray` | the same bytes. It is reached only through `autoParam` syntax objects (`Lean.Syntax`), not through mathematics |
| `OrderInfSet*`, `OrderSupSet*`, `WithTop.instInfSet` (only 31ce06e) | reached only in the edition's closure | they exist identically in both versions (the pretty-printed forms are identical); only reachability changed |

Nothing in the roadmap's own definitions, Dirichlet characters, L-functions, `vonMangoldt`, `legendreSym`, `quadraticChar`, `logDeriv`, `Real.log`, `Nat.totient`, `Finset.sum` or `Filter.atTop` differs.

## Files (in the MeaningOps working directory; not published)

- `OneSided.erased.{1b1ccf4,31ce06e}.tsv`: every constant in the closure, as `name, kind, type fp, value fp, root, first parent` (the parent gives a path to the roadmap).
- `OneSided.ppdiff.txt`: explicit pretty-printed diffs of the constants that differ. `OneSided.pp.*.txt`: both sides in full.
- `OneSided.{1b1ccf4,31ce06e}.tsv`: the same closure **without** proof erasure (5,617 / 5,616 constants; 79 differ, the other 32 only in proof terms, e.g. `Nat.primeFactorsList`: `_proof_1` became `Nat.factors_lemma`).
- `tool/Closure.lean`, `tool/compare.py`, `tool/ppdiff.py`, `run.sh NAME TAG`: reproduce.
