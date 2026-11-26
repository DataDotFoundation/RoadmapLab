# ShortGRH correspondence map at condensed@61d870d

RoadmapLab, 2026-11-26. Roadmaps: TauCetiRoadmap `@87991688`, `TauCetiRoadmap/ShortGRH/` (25 roadmaps), written from grh-lean `72fead1`. Upstream snapshot: leanprover-community/riemann-hypothesis `61d870d`. Nothing here has been posted anywhere.
Predictions, written before computing, are in `predictions.md` and scored at the end of this page.

## Files

| file | contents |
|---|---|
| `shortgrh-61d870d.tsv` | **one row per roadmap section** (903 sections plus 32 Suggested.lean targets). Columns: match, live61, changed, vanished, route_change, offroute, detail |
| `shortgrh-61d870d-names.tsv` | one row per (section, cited name). Columns: Librarian class, effective class, live72, live61, note (replacement or PR) |
| `src-verdicts.tsv` | source-level verdict for every name the Librarian classes `same-prefix` or `changed`. The Librarian merges it into its staleness table as `src_class` |
| `tools/` | `citations.py` (per-section `[ShortProof]` lines), `leandecls.py` (source statements), `changekind.py` (token diff), `replace.py` (replacement candidates), `final.py` (builder) |

Raw intermediate files are in `map/data/`: substantive-judged.tsv, plumbing-judged.tsv, manual-judged.tsv and replace.tsv.

## Method

1. **Citations** (computed). Each numbered section ends with `[ShortProof], file (decls)`. I parsed 1,117 such lines, giving 6,518 distinct names in 903 sections. The 32 Suggested.lean targets come from MeaningLib's matcher.
2. **Class** (computed). The source is the Librarian's `shortgrh-staleness-61d870d.tsv`, the crosswalk from condensed@686902a to condensed@61d870d. condensed@686902a is the same src tree as 72fead1:grh/src, so this is the roadmaps' exact edition. It is the authority for removed/renamed and for the PR that removed each name.
   - Its skeletons were cut at 600 characters. I reported this and the Librarian fixed it; long statements now appear as `same-prefix`.
3. **Did the statement change?** (computed, then read). I compared source token diffs of the statements at 72fead1 and 61d870d.
   - Instance-only and cosmetic diffs count as same-meaning (computed).
   - 75 substantive diffs and 16 elaboration-only diffs were read by two reader agents: 74 opened both sources, 17 were judged from the extract.
   - I read the 6 renames myself.
   - Verdicts compare the upstream declaration with the old one: **stronger** means new ⇒ old; **weaker** means old ⇒ new, not conversely.
4. **Replacements for removed names** (computed candidates).
   - Statement fingerprint at 61d870d: theorems with a non-trivial type only, because short def types collide (`dualResolutionFactor` vs `vacuumRoot`).
   - The same short name in another namespace.
   - The nearest surviving consumer at 72fead1, found by walking up the dependency graph of condensed@686902a.
   - The PR kind (inline / drop-direction / conjunction / method / doc) from the Librarian's bisection.
5. **Liveness** (computed). `live72` is the closure of `riemannHypothesis` in condensed@686902a. `live61` is the Librarian's `live-61d870d.txt`.

**Section match** (orientation: the upstream declaration compared with the section's statement):
- **same**: every cited name is same or same-meaning.
- **stronger** / **weaker**: at least one cited name changed in that direction, and none vanished.
- **partial**: some cited names vanished and others survive, or a change is incomparable.
- **none**: every cited name vanished. `detail` names the consumer that absorbed the argument.

Caveat: for a `def`, "same" compares the type and not the body. Bodies were read only for the 91 judged names.

## Results

**Names** (6,724 Librarian rows, aux excluded):
- 6,079 same.
- 225 same-meaning.
- 15 stronger, 11 weaker, 2 incomparable.
- 257 vanished:
  - 112 were **already dead at 72fead1**: off-route citations that upstream deleted as dead code.
  - 125 were absorbed into a surviving consumer (inlined, or a new argument in the consumer).
  - 5 were split into existing lemmas (conjunctions).
  - 5 lost one direction of an `iff`.
  - 10 have no survivor: the method was replaced (PR #6319, #7266).

**Sections** (903):
- 768 same, 9 stronger, 7 weaker, 111 partial, 8 none.
- 56 sections cite a name that was **live at 72fead1 and is gone** (route change).
- 73 sections cite a name that was dead at 72fead1 and is gone (off-route citation).
- 8 sections cite a surviving name that is no longer live: Crystalline 2.1, Galois 8.4, Norms 1.4, OneSided 1.2 / 3.7 / 6.4, SiegelWeil 6.8, ZeroFree 1.2.

**Per roadmap** (non-same sections; rc = sections with a route change, off = sections with an off-route citation):

| roadmap | sec | same | str | weak | partial | none | rc | off | Suggested targets |
|---|---|---|---|---|---|---|---|---|---|
| WeilRepresentationsOnBanachSpacesOfData | 62 | 42 | 0 | 0 | 19 | 1 | 9 | 15 | 0 |
| SiegelWeilAndRallisFormulasOnUnitaryGroups | 38 | 29 | 0 | 0 | 7 | 2 | 9 | 1 | 1 (def) |
| ThetaFunctionsAndUnitsOfCMLattices | 23 | 14 | 0 | 3 | 6 | 0 | 6 | 1 | 1 |
| OneSidedPrimeSumBoundsAndAdmissibleData | 26 | 17 | 3 | 1 | 5 | 0 | 2 | 5 | 3 thm + 5 def |
| DivisibilityOfThetaDerivatives | 34 | 23 | 1 | 0 | 10 | 0 | 3 | 7 | 0 |
| IdelicReciprocityCountsAndCyclotomicClassGroups | 42 | 33 | 0 | 0 | 9 | 0 | 3 | 6 | 2 (defs) |
| CrystallineRepresentationsAndKisinModules | 36 | 28 | 0 | 0 | 8 | 0 | 3 | 5 | 0 |
| DeterminantsOfThetaLiftChains | 36 | 32 | 1 | 0 | 2 | 1 | 3 | 0 | 0 |
| SecondMomentsOfPoincareSeries | 44 | 37 | 0 | 0 | 7 | 0 | 2 | 6 | 0 |
| PairsOfFramesAtOnePlace | 31 | 25 | 0 | 0 | 6 | 0 | 2 | 4 | 0 |
| NormsOfThetaLiftsAndExchangeIdentities | 39 | 34 | 0 | 0 | 5 | 0 | 1 | 4 | 0 |
| ThetaLiftChainsAndTheSeesawIdentity | 46 | 41 | 0 | 0 | 5 | 0 | 1 | 4 | 0 |
| (13 others) | | | | | | | ≤2 | ≤3 | |
| PadicComparison / AuxiliaryAlgebra | 25 / 7 | all same | | | | | 0 | 0 | 0 / 12 thm |

### Upstream 0ea5c74 (PR #7266, the ∞ rewrite: "prove the value of the equal-rank theta ratio directly on H ⊕ X")
It hits:
- **DeterminantsOfThetaLiftChains**:
  - §3.6 (descent by removing hyperbolic planes) is partial, absorbed.
  - §3.7 (vanishing descends along hyperbolic planes) is none.
  - §3.8 is **stronger**: the four exchange lemmas now hold for any `X` with a base-adapted splitting, and the old `stdSpace`/`J` form is the special case (read).
- **SiegelWeilAndRallis** §§6.7 and 6.9 (the real cone integral, the Tate vector, the continuation and functional equation) are removed.
- **WeilRepresentations** §6.11 (real zero terms) is removed.
- **AdelicUnitary** §3.7 (smooth sections of the isotropic orbit) is removed.

**NormsOfThetaLiftsAndExchangeIdentities cites no file this commit touched.** Its drift is 6 names gone: 5 were already dead at 72fead1 (§§2.2, 2.5 ×2, 5.4, 7.3), and `weylNormSq_firstFactor_le` (§7.2) was inlined (PR #7716). Everything else is cosmetic or drops `[WeilData E]`. The premise that Norms was affected does not hold, and it has been withdrawn.

### OneSidedPrimeSumBoundsAndAdmissibleData, next to the pilot (read)
- **§0.2 / the Suggested target `LFunction_ne_zero_of_primeRemainder_le`** (the one-sided criterion):
  - At 72fead1 the bound hypothesis was `∀ᶠ x, primeRemainder d q₀ x ≤ x^(β−1)`. At 61d870d it is `∃ A, ∀ᶠ x, primeRemainder d q₀ x ≤ A * x^(β−1)`.
  - So the **hypothesis was weakened, and the theorem strengthened**. The old statement is the case A = 1.
  - Commit `f2201365d2d` (Vladimir Gurevich, 2026-11-26), "refactor: carry the leading constant through Landau's criterion": upstream PR #5627, merged in batch PR #5636 (`fc32f25`). It also changes `IsPolar.landau` (Lib/Analytic/Landau.lean) to take a prefactor.
  - MeaningLib's matcher agrees: same conclusion, 5 of 6 hypotheses equal. Two remaining questions are cert-2 material: whether the roadmap's `[Fact d.Prime]` and the proof's `d : Primes` encode the same thing, and whether the two `primeRemainder` definitions are equal.
- **§6.2 (c) / the Suggested target `eventually_primeRemainder_le_rpow`**:
  - The same PR replaced it with `New.eventually_primeRemainder_le_mul_rpow`: `R ≤ (128·φ(q₀)+32)·y^(−1/2+ε)`. That is weaker by a constant.
  - The roadmap's form still follows: apply the new lemma with ε/2 and absorb the constant for large y. This is a short sufficiency certificate (inferred; not yet in Lean).
- **§3.7 is weaker** (read). `eventually_exists_data_of_isAdmissibleData` now produces data whose `HasFields` no longer pins five fields to the admissible tuple (`bPlaces`, `levelPrime`, `piMBar`, `N`, `piN`). No replacing lemma was found. Its consumer is now dead (live61 = partly). This needs a reading before any note.
- §§1.1, 3.3 and 5.1 cite only lemmas that were already dead at 72fead1: off-route citations, with no route change.

## Ranking: where a certified revision is worth most

Score: (route-change + weaker/incomparable sections) × cheapness. Cheapness counts three things: statable Suggested targets (cert 1 already passes for all 25, per MeaningLib), stronger-direction changes (a one-line `example`), and drift that comes from one PR.

1. **OneSidedPrimeSumBoundsAndAdmissibleData.** 2 route-change sections, 1 weaker, 3 stronger, 5 off-route.
   - Cheapest: 3 sorry'd theorem targets with matched upstream counterparts.
   - Cert 2 for §0.2 is `New.LFunction_ne_zero_of_primeRemainder_le` at A = 1, i.e. `example : target` by applying the new theorem to `⟨1, by simpa⟩`, after the `primeRemainder`/`Primes` port.
   - Cert 3 for §6.2(c) is absorbing the constant.
   - §3.7 (weaker) is the one item that needs real reading.
   - It sits next to the pilot. Hand it to RH-Dual/MeaningLib as pilot step 2 rather than run it in parallel.
2. **DeterminantsOfThetaLiftChains §§3.4–3.8.** All of it comes from one commit, 0ea5c74 / PR #7266.
   - §3.8 is stronger: certificate = `example : old ← New.Exchange.exists_equalRankThetaRatio_*`, specialising `X := W`, `p := Unit`, `A := removePlanes Unit W` (the reader agent read this; Lean not yet run).
   - §§3.6–3.7 describe a descent along hyperbolic planes that the proof no longer takes. The revision is to replace them with the H ⊕ X argument.
   - No Suggested targets, so the targets must be stated first (moderate cost).
   - It also carries the knock-on to SiegelWeil §§6.7 and 6.9, WeilRep §6.11 and Adelic §3.7: one note can cover all four roadmaps.
3. **ThetaFunctionsAndUnitsOfCMLattices.** The largest share of non-same sections (9/23): 6 route changes and 3 weaker.
   - Almost all of it is PR #6517, "prove local integrality of CM theta sections from a height bound".
   - The §3 integrality principle moved from `HasIntegralValues` to a naive-height bound.
   - §5.3 complex multiplication lost the ideal 𝔠 (`IsComplexMultiplicationData` is weaker; nothing replaces the Ω𝔠²/N(𝔠) identity).
   - §2.2 lost a conjunct.
   - Cheaper than SiegelWeil or WeilRep because the drift has a single cause and there is 1 Suggested target. But the weaker §5.3 makes it a reformulation, not a correspondence.

Not ranked:
- **WeilRepresentationsOnBanachSpacesOfData** and **SiegelWeilAndRallis** have the most stale sections, but no theorem targets and the method was replaced (PR #6319, the neighbour-lattice count is gone; PR #7266). They are revision notes, not certificates.
- **Norms** does not hold up: 1 route-change section, the rest cosmetic.

## Predictions, scored

- P1, 1,500–2,500 cited names: **wrong** (6,518).
- P2, 55–70% unchanged: **wrong** (about 94% same or same-meaning; 4% gone).
- P3, ≥ 90% of survivors live: **right** (8 sections cite a surviving dead name).
- P4, Norms / Holomorphic / PairsOfFrames / ThetaLiftChains / Determinants the most stale: **mostly wrong**. The most stale are WeilRep, SiegelWeil and ThetaFunctions; Holomorphic is near the bottom.
- P5, Crystalline / Padic / CohomologyOfFunctors the least stale: **2 of 3** (Padic and Cohomology yes; Crystalline has 8 partial sections, 5 of them off-route).
- P6, cheap certificates only where Suggested has signatures: **right**, with a caveat. Cert 1 passes everywhere, but only 3 roadmaps besides the pilot have theorem targets (OneSided 3, Auxiliary 12, plus 1 each in Abelian, Holomorphic and ThetaFunctions).
- P7, top 3 Norms / Holomorphic / OneSided: **1 of 3** (OneSided). The Norms premise failed, and Holomorphic has almost no drift.

## Open items

- 32 names in src-verdicts.tsv are `unknown`: my source parser missed one side. For these the Librarian class stands.
- The 54 elaboration-only changes not in the plumbing reading list were labelled same-meaning from skeleton diffs (computed, not read).
- Certificates themselves are not started. The ranking is the input for that.
