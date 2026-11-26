# Predictions: ShortGRH correspondence map at condensed@61d870d

Written 2026-11-26, before computing anything. Each is checked against the result in `shortgrh-61d870d.md`.

Known before predicting (read): the roadmaps cite `[ShortProof], file (decls)` per section, from grh-lean 72fead1 (= upstream's root commit, grh/src → src). There are 4,115 upstream commits from 72fead1 to 61d870d. The 907a395 → 61d870d crosswalk alone shows 735 removed, 260 changed and 7 renamed declarations (of about 26k).

P1. Cited declarations: about 1,500–2,500 distinct names across the 25 roadmaps.
P2. At 61d870d: 55–70% of cited names are unchanged; 10–20% changed (statement text differs); 15–30% gone (removed, or renamed and inlined).
P3. Liveness: at least 90% of cited names that survive are in the closure of `riemannHypothesis` at 61d870d. The roadmaps state the route, so dead cited names should be rare (under 5%).
P4. Most stale (share of sections with a gone or changed citation): NormsOfThetaLiftsAndExchangeIdentities (the ∞ rewrite in 0ea5c74), HolomorphicDiscreteSeriesOfUnitaryGroups (∞), PairsOfFramesAtOnePlace (places, #6836), ThetaLiftChains / DeterminantsOfThetaLiftChains (heavy refactor churn).
P5. Least stale: CrystallineRepresentationsAndKisinModules, PadicComparisonForFunctorCohomology, CohomologyOfFunctorsOnTestRings. These are algebraic leaves with less refactor traffic.
P6. Cheap certificates (elaboration and correspondence) are only possible where Suggested.lean has real signatures. That is mostly OneSidedPrimeSumBounds (113 lines), ZeroFree (106, the pilot), AuxiliaryAlgebraAndAnalysis (204), HolomorphicDiscreteSeries (73) and ThetaFunctionsAndUnits (57). Most others state nothing ("not statable at the pins").
P7. Top 3 for a certified revision: NormsOfThetaLiftsAndExchangeIdentities, HolomorphicDiscreteSeriesOfUnitaryGroups, OneSidedPrimeSumBoundsAndAdmissibleData. Low confidence on #2 and #3. Norms will be stale but expensive to certify, because its Suggested.lean is empty.

---

# Predictions: OneSidedPrimeSumBounds certificates (pilot step 2)

Written 2026-11-26, before porting any statement into the 61d870d environment.

Q1. §0.2 cert 2: `Target → ...`, i.e. the target follows from `New.LFunction_ne_zero_of_primeRemainder_le` at A = 1. The roadmap's `primeRemainder` is its own definition in Suggested.lean, so the cost is proving the two definitions equal. Prediction: they are definitionally or `simp`-equal (the roadmap transcribed upstream's). `[Fact d.Prime]` vs `d : Primes` is a two-line adapter. Confidence 75% that it closes in under 60 lines.
Q2. §6.2(c) cert 3: follows from `eventually_primeRemainder_le_mul_rpow` with ε/2. For large y, C·y^{−1/2+ε/2} ≤ y^{−1/2+ε} because y^{ε/2} ≥ C eventually. Confidence 85% that it closes in under 40 lines on top of Q1's definition bridge.
Q3. The third target `LFunction_ne_zero_of_forall_primeRemainder_le` (6.3 conditional): the same conclusion as upstream's 6.3 theorem, with q₀ = 18480·N and d₀ = 9240·N − 1. Prediction: upstream has a declaration with exactly this hypothesis shape (the `changeLevel` step seen at OneSidedBound.lean:269), and the certificate is a direct application. Confidence 60%; the parameters may differ.
Q4. Textual identity check: the target statements, once ported, elaborate unchanged at 61d870d's pins. Mathlib 1b1ccf4 → 31ce06e drift breaks at most one name. Confidence 80%.
Q5. §3.7: the lost `HasFields` fields are no longer needed downstream (they were pinned for an older consumer). The roadmap's §3.7 claims more than the route now uses, and the gap is harmless (a sufficiency, not a falsity). Confidence 70%.
Q1′ (added before writing the Lean file, after reading the definitions): §0.2 and §6.2(c) are both ↔, not just ←. For §0.2, A·x^{β−1} ≤ x^{β′−1} eventually for any β′ > β, and the conclusion only needs Re ρ > β′ for some β′ in (β, Re ρ). For §6.2(c), 128φ(q₀)+32 ≥ 1. Q3 is revised: upstream has NO standalone 6.3 conditional; the step is inlined in `New.grh` (OneSidedBound.lean:247). Its conclusion is also unconditionally true by `New.grh`, so a proof of Target 3 from `grh` is vacuous. The informative certificate derives it from the criterion, replaying grh's proof (~30 lines).

## Scored (OneSided certificates, computed 2026-11-26)
- Q1 / Q1′: **held.** §0.2 is ↔. The definition bridge took about 40 lines; all five definitions are provably equal.
- Q2: **held.** §6.2(c) is ↔, in about 25 lines.
- Q3: **revised before computing, and the revision held.** There is no standalone counterpart; `target_63_of_criterion` replays `New.grh`.
- Q4: **held.** Text identical; elaborated unchanged at 61d870d with no Mathlib-name breakage.
- Q5: **held.** §3.7's displayed claim is unaffected; the weakened lemma is dead.

---

# Predictions: PR #7266 note (Determinants §§3.4–3.8, SiegelWeil §§6.7/6.9, WeilRep §6.11, Adelic §3.7)

Written before reading the PR diff or the roadmap sections in detail.

R1. §3.8 ← certificate: each of the four 61d870d exchange lemmas specialises to its 72fead1 form with `X := W` (or `stdSpace E m`), `p := Unit`, `A := removePlanes Unit W`. The cost is stating the old forms, which have no Suggested.lean signature; they must be copied from 72fead1 source. Since all carriers exist at 61d870d, the old statements should elaborate verbatim. Confidence 65% for all four within about 150 lines. The main risk is `stdSpace`/`removePlanes` being renamed or removed.
R2. §3.4's `thetaLarge_eq_smul_of_areMatched` is same-meaning (only a set-builder notation change). Confidence 85%.
R3. §§3.6–3.7, SiegelWeil §§6.7/6.9, WeilRep §6.11 and Adelic §3.7 describe a hyperbolic-plane-by-plane descent with an analytic continuation and a functional equation. All of it is gone, replaced by a direct computation on H ⊕ X. No certificate is possible for them (falsity is not in question: the statements are true but unused). The note proposes a rewrite. Confidence 80%.
R4. Some removed statements may still hold and be cheaply derivable at 61d870d. For example, `ThetaLargeVanishes.of_add_plane` may follow from the new "vanishing descends on determinant vectors". Prediction: at most 1 of the ~20 removed names is re-derivable in under 50 lines. Confidence 60%.

## Scored (PR #7266, computed 2026-11-26)
- R1: **held.** All four §3.8 old forms are proved by specialising (X := W / stdSpace / J; A := removePlanes Unit _), in about 40 lines. They needed one pin adaptation, but that was in §3.4, not §3.8.
- R2: **held.** §3.4 is spelling only. The verbatim 72fead1 text no longer elaborates at Mathlib 31ce06e (a predicate used as a Set), which shows that "identical source" is pin-sensitive.
- R3: **held.** Six sections across four roadmaps have no certificate possible. They are off-route or replaced by determinant vectors.
- R4: **held** (0 re-derivable, bound ≤ 1). Old 3.7 (all Schwartz vectors) does not follow from the new descent (determinant vectors only).

---

# Predictions: OneSided revision PR artifact

Written before cloning or reading CONTRIBUTING or the coordination files.

S1. The diff is under 40 changed lines. README: §0.2 statement + citation line, §6.2(c) citation + one sentence, §6.3 one sentence, §3.7 citation edit, §§1.1/3.3/5.1 citation trims. Suggested.lean: the §0.2 hypothesis + 6.2 citation docstring.
S2. Revised Suggested.lean elaborates at the roadmap pins with only `sorry` warnings (confidence 90%). `∃ A : ℝ, ∀ᶠ …, … ≤ A * x ^ (β - 1)` uses nothing new.
S3. Coordination: at least one open TauCeti PR targets §0.2 or §6.2(c) with the current (A = 1) signature. Changing §0.2's signature then affects that PR. The note should say the old form remains a corollary (↔ proven), so no work is wasted. Confidence 60%.
S4. Non-author revision PRs to TauCetiRoadmap exist and were merged after review by the roadmap author (Chris Birkbeck). Typical size is small. Confidence 55%.
S5. The roadmap convention says section numbers are stable ("a section keeps its number"), so no renumbering; and a "Changes" or provenance note may be expected in the README. Confidence 50% on the latter.

---

# Predictions: review of TauCetiRoadmap #3182 (written after reading the diff, before checking any claim)

T1. `Valuation.toAbsoluteValue` is indeed Tau Ceti's, not Mathlib's, at the roadmap pins (Mathlib 1b1ccf4, TauCeti 2fd255d / main). Confidence 75%.
T2. The bijection "finite places of Ω ↔ valuation subrings of Ω other than Ω" is true only because Ω is algebraic over ℚ (higher-rank valuations, or valuations trivial on ℚ, exist on transcendental extensions). Prediction: §1.1 fixes Ω algebraic over a number field, so the claim holds, but the README does not say why. That makes a candidate review point. Confidence 65%.
T3. "[ShortProof] uses valuation subrings": true at 72fead1 (`New.IsPlaceOver` on `ValuationSubring`, `ClosurePlace`). Upstream at head has NOT moved places to absolute values; #6836 is an issue, and its stages are not merged. Confidence 60%.
T4. The umbrella edits are generated by the umbrella script, but hand-committing them in a content PR may conflict with the sync bot. A minor review point. Confidence 50%.
T5. Other ShortGRH roadmaps still say "a place of Ω is a valuation subring" (at least 2 besides Congruences). The PR updates only Congruences, so the family becomes inconsistent. Confidence 55%.
