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

---

# Predictions: theta lifts ↔ number fields, and "one Giambelli determinant" (2026-11-27, before computing)

G1. Bridge declarations at 61d870d: declarations whose direct dependencies include both a theta-lift constant and a number-field constant. Expect 300–900. Most of them (≥60%) sit in Lib/Weil, Lib/SiegelWeil and New/Determinant; fewer than 10% are in New/Reduction.
G2. Kinds: Hecke characters / tame characters dominate (≥40% of bridges), then adeles and places; class groups and units are rare (<10%).
G3. Liveness: ≥90% of bridges are live from riemannHypothesis.
G4. Weighted footprint (line spans of bridge declarations): 15k–40k lines, i.e. 5–15% of the proof's live lines.
G5. Giambelli relevance: bridges that also mention `Matrix.det` are 5–15% of bridges, concentrated in New/Determinant/Chain and the Gram determinants. None mention Schur functions in h or e (consistent with RH-Dual's 0/11).
G6. Savings: an honest upper bound for what a "single Giambelli determinant" reformulation could replace is the determinant-chain machinery (New/Determinant, ~10–20k lines). The expected realised saving with what is known today is ~0. That is a motivation for research, not a projected saving.

## Scored (theta lifts ↔ number fields; computed at 61d870d)
- G1: **held.** 591 live bridges (604 in all). 65% are in Lib/Weil, Lib/SiegelWeil and New/Determinant; 0 are in New/Reduction.
- G2: **partly wrong.** Hecke characters appear in 37% of bridges (220/591), not ≥40%. Places, adeles and conductors are near-universal, because the adelic groups carry them structurally; L-values appear in 63.
- G3: **held.** 98% of bridges are live.
- G4: **slightly off.** 14,560 lines, 4.9% of 294,471 live lines (predicted 15–40k, 5–15%).
- G5: **held.** 66 bridges (11%) use `Matrix.det`, 31 of them in New/Determinant. No Schur function in h or e anywhere.
- G6: **held.** The upper bound is New/Determinant at 13,759 live lines; the expected realised saving is ~0 (RH-Dual 0/11).
- Unpredicted: the bridges form ONE line of reasoning, a connected component of 581 of 591 bridges.
- Revision after RH-Dual's review (Θ 28 → 41, adding the theta kernels and the chain `lowerChain`/`Θ`): 741 live bridges, 18,445 lines (6.3%; G4 now **held**); 82 with det (11%; G5 held); 10 bridges in New/Reduction via the chain (G1's "<10% in New/Reduction" still held, at 1.3%); one component of 731 of 741.

---

# Predictions: implementing ThetaLiftsAsOneGiambelliDeterminant (2026-11-27, upstream 7c4ccbd, before any task runs)

Known before predicting (read at 7c4ccbd):
- `quotientRatio i (i+n) = lRatioProd (quotientPair n).character … (ϑ^n)` does not depend on i (`quotientRatio_add_eq_lRatioProd`), so the moduli are Toeplitz above the diagonal: C_n := quotientRatio 0 n.
- They enter `exists_inner_weightedChain_eq` (Chain/NormOfChain.lean) as the product ∏_{0<i<j≤m} quotientRatio i j = ∏_n C_n^{m−n}.

T1. Every use of `quotientRatio` (and every one of the 82 `Matrix.det` bridges) is a product over pairs or a single-lift Gram determinant; none is a determinant of a matrix whose entries are C_{j−i}. Confidence 85%. If this holds, a Toeplitz/Jacobi–Trudi structure is absent at the level of the chain norms.
T2. The product ∏_{i<j} C_{j−i} is not a principal specialisation of a Schur function. That would need C_n = g(a+n)/g(n) for one fixed g (q-number type); the C_n are products of ratios of Hecke L-values over 1 ≤ z ≤ t. Confidence 70%.
T3. The generic algebra holds: a one-sided symbol with c₀ = 1 gives (h, e) with H(X)E(−X) = 1, and RMTlib `giambelli_jt'` turns its Toeplitz minors into hook determinants. Lean in ≤ 150 lines on top of RMTlib. Confidence 90%. It is informative only if T1 or T2 comes out positive.
T4. The m = 2 Plücker test cannot be stated with actual quantities before amplitudes τ_λ are defined. The expected outcome is an obstruction from the scalar (non-additive) exchange law. Confidence 60%.

## Scored (implementation, upstream 7c4ccbd)
- T1: **held** (85%). None of the 82 det bridges and no use of `quotientRatio` is a determinant with Toeplitz entries: 45 χ(det g)-type, 5 minors of a variable matrix, 4 structural, 1 Gram, 27 with no det in their own source (RH-Dual#268, computed and read).
- T2: **held** (70%). P_m = ∏ C_n^{m−n} is a single Schur function only at m = 2 (P_2 = s_(1)). P_3 = s_4 + 2s_31 + s_22 + s_211; P_4 has 33 terms, P_5 has 510 (computed). There is no g(a+n)/g(n) form (inferred). Not predicted: c₀ ≠ 1 in general, and the symbol is two-sided as defined (proved by RH-Dual).
- T3: **held** (90%). `giambelli_toeplitz`, RMTlib 8057de4, about 15 lines on top of #181.
- T4: **not run.** Its premise (a determinant structure from T1/T2) failed, and τ_λ remain undefined; candidates are the turn ratios or T1's 5 minor-polynomial bridges.

---

# Predictions: next steps after L ≈ 0 (2026-11-27, upstream 7c4ccbd)

Known before predicting (read): `turnRatio i j = lRatioProd (χ_{i+1} χ_{j+1}) t (ϑ^{j+1})`. The character depends on i + j (geometric progression) and the twist on j, so the ratio is a function of (i + j, j), not of the content j − i.

D1. Lean, at upstream 7c4ccbd, on upstream's own `TwoGridPath`: (a) `Γ.squares` is a lower set of ℕ × ℕ in the orientation of `squares_last`; (b) `Γ.diagonalIndex = #{i | (i, i) ∈ Γ.squares}`, the Durfee rank; (c) a turn adds an addable corner. (a) and (c) will be proved within ~300 lines (80%); (b) will need an orientation fix or a restatement (50%).
T6. Up to the normalisation the proof allows (a constant and a power of N(Q), uniform over the cells), `turnRatio i j` is NOT separable as A(i)·B(j), and NOT of content type f(j − i). Confidence 80%. At the trivial twist ϑ = 1 it is Hankel (a function of i + j only) (read).
- D1: **held, better than predicted.** (a), (b) and (c) are all proved in 195 lines, with (d) (injectivity) as a bonus. (b) needed **no** orientation fix: the 50% hedge was too cautious. The lower set holds in the plain componentwise order. File RoadmapLab certs/GridDiagram.lean, checked against upstream 7c4ccbd; axioms propext, Classical.choice, Quot.sound.
- T6: **held** (80%). turnRatio i j = G(i+j, j+1) is none of separable, content or Hankel for any nontrivial twist (computed, free model, m ≤ 6; RH-Dual#269). The proof's normalisation is per cell, not uniform. All three properties hold trivially at ϑ = 1, where every turn ratio is 1 (proved).
