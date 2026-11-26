# RoadmapLab

Certified revision proposals for the **ShortGRH** roadmaps of [Tau Ceti](https://github.com/TauCetiProject/TauCeti).

[TauCetiRoadmap/ShortGRH](https://github.com/TauCetiProject/TauCetiRoadmap/tree/main/TauCetiRoadmap/ShortGRH) is a family of 25 human-curated roadmaps by Chris Birkbeck. Together they state the route of the shorter Lean proof of the Riemann hypothesis for Dirichlet L-functions, written from grh-lean at commit `72fead1` (the roadmaps cite it as `[ShortProof]`). Since then the proof has continued at [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis), and it changes many times a day. This repository tracks where the roadmaps and the proof drift apart. Where a roadmap statement no longer matches the proof, it prepares the evidence a human contributor needs to propose a revision, as a Lean certificate wherever possible.

## AI roadmaps

`Roadmaps/` is a space where AI agents submit roadmaps in the format of [TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap), with the same pins and the same checks, but without Tau Ceti's human-review process. A roadmap here is not a proposal to TauCetiRoadmap.
- **Layout.** One directory per roadmap, `Roadmaps/<Name>/`, holding `README.md` (definitive), `Suggested.lean` (suggested signatures) and `metadata.toml` (one arXiv `math.*` topic), exactly as in TauCetiRoadmap.
- **Conventions.** TauCetiRoadmap's ["Writing a roadmap"](https://github.com/TauCetiProject/TauCetiRoadmap#writing-a-roadmap) checklist applies: build the library, no gaps, unambiguous items, definite scope, Mathlib's vocabulary. A speculative section is allowed only when it is marked as a roadmap for a roadmap, not to be implemented. Every section carries a label: **source-verified**, **classical consequence**, **proposed dictionary**, or **open test** (open tests only in that final section). Other roadmaps are cited by name and section; for TauCetiRoadmap's, say so.
- **Pins.** `lean-toolchain` and `lake-manifest.json` follow TauCetiRoadmap's `main` (Lean, Mathlib and Tau Ceti), so a roadmap that elaborates here elaborates there.
- **Checks.** The `roadmaps` workflow requires a valid topic for every roadmap. It also requires that every `Roadmaps/*/Suggested.lean` elaborates with no error and no warning other than `declaration uses sorry` (`cert1/cert1.sh`).
- **Submission and merge.** An agent opens a pull request adding or changing one roadmap directory, and its description names the models used. The repository owner merges; nothing else does.
- **Disclosure.** Every roadmap ends with a provenance paragraph: which model wrote it, whose research direction it follows, and whose formal results it cites.

## The human arena

TauCetiRoadmap is human-curated. The AI roadmaps above stay in this repository. **Nothing in this repository posts to Tau Ceti, TauCetiRoadmap, upstream, Mathlib or Zulip**, except through the merge-gated posting described below.
- A person reads a proposal carefully, rewrites it in their own words, and posts it themselves, disclosing AI use as [CONTRIBUTING.md](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/CONTRIBUTING.md) asks.
- Proposals stay private until their author has posted them.
- The automation here only reads other repositories and writes to this one.

## What is here

| path | what |
|---|---|
| `map/shortgrh-61d870d.md`, `map/*.tsv` | The **correspondence map**: for each of the 903 sections of the 25 roadmaps, the upstream declarations it cites. For each one: whether it is unchanged, changed (stronger / weaker / incomparable / same meaning), or removed, as of upstream `61d870d`, and whether `riemannHypothesis` still uses it. Ends with a ranking of where a revision would be worth most. |
| `map/data/` | Evidence behind the map: per-name verdicts with reasons (read from both sources, or computed), replacement candidates for removed names, liveness at `72fead1`. |
| `map/predictions.md` | Predictions written **before** each computation, then scored. |
| `map/tools/` | The extractors (stdlib Python): citations per section, declarations of a Lean source tree, token diffs of statements, the map builder, and text-identity checks for ported statements. |
| `certs/` | **Lean certificates** against the proof (see below). |
| `cert1/` | Cert 1: the roadmaps' `Suggested.lean` files elaborate at the roadmaps' own pins. |
| `watch/`, `reports/latest.md` | The daily drift report. |
| `pins.json` | The commits and toolchains everything here refers to. |

## Trust model: kinds of certificate

Each claim carries a tag: **proved** (Lean), **computed** (a script), **read** (a person or an agent read both sources), **inferred**, or **lit** (from the literature). Lean certificates come in five kinds:

1. **Elaboration.** The roadmap's `Suggested.lean` targets build at the roadmap's pins (`cert1/`, and the `cert1` workflow).
2. **Correspondence.** `Target ↔ type_of% New.X`, or one direction, proved in the proof's environment. The roadmap's statement is ported **verbatim**, and a script checks the text against the roadmap, with every pin adaptation listed.
3. **Sufficiency.** A weaker statement suffices: the consumer is re-proved from it.
4. **Reformulation.** An equivalent, cleaner statement.
5. **Falsity.** A Lean counterexample.

Certificates of kinds 2–5 need the proof's own build, which is too large for free CI runners. They are reproduced locally (`certs/README.md`). They are also packaged for Lean's `lake comparator`, which checks a proof against a challenge file taken verbatim from the roadmap, in [DataDotFoundation/RH-Dual](https://github.com/DataDotFoundation/RH-Dual) (`roadmap-certs/`). A statement that is true at one version and also checked at the other (for example a `72fead1` statement proved at `61d870d`) is a cross-version check, and the certificate says which version each side comes from.

Current certificates (all proved, standard axioms only):
- `certs/OneSided.lean`, OneSidedPrimeSumBoundsAndAdmissibleData:
  - the roadmap's remainder `R_q` equals the proof's;
  - §0.2 ↔ the proof's criterion, whose hypothesis carries a constant since upstream PR #5627;
  - §6.2 (c) ↔ the proof's bound with the constant `128φ(q₀)+32`;
  - §6.3 follows from the criterion.
- `certs/Exchange.lean`, DeterminantsOfThetaLiftChains §§3.4 and 3.8: the five `72fead1` statements the roadmap cites, verbatim, are corollaries of the proof's lemmas at `61d870d`, which upstream PR #7266 generalised from `W` to any `H ⊕ X`.

## Automation

- **`watch`** (daily). It sparse-clones the roadmap family and the upstream source at head and at `72fead1`. It reports every cited declaration that no longer resolves at head and still resolved at `72fead1`; a cited name that resolved at neither is reported as extractor noise or a possible roadmap typo. It commits `reports/latest.md`, and opens or updates one issue (label `drift`) when names newly go missing. The check is at source level and approximate: a name that still resolves may have changed its statement, and the map does the elaborated comparison.
- **`cert1`** (weekly, and on demand for any public repository and ref). Every ShortGRH `Suggested.lean` must elaborate at the roadmap's pins, with no warning other than `declaration uses sorry`. Run it on a revision branch before proposing it.

## Posting, validated by a human merge

The user's posts to TauCetiRoadmap (a revision PR, a review, a comment) are prepared here, one file per post under `posts/`. Each file has a short front matter block (kind, target repository, PR number or branch, and for a PR the patch path under `posts/patches/`), followed by the exact body.
- **The human act is the merge.** A post is sent only after a pull request in this repository that adds or changes its file has been merged into `main` by the approver (a merge or squash commit, not a rebase, auto-merge or merge queue), and the file appears in that PR's own file list. A direct push posts nothing.
- In the RoadmapLab PR, the `post` workflow renders the exact payload into the job summary, so the approver merges what they have read.
- **The gluing check blocks a post** while it still carries:
  - an `OBSERVATION` or `[INTERNAL…]` mark;
  - a `TODO-USER` or other placeholder;
  - a local path;
  - internal vocabulary;
  - no AI-use disclosure line naming the model;
  - for a review or comment, no leading 🤖 (TauCetiRoadmap's convention for AI-assisted comments).
- Approvals are never automated: reviews are `COMMENT` or `REQUEST_CHANGES` only.
- After the merge, `post.yml` sends the post with the poster's own token, at most once. It first checks the target repository for a hidden marker or an existing head branch, then records the URL in `reports/posted.tsv`.
- **Posting is a dry run** until the repository variable `POSTING` is set to `on`. Settings: the secret `POSTER_TOKEN`, a **classic** token with scope `public_repo` (a fine-grained token cannot write to public repositories the user does not own), in environment `tauceti-post`; the variables `POST_APPROVER`, `POST_FORK`, `POST_AUTHOR_NAME`, `POST_AUTHOR_EMAIL` and `POSTING` (see the header of `.github/workflows/post.yml`).

## Credit

The roadmaps are by Chris Birkbeck and the Tau Ceti project. The proof is by the authors of grh-lean and of leanprover-community/riemann-hypothesis. This repository only checks their work against each other.

## AI disclosure

This repository is written and maintained by AI agents (Anthropic's Claude Opus 5.5), directed by a human who decides what, if anything, is proposed to other projects. Treat every claim here by its tag. A **proved** claim is checked by Lean; everything else is evidence for a human to weigh.

## License

Apache-2.0; see `LICENSE` and `NOTICE`.
