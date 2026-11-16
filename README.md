# correlated-credibility

[![Blueprint](https://github.com/mikaelandblom-coder/credible-lean/actions/workflows/blueprint.yml/badge.svg?branch=main)](https://github.com/mikaelandblom-coder/credible-lean/actions/workflows/blueprint.yml?query=branch%3Amain)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24054631.svg)](https://doi.org/10.5281/zenodo.24054631)

A Lean 4 + Mathlib formalization of *Generalized Bühlmann–Straub credibility
theory for correlated data* (M. Andblom, master thesis in actuarial
mathematics, Stockholm University, 2023:2;
[published version](https://urn.kb.se/resolve?urn=urn:nbn:se:su:diva-219872)).

The thesis extends the Bühlmann–Straub model to observations that are
correlated across cohorts within a period. The resulting credibility factor

    zⱼ = (1 − bⱼ) τ² / (τ² + σⱼⱼ² − s²)

uses GLS portfolio weights `b = K⁻¹u / uᵀK⁻¹u`, and reduces to Bühlmann–Straub
when the correlations vanish.

## Status

See **[PROGRESS.md](PROGRESS.md)** for every theorem and whether it's proved
(regenerate with `python3 scripts/progress.py`). All 399 theorems are
proved, with no `sorry`:

- **The thesis, §2.1–2.9** (`Blend`, `Weights`, `Data`, `Core`, `Model`,
  `BuhlmannStraub`, `Balance`, `TwoCohorts`, `Expectation`, `Estimation`),
  proved once at the level of a positive definite `K` (`Core`) with the
  thesis statements as corollaries.
- **Extensions** (not in the thesis): merging two cohorts; cohort-dependent
  series lengths `Tⱼ`, with their estimation and balance; a
  distribution-free moment layer (the second moments are the actual
  covariances of *any* random variables with those moments, and `zⱼ`
  minimises the true MSE), at the level of `K`, for unequal lengths and for
  the thesis model; a shared level within groups, towards hierarchical
  credibility, with its moment layer; forecasting next year's outcome (the
  same `z` is optimal); the best balanced blend and the best balanced
  correction; damping off-diagonal entries; and optimal cohorts as
  intervals (weighted k-means).

**[FINDINGS.md](FINDINGS.md)** lists gaps in the thesis and new results
found while formalizing (items 1–16), e.g. that two correlated cohorts can
push the credibility factor above one.

The **[app](https://mikaelandblom-coder.github.io/credible-lean/app/)**
(preview, `app/`) puts the results to work: pick a world (regions,
volumes, correlation, noise), draw data, and compare fitted credibility
models with the best blend for the true parameters. The fits see only the
data, with no hand-set tuning. Plan and the simulation studies behind it
(findings S1–S29): [`studies/PLAN.md`](studies/PLAN.md),
[`studies/damping-theta.md`](studies/damping-theta.md).

The **[handbook](https://mikaelandblom-coder.github.io/credible-lean/handbook.pdf)**
(draft, `handbook/handbook.tex`) is the short version for practitioners: the
key results with commentary and links to their Lean proofs, no proofs.

The **[blueprint](https://mikaelandblom-coder.github.io/credible-lean/)**
([pdf](https://mikaelandblom-coder.github.io/credible-lean/blueprint.pdf)) is
a condensed §2 of the thesis with every result linked to its Lean statement,
a dependency graph, and the findings as remarks. Its source is
`blueprint/src/content.tex`; CI (`.github/workflows/blueprint.yml`) builds it
and deploys it to GitHub Pages on pushes to `main`. Locally:

    pip install leanblueprint   # needs graphviz and a TeX install (xelatex)
    cd blueprint && leanblueprint pdf && leanblueprint web
    cd .. && python3 scripts/blueprint_check.py
    lake env lean --run scripts/CheckDecls.lean blueprint/lean_decls

## Layout

| Thesis | File |
|---|---|
| §2.1.1 best credibility factor, eq. (7) | `Credibility/Blend.lean` |
| §2.5 inverse-variance and GLS weights, eqs. (23)–(25) | `Credibility/Weights.lean` |
| §2.3 parameters and eq. (16) | `Credibility/Data.lean` |
| §2.5 credibility at the level of `K`: eq. (26), special shapes of `K` | `Credibility/Core.lean` |
| §2.3–2.5 data model, `K`, eqs. (21), (22), (26) | `Credibility/Model.lean` |
| §2.6 Bühlmann–Straub special case, eqs. (28)–(30) | `Credibility/BuhlmannStraub.lean` |
| §2.9 balance | `Credibility/Balance.lean` |
| §2.7 two cohorts, eq. (32) | `Credibility/TwoCohorts.lean` |
| §2.8 expectation of quadratic estimators | `Credibility/Expectation.lean` |
| §2.8 parameter estimation, eqs. (37)–(41) | `Credibility/Estimation.lean` |
| extension: merging two cohorts ([notes](notes/merging-cohorts.md)) | `Credibility/Merging.lean` |
| extension: cohort-dependent lengths `Tⱼ` ([notes](notes/unequal-lengths.md)) | `Credibility/Unequal.lean`, `Credibility/UnequalEstimation.lean` |
| extension: moment layer (distribution-free) | `Credibility/Moments.lean` |
| extension: moment layer for unequal lengths | `Credibility/UnequalMoments.lean` |
| extension: moment layer at the level of `K` and a level covariance `L` | `Credibility/CoreMoments.lean` |
| extension: a shared level within groups, towards hierarchical credibility | `Credibility/Hierarchical.lean`, `Credibility/GroupWeights.lean`, `Credibility/HierarchicalMoments.lean` (its moment layer) |
| extension: damping off-diagonal entries keeps PSD/PD | `Credibility/OffDiagonal.lean` |
| extension: optimal 1-D weighted k-means groups are intervals | `Credibility/KMeans.lean` |
| extension: exposure-weighted pooling is weighted k-means, so optimal cohorts are intervals ([notes](notes/kmeans-bridge.md)) | `Credibility/KMeansBridge.lean` |

Like the thesis, the formalization is **distribution-free**: only first and
second moments are assumed. Most files take the second moments (`τ²`, `σⱼₜ`,
`ρᵢⱼ`) as given numbers; `Moments` proves that they are the actual
covariances of *any* random variables with those moments, and that `zⱼ`
minimises the actual mean squared error (likewise `CoreMoments`,
`UnequalMoments` and `HierarchicalMoments`).

## Later goals

Planned next steps, in order: [`notes/roadmap.md`](notes/roadmap.md). How the
results become something a practitioner can use (the app, and the theorems it
still needs): [`studies/PLAN.md`](studies/PLAN.md).

Done since the thesis: the moment layer (FINDINGS items 11–12: the assumed
moments are consistent exactly when `ρ ⪰ 0`, or the per-period block condition
of item 8 with unequal lengths), cohort-dependent series lengths
([`notes/unequal-lengths.md`](notes/unequal-lengths.md), items 8–10), the
two small lemmas from van Rijn, Weber, Merz (`KMeans`, `OffDiagonal`), the
k-means bridge (item 14), group levels with their moment layer (item 13),
balance (items 15–16), forecasting, the blend through the two-cohort
singularity and against the best linear unbiased predictor, and the price
of ignoring or damping correlation (items 17–20). Open:

- **Choosing cohorts from the data.** Pick the partition into cohorts that
  minimises the total credibility MSE itself, rather than clustering
  credibility estimates by Euclidean distance (as in van Rijn, Weber, Merz,
  *Credibility Clustering for Experience Rating*, arXiv:2611.07110). Known
  so far: for exposure-weighted pooling, and for the blend with a common
  variance, the optimal cohorts are intervals of the sorted levels, so
  dynamic programming finds them exactly; with unequal variances the blend's
  optimum need not be an interval (FINDINGS item 14,
  [`notes/kmeans-bridge.md`](notes/kmeans-bridge.md); one pair:
  [`notes/merging-cohorts.md`](notes/merging-cohorts.md)). Open: how choosing
  cohorts from the same data biases the second-stage estimate (winner's
  curse), and how correlations between cohorts change the optimal partition.
  Starting points: Diao & Weng, *Regression tree credibility model*, NAAJ
  23(2) (2019); Campo & Antonio, *On clustering levels of a hierarchical
  categorical risk factor*, AAS 18(3) (2024), arXiv:2304.09046.
- **Hierarchical credibility.** With group levels (`Hierarchical`,
  `HierarchicalMoments`) a shared level drops out of credibility, the GLS
  weights are two-stage, and `τ̂²` needs pairs within and across groups
  (item 13). Open: consistency of the assumptions, and efficient estimation
  of `φ` from all pairs (PLAN G4).
- **Crossed levels.** Not started in Lean: cohorts in a table (country ×
  car type) sharing a level along both rows and columns, so that sport cars
  in Norway inform sport cars in Sweden. The balanced 2×2 case is worked out
  in [`notes/crossed-2x2.md`](notes/crossed-2x2.md): the best linear
  predictor has one credibility factor per layer (country, type, cell), and
  the thesis blend is the same formula with one common factor.
- **The app** (preview): unequal lengths and group levels in its world and
  fits, then proofs of the gaps it shows to matter (PLAN steps 4–5). Its
  study findings S1–S29 are numerical results in fixed simulated worlds,
  not theorems; they are reported with their world and script so they can
  be rerun. Statements about the best blend with known parameters have
  exact formulas and need no simulation.

## Sharing results

The thesis is the foundation: notation and model for all later work. Plan:

1. **The thesis formalization (§2) is done**, and so are the extensions
   above (v2.0.0). Next, pick further credibility papers to formalize
   (candidates such as Jewell's hierarchical model and Hachemeister's
   regression model), each as its own `Credibility/<Topic>.lean` and
   blueprint chapter in the thesis notation.
2. **Make the repo citable.** `CITATION.cff` (GitHub's "Cite this
   repository"); Zenodo archives each tagged release (concept DOI
   [10.5281/zenodo.24054631](https://doi.org/10.5281/zenodo.24054631),
   always the latest version);
   GitHub topics `credibility-theory`, `actuarial-science`, `lean4`,
   `formalization`.
3. **Preprint on arXiv** (the paper, `paper/outline.md`: the up-to-date
   version of the thesis, explaining the concepts and pointing to the
   handbook for formulas and to Lean for proofs) (q-fin.RM, cross-list stat.AP or math.ST) once the
   findings are proved: the new results (`FINDINGS.md`, merging cohorts),
   stating that every result is machine-checked and linking here. arXiv is
   indexed by Google Scholar; GitHub is not.
4. **Two audiences.** The credibility results to an actuarial journal
   (Scandinavian Actuarial Journal, ASTIN Bulletin, European Actuarial
   Journal, Variance). The formalization itself to CPP/ITP or *Annals of
   Formalized Mathematics*.
5. **General lemmas** stay here. Mathlib asks for hand-written code and
   comments in contributors' own words; the Lean code here is written with
   Claude Code (see "How it was made").

## Thesis source

The original LaTeX is in [`thesis/original/`](thesis/); all equation numbers
here refer to it. It is the final version and matches the published PDF at
<https://urn.kb.se/resolve?urn=urn:nbn:se:su:diva-219872> in text and
equation numbering, plus one later addition from the defence slides: the
two-cohort identity `b₁ = z₁/(z₁ + z₂)` (§2.7.1). The R code and the slides
are there too; see [`thesis/README.md`](thesis/README.md).

**Notation.** The formalization and blueprint follow the thesis notation
with one change: the cohort effect in eq. (15) is written `ηⱼ`
(`μⱼ = μ + τ ηⱼ`) instead of the thesis's `εⱼ`, so it is not confused with
the sampling noise `εⱼₜ` (`μⱼₜ = μⱼ + σⱼₜ εⱼₜ`).

## Building

Lean and Mathlib are pinned (`lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`):

    lake exe cache get   # download prebuilt Mathlib
    lake build

Cloud sessions run `setup-script.sh` (stored in the environment's setup-script
field), which installs elan and fetches the Mathlib cache.
`scripts/fetch_mathlib.sh` is a fallback if `.lake/packages/mathlib` is missing.

`CLAUDE.md` has the working rules: statements are the spec, one `sorry` per
commit, and findings go in `FINDINGS.md`.

## How it was made

The mathematics is Mikael Andblom's: the thesis, which statements to
formalize, the extensions, and the judgement on what the findings mean.
The Lean proofs, blueprint text and scripts were written by Claude Code
(Anthropic) in conversation with the author. Correctness doesn't rest on trusting
that: Lean checks every proof, and CI checks that no proof depends on
`sorry` or extra axioms.

## License

Apache-2.0 (see [LICENSE](LICENSE)), the same as Mathlib. This covers the
Lean code, blueprint, notes and scripts. The thesis source and slides in
`thesis/` are © Mikael Andblom and not covered by it.
