# correlated-credibility

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24054632.svg)](https://doi.org/10.5281/zenodo.24054632)

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
(regenerate with `python3 scripts/progress.py`). All 54 theorems are
proved, with no `sorry`: §2.1–2.8 of the thesis (`Blend`, `Weights`,
`Model`, `BuhlmannStraub`, `TwoCohorts`, `Estimation`) and the merging
extension (`Merging`).

**[FINDINGS.md](FINDINGS.md)** lists gaps in the thesis and new results
found while formalizing, e.g. that two correlated cohorts can push the
credibility factor above one.

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
| §2.3–2.5 data model, `K`, eqs. (16), (21), (22), (26) | `Credibility/Model.lean` |
| §2.6 Bühlmann–Straub special case, eqs. (28)–(30); §2.9 balance | `Credibility/BuhlmannStraub.lean` |
| §2.7 two cohorts, eq. (32) | `Credibility/TwoCohorts.lean` |
| §2.8 parameter estimation, eqs. (37)–(41) | `Credibility/Estimation.lean` |
| extension: merging two cohorts ([notes](notes/merging-cohorts.md)) | `Credibility/Merging.lean` |

Second moments are taken as given numbers.

## Later goals

Once the thesis results are proved:

- **Probabilistic layer.** Show that the second moments are actual
  covariances of random variables.
- **Cohort-dependent series length.** In practice cohorts have data series
  of different lengths, so replace the common horizon `T` with a
  cohort-dependent `Tⱼ` (index sets `Tⱼ ⊆ T`). Correlations then only act
  on the periods two cohorts share. Not in the thesis.
- **Choosing cohorts from the data.** Pick the partition into cohorts that
  minimises the total credibility MSE itself, rather than clustering
  credibility estimates by Euclidean distance (as in van Rijn, Weber, Merz,
  *Credibility Clustering for Experience Rating*, arXiv:2611.07110).
  Questions: when do the two criteria agree; how does choosing cohorts
  from the same data bias the second-stage estimate (winner's curse); how
  do correlations between cohorts change the optimal partition (a first
  answer for one pair: [`notes/merging-cohorts.md`](notes/merging-cohorts.md)). Starting
  points: Diao & Weng, *Regression tree credibility model*, NAAJ 23(2)
  (2019) (greedy splits on a credibility loss); Campo & Antonio, *On
  clustering levels of a hierarchical categorical risk factor*, AAS 18(3)
  (2024), arXiv:2304.09046.
- **Small lemmas from that paper.** (a) Optimal one-dimensional weighted
  k-means groups are contiguous intervals of the sorted values, so they
  can be found exactly by dynamic programming (Fisher 1958; Nielsen & Nock,
  arXiv:1403.2485). Possibly worth contributing to Mathlib. (b) Multiplying the
  off-diagonal entries of a covariance matrix `τ` by `ρ ∈ [0,1]` keeps it
  positive semidefinite, and positive definite if `ρ < 1` and the diagonal
  is positive.

## Sharing results

The thesis is the foundation: notation and model for all later work. Plan:

1. **The thesis formalization (§2) is done.** Next, possibly the
   probabilistic layer (see "Later goals"); then pick further credibility papers to formalize
   (candidates such as Jewell's hierarchical model and Hachemeister's
   regression model), each as its own `Credibility/<Topic>.lean` and
   blueprint chapter in the thesis notation.
2. **Make the repo citable.** `CITATION.cff` (GitHub's "Cite this
   repository"); Zenodo archives each tagged release (concept DOI
   [10.5281/zenodo.24054632](https://doi.org/10.5281/zenodo.24054632),
   always the latest version);
   GitHub topics `credibility-theory`, `actuarial-science`, `lean4`,
   `formalization`.
3. **Preprint on arXiv** (q-fin.RM, cross-list stat.AP or math.ST) once the
   findings are proved: the new results (`FINDINGS.md`, merging cohorts),
   stating that every result is machine-checked and linking here. arXiv is
   indexed by Google Scholar; GitHub is not.
4. **Two audiences.** The credibility results to an actuarial journal
   (Scandinavian Actuarial Journal, ASTIN Bulletin, European Actuarial
   Journal, Variance). The formalization itself to CPP/ITP or *Annals of
   Formalized Mathematics*, and announced on the Lean Zulip.
5. **General lemmas upstream** as Mathlib PRs (see "Small lemmas" above).

## Thesis source

The original LaTeX is in [`thesis/original/`](thesis/); all equation numbers
here refer to it. It is the final version and matches the published PDF at
<https://urn.kb.se/resolve?urn=urn:nbn:se:su:diva-219872> in text and
equation numbering, plus one later addition from the defence slides: the
two-cohort identity `b₁ = z₁/(z₁ + z₂)` (§2.7.1). The R code and the slides
are there too; see [`thesis/README.md`](thesis/README.md).

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

## License

Apache-2.0 (see [LICENSE](LICENSE)), the same as Mathlib. This covers the
Lean code, blueprint, notes and scripts. The thesis source and slides in
`thesis/` are © Mikael Andblom and not covered by it.
