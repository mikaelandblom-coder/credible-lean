# correlated-credibility

[![Blueprint](https://github.com/mikaelandblom-coder/credible-lean/actions/workflows/blueprint.yml/badge.svg?branch=main)](https://github.com/mikaelandblom-coder/credible-lean/actions/workflows/blueprint.yml?query=branch%3Amain)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24054631.svg)](https://doi.org/10.5281/zenodo.24054631)

Credibility theory for data that are correlated across cohorts, with every
result machine-checked in Lean 4 + Mathlib. It starts from the master thesis
*Generalized Bühlmann–Straub credibility theory for correlated data*
(M. Andblom, actuarial mathematics, Stockholm University, 2023:2;
[published version](https://urn.kb.se/resolve?urn=urn:nbn:se:su:diva-219872))
and extends it.

Cohorts observed in the same period are often correlated (a common market,
a common claims climate). The thesis shows how to keep the credibility blend
`zⱼ μ̂ⱼ + (1 − zⱼ) μ̂` optimal anyway: the portfolio mean `μ̂` uses GLS weights
`b = K⁻¹1 / 1ᵀK⁻¹1`, and

    zⱼ = (1 − bⱼ) τ² / (τ² + σⱼⱼ² − s²),

which reduces to Bühlmann–Straub when the correlations vanish.

## Main results

- **Correlation can push `z` above one.** For two cohorts, `z₁ > 1` exactly
  when `σ₁ < σ₂ρ`, whatever `τ²`. The blend itself stays continuous through
  the point where `z₁` changes sign (findings 3, 17).
- **Distribution-free, for real.** Any random variables with the assumed
  first and second moments give these covariances, and `zⱼ` minimises the
  actual mean squared error. Such variables exist exactly when the
  correlation matrix is positive semidefinite (finding 11).
- **The cost of ignoring correlation is bounded.** Using Bühlmann–Straub on
  correlated cohorts costs at most a factor `1/(1 − δ²)` in mean squared
  error, where `δ` measures how far the correlations are from zero
  (findings 19, 20).
- **Choosing cohorts.** For exposure-weighted pooling, the optimal cohorts
  are intervals of the sorted levels, so dynamic programming finds them
  exactly (finding 14).
- **Beyond the thesis:** cohorts observed over different periods, shared
  levels within groups (towards hierarchical credibility), balance, and
  forecasting.

The full list, including where the thesis needed an extra hypothesis, is in
**[FINDINGS.md](FINDINGS.md)**.

## Where to read

| | For | |
|---|---|---|
| **[Paper](https://mikaelandblom-coder.github.io/credible-lean/paper/)** ([pdf](https://mikaelandblom-coder.github.io/credible-lean/paper.pdf)) | understanding: the up-to-date thesis, concepts and intuition (draft) | `paper/` |
| **[Handbook](https://mikaelandblom-coder.github.io/credible-lean/handbook.pdf)** | using: the formulas, with notes on when to use them (draft) | `handbook/` |
| **[App](https://mikaelandblom-coder.github.io/credible-lean/app/)** | seeing: pick a world, draw data, compare fitted models with the best blend (preview) | `app/` |
| **[Thesis proposal](https://mikaelandblom-coder.github.io/credible-lean/thesis-proposal.pdf)** | a master thesis: extensions of the 2023 thesis to derive, review and test on card data (draft for discussion) | `studies/thesis-topics/` |
| **[Blueprint](https://mikaelandblom-coder.github.io/credible-lean/)** ([pdf](https://mikaelandblom-coder.github.io/credible-lean/blueprint.pdf)) | checking: every statement linked to its Lean proof, with a dependency graph | `blueprint/` |

The handbook and paper link each result to its Lean proof.

## Status

Every result is proved; there is no `sorry`. **[PROGRESS.md](PROGRESS.md)**
lists each theorem (regenerate it with `python3 scripts/progress.py`). CI
checks that no proved result depends on `sorry` or on axioms beyond Lean's
standard three.

Next steps: [`notes/roadmap.md`](notes/roadmap.md) (the mathematics) and
[`studies/PLAN.md`](studies/PLAN.md) (the app and its simulation studies).

## Repository

| Path | Contents |
|---|---|
| `Credibility/` | the Lean files: the thesis §2.1–2.9, then the extensions (the list from thesis section to file is in [`CLAUDE.md`](CLAUDE.md)) |
| `FINDINGS.md` | gaps in the thesis and new results, a dated log |
| `paper/`, `handbook/`, `blueprint/` | the three documents above (LaTeX) |
| `app/` | the app (`engine.js`, Node tests, `index.html`) |
| `notes/` | working notes on extensions, and the roadmap |
| `studies/` | the app plan, simulation studies, literature |
| `thesis/` | the original thesis source, R code and slides ([README](thesis/README.md)) |
| `scripts/` | progress and consistency checks used by CI |

Results are proved once at the level of a positive definite covariance
matrix `K` (`Core`), and each model (the thesis model, unequal lengths,
group levels) supplies only its `K`. The thesis statements are kept as
corollaries with their equation numbers.

**Thesis source.** `thesis/original/` is the final version: it matches the
published PDF in text and equation numbering, and adds one identity from the
defence slides, `b₁ = z₁/(z₁ + z₂)` (§2.7.1). All equation numbers here refer
to it. One change of notation: the cohort effect in eq. (15) is written `ηⱼ`
(`μⱼ = μ + τ ηⱼ`) instead of `εⱼ`, so that it is not confused with the noise
`εⱼₜ`.

## Building

Lean and Mathlib are pinned (`lean-toolchain`, `lakefile.toml`,
`lake-manifest.json`):

    lake exe cache get   # download prebuilt Mathlib
    lake build

Blueprint and checks (needs graphviz and a TeX install with xelatex):

    pip install leanblueprint
    cd blueprint && leanblueprint pdf && leanblueprint web && cd ..
    python3 scripts/blueprint_check.py
    lake env lean --run scripts/CheckDecls.lean blueprint/lean_decls

App tests: `node --test app/engine.test.js`.

CI (`.github/workflows/blueprint.yml`) builds the blueprint, handbook and
paper, tests the app, and deploys all four to GitHub Pages on every push to
`main`. Cloud sessions run `setup-script.sh`, which installs elan and
fetches the Mathlib cache; `scripts/fetch_mathlib.sh` is the fallback. [`CLAUDE.md`](CLAUDE.md)
has the working rules.

## Citing

Use GitHub's "Cite this repository" ([`CITATION.cff`](CITATION.cff)), or the
Zenodo concept DOI
[10.5281/zenodo.24054631](https://doi.org/10.5281/zenodo.24054631), which
always resolves to the latest release. Please cite the thesis as well.

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
