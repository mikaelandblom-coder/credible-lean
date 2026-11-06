# correlated-credibility

A Lean 4 + Mathlib formalization of *Generalized Bühlmann–Straub credibility
theory for correlated data* (M. Andblom, master thesis in actuarial
mathematics, Stockholm University, 2023:2).

The thesis extends the Bühlmann–Straub model to observations that are
correlated across cohorts within a period. The resulting credibility factor

    zⱼ = (1 − bⱼ) τ² / (τ² + σⱼⱼ² − s²)

uses GLS portfolio weights `b = K⁻¹u / uᵀK⁻¹u`, and reduces to Bühlmann–Straub
when the correlations vanish.

## Status

See **[PROGRESS.md](PROGRESS.md)** for every theorem and whether it's proved
(regenerate with `python3 scripts/progress.py`). `Blend` (§2.1.1) is fully
proved; the other files are stated, with some `sorry`s left.

**[FINDINGS.md](FINDINGS.md)** lists gaps in the thesis and new results
found while formalizing, e.g. that two correlated cohorts can push the
credibility factor above one.

A full blueprint (`leanblueprint`, with a dependency graph) is planned once
`Weights` and `TwoCohorts` are done.

## Layout

| Thesis | File |
|---|---|
| §2.1.1 best credibility factor, eq. (10) | `Credibility/Blend.lean` |
| §2.5 inverse-variance and GLS weights, eqs. (51), (58)–(61) | `Credibility/Weights.lean` |
| §2.3–2.5 data model, `K`, eqs. (26), (37), (44), (62) | `Credibility/Model.lean` |
| §2.6 Bühlmann–Straub special case, eq. (73); §2.9 balance | `Credibility/BuhlmannStraub.lean` |
| §2.7 two cohorts, eq. (81) | `Credibility/TwoCohorts.lean` |

Second moments are taken as given numbers. A probabilistic layer showing that
they are actual covariances of random variables is a later goal.

## Thesis source

The original LaTeX is in [`thesis/original/`](thesis/); all equation numbers
here refer to it.

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
