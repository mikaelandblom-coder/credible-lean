# correlated-credibility

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
(regenerate with `python3 scripts/progress.py`). `Blend` (§2.1.1) is fully
proved, and so are `Weights` and `TwoCohorts`; `Model` and
`BuhlmannStraub` are stated, with `sorry`s left.

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

Second moments are taken as given numbers. A probabilistic layer showing that
they are actual covariances of random variables is a later goal.

## Thesis source

The original LaTeX is in [`thesis/original/`](thesis/); all equation numbers
here refer to it. It is the final version, identical
in text and equation numbering to the published PDF at
<https://urn.kb.se/resolve?urn=urn:nbn:se:su:diva-219872>. The R code and the
defence slides are there too; see [`thesis/README.md`](thesis/README.md).

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
