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
All statements are in place with `sorry`. See `FINDINGS.md` for gaps and new
results surfaced by the formalization.

## Setup (once, from a phone)
1. Push these files to a GitHub repo.
2. In the Claude app's Code tab, add a cloud environment with Trusted network
   access and paste `setup-script.sh` into its setup script.
3. Start a session on the repo in that environment and say:
   "Do the first-session steps in CLAUDE.md."
