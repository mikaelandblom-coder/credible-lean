# Findings

Gaps, extra hypotheses and new results found while formalizing.

1. **Positive-definiteness of `K`.** The thesis takes it from "covariance
   matrix". A covariance matrix is only positive *semi*definite; `K` is
   positive definite here because `τ² > 0` and the correlations `ρ` form a
   positive-semidefinite matrix (`Model.K_posDef`).
2. **At least two cohorts.** With `J = 1` we get `b = 1` and `s² = τ² + σ²`,
   so eq. (26) is `0/0`. The reduction to Bühlmann–Straub (`bs_z`) needs
   `J ≥ 2`.
3. **Credibility above one (new).** In the two-cohort case,
   `z₁ = τ² / (τ² + σ₁² - σ₁σ₂ρ)`, so below the singularity `z₁ > 1` exactly
   when `σ₁ < σ₂ρ` (`TwoCohorts.z1_gt_one_iff`).

(Findings 1–3 come from the statements; confirm them as proofs land.)
