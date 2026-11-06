# Findings

Gaps, extra hypotheses and new results found while formalizing.

1. **Positive-definiteness of `K`.** After eq. (36) the thesis says "since
   `K̄` is a covariance matrix it is positive definite". A covariance matrix
   is only positive *semi*definite; `K` is positive definite here because
   `τ² > 0` and the correlations `ρ` form a positive-semidefinite matrix
   (`Model.K_posDef`).
2. **At least two cohorts.** With `J = 1` we get `b = 1` and `s² = τ² + σ²`,
   so eq. (62) is `0/0`. The thesis never assumes `J ≥ 2`, but the reduction
   to Bühlmann–Straub (`bs_z`, eq. (73)) needs it.
3. **Credibility above one (sharpened).** The thesis (§2.7) notes that
   `z₁ > 1` can happen and clips it in eq. (87), without saying when. In the
   two-cohort case `z₁ = τ² / (τ² + σ₁² - σ₁σ₂ρ)`, so below the singularity
   `z₁ > 1` exactly when `σ₁ < σ₂ρ` (`TwoCohorts.z1_gt_one_iff`).

Equation numbers refer to `thesis/original/main.tex` as compiled.

(Findings 1–3 come from the statements; confirm them as proofs land.)
