# Findings

Gaps, extra hypotheses and new results found while formalizing.

1. **Positive-definiteness of `K`.** After eq. (20) the thesis says "since
   `K` is a covariance matrix it is positive definite". A covariance matrix
   is only positive *semi*definite; `K` is positive definite here because
   `τ² > 0` and the correlations `ρ` form a positive-semidefinite matrix
   (`Model.K_posDef`).
2. **At least two cohorts.** With `J = 1` we get `b = 1` and `s² = τ² + σ²`,
   so eq. (26) is `0/0`. The thesis never assumes `J ≥ 2`, but the reduction
   to Bühlmann–Straub (`bs_z`, end of §2.6) needs it.
3. **Credibility above one (sharpened).** The thesis (§2.7) notes that
   `z₁ > 1` can happen and clips it in eq. (34), without saying when. In the
   two-cohort case `z₁ = τ² / (τ² + σ₁² - σ₁σ₂ρ)`, so below the singularity
   `z₁ > 1` exactly when `σ₁ < σ₂ρ` (`TwoCohorts.z1_gt_one_iff`).
   *Proved.* Below the singularity the denominator `τ² + σ₁² - σ₁σ₂ρ` is
   positive, so `z₁ > 1` iff `σ₁² < σ₁σ₂ρ`. The proof never uses `τ² > 0`:
   the condition is independent of the between-cohort variance.
4. **Weights from credibility factors (new, two cohorts only).** For two
   cohorts the GLS weight is `b₁ = z₁ / (z₁ + z₂)` (`TwoCohorts.b1_eq_z`,
   *proved*), the same form as Bühlmann–Straub's `b_j = z_j / z_*`. This is
   on the defence slides but not in the published thesis. So any binary
   split of a portfolio (two segments of a rating factor) keeps the classical
   weight formula under correlation. It fails for `J ≥ 3`: numerically with
   random `σⱼ`, `ρᵢⱼ` (e.g. `b = (0.536, 0.226, 0.238)` against
   `z/z_* = (0.564, 0.177, 0.259)`). Open: is there a clean condition on `ρ`
   under which it holds for `J ≥ 3`?

Equation numbers refer to `thesis/original/main.tex` as compiled.

(Findings 1–3 come from the statements; confirm them as proofs land.)
