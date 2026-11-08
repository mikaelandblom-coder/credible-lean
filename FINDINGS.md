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
   `z/z_* = (0.564, 0.177, 0.259)`). It also fails for equal correlations
   `ρᵢⱼ = ρ` when the `σⱼ` differ. For `J ≥ 3` the right condition is
   item 5.
5. **Equal covariances (new, any `J`).** If all cohort pairs have the same
   covariance `σ²ᵢⱼρᵢⱼ = c`, then `bⱼ = zⱼ/z_*` and the proposed factor is
   `zⱼ = τ²/(τ² + σ²ⱼⱼ - c)`, i.e. eq. (32) with `σ₁σ₂ρ` replaced by `c`
   (`Model.b_eq_of_equalCov`, `Model.bestZ_of_equalCov`, *proved*). Reason:
   `K = diag(dⱼ) + c·11ᵀ`, and a rank-one term along `u` does not change the
   direction of `K⁻¹u`. Bühlmann–Straub is `c = 0`, two cohorts are
   `c = σ₁σ₂ρ`. Extra hypotheses: `τ² + σ²ⱼⱼ ≠ c` (the singularity of
   Finding 3, now per cohort) and `bⱼ ≠ 1` (`0/0`, as in Finding 2).
   *Converse (on paper, not in Lean).* `bⱼ = zⱼ/z_*` for all `j` iff some `λ`
   gives `Σᵢ≠ⱼ (Kᵢⱼ + λ) bᵢ = 0` for every `j`. For `J = 3` with all `bⱼ ≠ 0`
   this forces equal covariances. For `J ≥ 4` it does not: with equal `σⱼ`,
   any correlation matrix with equal row sums gives `b = z/z_* = u/J`
   (e.g. `J = 4`, off-diagonal covariances `0.5, -0.1, 0.2, 0.2, -0.1, 0.5`).
6. **Equal credibility is not grouping (discussion, no Lean).** Under
   equal covariances (item 5), `bⱼ = zⱼ/z_*`, so cohorts with the same `z`
   get the same weight. The collective estimate `μ̂ = Σ bⱼ μ̂ⱼ` then sees them
   only through the sum of their `μ̂ⱼ`: pooling them is lossless for `μ̂`.
   But this is not the grouping that clustering (e.g. arXiv:2611.07110) is
   after. (a) Equal `z` means equal reliability (`σ²ⱼⱼ`), not equal risk:
   cohorts with `μ̂ⱼ = 0.5` and `1.5` keep different premiums
   `zμ̂ⱼ + (1-z)μ̂`. (b) Putting `i`, `j` in one risk group means assuming
   `μᵢ = μⱼ`, so their covariance goes from `0` to `τ²`. That changes `K`,
   every `z` and `μ̂`. Open question: when does merging two cohorts
   lower the total MSE? Probably it depends on the data, not on `zᵢ = zⱼ`.
   Natural setting: two-level (hierarchical) credibility, cohorts nested in
   groups (Bühlmann & Gisler, ch. 6). See README "Later goals".
   *Partly answered (on paper, `notes/merging-cohorts.md`).* With
   `d = E(μ₁-μ₂)²` and `V = Var(μ̂₁-μ̂₂) = σ₁² + σ₂² - 2σ₁σ₂ρ`, for a pair
   on its own (§2.7, `μ` estimated) merging lowers the total MSE iff
   `d < Vτ²/(V+τ²)`, i.e. `1/d > 1/V + 1/τ²`. Correlation enters only via
   `V`: `ρ > 0` makes merging harder. Equal `z` plays no role, and under
   the thesis model (`d = 2τ²`) merging never pays. Inside a large
   portfolio (`μ` known) the threshold is lower (equal `σ`, `ρ = 0`:
   merge iff the shared share of level variance `φ > (1+z²)/2`, against
   `1/(2-z)` for the pair alone); it has no simple general form. Open: the
   winner's curse when the merge is decided from the same data.

Equation numbers refer to `thesis/original/main.tex` as compiled.

(Findings 1–3 come from the statements; confirm them as proofs land.)
