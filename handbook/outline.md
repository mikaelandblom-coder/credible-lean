# Credibility handbook: outline (draft)

A practitioner's handbook for one unified credibility framework: the useful
results, each with a short comment and a link to its Lean proof. No proofs.
Independent of the thesis: its own numbering (thesis equations cited only in
the comments). Target: 6–8 pages, built by CI as a PDF next to the blueprint.
Only results that serve the credibility framework go in.

Per entry: **statement** (one display), **comment** (when to use it and why it
holds, in words), **Lean** (theorem name, linked to the source line).

Status: sections 0–1 drafted in `handbook.tex`; 2–5 to write.

## Pending
(Results proved since the last handbook update that may belong here.)
- Item 15, "watch out": with several groups `τ̂²` estimates `τ² - φτ²π`
  (`π` = weighted share of same-group pairs), so the plug-in `K̂` is off
  unless there is one group; pairs within vs across groups estimate
  `(1-φ)τ²` and `τ²`, so `φτ²` is identifiable (Finding 13) —
  `thm:estimation_G`, `cor:KHat_G_iff`, `cor:phiTauHat`. One group (a
  shared level) is the special case `π = 1`: `τ̂²` estimates `(1-φ)τ²`,
  which is all the blend needs — `cor:estimation_phi`.
- Item 15 can now say "in true MSE" (proved 2026-11-10): for any random
  variables `μⱼ = μ + √((1-φ)τ²) ηⱼ + √(φτ²) γ_{g(j)}` (group effects `γ_g`
  centred, unit, uncorrelated with `η`, `ε` and each other; `0 ≤ φ < 1`),
  `cov(μ̂ᵢ, μ̂ⱼ) = (K_G)ᵢⱼ`, the six fields of `momentsG` are the actual
  moments and the factor of `bestZ_G_eq` minimises the true MSE —
  `thm:G_cov_obs`, `thm:G_bestZ_mse`. "Unbiased with group levels" (the
  "watch out" above) is the true expectation — `thm:G_integral_quad`.
- Item 11 could lead with the general form: any random `μ̂ⱼ`, `μⱼ` with
  covariances `K` and `L` (nothing about how `μ̂ⱼ` is built), the blend's MSE
  is eq. (6) and `z = (Lⱼⱼ - (Lb)ⱼ)/(Kⱼⱼ - s²)` minimises it —
  `thm:Core_bestZ_mse`. The thesis, unequal lengths and group levels are
  three instances.
- Open: consistency of the group-level assumptions (existence of such
  `η`, `ε`, `γ`; expected: iff `ρ ⪰ 0`, as item 12), and the same layer for
  unequal lengths with groups (`Hierarchical.lean` is on `Model` only).
  `Unequal.Noise.integral_quad` covers forms that read only observed cells
  (item 13 in true expectation).
- Estimation section, one line under the unbiasedness entry: "unbiased" is
  the actual expectation for any random variables with the model's first
  two moments, no distribution assumed — `thm:integral_quad`
  (`Noise.integral_quad`).

- Section 5, "watch out" (Finding 14, on paper): choosing cohorts by
  sorting levels and cutting into intervals is exact only for
  exposure-weighted pooling; with unequal variances and a credibility blend
  the best cohorts need not be intervals. Now proved: "use it" entry
  `cor:pool_optimal_contiguous` (pooling = k-means plus #cohorts,
  `thm:pool_mse_eq_kmeansCost`), "watch out" stays a remark (Finding 14).

## 0. Setting and notation (1 page)
- The model: `μⱼₜ = μ + τ ηⱼ + σⱼₜ εⱼₜ`, `cov(εᵢₜ, εⱼₛ) = ρᵢⱼ δₜₛ`.
  Distribution-free: only first and second moments.
- Why error terms: correlation between cohorts is one line here, but awkward
  with independent risk parameters `Θⱼ`.
- Translation table to classical Bühlmann–Straub: `τ² ↔ a`,
  `σ²ⱼₜ ↔ σ²/wⱼₜ`, `μ ↔ m`. `ηⱼ` here is the thesis's `εⱼ`.
- The recipe: build `K = cov(μ̂ᵢ, μ̂ⱼ)`, check `K ≻ 0`, read off weights and `z`.

## 1. The core: everything follows from `K` (2 pages)
1. Best credibility factor, eq. (7), optimal and unique —
   `thm:bestZ_optimal`, `thm:bestZ_unique`.
2. Inverse-variance weights within a cohort, eq. (23) — `thm:invVarWeight_optimal`.
3. GLS portfolio weights `b = K⁻¹1 / 1ᵀK⁻¹1` and their variance —
   `thm:glsWeight_optimal`, `thm:glsWeight_value`.
4. The proposed factor `zⱼ = (1-bⱼ)τ² / (τ² + σ²ⱼⱼ - s²)`, eq. (26) —
   `thm:Core_bestZ_eq`.
5. `K` is positive definite (Finding 1: semidefinite is not enough) and
   `J ≥ 2` is needed (Finding 2).
5a. Damped plug-in `K̂`: `ρ̂ ⪰ 0`, `θ ∈ [0,1)`, `τ̂² ≥ 0` (truncated) give
   `K̂ ≻ 0` — `thm:U_dampedK_posDef` (drafted).

## 2. Special cases (1.5 pages)
6. Bühlmann–Straub at `ρ = 0`, and it is balanced — `thm:bs_z`, `thm:bs_balance`.
7. Two cohorts: `z₁ = τ²/(τ² + σ₁² - σ₁σ₂ρ)` and `b₁ = z₁/(z₁+z₂)` —
   `thm:z1_eq`, `thm:b1_eq_z` (Finding 4).
8. When `z₁ > 1` and the sign flip past the singularity —
   `thm:z1_gt_one_iff`, `thm:z1_neg_iff` (Finding 3).
9. Equal covariances, any `J`: `bⱼ = zⱼ/z_*` — `thm:b_eq_of_equalCov`,
   `thm:bestZ_of_equalCov` (Finding 5).

## 3. Estimating the parameters (1 page)
10. Unbiased estimators, eqs. (37)–(41), and what they need (`T ≥ 2`, `J ≥ 2`;
    Finding 7) — `cor:estimation`.

## 4. The moments are real (1 page)
11. Any random variables with these moments: the covariances, optimal weights
    and the MSE of the blend are the true ones — `thm:moments_eq`, `thm:bestZ_mse`.
12. The assumptions are consistent iff `ρ ⪰ 0` — `thm:exists_noise` (Finding 11).

## 5. Extensions beyond the thesis (1.5 pages)
13. Cohort-dependent lengths `Tⱼ`: `K` stays PD, same formula, balance survives —
    `thm:U_K_posDef`, `thm:U_bestZ_eq`, `thm:U_balance` (Findings 8–10, 12).
14. When merging two cohorts pays off: `1/d > 1/V + 1/τ²` — `thm:merge_iff` (Finding 6).
15. A shared group level drops out of credibility; two-stage GLS —
    `thm:bestZ_phi_eq`, `thm:glsWeight_blockDiag`.

Waiting list (in once they prove useful for credibility): optimal 1-D
k-means groups are intervals (`thm:kmeans_contiguous`). (Damping is in, as 5a.)

## Open choices for the owner
- Commentary voice: the thesis's, or a looser handbook tone?
