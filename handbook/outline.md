# Credibility handbook: outline (draft)

A practitioner's handbook for one unified credibility framework: the useful
results, each with a short comment and a link to its Lean proof. No proofs.
Independent of the thesis: its own numbering (thesis equations cited only in
the comments). Target: 6–8 pages, built by CI as a PDF next to the blueprint.
Only results that serve the credibility framework go in.

Per entry: **statement** (one display), **comment** (when to use it and why it
holds, in words), **Lean** (theorem name, linked to the source line).

Status (2026-11-11): all sections 0–5 drafted in `handbook.tex`, including
the moment layer (true MSE for any `K`, `L`), unequal-length estimation,
group levels (Finding 13) and choosing cohorts. Next: owner review of the
voice, then trim towards 8 pages.

## Pending
(Results proved since the last handbook update that may belong here.)
- Open: the moment layer for unequal lengths with groups
  (`Hierarchical.lean` is on `Model` only).


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
10a. Balance of Bühlmann–Straub (in section 2) — `thm:bs_balance`.

## 4. The moments are real (1 page)
11. Any random `μ̂ⱼ`, `μⱼ` with covariances `K`, `L`: GLS optimal and `z`
    minimises the true MSE — `thm:Core_bestZ_mse`, `thm:bestZ_mse`; "unbiased"
    is the true expectation — `thm:integral_quad`.
12. The assumptions are consistent iff `ρ ⪰ 0` — `thm:exists_noise` (Finding 11).

## 5. Extensions beyond the thesis (1.5 pages)
13. Cohort-dependent lengths `Tⱼ`: `K` stays PD, same formula, balance survives —
    `thm:U_K_posDef`, `thm:U_bestZ_eq`, `thm:U_balance`, `thm:U_exists_noise`;
    estimation with the per-pair count `nᵢⱼ` — `thm:U_unbiased`, `lem:U_den`
    (Findings 8–10, 12).
14. When merging two cohorts pays off: `1/d > 1/V + 1/τ²` — `thm:merge_iff` (Finding 6).
15. A shared level drops out (one group); several groups: `z` with `B_g`,
    true MSE, consistency; two-stage GLS; estimation biased with several
    groups, `φτ²` from pairs (Finding 13) — `thm:bestZ_phi_eq`,
    `thm:bestZ_G_eq`, `thm:G_bestZ_mse`, `thm:G_exists_noise`,
    `thm:glsWeight_blockDiag`, `thm:estimation_G`, `cor:KHat_G_iff`,
    `cor:phiTauHat`, `thm:G_integral_quad`.
16. Choosing cohorts (drafted): optimal cohorts are intervals of the sorted
    levels for exposure-weighted pooling (= weighted k-means + #cohorts) and
    for the blend with a common variance; find them by dynamic programming —
    `thm:pool_mse_eq_kmeansCost`, `cor:pool_optimal_contiguous`,
    `thm:blend_optimal_contiguous`. "Watch out": not for the blend with
    unequal variances (Finding 14).

(Damping is in, as 5a; 1-D k-means intervals are in via item 16.)

## Open choices for the owner
- Commentary voice: the thesis's, or a looser handbook tone?
