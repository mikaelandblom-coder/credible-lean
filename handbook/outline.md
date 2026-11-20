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
- Factor estimation part 1 (2026-11-20, `FactorEstimation.lean`): "year-on-year differences
  of two cards at lag `h` estimate `λᵢλⱼ(2Γ(h) - Γ(h-12) - Γ(h+12))` without bias, whatever the
  card means and seasons; the shock and the factor's lag-0 share need not be split"
  (`Credibility.Factor.yoy_unbiased_factor`, `Credibility.Factor.blup_eq_of_lag0`). Goes with
  the factor entry once the fit is complete.
- Common factor (2026-11-20, `Factor.lean`, Finding 25): "a demand factor over months
  (AR(1), or a block per regime) on top of the shock; its `K` is positive definite for any
  observed cells, `ℓ` for the next 12 months only sees the factor and the card level; watch
  out: the best weights can be negative even with positive autocorrelation"
  (`Credibility.Factor.K_posDef`, `Credibility.Factor.ell_apply_of_future`,
  `Credibility.Factor.blup_neg_of_ar1`). Entry together with the season once Step 4
  (estimating `Γ`, `λ`) gives a usable fit.
- Season (2026-11-20, `Season.lean`, Finding 24): "whole years do not make the season drop
  out: with seasonal volume the one-mean predictor leans on busy months and is biased by
  `Σₘ (Sₘ - cₘ)βₘ`; fit the season or divide by a known index and weight by expected claims"
  (`Credibility.Season.blup_eq_iff`, `Credibility.Core.Target.integral_bias`,
  `Credibility.Unequal.a_eq_of_volume`).
- General target with fixed effects (2026-11-20, `Blup.lean`, card-data Step 1): the best
  linear unbiased predictor `d* = K⁻¹ℓ + K⁻¹X(XᵀK⁻¹X)⁻¹(x₀ - XᵀK⁻¹ℓ)` for any target `Y`
  (`Credibility.Core.blup_optimal`), its error `v - ℓᵀK⁻¹ℓ + rᵀ(XᵀK⁻¹X)⁻¹r` with the price of
  estimating `β` as the last term (`Credibility.Core.predMse_blup`). Entry once the season
  (Step 2) gives it a practical use; the level BLUP entry can then cite it as `X = 1`. With it:
  "annual totals never beat monthly data with known covariances" (`Core.predMse_blup_le_aggregate`)
  and "an unneeded season has a price" (`Core.predMse_blup_nested`).
- Tapering (2026-11-17, `OffDiagonal.lean`): multiplying `K̂` entrywise by a correlation
  matrix keeps it positive (semi)definite and keeps the variances
  (`Credibility.posDef_hadamard_of_corr`); the distance taper `ρ^|tᵢ-tⱼ|` is one
  (`Credibility.distTaper_posSemidef`). One line next to the damped plug-in result
  (`res:damped`): "damping is one taper; ordered cohorts can use the distance taper".
- Finding 18 (2026-11-16): the best linear unbiased predictor and the price of the
  blend (`Core.blupWeight_optimal`, `Core.errVar_eq_blupWeight_add`,
  `Core.exists_blendWeight_eq_blupWeight_iff`): one entry in §1, "is the blend enough?".
  App (2026-11-17, `studies/PLAN.md` 3c): the plug-in BLUP on corrBS's `K̂` beats the blend
  under correlation (98% of the blend floor at `ρ = 0.6`), ties at `ρ = 0`: worth a "use it" line.


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
5b. What ignoring or damping correlation costs (Findings 19–20): sharp
   `(A + a)²/(4aA)` for equal correlations — `cor:Core_ignoreCorr_equicorr`,
   `cor:Core_damped_equicorr`, `thm:Core_damped_mse` (drafted).

## 2. Special cases (1.5 pages)
6. Bühlmann–Straub at `ρ = 0`, and it is balanced — `thm:bs_z`, `thm:bs_balance`.
   Which weights balance any blend (`uⱼ(1 − zⱼ) ∝ bⱼ`; diagonal `K`: precisions), with the
   watch-out that forcing exposure balance under correlation costs up to ≈40% even with the true parameters (exact; study findings S27–S28) —
   `thm:Core_balance`, `cor:Core_balance_diag`. If you must balance: don't bend `z`
   (best balanced blend, up to 2× the error; Finding 15) — `thm:Core_bestBalanced`;
   shift all rates, best for independent cohorts and within ≈2% under correlation
   (Finding 16) — `Core.Estimates.commonShift_mse_optimal_of_diag`.
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
13a. A known common trend (drafted): restate to the target year, then blend;
    `K̃ = (1+g)^(2n)K`, weights and `z` unchanged, relativities trend-free;
    "watch out": only for the true `g` (Finding 21) — `thm:U_detrend`,
    `thm:U_detrend_obs`, `thm:U_relativity`.
13b. Shock plus process noise (drafted, Finding 23): `K` for any cell weights, `K ≻ 0`;
    unbiased `Ĉ`, `ŝ²`, `τ̂²`, `K̂`; "watch out": shock and process noise separate only with
    volumes that vary over `T ≥ 3` periods, and then always with weightings `1`, `w` —
    `Shock.K_apply`, `Shock.KHat_unbiased`, `Shock.det_expo_neg`,
    `Shock.not_unbiased_s2_of_const`.
14. When merging two cohorts pays off: `1/d > 1/V + 1/τ²` — `thm:merge_iff` (Finding 6).
15. A shared level drops out (one group); several groups: `z` with `B_g`,
    true MSE, consistency; two-stage GLS; estimation biased with several
    groups, `φτ²` from pairs (Finding 13) — `thm:bestZ_phi_eq`,
    `thm:bestZ_G_eq`, `thm:G_bestZ_mse`, `thm:G_exists_noise`, with unequal lengths
    `thm:U_bestZ_G_eq`, `thm:U_G_bestZ_mse`, `thm:U_G_exists_noise`,
    `thm:glsWeight_blockDiag`, `thm:estimation_G`, `cor:KHat_G_iff`,
    `cor:phiTauHat`, `thm:G_integral_quad`.
16. Choosing cohorts (drafted): optimal cohorts are intervals of the sorted
    levels for exposure-weighted pooling (= weighted k-means + #cohorts) and
    for the blend with a common variance; find them by dynamic programming —
    `thm:pool_mse_eq_kmeansCost`, `cor:pool_optimal_contiguous`,
    `thm:blend_optimal_contiguous`. "Watch out": not for the blend with
    unequal variances (Finding 14).

17. Several quantities per cohort (drafted 2026-11-20): the best credibility matrix
    `Zⱼ = (Lⱼⱼ − (LW)ⱼ)(Kⱼⱼ − S)⁻¹`, best for every premium `aᵀμⱼ`; Bühlmann–Gisler
    and Hachemeister as instances; "use it": independent cohorts (blend = best predictor),
    no cross-component covariance (separate predictors), balance; "why": true MSE for any
    distribution; "watch out": the blend need not beat separate blends (Finding 22) —
    `res:vector`.

(Damping is in, as 5a; 1-D k-means intervals are in via item 16.)

## Open choices for the owner
- Commentary voice: the thesis's, or a looser handbook tone?
