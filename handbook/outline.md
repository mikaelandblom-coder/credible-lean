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
- Small form of `K_G⁻¹` (2026-11-24, `Unequal.KG_inv_eq`; general `Matrix.inv_mul_mul_transpose_add`,
  `Matrix.pushThrough`, `Matrix.hendersonMME` in `Henderson.lean`): computing tip for group levels
  ("use it": invert only a groups × groups matrix). Probably a one-line note, if any. With it:
  the group effects from Henderson's equations are BLUPs (`Unequal.groupEffect_eq_blup`), with true
  error `NoiseG.mse_groupEffect_blup` (a candidate formula entry: the group effect and its error).
- Cross term of the plug-in (2026-11-24, `Cumulants.crossTerm_of_balanced_cumulants`, Finding 38):
  with law (a); "watch out": law (a)'s kurtosis terms alone have the wrong sign for the total, the
  kurtosis effect on the BS plug-in's first-order MSE is `−(1 − 1/J)z(1 − z)(γL + γN/T)/J`.
  Any volumes (2026-11-25, `Cumulants.crossTerm_bs_of_cumulants`): the same term as sums over regions.
  Watch out (Finding 39, `crossTerm_bs_pos_example`): with a region's volume concentrated in one year
  the noise part turns positive; the level part is always ≤ 0 (2026-11-25,
  `Cumulants.crossTerm_bs_level_nonpos`). Not for the BLUP plug-in (Finding 40): there it can be slightly
  positive (< 0.4% of MSE per unit γL, strong ρ and very uneven volumes), so don't promise the sign.
- Variance of a quadratic estimator (2026-11-22, `Cumulants.variance_quad_of_cumulants`): the
  formula with skewness and kurtosis terms; add with its first use (G2 `V`, G4 weights).
  With a variance function `μᵖ` (2026-11-23, `VarianceFunction.variance_quad_of_powerVariance`):
  "mean of the conditional variance plus variance of the conditional mean"; watch out: the
  cumulants are averaged over the levels, not taken at the mean level. Same entry.
  Sample covariance over independent years (2026-11-23, `Cumulants.variance_sampleCov`):
  `Var ŝᵢⱼ = (VᵢᵢVⱼⱼ + Vᵢⱼ²)/(T−1) + κ₄ᵢⱼᵢⱼ/T`; "watch out": heavy tails add `κ₄/T` to the
  normal-theory variance of `ŝᵢⱼ`. But don't feed it to the damping rule in covariance form:
  it damps too much for the rates (studies S39); the app's rule is on the correlation scale. Add with G2's handbook entry. Weighted version
  for the shock model (`Cumulants.variance_crossResid`): same entry.
- Moments of the fit statistics (2026-11-24, `Cumulants.covariance_stat`, `covariance_statB_eq_zero`,
  `Core.linMse_lineWeight_sub`): exact Var/Cov of `P`, `Qn`, `B`; "watch out": `B` is uncorrelated
  with `P`, `Qn` only for normal cells and region means uncorrelated with residuals (Finding 37).
  Same entry: the balanced identity `ẑ = 1 − v̂/S²` and law (a), the price of fitting BS,
  `(2/J)(1 + (J−1)/(J(T−1)))(1 − z)/z ≤ (2/J)·T/(T−1)·(1 − z)/z` (`Cumulants.bsPrice_le_of_balanced`; from the cells alone: `bsPrice_of_balanced_cells`; corrected for kurtosis, `+ κL/(Js²) + γN z²/(JT)` in
  the bracket: `bsPrice_of_balanced_cumulants`):
  Law (b), own variances over a pooled one: `(1 − 1/J)²·z(1 − z)·2/(T − 1) ≤ z(1 − z)·2/(T − 1) ≤ 1/(2(T − 1))`
  (`Cumulants.ownPrice_sub_pooled_le_of_balanced`); "why": an own factor at fixed `τ²` pays `z²` times
  BS's price for the same noise in `v̂` (`ownPrice_eq_sq_mul_bsPrice`).
  "use it" to judge whether BS's fit costs more than it gains. Add with the "gain against price" entry
  once the app step lands.
- Noise shape (app, 2026-11-22, not proved): a "watch out" near Finding 35: the slope of
  `log σ̂ⱼ²` on `log μ̂ⱼ` from the same years is biased up under skew (≈ 2 when the truth is 0);
  cross-fit (even against odd years). Add when step 2 (skew correction) is settled. The "why":
  `cov(σ̂², μ̂) = Σₛ aₛκₛ Σₜ cₜ(δₜₛ − aₛ)²` (`Cumulants.covariance_resVar_mean`, 2026-11-23).

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
5a'. Optimal damping of the table `θ* = Σs²/(Σs² + ΣV)` and the safe range (G2) —
   `thm:bestTheta`, `thm:dampSafe`.
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
8a. When clipping `z` to [0, 1] is harmless: iff the true `z` is in [0, 1] (Finding 36, G3) —
   `thm:clipZ`.
9. Equal covariances, any `J`: `bⱼ = zⱼ/z_*` — `thm:b_eq_of_equalCov`,
   `thm:bestZ_of_equalCov` (Finding 5).

## 3. Estimating the parameters (1 page)
10. Unbiased estimators, eqs. (37)–(41), and what they need (`T ≥ 2`, `J ≥ 2`;
    Finding 7) — `cor:estimation`.
10c. One common covariance or correlation (PLAN G1, 2026-11-22): `E Qᵢⱼ`, the average `ĉ`, the
    pooled `ρ̂` with true `σ` — `cor:pooled`, `thm:U_pooled`.
10a. Balance of Bühlmann–Straub (in section 2) — `thm:bs_balance`.
10b. Estimated weights (2026-11-22, Finding 35): bias `Σᵢ cov(d̂ᵢ, μ̂ᵢ)`; exposure balance keeps the
    portfolio unbiased; watch out for skewed claims with region-specific variances —
    `Core.Estimates.integral_randomLin_sub`, `integral_portfolio_sub_of_balanced`.

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
    groups, `φτ²` from pairs, pooled over all pairs (Finding 13, G4) — `thm:bestZ_phi_eq`,
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
17a. Tapering (2026-11-22, with 5a): any correlation-matrix taper keeps `K̂ ≻ 0`; distance taper
    for ordered cohorts — `res:damped`.
10c. The price of plugging in (2026-11-22, after 10b): `mse(d*) + E B² + 2E[AB]`; normal noise:
    cross term 0; symmetric noise: unbiased — `res:plugIn`.
17b. The best linear predictor of any target (2026-11-22, Finding 18): universal kriging, its
    error, the price of the blend; aggregation and unneeded design columns — `res:blup`.
17c. Monthly data: the season (Finding 24) — `res:season`.
17d. The factor model (Finding 25) and estimating it (Findings 26–29) — `res:factor`,
    `res:factor_est`.
18. Monthly data with a common factor, constrained tables (drafted 2026-11-21, placed after
    shock and process noise): project the unbiased fit onto valid tables in its own metric `H`
    (exists, unique, closer to the truth in every draw; the app's check: never violated, median
    `‖p − θ‖²_H / ‖θ̂ − θ‖²_H ≈ 0.7`), valid tables give `K̂ ≻ 0` when every
    `ŝⱼ² > 0`; "use it": constrain the tables, take `φ` from a long index; "watch out":
    `ŝ² ≥ 0` alone is not enough (Finding 30) — `res:valid_tables`.
18a. Relativities under the factor (drafted 2026-11-21): the factor adds exactly `gᵀΓg` to any
    statistic; relativities with equal loadings and common month weights need no factor model;
    "watch out": same months is not enough (Finding 31) — `res:factor_extra`,
    `res:relativity_factor`.
19. Frequency times severity (drafted 2026-11-21, after the matrix blend): joint = separate
    without cross-covariance, and also in the Kronecker case (Finding 32); the exact bias of the
    pure premium, zero for separate fits of uncorrelated components (Finding 33) —
    `res:freqsev_joint`, `res:prodBias`.

(Damping is in, as 5a; 1-D k-means intervals are in via item 16.)

## Open choices for the owner
- Commentary voice: the thesis's, or a looser handbook tone?
