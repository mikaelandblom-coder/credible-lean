# Credibility handbook: outline (draft)

A practitioner's handbook for one unified credibility framework: the useful
results, each with a short comment and a link to its Lean proof. No proofs.
Independent of the thesis: its own numbering (thesis equations cited only in
the comments). Target: 6–8 pages, built by CI as a PDF next to the blueprint.
Only results that serve the credibility framework go in.

Per entry: **statement** (one display), **comment** (when to use it and why it
holds, in words), **Lean** (theorem name, linked to the source line).

Status (2026-11-25, review): restructured into 12 sections with a table of contents, in the
order of the paper: setting; core; special cases; the moments are real (and the error given the
level); beyond the blend (the BLUP); estimating (with **the recipe**, the app's no-tuning fit, and
what fitting costs); beyond second moments; unequal lengths; groups; choosing cohorts; monthly
data (shock, season, factor); trends and several quantities; appendix: a worked example (three
cohorts, four years, every number checkable by hand). Labels unchanged (the thesis proposal and
the paper cite them); numbers changed, so the paper was rerun with `paper_check.py --fix`.

**One home per explanation** (owner, 2026-11-25): the handbook is the formula book and holds every
formula. An entry is its statement, its Lean links, and at most two lines of "use it" and one short
"watch out"; no "why". Each section opens with "Context:" and the paper's section, cited by title
with `\paper{Title}` (checked by `handbook_check.py`: the title must be a heading or run-in paragraph
of `paper/paper.tex`). The paper also displays its ~10 key formulas, so it stands alone. The 6–8
page target is dropped: it is a reference, not a read.

## Pending
(Results proved since the last handbook update that may belong here.)
- *Done 2026-11-26:* subsection "Crossed levels" in §9 (groups): `res:crossed` (K ≻ 0, mixed form,
  Henderson, β² = 0 is `res:groups`), `res:crossed_balanced` (three factors, the blend's excess per
  layer), `res:crossed_missing` (a cell without data, 2×2), `res:crossed_balanced` also has the best common `z̄`, the predictor's total error and
  equicorrelated noise (σ²(1−ρ)); `res:crossed_est` (pair estimators of
  `α², β², γ²`, the ANOVA identity); moment layer links (`NoiseX`, true MSE, existence iff ρ ⪰ 0).
- *Done 2026-11-26:* Finding 42 (crossed ANOVA estimators miss the noise cross term) in the
  appendix and in `res:crossed_est` (rows, grand mean: Goulet's (67)–(69), two-way).
- *Done 2026-11-25:* Appendix "Findings" (all 41, one line each, counterexamples included, with Lean
  links); every Lean name the paper used is now linked from a handbook entry. New finding → add its
  line there in the same commit.
- *Done 2026-11-25:* Finding 41 "watch out" in `res:blend_intervals` (common `τ²` keeps intervals,
  a `τ²` per group makes an outlier bin, number of groups by gain against price); the normal-noise
  "why" sentence in `res:blup` (`knownMeanPred_mse_le_of_normal`).
- *Done 2026-11-25 (later):* OBP collective mean "watch out" at `res:bs` (study S59–S62: don't use it; a volume
  trend as a design column instead), and a line in the Finding 41 caveat: never cut sorted estimates by SURE (S61).
- *Done 2026-11-25 (review):* `res:varQuad` (variance of a quadratic estimator: cumulants,
  independent sources, sample covariance, variance function), `res:givenLevel` (error given the
  level, SURE, the OBP collective mean, moved out of `res:bs`), the recipe (§ Estimating), the
  damping rule on the correlation scale (`res:bestTheta`), aggregation and recency (`res:blup`),
  first-order skew bias (`res:randomWeights`), typical error (`res:plugIn`), the worked example.
- Still open from the old list: exact Var/Cov of `P`, `Qn`, `B` and the Finding 37 watch-out, if the
  gain-against-price entry ever needs them; the noise-shape watch-out (slope of `log σ̂ⱼ²` on
  `log μ̂ⱼ` biased up under skew; cross-fit) once the app's skew step is settled.

The numbered list below is the drafting record (old numbering), kept for history.

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
15a. Each group's own effect (2026-11-25): Henderson's equations give the GLS mean and the BLUP of
    each group effect, best in true MSE, with its error; the small form of `K_G⁻¹` — `res:groupEffect`.
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
10d. What fitting BS costs, to first order (2026-11-25, after 10c): law (a) with kurtosis, the cross
    term (Finding 38) and the net kurtosis effect, law (b), any volumes; "watch out": the sign is not
    guaranteed (Findings 39, 40) — `res:bsPrice`.
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
