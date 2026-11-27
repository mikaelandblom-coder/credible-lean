# Finished app plan items

Moved from the "Pending" list of `studies/PLAN.md` (2026-11-27) once done; kept as the record of
what was built, studied and proved. Order as they stood in the plan.

- [x] Crossed levels (2026-11-26, `Credibility/Crossed.lean`): a "crossed" switch for a table of
  cells with a row and a column (country × car type). World: `L = α²[same row] + β²[same column]
  + γ²I`. Show the three-factor predictor (`Crossed.blup_balanced`, general `K` via `Core.blup`)
  against the blend, the blend's excess per layer (`Crossed.sum_linMse_blend`) and a cell without
  data predicted from its row and column (`Crossed.missing_blup`). Fit: `α̂², β̂², γ̂²` from
  pools of same-row / same-column / neither pair estimators (`Model.crossed_unbiasedX`, unbiased
  for any weights summing to one per class; weights `∝ w_k w_l` are Dannenburg's ANOVA
  estimators). Choice of weights and truncation at 0 to be settled by simulation (no hand-set
  choices).
  *Built 2026-11-26* (`app/crossed.js`, tests `app/crossed.test.js`, card "Crossed levels"): world = the
  engine's thesis noise (τ = 0) plus row, column and cell effects; optional cell without data (row 1,
  column 1). Fit from the data: pair estimators with eq. (39) noise, three pools, `α̂², β̂², γ̂²`, `K̂ = L̂ + Σ̂`
  (corrBS's Σ̂, so `K̂ ≻ 0`), BLUP for every cell, including the empty one. Shown: the table (truth, own mean,
  crossed and thesis rates), the weights of cell (1,1), the exact blend excess per layer when balanced,
  many draws in % of the floor, the variances' bias (ANOVA's under ρ > 0, Finding 42). Tests: layer
  excess and three factors exact, `missing_blup`/`missing_predMse` (3.575), pools unbiased by an exact
  expectation (any weights, any ρ), ANOVA's γ̂² bias `−σ²ρ/w*` in a balanced table, projections.
  *Provisional, from `studies/crossed-fit.js` (a hypothesis, not a general result)* (1000 draws × 96 worlds: table 3×2/4×3/6×4 × four effect mixes ×
  ρ 0/0.5 × volume spread 0/1 × app/thesis regime; output `crossed-fit.out.txt`): **truncation: clip** (least
  squares on the pool equations, equal weights, is worse in 67 worlds, better in 10); **weights: inverse
  variance** `1/(P̂_class + noise of the difference)²` from a first equal-weight pass (worse than equal
  in 1, better in 59, max +2.3 points; better than volume products in 44, worse in 17). Equal and volume
  weights split by regime (volume better at low credibility, equal at the thesis level). Inverse variance is
  only nearly unbiased (γ̂² +7% of τ² at ρ = 0.5), so its step is "not proved yet". Mean over the grid in %
  of the floor: iv 130, equal 132, volume 134, ANOVA 135, best blend with true parameters 146, thesis fit 157.
  Watch out: with weak effects (z ≈ 0.2) the crossed fit (145) loses to the thesis fit (139): three
  noisy variances cost more than they buy. Lean candidate: unbiasedness is exact for fixed weights only.
  *General targets (lean chat), which would replace this ranking:* (1) the minimum-variance unbiased
  pool within a class is GLS on the pair estimators' covariance table (`glsWeight_optimal`, the table from
  `Cumulants.covariance_quad_of_cumulants`; distribution-free); (2) under normal noise
  Var((μ̂ᵢ − μ̂ⱼ)²) = 2(E(μ̂ᵢ − μ̂ⱼ)²)², so inverse variance is GLS's diagonal; the limits signal ≫ noise (equal
  weights) and noise ≫ signal (large cells favoured) explain the regime split; (3) balanced table: equal
  weights exactly optimal (symmetry). Then the app tries full GLS pool weights.
  *Proved 2026-11-26* (`Credibility/CrossedPoolWeights.lean`, `CrossedPoolNormal.lean`): (1)
  `Model.pairPool_gls_optimal` (any moments to order four; `variance_pairPool`: Var = aᵀVa with
  `V = pairCovTable` from `Cumulants.covQuad`); (2) `Model.variance_sq_muHat_sub_of_normal` (normal
  layer), `sqIVWeight_div`/`_anti`, `tendsto_sqIVWeight_atTop` (θ → ∞: equal weights; θ = 0: ∝ nₚ⁻²);
  (3) `Model.pairPool_equal_optimal_of_balanced` (full table, equal volumes, moments invariant under
  row and column permutations). So the regime split of the study is the two limits of (2), and equal
  weights are exactly right in a balanced table. *App next:* a fit variant with full GLS pool weights
  (V from fitted moments: normal-noise `covQuad` with κ₃ = κ₄ = 0 is the natural first plug-in);
  compare with inverse variance (GLS's diagonal) in `studies/crossed-fit.js` before changing the default.
- [x] Plug-in MSE (2026-11-22, `Core.Target.integral_sq_plugIn`). *Done 2026-11-22:* `simulate`
  returns `split` per fit (E B², 2E[AB], SEs; A = oracle BLUP error, B = fit − oracle rate,
  exposure-weighted; sums to the excess draw for draw), shown under Many draws; world switch
  "Normal noise" (`params.normal`). Test: identity, cross term 0 under normal noise
  (`plugIn_mse_of_normal`), clearly negative in the gamma world. **Seen (3000 draws, BLUP on
  corrBS's K̂, in % of the oracle's MSE):** default world: E B² +18, 2E[AB] −6 (gamma) vs +15, +0.5
  ± 1.2 (normal); `T = 4`, shapes 1: cross term −1.8e-3 against E B² 3.2e-3, so skew roughly halves
  the price of estimation (S9: the fit can beat the oracle). With `ρ > 0` the theorem's predictor
  uses the cohort means only, which are then not sufficient; the cross term was still within noise.
- [x] Plug-in bias (2026-11-21, `Core.Target.blup_plugIn_unbiased_of_symmetric`). *Done 2026-11-22:*
  `simulate` returns `bias` per fit and for the oracle (exposure-weighted mean error and per region,
  with SEs), shown under Many draws. Test: `fitBLUP` is translation invariant (X + c) and even
  (−X) to 1e-10; unbiased under normal noise per region; oracle and BS unbiased. **Seen (4000
  draws, pooled mean error in % of the tariff):** default gamma world: oracle, BS, own, pool −0.05
  (z −1.3, i.e. 0); corrBS −0.35, BLUP −0.37 (z ≈ −9); `T = 4`, shapes 1: corrBS −2.2, BLUP −2.4
  (z ≈ −37), BS +0.01. Normal: all 0. So under skew corrBS and its BLUP *under-price the portfolio*;
  BS escapes by exposure balance. Likely cause (not checked): a region with high noise draws has a
  high mean and a high σ̂ⱼ² together, so it gets less weight. Open for the owner: log as a finding
  (outside the distribution-free core: the core only promises unbiasedness for known K), and
  try a fix that keeps the plug-in BLUP but restores balance, e.g. the G7 balanced shift.
  *Logged as Finding 35 (2026-11-22).* The pooled `σ̂²` removes it (scratch check, not in the app).
- [x] Finding 35 remedies (2026-11-22): fits `blupPool` (pooled σ̂², `vcEstimate(data, { pooled })`)
  and `blupBal` (BLUP + common shift D, exposure-balanced every draw, exact plug-in MSE with the
  shifted weights; `Core.commonShift_optimal`), with recipes and a Node test. **Seen (3000 draws;
  MSE in % of the oracle / portfolio bias in % of the tariff):**
  | world | BLUP | pooled | balanced | BS |
  |---|---|---|---|---|
  | default (gamma) | 113 / −0.36 | 111 / −0.05 | 112 / −0.05 | 111 / −0.05 |
  | normal | 113 / 0.04 | 113 / 0.04 | 112 / 0.04 | 113 / 0.04 |
  | T = 4, shapes 1 | 126 / −2.33 | 109 / 0.00 | 115 / 0.02 | 108 / 0.02 |
  | ρ = 0.6 | 111 / −0.61 | 110 / −0.54 | 130 / −0.11 | 152 / −0.11 |
  | σ spread 1 | 123 / −0.83 | 138 / −0.06 | 125 / −0.06 | 137 / −0.06 |
  | ρ = 0.6, spread 1 | 119 / −0.99 | 152 / −0.38 | 142 / −0.14 | 167 / −0.14 |
  | J = 20 | 107 / −0.32 | 105 / −0.01 | 107 / −0.01 | 105 / −0.01 |
  So without correlation the shift fixes the bias at no cost (it even helps under strong skew);
  the pooled σ̂² also fixes it, but loses the region variances when they really differ.
  Under correlation no remedy is free: the shift costs ~20 points (exposure balance is the wrong
  balance there, S28), the pooled σ̂² leaves the `ρ̂` channel (−0.5%). Tried and dropped: shifting the
  BLUP to the pooled BLUP's portfolio level (no better than the shift, worse under ρ). Open: a
  remedy for the `ρ̂` channel (hypothesis and cross-fitting candidate: Pending, "Finding 35: the ρ̂ channel"). *Owner, 2026-11-22: balance by default* (below). Lean done (2026-11-22,
  `Credibility/RandomWeights.lean`): (a) `Core.Estimates.integral_randomLin_sub`, (b)
  `Core.Estimates.integral_portfolio_sub_of_balanced` (the balanced BLUP is such a fit). *Done 2026-11-22:*
  `simulate` returns `covDiag` (sample `Σᵢ cov(d̂ᵢ, μ̂ᵢ)` over draws, own weight vs other regions,
  per region and exposure-weighted; `weightsOf` for the BLUPs and blends), shown under Bias; test.
  **Seen:** the sum matches the bias (BLUP, T = 4 skew: −2.34 vs −2.33; default −0.31 vs −0.36) and is
  less noisy (no level draws in it); the *other* regions' terms carry it (default: own +0.04, other
  −0.35; T = 4: −0.70, −1.64), i.e. the GLS portfolio weights; BS and the balanced fits give 0 exactly.
  The monthly fit (season `β̂` by GLS, moments from residuals) is not checked yet.
- [x] Balance switch (owner, 2026-11-22; replaces "no balance switch" in G7/3b for the fits): "Balance
  the total premium", **on by default**, shifts every rate of any fit not already balanced (BS, own,
  pool are) by one `D = Σᵢ wᵢ*(μ̂ᵢ − rateᵢ)/w**` (`Engine.balanceFit`, `fitWith`, `recipeSteps`; recipe
  step "balance" linked to `integral_portfolio_sub_of_balanced`). Linear fits keep exact plug-in MSE
  with the shifted weights; the jackknife MSEP is not shown for a balanced fit. `simulate(..., { balance })`
  also returns the unbalanced MSE (`raw`), shown as the cost of balancing. The separate `blupBal`
  model is gone (BLUP + switch). Why default on: the bias is one-sided and does not average out over
  regions or years; the cost is regional noise, 0–4 MSE points up to ρ = 0.2, ~10 at 0.45, ~20 at
  0.6 (table in the Finding 35 remedies item and the chat of 2026-11-22). No automatic choice by
  `ρ̂` (would need a hand-set threshold). Balance protects the portfolio, not each region.
- Noise shape (2026-11-22, discussion after Finding 35): no distribution fitting, only moments.
  (1) Residual diagnostics per region on the fitted data: skewness, kurtosis, and whether the
  variance scales with the mean (a power law as in Tweedie GLMs). (2) If skew is clear: a
  skew-based correction of the Finding 35 bias (first order (c): skewness × `σⱼ/√(T wⱼ*)` × `ζⱼ`,
  with `κ₃` estimated from residuals, no hand-set hyperparameters), compared with the pooled σ̂² and
  the balance switch. (3) If the variance follows the mean: a variance model by volume and mean in place of
  region-specific `σ̂ⱼ²`. Any Lean result that assumes a family goes in the distribution layer.
  Out of scope: fitting a full noise family for intervals or quantiles.
  *Step 1 built 2026-11-22* (`Engine.noiseDiagnostics`, page "Noise shape" under One draw, Node test):
  per region `κ̂ⱼ`, an exactly unbiased third cumulant (k-statistic style, third cumulant `κⱼ/w^q`,
  `q = 3/2` as in the world, `q = 2` for unit sums), skewness `κ̂ⱼ/σ̂ⱼ³`, pooled `ĝ` = mean `κ̂` over
  (mean `σ̂²`)^(3/2) with a jackknife SE over regions; the variance power `p` (`σⱼ² ∝ μⱼᵖ`)
  cross-fitted, even against odd years, each direction centred on its own means. Kurtosis
  dropped: no unbiased fourth cumulant with unequal weights without squares of `σ̂²`, and step 2
  needs only `κ`. **Seen** (2000–3000 draws): `κ̂ⱼ/σⱼ³` within 1 SE of the truth in 7 worlds
  (normal: 0); pooled `ĝ` −10% (default), −20% (`ρ = 0.6`, regions share year shocks, SE then too
  small), +6% (`σ` spread 1, unequal `σⱼ`); power cross-fitted −0.08 ± 0.03 (truth 0), the naive
  same-years slope +2.1 (+4.3 at `T = 4`, shapes 1): skew alone fakes a gamma variance. But one
  draw's power has SE ≈ 1.4 at `τ = 0.1`: step (3) by mean is not identifiable from one such
  portfolio; keep it only for wide level spreads. Next: step (2) with `κ̂ⱼ` (unbiased, so the
  correction needs no ratio), compared with the pooled `σ̂²` and the balance switch.
- `degenerateTable` (2026-11-21, Finding 34): exact for the app's full panel and `φ̂ < 1`
  (`Factor.tableK_ar1_posDef_iff`). If the world gets cards entering and leaving (Step 7), the test
  is only sufficient: there, check `K̂` itself (Cholesky) instead.
- Pure premium (2026-11-21, Finding 33): when the world has a frequency–severity level
  correlation, show the exact bias of the product of separate predictions
  (`CoreVector.VecEstimates.integral_mul_pred_sub`) next to the simulated one.
- Relativities (2026-11-21, Finding 31): in the card world, show the relativity error of a
  shock-only fit against the factor fit; it is exact (`Factor.quadTab_eq`) and zero only with
  equal loadings and equal month weights (`Factor.relCoef_factor_free`). Joint against separate
  frequency × severity (`FreqSev.blupW_eq_separate`, Step 7 study): report the gain, not only the
  residual correlation (Finding 32).
- Henderson III fit (2026-11-21, `FactorEstimation.lean`): before solving, check that the basis
  tables are independent (`Model.exists_hendersonMat_det_ne_zero_iff`); drop `sⱼ²` (report
  `Cⱼⱼ + sⱼ²/wⱼ`) for a cohort with constant volume (`Factor.hendersonMat_shock_det_eq_zero`), and
  the factor when `φ = 0` (`Factor.not_unbiased_factor_of_indep`); a per-cohort AR(1) shape adds
  one scale per cohort (`Factor.henderson_factorG_unbiased`), but per-cohort white noise is the shock.
  Message in the app when the fit hits one of these. With a cohort season as fixed effects,
  leave `τ²` out of the Henderson / MINQUE parameters (Finding 27,
  `Factor.hendersonMat_cohortSeason_det_eq_zero`); test MINQUE nonsingularity by the rank of the
  `RVₖR` (`Model.minque_det_ne_zero_iff`). Under a cohort season (Finding 28): require at least
  two years per cohort for the second-moment fit (`Factor.unbiasedMean_cohortSeason_eq_zero`), and
  warn when `φ̂` is near `0` or `1` (`Factor.hendersonMat_cohortSeason_det_eq_zero_of_shape`).
  Finding 29: with two years, warn for a cohort whose `1/wⱼ,₍₀,ₘ₎ + 1/wⱼ,₍₁,ₘ₎` is flat over the
  months (`Factor.minque_cohortSeason_det_eq_zero_of_volume`) and report `Cⱼⱼ + sⱼ²h/2` there;
  otherwise the AR(1) fit is nonsingular for any prior (`Factor.minque_ar1_two_years_unbiased`),
  so the world can default to two years with seasonal volumes.
  *Engine built 2026-11-21 (`app/monthly.js`, tests `app/monthly.test.js`, no page yet):* a
  monthly world (cohorts × `12Y` months, AR(1) factor, shock, process noise, cohort level,
  cohort season, volumes `seasonal` / `yearOnly` / `flat`), the table `covTable`, and `fit`:
  `φ̂` from the pooled year-on-year cross-products at lags 1–6 (badge not proved yet), then
  MINQUE with `W = I` given `φ̂`, `τ²` dropped (proved: `Factor.minque_ar1_two_years_unbiased`),
  with warnings for one year, flat volume sums (Finding 29), `φ̂` near 0 or 1, and a singular
  system (rank of the scaled `H`). Tests: nonsingular / singular exactly where the Lean results
  say; unbiased given the true `φ` (500 draws, within 4 SE, `τ² = 0.05` and a season present);
  `yoyPooled` unbiased. **Seen:** with two years `φ̂` is very noisy (true `φ = 0.6`, `J = 4`:
  quartiles 0.01 / 0.29 / 0.86; `J = 8` with a strong factor 0.04 / 0.38 / 0.78); with three
  years 0.25 / 0.66 / 0.93. So the page should show the price of estimating `φ` next to the
  oracle `φ`, and suggest three years. Next: the page section (world switches, the fitted
  table against the truth, the warnings), then `φ̂` by profiling the MINQUE fit (REML-like)
  if the moment `φ̂` stays this noisy.
  *Page built 2026-11-21* (section "Monthly cohorts" in `app/index.html`): switches `J`, `Y`, `φ`,
  volume pattern and how the fit gets `φ` (profile / year-on-year / oracle); one draw with the
  profile curve, fitted `γλλᵀ`, `C`, `s²` against the truth, the warnings and the steps; 200
  draws with histograms of both `φ̂` and the table error given `φ̂` against the oracle `φ`; CSV
  download of the data (also for the regions draw). MINQUE now in Kronecker form (`E_ab ⊗ M`,
  `R = I_J ⊗ P`; tested equal to the dense version), about 12 ms per profiled fit.
  **Profile `φ̂`** (`phiProfile`): MINQUE given `φ` is least squares of `rrᵀ` on `RVₖR`, so
  profile `φ` by its residual `‖rrᵀ‖² − qᵀθ̂(φ)` (distribution-free; not proved). A plug-in REML
  profile fails: the unbiased `θ̂(φ)` often gives a table that is not positive definite. **Seen**
  (150 draws): RMSE profile / year-on-year 0.36 / 0.42 (default), 0.34 / 0.38 (`Y = 3`),
  0.29 / 0.34 (`Y = 4`), 0.38 / 0.51 (`φ = 0.9`), but 0.45 / 0.42 at `φ = 0.3` (profile drifts
  to 1). Both pile up at 0 and 1, where MINQUE is nearly singular (Finding 28) and the tables
  explode. **Information limit:** REML on the factor path itself, observed without noise, with
  12 month means: RMSE 0.26 (`Y = 2`), 0.17 (`Y = 3`), 0.12 (`Y = 5`) at `φ = 0.6`. So the
  noise is mostly the data (one common series, about 12 year-on-year differences), not the
  estimator; more cohorts do not help.
  *External index (2026-11-21):* world switches "index years before the data" (0–20) and
  "index noise" (× γ); the draw now builds the cells from an explicit factor path (same table,
  tested by simulation), and the index `I_t = season + f_t + noise` follows the same path.
  `phiIndex`: Gaussian quasi-likelihood of AR(1) + noise by Kalman filter (month means removed,
  γ concentrated out), consistent for any distribution (an estimating equation, not a model
  assumption); not proved. The lag-ratio fit of the index autocovariances was worse (RMSE 0.25
  against 0.19 at 10 years). **Seen** (150 draws, `J = 4`, `Y = 2`, `φ = 0.6`): index φ̂ RMSE 0.23 /
  0.19 / 0.15 for 5 / 10 / 20 index years (0.31 with index noise ×4); median relative error of
  γλλᵀ given φ̂: profile 4–7, index 1.3–1.5, oracle 1.1. So the index nearly removes the price of
  φ, and what is left is the two-year data itself (the oracle's error is over 100%). CSV download
  appends the index as rows `cohort = index` (years ≤ 0 before the data).
  *Shrinking φ̂ away from 0 and 1: not built.* No hyperparameter-free rule found: Andrews (1993)
  median-unbiased and Sørbye et al. bias correction assume normal errors (distribution layer) and
  simulate inside each fit (literature §10h).
  *Joint φ from data and index: not built.* Upper bound by simulation (150 draws), mixing the
  profile and index φ̂ with the best fixed weight (read off the truth, so unattainable): RMSE
  0.161 → 0.148 (10-year index), 0.198 → 0.189 (5 years), 0.320 → 0.258 (5 years, noise ×4).
  Estimated weights would get less, and the profile φ̂ has no cheap variance estimate. Revisit
  only for short or noisy indices.
  *Valid tables (2026-11-21, `constrainPSD`, page switch "Tables", default on):* MINQUE given φ
  is least squares θᵀHθ − 2qᵀθ, so the constrained fit (γλλᵀ ⪰ 0, C ⪰ 0, s² ≥ 0) is the
  projection of the unbiased θ̂ onto that cone in the H-metric (Pukelsheim 1981, Hartung 1981).
  Each block's Hessian is a constant times the Frobenius weights, so block coordinate descent
  with eigenvalue clipping solves it exactly (about 30 sweeps; up to 5000 when φ̂ is at an edge,
  ≤ 70 ms). Biased. *Proved* (2026-11-21, `ConeProjection.lean`): for any convex set containing the truth
  the H-projection is no further from it in every draw, `‖p-θ‖²_H + ‖θ̂-p‖²_H ≤ ‖θ̂-θ‖²_H`
  (`hsq_proj_add_le`), so its H-weighted MSE is at most the unbiased one's (`integral_hsq_proj_le`);
  it exists and is unique for `H ≻ 0` (`exists_hsq_proj`, `hsq_proj_unique`); valid tables are
  convex (`convex_setOf_posSemidef`). No app change needed (the switch exists); the page could
  show `‖θ̂-θ‖²_H` against `‖p-θ‖²_H` per draw (never negative) as a check. **Seen**
  (100 draws, median relative error γλλᵀ / C / s²): defaults, profile φ̂: unbiased 10.5 / 7.6 /
  2.2, valid 1.2 / 2.1 / 0.9; true φ: unbiased 1.1 / 5.8 / 2.2, valid 0.9 / 2.3 / 0.9. With
  `Y = 4`: valid 0.6 / 1.5 / 0.8. So the constraint removes most of the price of φ̂ and most of
  the noise of C; never γλλᵀ = 0 in these draws.
  *Premium (2026-11-21):* `drawFuture` draws the 12 months after the data (unseen by the fit);
  `predictor` is `Core.blup` for the target `Σₜ bₜX_{jt}`, `bₜ = 1/12` (`Factor.blup_season_optimal`,
  `ℓ` from `Factor.ell_apply_of_future`), season as fixed effects, τ² left out (tested: the
  weights do not change with τ², the level is in the season's span), exact MSE
  `dᵀKd − 2dᵀℓ + v` (`Factor.predMse_blup`; tested against simulation). Page: one-draw premium
  table (fit, floor, last-year mean, the world's outcome) and many draws with the MSE above the
  floor, paired over the same draws (Diebold–Mariano style, literature §10i). **Seen** (300
  draws, valid tables, MSE above the floor ±2 SE): defaults: last-year mean +30 ± 11%, profile φ̂
  +21 ± 10%, true φ +1.6 ± 1.7%; 10-year index: last +45%, profile +50 ± 19%, index φ̂
  +2.0 ± 3.1%, true φ +1.4%; `Y = 3`: profile +8.5 ± 9%; `φ = 0.9`: index +8 ± 6%, true φ +6 ± 5%.
  Unbiased tables: K̂ not positive definite in ~100% of draws, so no premium at all. So given a
  good φ, estimating γλλᵀ, C, s² costs 1–2%; the plug-in price is φ, and an external index pays
  it. Handbook note "constrain the tables; take φ from a long index" done (Result "Constrained
  tables"). *Proved* (2026-11-21): valid tables give `K̂ ≻ 0` when every `ŝⱼ² > 0`
  (`Factor.tableK_posDef`, `tableK_ar1_posDef`; any `Â ⪰ 0`, not only rank one, no `τ²`), but
  not with `ŝ² ≥ 0` alone (Finding 30, `tableK_not_posDef`); the valid set is closed and convex
  (`ConeProjection.isClosed_setOf_posSemidef`). App (2026-11-21): `sZeroCohorts`,
  `zeroVarianceCohorts`; the many-draws premium table shows, per valid row, "no premium in x%"
  next to "some ŝⱼ² = 0 in y%", and the one-draw premium names the clipped cohorts. Test: no
  premium only with some ŝⱼ² = 0, a zero-variance cohort means no premium, a full-rank Â with
  ŝ² > 0 gives one. **Seen** (150 draws per world, valid tables): some ŝⱼ² = 0 in 81–100% of
  fits (defaults 89%, `J = 6` 100%, `s² = 4` 98%), yet no premium failed and no cohort had
  Â = Ĉ = ŝ² = 0: Âⱼⱼ or Ĉⱼⱼ always stayed positive. So the guarantee is often lost but has not
  bitten; s² is seen only through volume variation (Finding 23), so the projection clips it. Next: exposure-weighted targets (`bₜ ∝ wⱼₜ`, needs future volumes) and
  the rolling-origin comparison on data (card-data Step 7b): *built 2026-11-21* (page section
  "Comparing fits on data"; status and what was seen in `notes/card-data.md` Step 7b). Candidate
  for Lean (argued in `degenerateTable`, not proved): for valid tables, `K̂ ≻ 0` iff
  `Â_ZZ + Ĉ_ZZ ≻ 0`, `Z` the cohorts with `ŝⱼ² = 0` (contains `Factor.tableK_posDef`, `Z = ∅`, and
  `tableK_not_posDef`).
  *H-norm check (2026-11-21):* `fit` returns θ̂, the projection p and H (`minq`); the world-side
  `hNormCheck` computes ‖θ̂ − θ‖²_H, ‖p − θ‖²_H, ‖θ̂ − p‖²_H and the slack of
  `ConeProjection.hsq_proj_add_le`. Page: per draw under the tables (valid tables only) and over
  many draws per φ. Test: slack ≥ −10⁻⁶‖θ̂ − θ‖²_H over 320 fits (profile and true φ). **Seen**
  (500 draws, five worlds): never negative, smallest relative slack 4·10⁻⁴; ratio projected /
  unbiased quartiles 0.55 / 0.75 / 0.87, max 0.998.
- Factor estimation part 1 (2026-11-20, `FactorEstimation.lean`): the first unbiased step of
  the factor fit is the year-on-year lagged cross-product per cohort pair and lag
  (`Factor.yoy_unbiased_factor`; free of `C`, `s²`, `τ²`, per-cohort `G` and of any per-cohort
  calendar season). Report loadings normalised to exposure-weighted mean `1` (`blup_rescale`:
  presentation only); with a stationary `Γ` the app need not split lag-0 covariance between
  shock and factor (`blup_eq_of_lag0`), so show `C + γλλᵀ` as one matrix.
  2026-11-21: individual loadings need three cohorts (`load_sq_of_three`); with two the app
  should report only `λ₁λ₂` (`two_cohorts_not_identified`). `φ̂ = Σ₂/Σ₁` from pooled
  cross-moments (`ar1_identified`). Finding 26: the world-vs-fit comparison should show that
  a shock-only fit on factor data misreads `C` (`crossHat_ar1_two`: `C + (1 - φ)γλλᵀ`).
  Its `ŝ²` and `τ̂²` too (`tauHat_factor_unbiased`): show the shock fit's `τ̂²` against the
  true `τ²` when loadings differ. Fit given `φ`: MINQUE with the forms `RVₖR`
  (`Model.minque_unbiased`, parameters `Factor.shapeBasis`), prior `W` from the previous
  iterate, profile over `φ` (plan item 4); report the raw estimate as unbiased, the
  truncated one as the fit.
  *Status 2026-11-22:* built in `app/monthly.js`: `φ̂` (year-on-year, profile, index), MINQUE given
  `φ̂`, `γλλᵀ` shown as one matrix. Open: the shock-only fit on factor data (Finding 26: its `Ĉ`,
  `τ̂²` against the truth); loadings `λ̂` normalised to mean 1, only `λ₁λ₂` with two cohorts.
- Common factor (2026-11-20, `Factor.lean`, Finding 25): the fit switch "latent factor over
  time: none / independent months / AR(1) / break at known dates" with `K` from `Factor.K`,
  `ℓ`, `v` from `Factor.ell`, `Factor.var` and weights from `Core.blup` (oracle with the true
  `Γ`; estimated `Γ`, `λ` after Step 4). The app should show negative cell weights as normal
  (`Factor.blup_neg_of_ar1`), not flag them as an error. Also "per-cohort AR(1)" (`Factor.KG`,
  `ellG`, `varG`); the world can simulate any cells with these moments (`Factor.Cells`).
  Estimation (literature §10h): fit `φ̂` from lag ratios, `λ̂`, `Ĉ` by moments given `φ̂`,
  then Gaussian quasi-ML by Kalman EM (missing cells for cohorts entering and leaving);
  sandwich standard errors, no hyperparameters.
  *Status 2026-11-22:* built: AR(1) with the true or fitted table, premium by `Core.blup`. Open: the
  switch "none / independent months / break", per-cohort AR(1), negative cell weights shown as
  normal, Kalman quasi-ML with missing cells (needs cohorts entering and leaving).
- Season (2026-11-20, `Season.lean`, Finding 24): a fit switch "season: none / estimated
  (one fixed effect per month) / known index". Ignoring a real season biases the forecast by
  `Σₘ (Sₘ(d*) - cₘ)βₘ` (`Core.Target.integral_bias`), which the app can show per cohort; the
  known-index oracle weights cells by expected claims `cₜwⱼₜ` (`Unequal.a_eq_of_volume`).
  *Status 2026-11-22:* built: season as fixed effects (always on). Open: the switch "none / known
  index" and the bias of ignoring it per cohort.
- General best predictor (2026-11-20, `Blup.lean`): any target (e.g. a 12-month total)
  and fixed effects (a season) via `Core.blup`; its error shows the price of estimating the
  season (`Core.predMse_blup`). For Step 7 of `notes/card-data.md`. With known covariances,
  annual totals lose exactly `(Ac - d*)ᵀK(Ac - d*)` (`Core.predMse_aggregate_eq_blup_add`) and
  an unneeded season costs `(d₂* - d₁*)ᵀK(d₂* - d₁*)` (`Core.predMse_blup_nested`): the oracle
  side of the Q3 study (monthly against annual), against which the estimated fits are compared.
  *Status 2026-11-22:* built: 12-month target and its exact MSE (`predictor`, tested). Open: the
  annual-totals and unneeded-season oracle losses next to the estimated fits.
- Finding 23 (2026-11-19): the world model's period shock should be `C + s²/w` (does not
  shrink with volume), not `σ²ρ/w`. Check what `engine.js` simulates; with growing volumes
  the thesis fit is then misspecified, which the app could show. Now proved
  (`Credibility/Shock.lean`): a fit switch "shock + process noise" with `K` from
  `Shock.K_apply` and `Ĉ`, `ŝ²` from `Shock.CHat`, `Shock.s2Hat` (exposure weights, weightings
  `1` and `w`; works whenever `T ≥ 3` and the volumes vary (`Shock.det_expo_neg`), else fall back to the thesis fit), and `τ̂²`, `K̂` from `Shock.tauHat`,
  `Shock.KHat` (portfolio weights `x = w_{j*}/w_{**}`; proved 2026-11-20).
  *Status 2026-11-22:* not built: `engine.js` still draws the period shock as `σⱼσₖρ/√(wⱼwₖ)`.
- Monthly cohort data (2026-11-20, `notes/card-data.md` Step 7): a world with a monthly season,
  an AR(1) demand factor (optional break) seen through a noisy observed index, equal or unequal
  loadings and cohorts entering and
  leaving; every switch of the note's toolbox table as a fit. After its Lean Step 3.
- Matrix blend (2026-11-19, `CoreVector.lean`): vector levels with a credibility matrix `Z`,
  matrix GLS and matrix eq. (26) `Zⱼ = (Lⱼⱼ - EⱼᵀLW)(Kⱼⱼ - (UᵀK⁻¹U)⁻¹)⁻¹` are proved. App: the
  frequency × severity comparison (`notes/time-trends.md` §3 item 3) can add a fourth fit,
  the bivariate blend, once the step from `(φ, ψ)` to the premium is settled. Finding 22:
  the bivariate *blend* can lose to separate blends with correlated cohorts (small gap);
  the bivariate best predictor `blupW` never does. Show both, or the predictor. Hachemeister
  with correlated cohorts is proved too (`hachemeister_bestZ`): an app step "cohort trend
  lines" (level + slope per cohort, shared year shocks) would show `Z` as a 2 × 2 matrix.
  *Studied 2026-11-27 (S65, `studies/vector-lambda.js`):* fit `Λ̂` diagonal by default (level, slope,
  F, Y as four scalar credibilities after centring); a block (full) `Λ̂` loses up to 31 (59) points against it
  to estimation noise and wins only for a well-measured component with a strong
  level–slope correlation. Next: damped off-diagonals (θ from data), year shocks, a better `Λ̂`.
  *Revised 2026-11-27 (S66, `studies/vector-lambda-damp.js`):* default to the exposure-weighted moment
  `Λ̂` with off-diagonals damped by the plug-in `θ̂` (`Damping.lean`'s `θ*`) and projected PSD: never
  significantly worse than the diagonal fit in 64 worlds (with and without year shocks), up to 26
  points better. *Revised again (S67, `studies/vector-lambda-shocks.js`):* with year shocks, fit the
  joint damped BLUP (`ρ̂` from same-year residual pairs, `Λ̂` corrected for the noise covariance between
  cohorts, `K̂ = I ⊗ Λ̂ + N̂`): at most 2–3 points dearer without shocks, up to 27–147 points better with
  them. Lean target: the corrected moment identity (S67 Consequence).
  Also proved: with independent cohorts the bivariate blend is the best predictor, and with
  no frequency–severity covariance (in `K` and `L`) the separate best predictors are the
  bivariate one, so the app's fourth fit only matters when cohorts or components correlate.
  Balance of the matrix blend (`vecBalanced_iff`) needs no app switch beyond the scalar one.
  Moment layer (`CoreVectorMoments.lean`): the matrix MSE formulas are the true error
  covariances of any random vectors with these moments, so the app's simulated bivariate
  fits can be checked against `errVar Z` exactly as the scalar ones; no new switch.
- Claim trend (2026-11-19, `Trend.lean`, Finding 21): restating with the true `g` moves no
  weight (`K̃ = (1+g)^(2n)K`, `bestZ_detrend`); with `ĝ ≠ g` relativities move slightly. App:
  switch "claim trend g" (today `growth` is volume growth) and the `ĝ` study of
  `notes/time-trends.md` step 2 should show the size of that effect.
- Taper switch (2026-11-17, `OffDiagonal.lean`): repair or regularize `K̂` by tapering it
  with a correlation matrix `R` instead of only damping (`posDef_hadamard_of_corr`: `R ⪰ 0`
  with unit diagonal keeps `K̂ ≻ 0` and the variances). Options: "damp θ" (today's
  `R = θ11ᵀ + (1-θ)I`) and "distance ρ^|tᵢ-tⱼ|" for cohorts with an order (years, age
  bands; `distTaper_posSemidef`, ties allowed). Badge "proved" for both when `Σ̂ ⪰ 0`.
  Its `ρ` must be fitted, not hand-set (§1): e.g. choose it like `θ`, by the plug-in
  criterion of `studies/damping-theta.md`. *Done 2026-11-22:* fit "corr taper"
  (`fitCorr(data, { taper: 'distance' })`, `taperRho`: S3's loss per distance, ρ̂ on a 0.001 grid,
  equal to S3's θ̂ when all pairs are at distance 1), badge "proved" (`posDef_distTaper_hadamard`)
  when `Σ̂ ⪰ 0` and `τ̂² > 0`; world switch "decays with distance" (`params.ordered`, noise
  correlation `ρ^|i−j|`). Node test. **Seen** (`studies/taper.js`, S33–S35): no gain over damping
  for the blend, even at the best fixed ρ; corrBS stays best. *Then (2026-11-22):* "corr" damps by S3's
  θ̂ (old grid rule kept as `thetaRule: 'grid'`); fit "BLUP taper" (`fitBLUPTaper`, `blupOn`),
  Node tests. **Seen** (`studies/taper-blup.js`, S36–S37): with J = 20 ordered regions the BLUP on
  the tapered `K̂` is 9–28 points (of the blend floor) better than BLUP on corrBS's `K̂`; about even at
  J = 8, T = 10; worse with T = 5 or a common ρ. *Data-side signal 2026-11-24* (`studies/taper-signal.js`,
  S46–S48): `Engine.taperSignal` compares S3's plug-in loss of the tapered correlation table with that
  of one common r̄, no tuning; `fitBLUPAuto` takes the BLUP on the preferred table. Safe (tapers a
  common-ρ world in 0–2% of draws, never costs more than 4 points against BLUP) but timid (tapers 13–61%
  of draws in ordered ρ = 0.9 worlds, where the taper gains up to 29 points; regret up to 13).
  *On the page 2026-11-24:* fit "BLUP auto" (`blupA`), with a conditional recipe (below). Leave-one-year-out (`Engine.loyoLoss`, `fitBLUPLoyo`, S49) was tried: bolder in ordered worlds, but
  tapers a common ρ in 26–45% of draws (up to 13 points); mean regret 2.0 against 1.4. Keep the plug-in signal.
- [x] Temporal decay (2026-11-22, literature §10l, Morris 2026): compare an EWMA weighting of
  years, with λ fitted, against the BLUP under an AR(1) `Γ` in the card world. *Done 2026-11-24*
  (`studies/ewma-decay.js`, S43–S45 in `damping-theta.md`): EWMA of own annual means is a predictor
  from aggregated data, exact excess `Blup.predMse_aggregate_eq_blup_add` (Node test). Oracle λ* costs
  0–31% over the BLUP: it sees only its own cohort, while the BLUP reads the common factor from all
  cohorts. λ* falls with s²ⱼ/wⱼ (bigger cohorts, shorter memory; φ = 0.97: 0.5–0.7 at w0 = 100,
  0.06–0.08 at 10 000), so Morris's size-dependent λ comes out of the model. Fitted: BLUP 110–123%
  of the oracle, EWMA λ̂ 110–136, last year 127–166. App: rolling-origin fit `ewma` ("EWMA of own
  years, λ fitted", `Monthly.ewmaYears`, `ownYearsBest`) for comparison, not a recommendation.
  Lean: nothing new (no Finding).
- [x] OBP collective mean (2026-11-25, literature §10p, Zhang & Jiang): the observed best predictor's
  collective mean is the `(1 − zⱼ)²`-weighted mean (SURE of the MSE given the levels). Possible study: a
  world switch "levels trend with volume" (the collective mean is misspecified), comparing BS, BS with the OBP mean,
  and grouping (KMeansBridge). Expect OBP to lose in the exchangeable worlds (`studies/sure.js` (B)). Not a
  fit to recommend before that study. *Proved 2026-11-25* (`Credibility/ObservedBest.lean`): the error
  given the level, its SURE, and that `Core.obpMean` minimises both the total error given the levels and
  its observed estimate. App: the study's "OBP mean" fit would use `obpMean` on the `x̄ⱼ`.
  *Studied 2026-11-25 (`studies/obp-mean.js`, S59–S62 in `damping-theta.md`):* no. Fitted, it is ±1–5% of BS
  (worse without a trend, better only with a trend of τ or more), it breaks balance, and with known per-cohort
  variances it is up to 58% worse (its own noise). No app fit; a handbook "watch out" at `res:bs`.
  Two side results: grouping by cuts of the sorted estimates chosen by SURE is 2–74% worse than BS (S61,
  see "Grouping cohorts" above), and a volume trend as a design column `[1, log w]` (BLUP) gains 3–35% at a
  trend ≥ τ for a price of 0.5–12% without one (S62).
