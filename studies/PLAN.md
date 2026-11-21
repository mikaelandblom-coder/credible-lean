# From theorems to practice: the credibility app

Written 2026-11-13, revised the same day (an interactive app instead of
written simulation studies). Status: steps 1–3 built 2026-11-14 (`app/`,
live at `/app/`). Tick items off as they are done.

**Aim.** Give a practitioner clear examples of what each result buys. One
page, usable on a phone: choose how complex the *world* is, choose how
complex the *fitted model* is, and see what happens when they differ.

## 1. Principles

1. **The fit never sees the truth.** A fitted model gets the data and
   nothing else: every parameter it uses is estimated. In the code the
   fitting functions take only the data table, so this cannot be broken by
   accident.
2. **A theorem is practical only when it ends in a recipe from data.**
   Results that assume known parameters are building blocks, not results
   for the app (section 5).
3. **One world, two models, side by side.** The fitted model is always
   shown against a reference model the user picks.
4. **Short and visual.** No study to read: a few switches, one chart, one
   number.
5. **No tuning.** A fit is determined by its data alone: no hyperparameters
   (owner, 2026-11-14). A choice such as a damping θ must itself be
   estimated from the data, or the model changed so it is not needed.
6. **Every new extension of the framework gets a switch.** The app is
   built so that adding one is a small, local change (section 6).

## 2. What the user sees

**World** (the truth; a switch or slider per feature):

| Feature | Off | On |
|---|---|---|
| Correlation between cohorts within a year | `ρ = 0` | slider `ρ` |
| Unequal lengths | all cohorts 10 years | some start late |
| Group levels | cohorts unrelated | a shared level within groups, slider `φ` |
| Size | sliders for the number of cohorts and years, and how unequal the volumes are | |

**Fitted model** and **reference model**: the same list of features, each
on or off. Presets for the reference: Bühlmann–Straub (default), and the
thesis model with correlation.

**The mismatch is the point.** For each feature there are four cases:

| | not in the fit | in the fit |
|---|---|---|
| **not in the world** | baseline | cost of estimating something that is not there |
| **in the world** | cost of ignoring it | gain from modelling it |

**Output**, top to bottom:

1. *One draw.* Per cohort: the true level, the cohort's own mean, the rate
   from the fitted model and from the reference. "New draw" button.
2. *Many draws.* Total error (exposure-weighted MSE of the rates) of fit
   and reference over a few thousand draws of the same world, computed
   live, with a third line as the floor: the best possible if the
   parameters were known. The floor is a benchmark, never a fit. The gap
   between fit and floor is the price of estimation.
3. *The fitting steps*, on the current draw: data → cohort means → `σ̂²` →
   correlations → `τ̂²` → damped `K̂` → weights `b` → `z` → rates. Each
   step shows its formula, its numbers and a badge:
   **proved** (link to the handbook result and the Lean theorem) or
   **not proved yet** (a heuristic step; these are the gaps of section 5).
4. *Warnings* when they occur: `τ̂² < 0` (truncated), `z > 1`, negative
   `b`, off-balance.
5. *Recipe* (added 2026-11-19, owner's request), at the bottom: for the fit or the
   reference, every formula and rule in order (truncations, the choice of `θ`, the
   jackknife), the notation it needs and the badges, with "Copy as text", so the model
   can be applied outside the app. Built from `RECIPES` in `engine.js`, which shares the
   formula table `F` with the fits; a test checks that recipe and fit agree step by step
   and that every symbol is defined. A new fit model needs its recipe entry.

## 3. The world's story

Generic and textbook: **motor insurance, claim cost per vehicle-year by
region, regions grouped in countries, 10 years.** (The classical
credibility datasets look like this, e.g. Hachemeister's states by
quarter.)

- A cohort is a region; its volume is vehicle-years; its level `μⱼ` is how
  expensive the region really is relative to the tariff (`μ = 1`).
- Correlation: a hard winter raises claims in all regions that year, most
  within the same country.
- Unequal lengths: regions the company entered recently.
- Groups: regions of one country resemble each other.

Purely simulated, so the truth is known. Skewed distributions, since the
theory is distribution-free.

## 4. Technology

- **One self-contained page** `app/index.html`, no external libraries or
  network requests after loading. Published by the existing CI next to the
  blueprint: `https://mikaelandblom-coder.github.io/credible-lean/app/`.
- **Offline**: a small service worker and manifest, so the page can be
  added to the phone's home screen and opened without a connection.
- **The engine is JavaScript, not Python.** Reason: the app must compute
  on the phone, and Python in a browser means a download of about 10 MB
  and a slow start. The math is small (12 × 12 matrices), so plain
  JavaScript does thousands of draws in a blink. To keep a single source of
  truth, the same engine file `app/engine.js` is run by CI under Node for
  the tests. (Owner: say so if you prefer Python despite this; the
  alternative is Pyodide.) *Decided 2026-11-14: JavaScript; the floor line
  stays.*
- **Tests are the proved identities**, to machine precision: BS at
  `ρ = 0`; balance; `b₁ = z₁/(z₁+z₂)`; the equal-covariance closed form;
  eq. (26) minimises the MSE; `K̂ ≻ 0` after damping; estimators unbiased
  on average. Plus one structural test: no fitting function receives the
  world's parameters.

## 5. What is practical today

Revised with principle 2. A step is in the app as **proved** only if it is
a recipe from data.

| Fit feature | Recipe from data | Proved | Missing |
|---|---|---|---|
| Bühlmann–Straub | yes | `bs_z`, `bs_balance`, `σ̂ⱼ²` (`sigRhoHat_self`), `τ̂²` of eq. (13) (`tauHatBS_unbiased`) | |
| Correlation, full `K̂` | yes: eqs. (37)–(41), damping | `KHat_unbiased`, `dampedK_posDef` | choice of the damping `θ` (G2) |
| Correlated BS, credibility-weighted variances (`fitVC`, default reference) | yes: σ̃ⱼ², ρ̂, τ̂² by moment equations, no damping | `K_posDef` (common ρ̂ ∈ [0, 1)), GLS `b`, `z` | unbiasedness of `ρ̂σ²`, `Wⱼ`, `β²` (G1); jackknife MSEP is numerical only |
| Correlation, one common covariance (not recommended, finding S4) | average of the pairwise estimators | closed form for `z` (`bestZ_of_equalCov`) | the estimator (G1) |
| Unequal lengths | yes | `Unequal.KHat_unbiased`, count `nᵢⱼ` | |
| Group levels | `φτ²` from pairs | `phiTauHat_unbiasedG` (one pair of each kind) | pooling all pairs (G4) |
| `z > 1`, negative `b` | clip (thesis eq. (34)) | diagnosis only | G3 |
| Choosing cohorts | not yet: the rules need the true levels or the true `d` | `merge_iff`, `pool_optimal_contiguous` | G5; not in the first version |

Known-parameter results (optimal `z`, GLS weights, true MSE) appear only as
the floor line and in the tests.

**Gaps: candidate theorems**, in the order the app needs them:

- **G0. The classical BS `τ̂²`** of eq. (13) is unbiased when `ρ = 0`.
  The Lean `tauHat_unbiased` is the thesis estimator (39)–(41), which uses
  all pairs `ĉⱼ`; the app's BS fit uses eq. (13) and shows it as "not
  proved yet". The Node test checks it by simulation only. Probably easy.
  *Proved 2026-11-15 (`Model.tauHatBS_unbiased`, with the `1/J` of Finding 7):
  for uncorrelated cohorts with a common `σ`, it differs from (39) by a term
  with expectation 0. The app's BS `τ̂²` step now shows "proved".*

- **G1. One common covariance.** The average of the pairwise estimators
  (39) is unbiased for a common `c`. One extra parameter on top of BS;
  probably the most practical form of the thesis model. *Numerical study
  2026-11-14 (`studies/damping-theta.md`): with unequal volumes a common
  covariance is misspecified and its z explode; a common **correlation**
  `Σᵢⱼ = ρ̄√(ΣᵢᵢΣⱼⱼ)` is the better one-parameter model (H1 there).*
- **G4. Pooled pair estimator of `φτ²`**, unbiased for any weights.
- **G3. Clipping** `z` to `[0, 1]`: when is it harmless?
- **G2. Damping as shrinkage.** Is there a safe `θ`? *Numerically, the
  rule `θ̂ = ρ̄²/(ρ̄² + (1−ρ̄²)²/(T−1))` is within 2 points of the best fixed
  `θ` in 23 of 24 worlds (H2 in `studies/damping-theta.md`).*
- **G6. Forecasting.** The same `z` is optimal for next year's outcome
  (MSE grows by next year's noise). Then the app can show a premium, not
  only a level.
  *Proved 2026-11-15 (`Core.Estimates.mse_forecast`, `bestZ_forecast_optimal`):
  for `Yⱼ = μⱼ + εⱼ` with fresh noise uncorrelated with the estimates and the
  level, MSE = level MSE + `Var(εⱼ)`, and `zⱼ` stays optimal. App: add a
  **premium step** after the blend: premium `= μ̂ⱼᵇ` (no change to `z`), its
  forecast error `= MSE + σ̂ⱼ²/wⱼ,next` with next year's volume `wⱼ,next` (a
  new input, default this year's mean `wⱼ*/T`), badge "proved"; the floor line
  compares with the world's actual next-year draw.* *App step added 2026-11-15: `Engine.premium`
  (plug-in level MSE, or the jackknife MSEP for corrBS, plus `σ̂ⱼ²/wⱼ,next`), a slider
  for next year's volume (× `wⱼ*/T`), next-year columns in the draw table, and a
  line under Many draws comparing fit, reference and floor with the world's
  next-year outcome and the floor's theory; Node test: the simulated next-year
  error matches `floorForecast` per region.*
- **G7. Balance** under correlation: the best balanced blend. *Proved
  2026-11-15 (`Core.bestBalanced_optimal`, true MSE
  `Estimates.bestBalanced_mse_optimal`, Finding 15): keeping `b`, the
  balanced blends are `zⱼ = 1 − c·bⱼ/uⱼ` and the best `c` is a weighted least
  squares fit. But it is a poor way to balance (up to 2× the floor's error in
  `studies/vc-balance.js`, column `opt`), so the app gets no switch for it:
  its balance step stays the common shift. Next candidate (G7b): the
  shift `μ̂ⱼᵇ + Σuᵢ(μ̂ᵢ − μ̂ᵢᵇ)/u*` is the best balanced correction of the
  form "blend plus a common linear term" (Wang–Fuller–Qu with loss weights
  `φ = u`), likely by the same parabola argument.* *G7b proved 2026-11-15
  (`Core.bestCorrection_optimal`, `commonShift_optimal`, true MSE
  `Estimates.bestCorrection_mse_optimal`, `commonShift_mse_optimal(_of_diag)`,
  Finding 16): the best correction `μ̂ⱼᵇ + cⱼD` has a closed form (WFQ). It is
  the common shift exactly when `cov(μ̂ⱼᵇ − μⱼ, D)` is the same for all `j`.
  That always holds for independent cohorts, but not under correlation,
  where the shift loses at most about 2% in random worlds. The app keeps the
  shift; no switch.*
- **G5. Decisions from data** (merging, choosing cohorts). Hardest, last.

The app itself decides the priority: a gap that makes no visible
difference on the screen is dropped.

## 6. Built for expansion

A feature is one entry in a list in `engine.js`:

- its name and controls;
- its recipe (`RECIPES`: formulas from `F`, rules, badges);
- how it changes the world (generator);
- how it changes the fit (which estimation steps it adds);
- per step: formula, handbook result, Lean theorem, proved or not.

The page is drawn from that list. So a new extension (serial correlation,
trends, crossed levels) means: prove it, add one entry, add its test.
`CLAUDE.md` asks the question for every new result, as it does for the
handbook.

## 7. Order of work

One chat per step; none needs Lean except step 5.

- [x] 1. `engine.js`: world generator, BS fit, floor; identity tests under
  Node in CI (`app/engine.test.js`, run by the `docs` job).
- [x] 2. `app/index.html`: world and fit switches, the one-draw chart, the
  many-draws bars. Published on the site. First usable version. Notes:
  references are "own mean" (z = 1) and "one tariff" (z = 0) until step 3
  adds a second real fit; correlation is one common `ρ` for now (the
  country structure comes with group levels); the fitting-steps panel data
  is already in `fitBS(...).steps`, the panel itself is step 3. Not yet
  tested from the Node side: damping (`K̂ ≻ 0`), which arrives with `K̂`.
- [x] 3. Correlation fit (full `K̂` damped, and common covariance), the
  fitting-steps panel with badges, warnings. Notes: `fitCorr` in
  `engine.js`; reference preset is now the correlation fit. Damping: `θ =
  0.95`, lowered in steps until `K̂ ≻ 0` (badge "proved" only when `Σ̂ ⪰ 0`,
  by `posDef_shrinkOffDiag`; otherwise a numerical check, G2). The common
  variant takes `ĉ` = mean of the pairwise `σ²ᵢⱼρᵢⱼ^`, uses it in `ĉⱼ` and
  `τ̂²` too (G1), and the closed form `zⱼ = τ̂²/(τ̂² + v̂ⱼ − θĉ)`. Seen on
  screen: with unequal volumes and `ρ > 0` the common variant gives `z > 1`
  in most draws (true covariances shrink with volume, so `ĉ` exceeds the
  large regions' `vⱼ`), and an error many times the floor: a common
  *correlation* may be the better one-parameter model (candidate for G1).
  The full fit is not balanced (off-balance warning above 1%); at `θ = 0` it
  is BS with one `σ̂ⱼ²` per region (tested). A seed field (default 12345)
  fixes the one draw and the many draws. A Node test checks that every step
  marked proved names a declaration in `progress.py --proved`.
- [x] 3b. No-tuning fit and its error (2026-11-15; `studies/damping-theta.md`, findings
  S15–S26). `fitVC` in `engine.js`: correlated BS with credibility-weighted variances
  (`variance-credibility.js`, mode `cred`), every parameter by a moment equation, no `θ`;
  the default reference. The common-covariance fit stays in the list, marked not recommended
  (finding S4). `jackknifeMSEP` (`msep.js`) gives each region a "typical error" of the `vc`
  rate, shown in the one-draw chart and table as an average-case error, not an interval
  (finding S26). Tests: `K̂ ≻ 0` on every draw; equal to BS when `ρ̂ = 0` and `β² = 0`;
  identical to the study scripts; jackknife MSEP within 25% of the actual MSE on average in
  one fixed-seed world (ratio 1.00).
  World switch "spread of noise across regions" (`noiseSpread`, 2026-11-15): σⱼ = σ·4^(s((j mod 4)/3 − ½)),
  s = 1 is the ×0.5–2 spread world of `variance-credibility.js` and `msep.js` (σⱼ column in the
  one-draw table). Checked in the app's own world (gamma noise, 1000 draws, % of floor): at ρ = 0.6
  BS / corrBS / corr = 151 / 113 / 118 (J=8 T=10), 167 / 135 / 144 (T=5), 183 / 114 / 118 (J=20);
  jackknife predicted/actual 0.81, 0.89, 0.86 (finding S19: 0.85–0.90). At ρ = 0 and T = 5 the three
  tie (≈150). Tests: σⱼ and true `K` equal the studies'; draws have Var σⱼ²/w and corr ρ; corrBS
  beats BS and corr, and the jackknife ratio is in (0.75, 0.95), in one fixed-seed spread world.
  Expected flags (2026-11-15, `studies/vc-balance.js`, findings S27–S29): the floor (true K) has
  negative b and is off exposure balance too; forcing balance costs up to ≈30% more error, so no
  balance switch (the floor's costs are exact: `studies/exact-balance.js`, pinned by a test).
  corrBS returns `notes` (shown as ℹ, not ⚠) for negative b, z > 1 and off-balance
  when ρ̂ > 0 (off-balance also when β² > 0); `simulate` reports their share as `expected`. Tests:
  the floor's b < 0, z < 1 and balance in bⱼ/(1 − zⱼ); notes ↔ expected flags; balancing costs > 5%.
- [x] 3c. Findings 17–20 in the app (2026-11-17). Cohort "Is correlation worth modelling?":
  from the draw, `δ̂₋`, `δ̂₊` (eigenvalues of corrBS's noise correlation, one `ρ̂`) and the
  bound `(a + A)²/(4aA)` for ignoring it and for each model's `θ` (BS 0, corr `θ̂`, corrBS and
  BLUP 1; `Engine.correlationIndicator`, `dampedBound`); in the world, exact MSE of the BLUP,
  the best blend (+ price of the blend, Finding 18) and BS with true variances (+ price of
  ignoring, Finding 19), per region in a table (`Engine.worldPrice`). New fit "BLUP": the
  plug-in BLUP on corrBS's `K̂` (`fitBLUP`); a second floor, the BLUP with true `K`, in the
  Many draws table. `z < 0` is a warning with the Finding 17 text; the draw table shows the
  own-data weight `cⱼ`. Tests: BLUP optimality and Pythagoras, diagonal case, two-cohort
  equality, the Finding 18–19 example pinned (2.8/3.1/0.1%, 14.3/9.2/0.4%), equal-correlation
  `δ±` and closed form, bound never violated in 40 app worlds (also damped), floor BLUP
  matches its exact MSE. **Seen (2000 draws, typical error in % of the blend floor; BS /
  corrBS / BLUP / BLUP floor):** `ρ = 0`: 104 / 105 / 105 / 100; `ρ = 0.3`: 108 / 104 / 103 / 99;
  `ρ = 0.6`: 115 / 103 / 98 / 93; with noise spread 121 / 105 / 102 / 94; `T = 5`:
  119 / 106 / 102 / 93; `J = 20`: 119 / 103 / 91 / 87; `J = 4`: 110 / 104 / 101 / 97. So the
  plug-in BLUP survives estimation on corrBS's few-parameter `K̂` and beats the blend
  under correlation, often below the blend's own floor; it costs nothing at `ρ = 0`.
  Owner: make BLUP the default reference? (Not done: the blend is the thesis's object.)
  *Pair-specific correlation (2026-11-17, `blup-pairs.js`, S30–S32 in `damping-theta.md`):* with
  countries or heterogeneous loadings (corrBS's one-ρ̂ `K̂` misspecified) the BLUP on it is never
  more than 1 point worse than corrBS and up to 23 better; the blend form costs 22–73% over the
  BLUP with true parameters in country worlds; the BLUP on the full damped `K̂` wins only with
  J = 20 and strong structure, and is worst at T = 5. For step 4: a group-structured `K̂` (ρ within
  and between) with a BLUP on it, and a world switch for countries.
- [ ] 4. Unequal lengths and group levels (world and fit). Offline support.
- [ ] 5. Prove the gaps the app shows to matter (Lean chats); badges turn
  to "proved".
- [ ] 6. Link the app from the README and handbook; screenshots of a few
  telling settings as the handbook's worked examples.
  - [x] README: linked as a preview (2026-11-16, v2.0.0).
  - [ ] Handbook link and screenshots.

## Pending
(Results or findings that may need a switch, step or message in the app.)
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
- Common factor (2026-11-20, `Factor.lean`, Finding 25): the fit switch "latent factor over
  time: none / independent months / AR(1) / break at known dates" with `K` from `Factor.K`,
  `ℓ`, `v` from `Factor.ell`, `Factor.var` and weights from `Core.blup` (oracle with the true
  `Γ`; estimated `Γ`, `λ` after Step 4). The app should show negative cell weights as normal
  (`Factor.blup_neg_of_ar1`), not flag them as an error. Also "per-cohort AR(1)" (`Factor.KG`,
  `ellG`, `varG`); the world can simulate any cells with these moments (`Factor.Cells`).
  Estimation (literature §10h): fit `φ̂` from lag ratios, `λ̂`, `Ĉ` by moments given `φ̂`,
  then Gaussian quasi-ML by Kalman EM (missing cells for cohorts entering and leaving);
  sandwich standard errors, no hyperparameters.
- Season (2026-11-20, `Season.lean`, Finding 24): a fit switch "season: none / estimated
  (one fixed effect per month) / known index". Ignoring a real season biases the forecast by
  `Σₘ (Sₘ(d*) - cₘ)βₘ` (`Core.Target.integral_bias`), which the app can show per cohort; the
  known-index oracle weights cells by expected claims `cₜwⱼₜ` (`Unequal.a_eq_of_volume`).
- General best predictor (2026-11-20, `Blup.lean`): any target (e.g. a 12-month total)
  and fixed effects (a season) via `Core.blup`; its error shows the price of estimating the
  season (`Core.predMse_blup`). For Step 7 of `notes/card-data.md`. With known covariances,
  annual totals lose exactly `(Ac - d*)ᵀK(Ac - d*)` (`Core.predMse_aggregate_eq_blup_add`) and
  an unneeded season costs `(d₂* - d₁*)ᵀK(d₂* - d₁*)` (`Core.predMse_blup_nested`): the oracle
  side of the Q3 study (monthly against annual), against which the estimated fits are compared.
- Finding 23 (2026-11-19): the world model's period shock should be `C + s²/w` (does not
  shrink with volume), not `σ²ρ/w`. Check what `engine.js` simulates; with growing volumes
  the thesis fit is then misspecified, which the app could show. Now proved
  (`Credibility/Shock.lean`): a fit switch "shock + process noise" with `K` from
  `Shock.K_apply` and `Ĉ`, `ŝ²` from `Shock.CHat`, `Shock.s2Hat` (exposure weights, weightings
  `1` and `w`; works whenever `T ≥ 3` and the volumes vary (`Shock.det_expo_neg`), else fall back to the thesis fit), and `τ̂²`, `K̂` from `Shock.tauHat`,
  `Shock.KHat` (portfolio weights `x = w_{j*}/w_{**}`; proved 2026-11-20).
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
  criterion of `studies/damping-theta.md`.
