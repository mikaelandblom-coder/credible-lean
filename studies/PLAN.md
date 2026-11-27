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

### Study conventions (2026-11-24, after `studies/runs/taper-signal.js`)

**General results first (owner, 2026-11-26).** A result that holds for every world (a theorem, or a
statement with its conditions) is worth far more than a ranking in the worlds a study visits. Simulations
illustrate and build hypotheses; a study's winner is a provisional default, and its next step is the
general statement that explains it (a Lean target, or a Finding when it fails). Report a study's
outcome as a hypothesis with its conditions, never as settled.

The simulation studies (`studies/runs/*.js`, numbered observations S1, S2, … in `LOG.md`, indexed at its top) are cheap
(seconds to minutes) but answer only for the worlds they visit. Each study states its purpose in its
header, since the rules differ (of S1–S48: 43 numerical, 12 exact, 6 hypotheses):
- **Decide** (most of them): which fit or rule the app recommends (S3's θ̂, corrBS, the taper signal).
  Needs realistic regimes and honest error bars: rules 1–3 below. Outcome: a recipe or default, and its
  conditions (the worlds where it loses).
- **Conjecture** (pre-step for Lean): find a statement and try to break it. Extreme and adversarial
  worlds are welcome, regimes are not needed, exact computation beats simulation (rule 4), and a
  counterexample is worth more than an average. Outcome: a candidate theorem or a Finding with its
  counterexample.
- **Illustrate**: the app's pages simulate live, so they need no study script. A script is needed only
  to check that the page's message holds beyond its default world.
Rules (helpers in `studies/runs/lib.js`):
1. **Three regimes** (`lib.regimes`). The app default (volume 500, z ≈ 0.2–0.9); "thesis" (volume 4400,
   z ≈ 0.7–1.0: the credibility level of the thesis simulation, §4 Table 4.1: τ = 0.6, σⱼ²
   lognormal(16, √2), wⱼ ≈ 3·10⁷); and "thesisShape" (the same, plus that table's nearly equal volumes
   and σⱼ² × 1/16–16, which brings the noisiest cohorts back to z ≈ 0.3). Volume alone shrinks the gaps
   between fits about threefold and can flip a ranking (S48). The thesis's σⱼ spread restores them (S51).
2. **Paired standard errors.** Same draws for every fit (common random numbers), and report
   differences as `m ± 2SE` of the paired difference (`lib.paired`), not two means side by side.
   "About even" needs an SE: at 600 draws it is ±1–6 points of the floor.
3. **A factorial design**, not hand-picked cells (`lib.grid`): every combination of the axes, so a
   conclusion is a statement over the grid and its edge is visible. Name the ranges in the output.
4. **Exact where possible.** Oracle MSEs, restricted predictors and floors come from the formulas
   (as `runs/ewma-decay.js` Part A), and simulation only for what depends on fitted parameters.
5. **Say where the ranges come from.** Engine worlds: anchored by the thesis regime above. The
   monthly card world (`app/monthly.js`: γ, s², w0) has no anchor yet; its ratios s²/(wγ) and φ should
   be set from the owner's card data (summary moments only) before its studies are cited as practice.

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
| Correlated BS, credibility-weighted variances (`fitVC`, default reference) | yes: σ̃ⱼ², ρ̂, τ̂² by moment equations, no damping | `K_posDef` (common ρ̂ ∈ [0, 1)), GLS `b`, `z`, `ρ̂` unbiased with true σ (`rhoPooled_unbiased`) | `ρ̂` with σ̃ plugged in, `Wⱼ`, `β²` (G1); jackknife MSEP is numerical only |
| Correlation, one common covariance (not recommended, finding S4) | average of the pairwise estimators | closed form for `z` (`bestZ_of_equalCov`), `ĉ` unbiased (`commonCovHat_unbiased`) | — (`ĉⱼ`, `τ̂²` on `ĉ`: `tauHatCommon_unbiased`) |
| Unequal lengths | yes | `Unequal.KHat_unbiased`, count `nᵢⱼ` | |
| Group levels | `φτ²` from pairs | `phiTauHat_unbiasedG` (one pair of each kind), pooled `phiTauPooled_unbiasedG` (G4) | best pair weights (fourth moments) |
| `z > 1`, negative `b` | clip (thesis eq. (34)) | diagnosis only; clipping harmless iff true `z ∈ [0, 1]` (`errVar_clipZ_le_iff`) | estimated `ẑ` (G3) |
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
  2026-11-14 (`studies/LOG.md`): with unequal volumes a common
  covariance is misspecified and its z explode; a common **correlation**
  `Σᵢⱼ = ρ̄√(ΣᵢᵢΣⱼⱼ)` is the better one-parameter model (H1 there).*
  *Proved 2026-11-22 (`Unequal.qHat_unbiased`, `commonCovHat_unbiased`, `rhoPooled_unbiased`;
  `Model` twins): `E Qᵢⱼ = σᵢσⱼρᵢⱼ(nᵢⱼ + Sᵢⱼ²/(wᵢ*wⱼ*))` (`nᵢⱼ = T − 2`), so the average `ĉ`
  is unbiased for a common covariance and the pooled `ρ̂` with the **true** `σⱼ` in its
  denominator for a common correlation. App badges for `ĉ` and `ρ̂` now "proved". Still open:
  `ρ̂` with `σ̃ⱼ` plugged in (a ratio), `Wⱼ`, `β²` (fourth moments). `ĉⱼ`, `τ̂²` on the common
  `ĉ`: proved the same day (`cHatCommon_unbiased`, `tauHatCommon_unbiased`), badges "proved".*
- **G4. Pooled pair estimator of `φτ²`**, unbiased for any weights.
  *Proved 2026-11-22 (`Model.phiTauPooled_unbiasedG`): weights summing to one on the pairs
  across groups and on the pairs within groups, any choice (e.g. `wᵢ*wⱼ*`). Which weights
  minimise the variance needs fourth moments (open). The app has no group fit yet, so no badge.*
- **G3. Clipping** `z` to `[0, 1]`: when is it harmless?
  *Proved 2026-11-22 (`BlendMoments.errVar_clipZ_le_iff`, Finding 36): for a fixed `z`, clipping
  never increases the error iff the best `z*` is in `[0, 1]`; otherwise clipping `z*` costs
  `Var(μ̂ⱼ − μ̂)·dist(z*, [0, 1])²`. Open: an estimated `ẑ` (the error in a draw is a different
  parabola). App: the `z > 1` warning now says this; no clip switch added (the app does not clip).*
- **G2. Damping as shrinkage.** Is there a safe `θ`? *Numerically, the
  rule `θ̂ = ρ̄²/(ρ̄² + (1−ρ̄²)²/(T−1))` is within 2 points of the best fixed
  `θ` in 23 of 24 worlds (H2 in `studies/LOG.md`).*
  *Proved 2026-11-22 for the table loss (`Credibility/Damping.lean`): with means `s` and variances
  `V` of the off-diagonal estimates, `E Σ(θŝ − s)²` is minimised at `θ* = Σs²/(Σs² + ΣV)` (Ledoit–Wolf
  / Schäfer–Strimmer intensity), and `θ` beats both `θ = 0` and `θ = 1` iff
  `|θ − θ*| ≤ min(θ*, 1 − θ*)` (`safe_iff`). The app's rule is the one-entry `θ*` with normal-theory
  `V` plugged in. Open: the rates' MSE (S12: they want less damping), and `θ̂` with estimated
  inputs. App: the damping note now names `bestTheta_optimal`; the badge stays (it is about `K̂ ≻ 0`).*
  *Exact `V` tried 2026-11-23 (`studies/runs/damping-cumulant.js`, S38–S40): `θ*` in covariance form with
  the proved `Var Σ̂ᵢⱼ` (`variance_sum_mul_lin`, √w weights; `variance_crossResid` for unit weights),
  κ = 0 or the true shock κ, matches the oracle `θ*` but damps more than S3 and costs up to 11 points
  at ρ = 0.9 (gamma and Lomax worlds alike; ±2 at ρ ≤ 0.6). App: S3 stays; `thetaRule: 'cov'` is a
  studies option. No `κ̂₄` for G2. *Correlation scale done 2026-11-23 (`studies/runs/damping-corr-exact.js`,
  S41–S42): the exact delta-method `Var r̂ᵢⱼ` with κ = 0 is S3; with the true cumulants θ̂ moves by
  ≤ 0.05 and the MSE by ≤ 1 point; with infinite kurtosis (Lomax α = 3) it gives θ̂ = 0 and costs up to
  40 points. S3 stays; the κ̂₄ question is closed for G2.*
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
  `studies/runs/vc-balance.js`, column `opt`), so the app gets no switch for it:
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
- [x] 3b. No-tuning fit and its error (2026-11-15; `studies/LOG.md`, findings
  S15–S26). `fitVC` in `engine.js`: correlated BS with credibility-weighted variances
  (`runs/variance-credibility.js`, mode `cred`), every parameter by a moment equation, no `θ`;
  the default reference. The common-covariance fit stays in the list, marked not recommended
  (finding S4). `jackknifeMSEP` (`runs/msep.js`) gives each region a "typical error" of the `vc`
  rate, shown in the one-draw chart and table as an average-case error, not an interval
  (finding S26). Tests: `K̂ ≻ 0` on every draw; equal to BS when `ρ̂ = 0` and `β² = 0`;
  identical to the study scripts; jackknife MSEP within 25% of the actual MSE on average in
  one fixed-seed world (ratio 1.00).
  World switch "spread of noise across regions" (`noiseSpread`, 2026-11-15): σⱼ = σ·4^(s((j mod 4)/3 − ½)),
  s = 1 is the ×0.5–2 spread world of `runs/variance-credibility.js` and `runs/msep.js` (σⱼ column in the
  one-draw table). Checked in the app's own world (gamma noise, 1000 draws, % of floor): at ρ = 0.6
  BS / corrBS / corr = 151 / 113 / 118 (J=8 T=10), 167 / 135 / 144 (T=5), 183 / 114 / 118 (J=20);
  jackknife predicted/actual 0.81, 0.89, 0.86 (finding S19: 0.85–0.90). At ρ = 0 and T = 5 the three
  tie (≈150). Tests: σⱼ and true `K` equal the studies'; draws have Var σⱼ²/w and corr ρ; corrBS
  beats BS and corr, and the jackknife ratio is in (0.75, 0.95), in one fixed-seed spread world.
  Expected flags (2026-11-15, `studies/runs/vc-balance.js`, findings S27–S29): the floor (true K) has
  negative b and is off exposure balance too; forcing balance costs up to ≈30% more error, so no
  balance switch (the floor's costs are exact: `studies/runs/exact-balance.js`, pinned by a test).
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
  *Pair-specific correlation (2026-11-17, `runs/blup-pairs.js`, S30–S32 in `LOG.md`):* with
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
Finished items are in `studies/PLAN-done.md`.
- [ ] Small form of `K_G⁻¹` (2026-11-24, `Unequal.KG_inv_eq`, from `Matrix.inv_mul_mul_transpose_add`):
  with group levels the engine can invert `A = K(M_φ)` (diagonal for uncorrelated errors) plus one
  `G × G` matrix instead of `K_G`, also with errors correlated across groups. Only a speed-up; use
  it if the engine inverts `K_G` for many cohorts. Also: the group effects `b̂_g` (BLUP, from
  Henderson's equations, `Unequal.groupEffect_eq_blup`) could be shown per group, a readout of
  "how far is this group from the portfolio". Its true error is known (`NoiseG.mse_groupEffect_blup`:
  `φτ² − ℓᵀK_G⁻¹ℓ + (1ᵀK_G⁻¹ℓ)²/1ᵀK_G⁻¹1`), so the readout can carry an error bar; world vs fit.
- [ ] Cross term with kurtosis (2026-11-24, Finding 38, `Cumulants.crossTerm_of_balanced_cumulants`):
  the first-order `2E[AB]` of the BS plug-in, relative to `(1 − z)τ²`, is `−2(1 − 1/J)z(1 − z)(γL + γN/T)/J`
  (`D` estimated). The "Noise shape" readout's price with γ̂N (law (a) only) adds
  `+(1 − 1/J)z(1 − z)γN/(JT)`; with the cross term the kurtosis total is `−(1 − 1/J)z(1 − z)(γL + γN/T)/J`,
  so the correction has the wrong sign. Next app chat: price = law (a) + cross term (show both), and
  check against the simulated `2E[AB]` (−6% under gamma). *Unequal volumes (2026-11-24,
  `studies/runs/cross-term.js`):* the first-order term for any `wⱼₜ` from the moment tables (`firstOrder` there:
  linearize the fit's weights in (P, B), then the `integral_lin_lin_sumSq` identity) matches simulation,
  noise part within SE, level part ~30% too large at J = 8 (fine at J = 30). Use that general form in the
  engine rather than the balanced closed form; γL stays a sensitivity.
  *Proved 2026-11-25 (`Cumulants.crossTerm_bs_of_cumulants`):* the closed form for any volumes (finite
  sums over regions, Finding 38); the engine can use it directly instead of the numeric `firstOrder`.
  *Finding 39 (2026-11-25):* the noise part has no sign: with a region's volume concentrated in one
  year it is positive (+7.5% of that region's MSE, simulated). So the engine must use the general
  formula per region, and the readout should show its sign, not assume "kurtosis lowers the price".
- [ ] Gain against price (2026-11-24, S53–S55, `studies/runs/price-formula.js`): a data-side choice between
  fits from formulas, not simulation. Oracle gap from the fitted `K̂` (exact for given parameters,
  `CoreMoments.mse_blend_eq_blup_add`) against the first-order price from the plug-in moments of the
  statistics (Prasad–Rao g₃). It decides the sign in all clear cases of S53. *2026-11-24:* closed-form
  laws (S56): fitting BS costs ≈ (2/J)·T/(T − 1)·(1 − z)/z, own variances ≈ z(1 − z)·2/(T − 1), valid for
  z ≥ 0.6. `Engine.gainPrice` (Node test) chooses region against pooled variances by exact gain against
  law (b). Regret ≤ 3.3, 1.2 points better than corrBS on average (S57). *Built 2026-11-24:* the panel
  "Gain against price" in the card "Is correlation worth modelling?" (`renderGainPrice`), and the fit
  "corrBS g/p" (`fitVCGP`). Conditional recipes: a step may carry `branch` (labels in `RECIPES[id].branches`),
  the fit reports the `branch` it took, and `recipeSteps(id, { branch })`, the recipe test, the page
  ("Only if …", "Taken because …") and the copied text filter or mark by it; a Node test reaches every
  branch of both fits. Open: which fit the app recommends (owner: corrBS today; candidates BLUP, S52, and
  corrBS g/p, S57). Spec as built: for the
  fitted data, three rows "corrBS over BS", "BLUP over the blend", "region variances over pooled", each with
  its gain (exact on K̂, badge "proved" via `CoreMoments.mse_blend_eq_blup_add`) and its price (S56 law,
  badge "not proved yet", shown only where `valid` ≥ ½), and the verdict. Then a fit "corrBS, variances
  by gain against price" once recipes can hold a conditional step (as "BLUP auto"). Lean: Var/Cov of P, Qn,
  B from `Cumulants` *(done 2026-11-24, `FitStatistics.lean`: `covariance_stat`; cov(B, P) = 0 needs also
  κ₄ = 0 and means uncorrelated with residuals, Finding 37; the app's exact moments of s may assume
  normal cells, but should not assume cov(B, ·) = 0 with non-proportional volumes)*; the balanced identity ẑ = 1 − v̂/S² and law (a)'s
  first-order variance *(done 2026-11-24: `Cumulants.bsZ_bsTau2Hat_of_balanced`, `bsPrice_of_balanced`:
  exact first-order price (2/J)(1 + (J − 1)/(J(T − 1)))(1 − z)/z; `engine.js` `priceFit` uses the upper
  bound (2/J)·T/(T − 1)·(1 − z)/z (`bsPrice_le_of_balanced`), within a factor T/(T − 1) of it; switch to
  the exact form at the next app chat, and relabel law (a) in the formula panel as proved in the
  balanced world)*. *Corrected for kurtosis (2026-11-24, `bsPrice_of_balanced_cumulants`):* add
  κL/(Js²) + γN z²/(JT) inside the bracket, γN the pooled residual excess kurtosis (estimable), κL/s²
  the levels' (not estimable with few regions: a sensitivity). Candidate for the "noise shape"
  readout: price with and without the kurtosis terms. *Built 2026-11-24:* `priceFit` is the exact law
  (a) with γ̂N (`Engine.bsPriceLaw`, `gainPrice(data, { gammaL })`), `Engine.noiseShape` (unbiased
  per-region moment equations for σ⁴, κ₄ of the √w-scaled residuals, pooled as ratios); the "Noise
  shape" readout under Gain against price (skew, γ̂N with normal-case SEs √(6/N), √(24/N); price
  without, with γ̂N, and per unit γL; γL = 3, 6), law (a) badged proved in the balanced world. **Seen:**
  the normal-case SE is far too small for skewed noise (gamma, kurtosis 3, J = 8, T = 10: one draw's
  γ̂N mean 2.8, median 1.5, SD ≈ 4.5 against 0.55; T = 5: mean 5.3); skewness reads ~20% low. The
  noise term γN z²/(JT) moves the price by < 1 point in the default world; γL adds ≈ 2 points per unit.
  Open: an SE for γ̂N from the data (eighth moments, or a jackknife over regions). *World switch
  2026-11-24:* "Noise shape shrinks with volume" (`params.shrink`, literature §10m): the gamma region
  part has shape k·w/500, so the noise turns normal with volume; the year shock and levels keep
  theirs. Off by default: on, the default world's small regions get shape ≈ 0.4 and the simulation
  checks quoted on the page (skew link, skew bias, gamma tests) would need rerunning. Open: make it
  the default after that recheck (owner asked for it, 2026-11-24); the fits' skew machinery
  (`skewLink`, `skewBias`: third moments ∝ w^−3/2) then needs the power w^−2 or a fitted power.
  *Law (b) proved (2026-11-24, `Cumulants.ownPrice_sub_pooled_of_balanced`):* the exact first-order
  extra price of own variances over a pooled one is (1 − 1/J)²·z(1 − z)·2/(T − 1); `engine.js` `priceVar`
  uses the study's z(1 − z)·2/(T − 1), its upper bound (`ownPrice_sub_pooled_le_of_balanced`), 1.31× at
  J = 8. Switching to the exact form makes the 'region' verdict more likely; S56 saw (b) overstate
  1.1–2× for z ≥ 0.6 but understate up to 5× below z ≈ 0.3 (bias of 1/σ̂ⱼ², not first order), so
  recheck the regret table of S57 before switching; relabel (b) "proved in the balanced world".
  *Done 2026-11-24 (S58):* the exact form keeps the mean regret (−0.5) but worsens the worst world (equal
  σⱼ, ρ = 0, T = 5: 2.8 → 4.9), so `priceVar` keeps the bound, now cited as proved
  (`ownPrice_sub_pooled_le_of_balanced`); `opts.lawB = 'exact'` for comparison, Node test exact = (1 − 1/J)²·bound;
  page and recipe relabelled "proved in the balanced world". Next, if any: a price for the low-z bias of 1/σ̂ⱼ².
  *Caveat (2026-11-24, literature §10m, Chen–Lahiri–Rao):* law (a) prices `E B²` only. Under
  non-normality the cross term `2E[AB]` is first order too. For the levels it is `−2z(1 − z)γL/J`
  (with D known), so the γL sensitivity row overstates; the net effect of level kurtosis is
  `−z(1 − z)γL/J`. Once the cross term is proved (Lean target in §10m), show the net price, or add a
  watch-out to the γL row. *Also (literature §10o, Datta–Lahiri 2000):* with spread volumes the price
  of `τ̂²` depends on its estimator (ANOVA: arithmetic mean of `(τ² + vⱼ)²`; REML or a
  precision-weighted Fay–Herriot moment equation: harmonic mean, far smaller). Candidate: a FH
  moment `τ̂²` as a corrBS option, checked against the app's simulations. Law (a) applied region by
  region is exact only balanced.
- [ ] Fourth-moment layer (2026-11-22, `notes/fourth-moments.md`): one lemma for `Var` of a quadratic
  form with third and fourth cumulants (G1 `Wⱼ`, `β²`; G2 `V`; G4 pair weights), plus the third-moment
  pieces (`Cov` with a linear form, `E` of the cubic `κ̂ⱼ`). Approved (owner); assumptions 1 + 6 with the
  conditional version (b). *General lemma proved 2026-11-22 (`Cumulants.variance_quad_of_cumulants`).*
  App: nothing yet; the G2 `V` and the G4 weights will use it once the source corollary is in.
  *Third moments proved 2026-11-22* (`integral_cubic_of_cumulants`, `covariance_quad_lin_of_cumulants`):
  `κ̂ⱼ` of `noiseDiagnostics` unbiased *proved 2026-11-23* (`Cumulants.kappaHat_unbiased`, any level,
  third moments diagonal over years; app badge "proved" on the Noise shape page). Finding 35 (c):
  the exact `cov(σ̂², μ̂) = Σₛ aₛκₛ Σₜ cₜ(δₜₛ − aₛ)²` *proved 2026-11-23*
  (`Cumulants.covariance_resVar_mean`; noise squares uncorrelated with the level). *Built 2026-11-23:* the
  Noise shape page shows a per-region "skew link" (% rise of σ̂ⱼ² per +1% of μ̂ⱼ from the noise,
  `Engine.skewLink`, with the pooled ĝ: κ̂ⱼ alone has SD ≈ 3 per region, and κ̂ⱼ/σ̂ⱼ⁴ reads ~40% low as
  σ̂ⱼ² rises with κ̂ⱼ), its mean over regions against the world's (5–20% high), and the predicted skew
  bias of the same-years power (0–25% high without correlation, 0 under normal noise; overstated
  with a common year shock, ρ = 0.6: 2.4 against 0.7, since the shared part cancels between regions).
  Node test: cov against Monte Carlo. *Plug-in portfolio bias predicted 2026-11-23* (`Engine.skewBias`,
  `studies/runs/skew-bias.js`, 1500 draws): first order `Σᵢ ∂d̂ⱼᵢ/∂σ̂ᵢ² · cov(σ̂ᵢ², μ̂ᵢ)`, the derivative by
  refitting with region i's residuals scaled. Mean prediction against simulated (vs BS on the same
  draws): default −0.37 / −0.31%, T = 4 shape 1 −1.75 / −2.15%, σⱼ spread −1.06 / −0.78%, J = 20
  −0.28 / −0.31%, Lomax α = 4 −0.18 / −0.16%, normal and pooled BLUP 0 / 0; misses the ρ̂ channel
  (ρ = 0.6: −0.15 / −0.27%, pooled BLUP 0 / −0.33%). One data set's value is rough (SD ≈ mean).
  Noise shape page: a row per unbalanced fit/reference. *ρ̂ channel added 2026-11-23:* for corrBS and
  its BLUPs each σ̂ₖ² and ρ̂'s numerator Σ Qᵢⱼ perturbed alone (`vcEstimate` perturb hook), covariances
  from `covariance_quad_lin_of_cumulants` with a pooled cross-region third moment γ̂ (`crossSkew`, a
  ratio: 0.39 against 0.66 at ρ = 0.6, T = 10; → truth as T grows). ρ = 0.6: BLUP −0.42 / −0.41%,
  pooled BLUP −0.30 / −0.33%, corrBS −0.33 / −0.27%; T = 5 or J = 20: about half the BLUPs' bias
  (γ̂ low). *Refined 2026-11-23:* γ̂'s low reading is the denominator (E σ̂ₐσ̂ᵦσ̂꜀ > σₐσᵦσ꜀ under a shared
  shock; with the true σ it is exact; leave-one-year-out does not help), so the cross moments are now
  per-triple unbiased k-statistics (`crossThird`); plus a τ̂² channel with the level third cumulant by a
  moment equation (`levelThird`). Neither moves the prediction much (T = 5, ρ = 0.6: BLUP −0.78 against
  −1.07%; J = 20: −0.47 against −0.74 ± 0.18%, −0.61 ± 0.15% with another seed). Level skew adds
  ~0.1 point (`studies/runs/level-skew-bias.js`). The rest at T ≤ 5 is beyond first order. Stop here: the
  prediction gets sign and size (within ~30%), and the balance switch removes the portfolio part anyway.
  *Independent sources proved 2026-11-22* (`variance_quad_of_sources`): exact `Var` of any quadratic
  estimator from one `κ₃`, `κ₄` per source; first use: the G2 `V` of `ĉᵢⱼ` (app: replace the
  normal-theory `V` once the noise cumulants are estimated, `κ₄ = 0` as the default).
  *Conditional version (b) proved 2026-11-23* (`VarianceFunction.variance_quad_of_conditional_sources`,
  `variance_quad_of_powerVariance`): the exact `Var` when the noise cumulants follow the random level
  through `μᵖ`. App: when the G2 `V` is replaced, compute it with the fitted `p` (averaging the
  cumulants over the fitted levels, not at the mean level) next to `p = 0`.
  *G2 `V` proved 2026-11-23, balanced case* (`Cumulants.variance_sampleCov`): equal weights and
  independent years, `Var ŝᵢⱼ = (VᵢᵢVⱼⱼ + Vᵢⱼ²)/(T−1) + κ₄ᵢⱼᵢⱼ/T` exactly; the app's S3 rule uses the
  first term only (in correlation form). App, pending: a kurtosis term needs a `κ̂₄ᵢⱼᵢⱼ` from the
  residuals (cross-region, so not the dropped per-region kurtosis); default `κ₄ = 0` keeps today's
  rule. *Weighted `Shock.crossHat` proved 2026-11-23* (`Cumulants.variance_crossResid`): exact
  `Var Ĉᵢⱼ` for any cohort weights and volumes, from the year covariances `Nₛ` (shock + process
  noise) and the within-year fourth cumulants; the levels cancel. App: this is the `V` to plug into
  `θ* = Σs²/(Σs² + ΣV)` (`Damping.bestTheta`) in covariance form, with `κ₄ = 0` as the default. *Done 2026-11-23:
  worse than S3 for the rates (S39), see G2.*
- [ ] Cumulant layer (2026-11-22, literature §10l): an optional assumption that the independent
  noise has a variance function `V(μ)` with dispersion `φ/w`, so that every cumulant follows from
  it (`κₙ₊₁ = (φ/w) V dκₙ/dμ`). The random effects (levels, shocks, factor) are Gaussian-like
  (Isserlis) or get their own `V`. It would give the exact variance of `ŝ²`, `Ĉ` and `K̂` (the
  plug-in `g₃` term), a per-region shrunk `σ̂ⱼ²` (Wen & Liu 2026), and the quadratic credibility
  of Zhao & Poudyal (2026). Like the distribution layer, it goes in its own files, named "under
  a variance function", and nothing in the core depends on it. The app's `noiseDiagnostics`
  already estimates `p` and `κ` (§10k): check `κ̂ⱼ` against the Tweedie prediction `p φ² μ^(2p−1)`
  before relying on it. Heavy tails (§10l): no variance function gives them. Use a compound
  Poisson cell instead, with `κₙ(S) = λw E[Yⁿ]` and a Lomax (`α, θ`) or lognormal severity, whose
  raw moments follow a two-parameter recursion. The fourth-moment results then need `α > 4`, and
  should say what fails for `α ≤ 4`. Fitting individual claims (Hill estimator) is out of scope
  (owner, 2026-11-22). From cell totals only, severity moments could come from cell cumulants
  (`κ̂ₙ / (λw)`), but `κ̂₃` and `κ̂₄` are very unstable under heavy tails. So the app world could
  draw Lomax claims to show where the tools break, without fitting `α`. Lean work needs the
  **lean** environment.
  *App switch built 2026-11-22:* world "Lomax claims" (`params.lomax = α`, slider 2.2–8, default 3;
  excludes "Normal noise"). The region part `ξⱼₜ` of each cell is a standardized compound Poisson sum
  (`Engine.claimNoise`) with `λⱼ = μ²(E Y²/(E Y)²)/σⱼ²` claims per vehicle-year (0.11 at `σ = 6`,
  `α = 3`), so mean and variance, and hence `K` and the floor, are unchanged (Node test). Above 200
  expected claims per cell, claims beyond the level exceeded by 50 expected claims are drawn exactly
  and the rest summed as a moment-matched gamma, so the tail is exact and the first two moments too.
  The year shock `ηₜ` stays gamma. The noise page gives the world skewness at the middle volume (∞ for
  `α ≤ 3`). **Seen** (`studies/runs/lomax-tails.js`, 3000 draws, seeds 1 and 2; Monte Carlo SEs are
  unreliable for `α ≤ 4`, the two seeds agree): (1) Default world (~55 claims per cell): no damage.
  MSE above the floor is +8 to +12% for every fit down to `α = 3.5`, as with gamma noise. It falls at
  heavier tails (+4 to +8% at 2.5) and turns negative at `α = 2.2` (−1 to −4%): the plug-in fits beat
  the known-`K` floor. That floor is the best *linear* predictor. An estimated `σ̂²` jumps with a large
  claim and then shrinks that region harder, which acts like a crude robust estimator (S9 effect,
  amplified). (2) Small cells (`volume = 50`, ~5 claims, under 2 in the smallest regions): the fits with
  region-specific variances suffer. corrBS and BLUP are +50 to +58% unbalanced (gamma +40%) and the
  portfolio under-pricing grows (corrBS −250 to −285 bp against −184 under gamma and ≈ 0 under normal:
  the Finding 35 channel). BS and BLUP pooled stay at +19 to +26%. Even `α = 8` is worse than gamma
  there: a claims world's skewness grows like `1/√claims` in the small regions, while the gamma noise
  has the same skewness at every volume. (3) Jackknife MSEP of corrBS: right on average (ratio
  0.94–1.05 in the default world), but the typical draw reads low as `α` falls. The median ratio is
  0.77–0.85 at `α = 2.2`, so one draw's "typical error" understates the error by 15–25%. In small cells
  it overstates (1.1–1.5) in every world. Practical rule for the app's text: with heavy tails and small
  cells, use pooled variances (BS, BLUP pooled) or the balance switch, as for Finding 35. No new Finding:
  no theorem's statement is affected.
  *Rule shown in the app 2026-11-22* (note under the Lomax slider).
- [ ] Grouping cohorts in two dimensions (2026-11-24, literature §10n): spatially clustered Fay–Herriot
  (Maranzano, Mattera & Sugasawa) finds contiguous regions, each with its own collective mean and `τ²`.
  This is the 2-D form of `KMeansBridge.lean` (in 1-D the optimal groups are intervals, Finding 14). A
  possible app step: "group the cohorts" before the blend, with group sizes and `τ²` per group fitted
  (no hand-set number of groups, §1). *Read 2026-11-25 (literature §10p):* their `K` by BIC and the
  contiguity weight `φ` by a stability plateau are hand-set choices. BIC over-clusters with no regimes. In 1-D,
  cohorts ordered by volume or time are grouped into intervals, so there is no `φ`, and `K` should come
  from gain against price with `K = 1` as reference. *Checked 2026-11-25 (Finding 41, `notes/group-variances.md`):*
  with its own `τ²` per group, no: a group that does not shrink collects the outliers of both tails, even with equal volumes.
  With own means and one common `τ²`, yes, for any volumes (weighted k-means with weights `u(1 − z)²`). So the
  app step fits own means and a common `τ²` by cuts of the sorted estimates (DP). Proved 2026-11-25:
  `group_optimal_contiguous` (corollary of `kmeans_contiguous`). *Warning 2026-11-25 (S61):* do not choose the
  cut of the sorted estimates by SURE: 2–74% worse than one group; the step needs a selection-aware
  criterion (cross-fitting, or a price that includes the choice of the cut) before it is built.
- [ ] *Parked (owner, 2026-11-25: a size trend is niche; tariffs usually carry size already).* Volume trend as a
  design column (S62): the offset `E μⱼ = α + γ log wⱼ`, a fit "BLUP with log volume" (`res:blup`,
  X = `[1, log w]`). Build only if real data show a slope: regress `μ̂ⱼ` on `log wⱼ` with weights `1/(τ̂² + D̂ⱼ)`
  and compare `γ̂` with `τ̂`. Then switch it on by gain against price (S57), which needs the price of an extra
  column in `Engine.gainPrice`. A known `γ` (from a tariff factor) is a plain offset: subtract it, BS, no price.
  `runs/obp-mean.js` has `fitTrendX` and the trend world.
- [ ] Any learner as the collective mean (2026-11-25, literature §10p, "Small area learning"): the
  correction weight `a*` there is `bestZ` on the learner's residuals, estimable from their spread
  (Bühlmann–Straub on residuals). A possible later fit "learner + credibility". It needs cross-fitting or a
  bias term for fitting the learner on the same data (Finding 35). Not now: the app has no covariates.
- [ ] BLUP in credibility form (2026-11-26, `notes/blup-credibility-form.md` §1–2): `μ̂ᴮᴸᵁᴾ = 1μ̂_GLS + Z r`,
  `Z = LK⁻¹` (`τ²(τ²I + V)⁻¹` in the thesis model), residuals `r = μ̂ − 1μ̂_GLS`; the blend is row `j`
  restricted to `z eⱼ`; path `w + θ(d* − w)` with `MSE(θ) = MSE(d*) + (1 − θ)²·price`. Lean first (targets
  1–3 in the note, `Core.lean`: done 2026-11-26, `Core.blupWeight_dotProduct`,
  `Core.linMse_add_smul_blupWeight_sub`). App then: show `Ẑ` (diagonal next to the blend's `ẑ`, off-diagonal as
  "borrowed") in the card "Is correlation worth modelling?"; later a fit with `θ̂` from gain against price
  (S57), once the best `θ` for a plug-in is stated (stated 2026-11-26, `PlugInMix.lean`:
  `θ* = ½ + (M₀ − M₁)/(2S)`, `S` the spread of the fitted blend and BLUP; the app can show `S` and
  the safe range `M₁ − M₀ ≤ (1 − θ)S`). Fitted `θ̂` (2026-11-26, `Target.integral_sq_plugIn_mix_proxy`,
  `proxy_neg_div_eq`): fit on years `1..T−1`, regress year `T`'s blend error on `Δ` across cohorts,
  clip to `[0, 1]` (`mixLoss_clip_le`); exact in mean when year-`T` noise is independent of the fit
  (an iid year shock included), biased by `E[Δε]/EΔ²` when the shock persists across years.
  *Studied 2026-11-27* (S64, `studies/runs/held-out-theta.js`): no. `θ̂` costs 1–15 points against `θ = 1` under a
  common shock (the plug-in BLUP is within 0.7 of the best fixed `θ`), pooled over years too; the price of
  one held-out year is exactly `ΔᵀWΣWΔ/ΔᵀWΔ ≥ σ²(1 − ρ)`, 7–14× the gain available. So no `θ̂` step: keep
  `θ = 1`, show `S` only. Lean target 1 of S64 done 2026-11-27 (`integral_wLoss_heldOutTheta`,
  `le_heldOutPrice`); target 2 done 2026-11-27 (`Factor.HeldOut.integral_wsum_noise`). Gauge of `Z`'s rows settled 2026-11-27 (handbook `res:blup_gauge`): show the zero-sum row `d̂* − b̂` next to
  the blend's `ẑ(eⱼ − b̂)` in the card.
- [ ] Finding 35: the ρ̂ channel (2026-11-26, `notes/blup-credibility-form.md` §3). Hypothesis: with the
  pooled `σ̂²` the remaining bias runs through `ρ̂` and the GLS weights `b̂`, a third cross-cumulant that
  needs skew and correlation together; vanishes for exchangeable regions (P1). Candidate remedy R1:
  leave-one-year-out cross-fitting of `ρ̂`, `σ̂²` (weights from the other years), exactly unbiased in
  that channel for any distribution, without forcing exposure balance. *Studied 2026-11-26* (S63,
  `studies/runs/rho-channel.js`, 4000 draws): the cross-fit is unbiased in all ten worlds but costs 4–17 points as
  a predictor; the BLUP shifted to the cross-fitted portfolio level is unbiased and costs ≤ 1 point against
  exposure balance without correlation and 2–46 points less with it (ρ = 0.6). `ρ̂` is about half the channel.
  **Owner to decide:** let the balance switch balance to the cross-fitted level (`balanceFit` with a target
  level; recipe step, Node test). Lean first: the cross-fitted level's bias is the level channel only
  (S63 "Consequence", a corollary of `Core.Estimates.integral_randomLin_sub`; **lean** chat).
  *Lean done 2026-11-26:* `Core.Estimates.integral_crossFit_sub` (common year weights, weights independent of
  their year's noise: bias `Σₛ πₛ Σᵢ cov(d̂ᵢ⁽ˢ⁾, μᵢ)`, any distribution). The app's proportional volumes give
  common year weights, so the identity applies there; only the owner's decision remains. *2026-11-27:*
  `integral_crossFit_sub_eq_zero`: exactly unbiased when the cross-fitted weights are uncorrelated with the
  levels (residual-only `ρ̂`, `σ̂²`, `residual_eq_noise`); a `τ̂²` from all years keeps a level channel.
