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
- [x] 3c. Findings 17–20 in the app (2026-11-17). Card "Is correlation worth modelling?":
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
- Taper switch (2026-11-17, `OffDiagonal.lean`): repair or regularize `K̂` by tapering it
  with a correlation matrix `R` instead of only damping (`posDef_hadamard_of_corr`: `R ⪰ 0`
  with unit diagonal keeps `K̂ ≻ 0` and the variances). Options: "damp θ" (today's
  `R = θ11ᵀ + (1-θ)I`) and "distance ρ^|tᵢ-tⱼ|" for cohorts with an order (years, age
  bands; `distTaper_posSemidef`, ties allowed). Badge "proved" for both when `Σ̂ ⪰ 0`.
  Its `ρ` must be fitted, not hand-set (§1): e.g. choose it like `θ`, by the plug-in
  criterion of `studies/damping-theta.md`.
