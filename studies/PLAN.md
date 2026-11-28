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
6. **Keep runs short (2026-11-27, S71: 27 min → 48 s).** Run worlds in parallel on all cores
   (`lib.mapWorlds`, heaviest first; `lib.args` gives `--jobs`), rerun only the fits that changed (`--only=a,b`:
   same seed, so the other rows are unchanged), and profile before a long run (`node --prof`). In the
   engines, factor a matrix once per fit and reuse it, never one solve per column or per cell (n³, not n⁴).
   Write long runs' output to the scratchpad and copy it in when done. Count a paired difference as a
   win or loss only beyond float noise (`lib.sig(d, tol)`): identical fits differ by ~10⁻¹⁶.

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
| Correlated BS, credibility-weighted variances (`fitVC`, default reference) | yes: σ̃ⱼ², ρ̂, τ̂² by moment equations, no damping | `K_posDef` (common ρ̂ ∈ [0, 1)), GLS `b`, `z`, `ρ̂` unbiased with true σ (`rhoPooled_unbiased`) | `ρ̂` biased up through σ̃'s level, kept (Finding 48, S81); `Wⱼ` biased low, kept (Finding 47, S80); jackknife MSEP is numerical only |
| Correlation, one common covariance (not recommended, finding S4) | average of the pairwise estimators | closed form for `z` (`bestZ_of_equalCov`), `ĉ` unbiased (`commonCovHat_unbiased`) | — (`ĉⱼ`, `τ̂²` on `ĉ`: `tauHatCommon_unbiased`) |
| Unequal lengths | yes | `Unequal.KHat_unbiased`, count `nᵢⱼ` | |
| Group levels | `φτ²` from pairs, one GLS pass; groups or none on held-out years (fit "BLUP groups", 2026-11-27) | `phiTauPooled_unbiasedG`, best weights `phiTauPool_blue_optimal`, choice `CrossFit.integral_heldOutScore_sub` | the GLS pass with plug-in `V̂` (λ̂ 20–40% high) |
| `z > 1`, negative `b` | clip (thesis eq. (34)) | diagnosis only; clipping harmless iff true `z ∈ [0, 1]` (`errVar_clipZ_le_iff`) | estimated `ẑ` (G3) |
| Choosing cohorts | not yet: needs a held-out study first | `merge_iff`, `pool_optimal_contiguous`, `CrossFit.integral_heldOutScore` | G5 (steps 7–8 below) |

Known-parameter results (optimal `z`, GLS weights, true MSE) appear only as
the floor line and in the tests.

**Gaps: candidate theorems.** Closed gaps are one line each (details in the
commit log, `FINDINGS.md` and the blueprint); open ones carry the plan to
close them (agreed with the owner 2026-11-28), in the order of work below.

*Closed:*
- **G0. Classical BS `τ̂²`** (eq. 13) unbiased when `ρ = 0`: `Model.tauHatBS_unbiased` (2026-11-15).
- **G4. Pooled pair estimator of `φτ²`**: unbiased for any weights (`Model.phiTauPooled_unbiasedG`),
  best weights by Gauss–Markov (`Model.phiTauPool_blue_optimal`, `GroupPoolWeights.lean`); plug-in GLS
  pass in the app's step 4 (S69).
- **G6. Forecasting**: same `z`, MSE + next year's noise (`Core.Estimates.mse_forecast`,
  `bestZ_forecast_optimal`); the app's premium step.
- **G7. Balance under correlation**: best balanced blend and best correction (`Core.bestBalanced_optimal`,
  `bestCorrection_optimal`, `commonShift_optimal`; Findings 15–16); the app keeps the common shift
  (`balance: 'auto'`, `BalanceCost.lean`, Finding 46).

*Partly closed* (what is proved):
- **G1.** `ĉ`, `ĉⱼ`, `τ̂²` on the common `ĉ`, and `ρ̂` with the **true** `σⱼ` are unbiased
  (`Unequal.qHat_unbiased`, `commonCovHat_unbiased`, `rhoPooled_unbiased`, `cHatCommon_unbiased`,
  `tauHatCommon_unbiased`). `E Wⱼ` exactly and `β̂²` unbiased given the corrected `W̃` (`VcW.lean`, Finding 47; the app keeps the raw `Wⱼ`, S80). `ρ̂` with `σ̃ⱼ` plugged in: biased up through σ̃'s level (Finding 48). Open, low value: `σ̃ⱼ²` as `bestZ`, `τ̂²` on the common-ρ `Σ̂`.
- **G2.** `θ* = Σs²/(Σs² + ΣV)` optimal for the table loss, safe range `safe_iff` (`Damping.lean`);
  exact `V` and κ̂₄ tried and closed (S38–S42: S3 stays); `K̂ ≻ 0` by theorem in every draw (step 1, done).
  Open: the rates' MSE.
- **G3.** For a fixed `z`, clipping is harmless iff `z* ∈ [0, 1]` (`BlendMoments.errVar_clipZ_le_iff`,
  Finding 36); the same for a held-out `ẑ` (`integral_sq_blend_clip_le_iff`); `z*` is unknown, so the app keeps `ẑ` (S83).
- **G5.** The math of the choice is in place: `Merging.merge_iff`, intervals are optimal
  (`KMeansBridge.lean`: `pool_optimal_contiguous`, `group_optimal_contiguous`, Finding 41), held-out scoring
  (`CrossFit.integral_heldOutScore(_sub)`, winner's curse `integral_min_score_le`), never merge by the
  observed gap (`PreTestNormal`, Finding 43). Open: a study and the app step.

*Plan, in order of work* (each step about one chat; env = cloud environment):

1. **G2a. `K̂ ≻ 0` always by theorem.** *Done 2026-11-28 (S78):* the corr fits build `K̂` on `Σ̂⁺`, the
   nearest PSD table (`Engine.projectPSD`, `ConeProjection.existsUnique_proj_posSemidef`); the damped `K̂` is
   "proved" in every draw, the tapered one when `τ̂² > 0`. The error moves ≤ 0.5 points. `Σ̂` fails to be PSD
   only with volumes of different shapes and short histories (`T = 3`, `J > T`: every draw); with one shape
   (`wᵢₜ = aᵢgₜ`, all of the app's worlds) it is PSD by construction, a candidate lemma (S78). Not done: one
   common covariance (`corrC`, not recommended) keeps the numerical check.
2. **G1a. `E Wⱼ` exactly** — *Done 2026-11-28* (`VcW.lean`, Finding 47, S80): low by a relative O(1/T);
   the unbiased `W̃` (`opts.corrW`) worsens the rates, so the app keeps the raw `Wⱼ`.
3. **G1b. `β²` and `σ̃ⱼ²`** — *`β²` done 2026-11-28* (`VcW.integral_betaHat`, `integral_betaHat_equal`):
   unbiased with the corrected `W̃` for uncorrelated regions; with `ρ ≠ 0` it needs cross terms `Ŵᵢⱼ`
   (logged in Finding 47, not chased: S80 says unbiased inputs do not help the rates). `σ̃ⱼ²` as `bestZ` stays
   open but is low value for the same reason.
4. **G1c. `ρ̂` with `σ̃ⱼ` plugged in** — *Done 2026-11-28* (`VcW.sum_shrink_le_iff`, `rhoPooled_ge_levelMatched`, Finding 48,
   S81): `ρ̂` is biased up (+0.06 to +0.13) through σ̃'s low level, which is exact and pointwise; neither `ρ̂` from
   the own σ̂ⱼ nor a rescaled σ̃ helps the rates, so no app change. `τ̂²` on the common-ρ `Σ̂` not pursued (same reason).
5. **G3b. Clipping an estimated `ẑ`** — *Done 2026-11-28* (`ClipHeldOut.lean`, S83): a held-out `ẑ` can be clipped
   safely iff `z* ∈ [0, 1]` (`integral_sq_blend_clip_le_iff`), but `z*` is unknown and a true `z* > 1` makes clipping
   costly (+30% in Finding 36's two-cohort example); in sample clipping can hurt slightly even with `z* ∈ [0, 1]` (S83).
   The app keeps `ẑ` and warns; a held-out "clip or keep" choice is in Pending.
6. **G2b. Damping for the rates' MSE** (*exploration*; study first). S12: the rates want less damping
   than S3. Does any first-order `θ*` for the rates' loss beat S3 by more than 2 points? If not, park
   it with that result.
7. **G5a. Study: cross-fitted cut against one group** (Default env; next free S number): S61's worlds,
   `T = 3–5` included, the chosen cut's error from an outer fold (the Pending item "Grouping cohorts").
8. **G5b. App step "group the cohorts"** if step 7 wins: cuts of the sorted estimates by DP, the cut
   by held-out score, one group as reference. No new Lean.

Not planned: the jackknife MSEP of corrBS stays numerical (labelled so in the app).
After each step: update its gap above, the app badge (`gap:` in `engine.js`) and the documents as in
`CLAUDE.md` ("When you close a `sorry` or log a finding").

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
  *Group levels done 2026-11-27:* world switch (G groups, region j in group j mod G, slider `φ`), group-aware
  floors (`bestBlendWeightsL`, BLUP with `L`), fit "BLUP groups" (`fitGroupLevels`: pairs with the eq. (39)
  noise estimates, volume-weighted first pass, one GLS pass, BLUP with `L̂`; `fitGroups`: groups or none by
  leave-one-year-out score), tests. Open: unequal lengths; group sizes other than `j mod G`.
- [ ] 5. Prove the gaps the app shows to matter (Lean chats); badges turn
  to "proved".
- [ ] 6. Link the app from the README and handbook; screenshots of a few
  telling settings as the handbook's worked examples.
  - [x] README: linked as a preview (2026-11-16, v2.0.0).
  - [ ] Handbook link and screenshots.

## Pending
(Results or findings that may need a switch, step or message in the app.)
Finished items are in `studies/PLAN-done.md`.
- [ ] Clip or keep `ẑ`, chosen on held-out years (2026-11-28, owner: "in real life you don't know if the true z is in
  [0, 1]"; Finding 36, S83). Score corrBS with `ẑⱼ` kept against `ẑⱼ` clipped by the leave-one-year-out score
  (`CrossFit.integral_heldOutScore`, unbiased for any rule) and show it beside the "z > 1" warning. First a study
  in worlds that can put z* well above 1 (a quiet region beside noisier correlated ones; the app's worlds reach only
  1.01): does the held-out choice keep clipping's small gain where z* ∈ [0, 1] and avoid its large loss where z* > 1?
- [ ] Finding 49 (2026-11-28): the app's Bühlmann–Straub fit on correlated worlds has `E τ̂² = τ² − c̄`; a line in
  its message ("BS also lowers τ²") once a study checks the size of `c̄` against `τ²` in the app's worlds.
- [ ] Cohort trend lines step (2026-11-27, `LineResidualsMoments.integral_correctedLambda_pooled`): level + slope
  per cohort, `ŝ²` and `ρ̂ŝ²` with SUR divisors `T − 2p + tr(PᵢPⱼ)` (handbook `res:lineResid`), corrected `Λ̂`,
  joint damped BLUP (S67); show the 2 × 2 `Z`. Engine helpers exist in `studies/runs/vector-lambda-shocks.js`.
  *Forecast (2026-11-27, `CoreVector.VecEstimates.forecast_mse_optimal`, handbook `res:vecForecast`):*
  show next period's level `a + b(T+1)` per cohort as `cᵀ·BLUP`, with the error bar `cᵀ linMse c` (world vs fit).
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
  region is exact only balanced. *Cross-term caveat done 2026-11-27:* the Noise shape readout shows the net
  price, law (a) + `2E[AB]` (`crossTerm_bs_of_cumulants`, any volumes; PLAN-done: cross term with kurtosis).
  Still open here: which fit the app recommends (owner), the FH moment `τ̂²` candidate. *S72 (2026-11-27,
  `runs/recommended-fit.js`):* balanced, no candidate wins everywhere (BLUP −15.5 to +21.6 points against corrBS,
  losing with a wide σⱼ spread; g/p ±4; held-out choice at most +10, regret +1.7). Next: the price of the BLUP
  over the blend on the same `K̂` ("none extra" in `gainPrice` is wrong under a σⱼ spread), then a
  gain-against-price verdict for the BLUP as for the variances. *Price stated 2026-11-27 (Finding 45, S73,
  `BlupPrice.lean`):* first order `rᵀQr` against the blend's law, no sign in general, +32 to +38 points at app
  volume with σⱼ spread 2. Still open: `Var θ̂` of corrBS's (ρ̂, σ̃ⱼ², τ̂²) (delta method), then the BLUP column
  in `gainPrice` and its formula line (`F.gainPrice` "none extra" is wrong). *S74 (2026-11-27):* the
  bootstrapped verdict adds nothing (regret 1.5 against held-out 1.6), and the BLUP wins unbalanced (worse in
  6 of 56, ≤ +6); so no BLUP column. Fix the formula line only: "none extra" → the weight price, cross term
  unknown.
- [ ] Balance switch cost with unequal σⱼ (2026-11-27, S74, owner decision): balancing to the cross-fitted level
  costs corrBS +21.8 points of the floor on average over S72's grid, up to +205.6 (app volume, σⱼ spread 2, T = 5),
  +49.5 even at ρ = 0. The default is "on". General target first: the MSE of the common shift to the cross-fitted
  level against the portfolio bias it removes (`Core.Estimates.integral_crossFit_sub` gives the bias side).
  *Proved 2026-11-27 (Finding 46, S75, `BalanceCost.lean`):* cost = `E(T − μ̄)² − E(r̄ − μ̄)²` exactly; the cross-fitted
  level is the worse estimate of `μ̄` with σⱼ spread (1.2–2.2×). Open: a data-side check of that difference,
  then the owner decides the default; the page's balance note should state the trade (handbook `res:balanceCost`).
  *S76:* the plug-in rule (balance iff `mse(c̄) − mse(c)` < 0 on `K̂`) has regret ≤ 6.9 against 205.6 for "on";
  candidate `Engine.balanceAuto` with the cost and the portfolio bias it leaves shown. *Done 2026-11-27 (owner: plug-in rule,
  show the bias):* the switch is `balance: 'auto'` (`Engine.balanceAuto`, Node test "Balance when it pays"); the page
  shows per draw the two portfolio-level errors and the estimated under-pricing (gap to the cross-fitted level ± 2 SE),
  and under Many draws the share balanced and the bias as priced against unbalanced. Open: a bias-aware variant if a
  portfolio must not be under-priced.
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
  *Criterion settled 2026-11-27 (`CrossFit.integral_heldOutScore`, handbook `res:heldout`):* leave one year
  out, choose the cut and fit on the other years, score on the left-out year; compare cuts (and one group)
  by the difference of the averaged scores (the noise price cancels, `integral_heldOutScore_sub`). Next: a
  study (next free S number) of the cross-fitted cut against one group in S61's worlds, short histories (`T = 3–5`)
  included, before the app step; the winning score is optimistic (`integral_min_score_le`), so report the
  chosen cut's error from an outer fold. Never merge a pair by its observed gap (Finding 43).
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
  *Ẑ shown 2026-11-27:* the card "Is correlation worth modelling?" has a table per region: blend `ẑⱼ`, BLUP own
  `Ẑⱼⱼ` and borrowed `Σᵢ≠ⱼ Ẑⱼᵢ` on corrBS's `K̂` (badge proved, `Core.blupWeight_dotProduct`). Open: the fit with
  `θ̂` and the readout of `S` with the safe range.
  *Studied 2026-11-27* (S64, `studies/runs/held-out-theta.js`): no. `θ̂` costs 1–15 points against `θ = 1` under a
  common shock (the plug-in BLUP is within 0.7 of the best fixed `θ`), pooled over years too; the price of
  one held-out year is exactly `ΔᵀWΣWΔ/ΔᵀWΔ ≥ σ²(1 − ρ)`, 7–14× the gain available. So no `θ̂` step: keep
  `θ = 1`, show `S` only. Lean target 1 of S64 done 2026-11-27 (`integral_wLoss_heldOutTheta`,
  `le_heldOutPrice`); target 2 done 2026-11-27 (`Factor.HeldOut.integral_wsum_noise`). Gauge of `Z`'s rows settled 2026-11-27 (handbook `res:blup_gauge`): show the zero-sum row `d̂* − b̂` next to
  the blend's `ẑ(eⱼ − b̂)` in the card.
