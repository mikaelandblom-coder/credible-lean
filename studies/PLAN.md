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
5. **Every new extension of the framework gets a switch.** The app is
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
| Bühlmann–Straub | yes | `bs_z`, `bs_balance`, `σ̂ⱼ²` (`sigRhoHat_self`) | the classical `τ̂²` of eq. (13) (G0) |
| Correlation, full `K̂` | yes: eqs. (37)–(41), damping | `KHat_unbiased`, `dampedK_posDef` | choice of the damping `θ` (G2) |
| Correlation, one common covariance | average of the pairwise estimators | closed form for `z` (`bestZ_of_equalCov`) | the estimator (G1) |
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
- **G7. Balance** under correlation: the best balanced blend.
- **G5. Decisions from data** (merging, choosing cohorts). Hardest, last.

The app itself decides the priority: a gap that makes no visible
difference on the screen is dropped.

## 6. Built for expansion

A feature is one entry in a list in `engine.js`:

- its name and controls;
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
- [ ] 4. Unequal lengths and group levels (world and fit). Offline support.
- [ ] 5. Prove the gaps the app shows to matter (Lean chats); badges turn
  to "proved".
- [ ] 6. Link the app from the README and handbook; screenshots of a few
  telling settings as the handbook's worked examples.
