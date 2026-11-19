# Roadmap (ideas, not commitments)

Written 2026-11-11 from a planning chat. The aim: tie the extensions and
stand-alone lemmas into the framework, then extend it, and end with
something a practitioner can use. Tick items off or delete them as they are
done; details of finished work live in `FINDINGS.md` and `PROGRESS.md`.

## 1. Finish the integration

- [ ] **k-means bridge.** `kmeans_contiguous` is used by nothing. Target:
  with a common variance `V`, the total credibility MSE of a partition into
  cohorts is a constant plus a weighted k-means cost, so the MSE-optimal
  cohorts are intervals of the sorted means (exact by dynamic programming).
  With unequal `V` the merge rule `1/d > 1/V + 1/τ²`
  (`notes/merging-cohorts.md`) has a pair-dependent scale, so contiguity may
  fail: a counterexample would be a finding. *On paper 2026-11-11*
  (`notes/kmeans-bridge.md`, Finding 14): exact for exposure-weighted
  pooling, any `V`; counterexamples with unequal `V` for the blend and the
  unweighted loss. Next: the two Lean statements listed in the note.
- [x] **Damping bridge** (done 2026-11-11: `Unequal.dampedK_posDef`, holds for
  any `τ̂² ≥ 0`, so truncating `τ̂²` at zero is safe; handbook result
  `res:damped`).
- [x] **Moment layer once, for a level covariance `L`** (done 2026-11-10:
  `Core.Estimates`, `HierarchicalMoments.lean`).
- [ ] **Housekeeping.** Handbook sections 2–5; README status paragraph
  (done 2026-11-17: the README no longer carries counts); backlog from
  `progress.py --dupes`.

## 2. Time trends (in this order)

Detailed plan, with frequency × severity: [`time-trends.md`](time-trends.md)
(2026-11-19: known common trend first, then estimated, then Hachemeister
via a matrix Blend shared with bivariate frequency–severity credibility).

- [ ] **Period shocks are already in the model.** A common random period
  effect is an equal-correlation `ρ`; loadings `λᵢλⱼ` give the rank-one `K`
  of Core. A short interpretation theorem: where `ρ` comes from.
- [ ] **Shock plus process noise (Finding 23).** Replace `σᵢₜσⱼₜρᵢⱼ` by
  `Cᵢⱼ + δᵢⱼ sᵢ²/wᵢₜ`: a period shock that does not shrink with volume. New `obsCov`
  table; `K`, positive definiteness (`C ⪰ 0`, `s² > 0`) and unbiased estimators of `C`
  and `s²` (rank-one `C = λλᵀ` as the one-parameter-per-cohort case). Compare with the
  thesis estimators when volumes grow.
- [ ] **Serial correlation.** Replace `δₜₛ` in `cov(εᵢₜ, εⱼₛ)` by a general
  PSD table over cells `(j,t)`, AR(1) as the example. New `K`, prove it PD,
  Core applies unchanged; unequal lengths become a special case.
- [ ] **Deterministic trend (Hachemeister).** A slope per cohort makes `z` a
  matrix, so `Blend` needs a matrix version. Biggest step, most recognised
  by actuaries. The target changes from `μⱼ` to next period's level.

## 2b. Classical extensions without correlation (2026-11-19)

Correlation is one choice of `K`; these extend the linear, second-moment theory itself.
Lean work (**lean** environment).

- [ ] **Scalar inhomogeneous credibility.** Known collective mean `μ`: best `z` for
  `μ + z(μ̂ⱼ - μ)`, a short Core corollary (the vector version exists:
  `CoreVector.moments_bestZ_buhlmannGisler`). Compare with the homogeneous `z` of eq. (26).
- [ ] **General target (evolutionary credibility).** Predict any random target `Y` with known
  `Cov(Y, μ̂)` instead of the fixed level `μⱼ`. Gives next period's claim under random-walk or
  AR(1) levels (Gerber & Jones 1975; Bühlmann & Gisler ch. 10, Kalman filter), and joins the
  serial-correlation item in §2. Check first whether `Core.Estimates` with its `L` already
  covers it.
- [ ] **Balanced loss.** Loss `ω(δ - X̄)² + (1 - ω)(δ - target)²` (Zhang & Chen 2018,
  `studies/literature.md` §3): still linear and quadratic, so the best `z` should be a
  convex shift of eq. (26); prove at Core level.

## 3. Complex numbers (low priority)

- [ ] **Remark now.** `b = K⁻¹1 / 1ᵀK⁻¹1` is the minimum-variance
  distortionless-response (Capon) beamformer of array signal processing,
  where the data are complex. Worth one blueprint remark.
- [ ] **Later, one file.** Core for Hermitian `K` over `RCLike`. Catch:
  complex variables also have a pseudo-covariance, so "only first and second
  moments" splits into the proper and the general case.

## 4. Being of use

Detailed plan (an interactive app, world against fitted model; gap theorems):
[`studies/PLAN.md`](../studies/PLAN.md).

- [ ] **Reference implementation** in R (the thesis code is R): data →
  estimators → damped `K̂` → `b`, `z` → premiums. Tests are the proved
  identities (balance, Bühlmann–Straub at `ρ = 0`), run on a public dataset.
- [ ] **Plug-in honesty.** Everything proved is optimal for known
  parameters. Even one result with estimated ones (truncating `τ̂²` at zero,
  negative `b`) is what practitioners ask first.
- [ ] **Handbook and preprint**, with the worked example in both.
- [ ] **XoL: experience against exposure rating.** Eq. (7) with an MLE
  experience estimate and a rating tool (possibly expert judgment); `τ²` and
  the tool's bias from the current book's gaps. Discussion:
  [`xol-blend.md`](xol-blend.md).

Suggested order: the two bridges in 1, the handbook, serial correlation,
the R package.

## 5. Open problems (moved from the README, 2026-11-17)

- **Choosing cohorts from the data.** Pick the partition into cohorts that
  minimises the total credibility MSE itself, rather than clustering
  credibility estimates by Euclidean distance (as in van Rijn, Weber, Merz,
  *Credibility Clustering for Experience Rating*, arXiv:2611.07110). Known
  so far: for exposure-weighted pooling, and for the blend with a common
  variance, the optimal cohorts are intervals of the sorted levels, so
  dynamic programming finds them exactly; with unequal variances the blend's
  optimum need not be an interval (FINDINGS item 14,
  [`kmeans-bridge.md`](kmeans-bridge.md); one pair:
  [`merging-cohorts.md`](merging-cohorts.md)). Open: how choosing cohorts
  from the same data biases the second-stage estimate (winner's curse), and
  how correlations between cohorts change the optimal partition. Starting
  points: Diao & Weng, *Regression tree credibility model*, NAAJ 23(2)
  (2019); Campo & Antonio, *On clustering levels of a hierarchical
  categorical risk factor*, AAS 18(3) (2024), arXiv:2304.09046.
- **Hierarchical credibility.** With group levels (`Hierarchical`,
  `HierarchicalMoments`) a shared level drops out of credibility, the GLS
  weights are two-stage, and `τ̂²` needs pairs within and across groups
  (item 13). Open: consistency of the assumptions, and efficient estimation
  of `φ` from all pairs (PLAN G4).
- **Crossed levels.** Not started in Lean: cohorts in a table (country ×
  car type) sharing a level along both rows and columns, so that sport cars
  in Norway inform sport cars in Sweden. The balanced 2×2 case is worked out
  in [`crossed-2x2.md`](crossed-2x2.md): the best linear predictor has one
  credibility factor per layer (country, type, cell), and the thesis blend
  is the same formula with one common factor.
- **The app** (preview): unequal lengths and group levels in its world and
  fits, then proofs of the gaps it shows to matter (PLAN steps 4–5). Its
  study findings are numerical results in fixed simulated worlds, not
  theorems; they are reported with their world and script so they can be
  rerun. Statements about the best blend with known parameters have exact
  formulas and need no simulation.
- **Further credibility papers** to formalize in the thesis notation, each
  as its own `Credibility/<Topic>.lean` and blueprint chapter (candidates:
  Jewell's hierarchical model, Hachemeister's regression model).
