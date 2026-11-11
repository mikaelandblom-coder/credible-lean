# Roadmap (ideas, not commitments)

Written 2026-11-11 from a planning chat. The aim: tie the extensions and
stand-alone lemmas into the framework, then extend it, and end with
something a practitioner can use. Tick items off or delete them as they are
done; details of finished work live in `README.md` and `FINDINGS.md`.

## 1. Finish the integration

- [ ] **k-means bridge.** `kmeans_contiguous` is used by nothing. Target:
  with a common variance `V`, the total credibility MSE of a partition into
  cohorts is a constant plus a weighted k-means cost, so the MSE-optimal
  cohorts are intervals of the sorted means (exact by dynamic programming).
  With unequal `V` the merge rule `1/d > 1/V + 1/τ²`
  (`notes/merging-cohorts.md`) has a pair-dependent scale, so contiguity may
  fail: a counterexample would be a finding. Unverified: state it on paper
  first.
- [x] **Damping bridge** (done 2026-11-11: `Unequal.dampedK_posDef`, holds for
  any `τ̂² ≥ 0`, so truncating `τ̂²` at zero is safe; handbook result
  `res:damped`).
- [x] **Moment layer once, for a level covariance `L`** (done 2026-11-10:
  `Core.Estimates`, `HierarchicalMoments.lean`).
- [ ] **Housekeeping.** Handbook sections 2–5; README status paragraph
  (theorem count, list of extensions); backlog from
  `progress.py --dupes`.

## 2. Time trends (in this order)

- [ ] **Period shocks are already in the model.** A common random period
  effect is an equal-correlation `ρ`; loadings `λᵢλⱼ` give the rank-one `K`
  of Core. A short interpretation theorem: where `ρ` comes from.
- [ ] **Serial correlation.** Replace `δₜₛ` in `cov(εᵢₜ, εⱼₛ)` by a general
  PSD table over cells `(j,t)`, AR(1) as the example. New `K`, prove it PD,
  Core applies unchanged; unequal lengths become a special case.
- [ ] **Deterministic trend (Hachemeister).** A slope per cohort makes `z` a
  matrix, so `Blend` needs a matrix version. Biggest step, most recognised
  by actuaries. The target changes from `μⱼ` to next period's level.

## 3. Complex numbers (low priority)

- [ ] **Remark now.** `b = K⁻¹1 / 1ᵀK⁻¹1` is the minimum-variance
  distortionless-response (Capon) beamformer of array signal processing,
  where the data are complex. Worth one blueprint remark.
- [ ] **Later, one file.** Core for Hermitian `K` over `RCLike`. Catch:
  complex variables also have a pseudo-covariance, so "only first and second
  moments" splits into the proper and the general case.

## 4. Being of use

- [ ] **Reference implementation** in R (the thesis code is R): data →
  estimators → damped `K̂` → `b`, `z` → premiums. Tests are the proved
  identities (balance, Bühlmann–Straub at `ρ = 0`), run on a public dataset.
- [ ] **Plug-in honesty.** Everything proved is optimal for known
  parameters. Even one result with estimated ones (truncating `τ̂²` at zero,
  negative `b`) is what practitioners ask first.
- [ ] **Handbook and preprint**, with the worked example in both.

Suggested order: the two bridges in 1, the handbook, serial correlation,
the R package.
