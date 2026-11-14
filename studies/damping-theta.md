# Damping θ and the common-covariance fit: a numerical study

2026-11-14. Script: `studies/damping-theta.js` (run `node studies/damping-theta.js 1000 tau`;
output in `damping-theta.out.txt`). It uses the app engine's world (motor by region, skewed draws,
σ = 6, 500 vehicle-years per region and year, volume spread 1) and its fits, with the same
1000 draws for every column (common random numbers). Entries: exposure-weighted MSE of the rates
relative to the floor (100 = best blend with known parameters).

## Observations

1. **The best fixed θ grows with the correlation and with the data.** It is 0 at ρ = 0 and close
   to 1 at ρ = 0.9 or with T = 20 years. The curve is flat near its minimum: θ = 0.95 is within a
   few points of the best, *except* with a short history (T = 5) or a small τ (τ = 0.03 at ρ = 0:
   182 against 156 at θ = 0).
2. **θ = 1 (no damping) is risky.** With T = 5 years and 8 regions, `K̂` is not positive definite
   in up to 23% of draws. With a small τ, θ = 1 costs +60–100 points.
3. **A shrinkage rule from data is near the best fixed θ.**
   `θ̂ = ρ̄² / (ρ̄² + (1 − ρ̄²)²/(T − 1))`, with ρ̄ the average estimated correlation over the pairs:
   signal ρ̄² against the sampling variance of a correlation from T years. It lands within 0–2
   points of the best fixed θ in 23 of 24 worlds (worst: +7, at τ = 0.03, ρ = 0.6). It needs no
   tuning and goes to 0 by itself when there is no correlation.
4. **The common-covariance fit (G1 as stated) breaks down when volumes differ.** At θ = 0.95 it
   is 116–193 180 % of the floor. True covariances scale like `1/√(wᵢ* wⱼ*)`, so one common `c`
   exceeds the noise variance `vⱼ` of the large regions. Then `τ̂² + vⱼ − c` in
   `zⱼ = τ̂²/(τ̂² + vⱼ − c)` is near zero: |z| > 3 in 18% of draws at ρ = 0.6 (max |z| ≈ 1600).
   Equal covariances is the wrong one-parameter model unless the volumes are equal.
5. **A common *correlation* works best overall.** `Σ̂ᵢⱼ = ρ̄ √(Σ̂ᵢᵢ Σ̂ⱼⱼ)`, damped by θ̂: best or
   tied best in almost every world, often better than the best fixed θ of the full `K̂` (fewer
   parameters to estimate). Its Σ̂ is positive semidefinite for ρ̄ ≥ 0, so `dampedK_posDef`
   applies.
6. **At ρ = 0, BS is still slightly better** (111 against 114 for the full fit). That is the
   cost of estimating correlations that are not there. Under correlation, BS loses 10–80 points.

## Hypotheses (candidate theorems, replace G1/G2 in PLAN.md)

- **H1 (G1 restated).** With `σⱼₜ² = σ²/wⱼₜ` and a common correlation ρ, the pairwise estimators
  give an (asymptotically) unbiased ρ̄, and the blend with `Σᵢⱼ = ρ √(ΣᵢᵢΣⱼⱼ)` has a usable closed
  form (a rank-one plus diagonal `K`: `Core` already has rank-one `K`).
- **H2 (G2).** The shrinkage θ̂ above is the MSE-optimal θ to first order in 1/T. Hard to prove
  exactly; first check the derivation on paper (Ledoit–Wolf-style).
- **H3.** Clipping is not the main fix for wild z: the wild z come from the misspecified common
  covariance, not from the thesis fit (G3 drops in priority).

Not tested yet: unequal lengths, group levels, negative ρ, a country structure in ρ.

## Does it depend on the noise distribution? (`damping-dist.js`, output `damping-dist.out.txt`)

Same study, J = 8, T ∈ {5, 10}, noise laws with mean 0, variance 1 and excess kurtosis
κ = −2 (two-point), 0 (normal), 3 (gamma k = 2), 6 (exponential), 24 (gamma k = 0.25).

7. **The best fixed θ depends on the distribution**, not only on two moments. At T = 5, ρ = 0.3
   it is 0 for normal or two-point noise and 0.75 for κ = 24. So no theorem with only first and
   second moments can give the optimal θ: fourth moments must enter, as given numbers.
8. **The θ̂ rule tracks the best θ under every law** (within 0–3 points in all 40 cases), although
   its variance term `(1 − ρ̄²)²/(T − 1)` is the normal-theory one. It adapts per draw, and the
   error curve is flat near its minimum.
9. **The fit can beat the floor under heavy tails** (93–99 at κ ≥ 6, ρ ≥ 0.6). The floor is the
   best blend with *fixed* weights `z, b`; the fitted weights depend on the data, so the fit is a
   non-linear estimator and is not bound by it. The app should call the floor "the best fixed
   blend", not "the best possible".
10. **Per-region variances are fragile with short histories.** Two-point noise, T = 5, ρ = 0: the
    full fit scores 184 even at θ = 0, BS 118. With T = 5 a region's σ̂ⱼ² is often near 0
    (all years on one side), so its vⱼ ≈ 0 and it grabs the weight. BS pools σ̂² over regions.

## What a distribution-free theorem can say

- The thesis model assumes only that years are *uncorrelated*. The variance of the pairwise
  estimators involves fourth moments `E[εᵢₜεⱼₜεₖₛεₗᵤ]` across years, which "uncorrelated" leaves
  free. A theorem about Var of the estimators needs either those numbers as parameters or a
  stronger assumption on years (e.g. independent years with given fourth moments). That is a
  modelling choice, not a distribution.
- **Exact and distribution-free:** for estimates `ŝᵢⱼ` with mean `sᵢⱼ` and variance `Vᵢⱼ` (given
  numbers), `E Σ (θŝᵢⱼ − sᵢⱼ)²` is minimised at `θ* = Σs²/(Σs² + ΣV)`. θ̂ is a plug-in of this.
  The link from this proxy loss to the rates' MSE stays numerical.
- **The ratio ρ̄** has no exact moment-based expectation. Avoid it: with a common σ (BS noise)
  the common-correlation `K` needs only `ρσ²` and `σ²`, both with unbiased *linear* estimators,
  so `K̂` is entrywise unbiased with no ratio. With region-specific σⱼ the ratio is unavoidable;
  then only asymptotic results (T → ∞, needs a law of large numbers and independent years) exist.
