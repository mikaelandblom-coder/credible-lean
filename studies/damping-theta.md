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
