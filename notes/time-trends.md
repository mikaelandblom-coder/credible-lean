# Time trends, and frequency × severity

Planning note, 2026-11-19 (owner's question). Not in the thesis. Expands
`notes/roadmap.md` §2 ("Deterministic trend") and answers how to blend when
frequency and severity are observed separately. Steps 1–2 are proved in
`Credibility/Trend.lean` (2026-11-19); step 2's claim holds only for the true
`g` (Finding 21).

## 1. Trends: four steps, simplest first

Model today (thesis eq. 15, `Unequal`): `μⱼₜ = μⱼ + σⱼₜ εⱼₜ`, no drift in `t`.

### Step 1: a known common trend `g` (x % a year). Nothing new to prove.

World: `E[Xⱼₜ | μⱼ] = μⱼ · (1+g)^t`, and the noise scales with the level
(constant coefficient of variation), `Xⱼₜ = (1+g)^t (μⱼ + σⱼₜ εⱼₜ)`.

Detrend to the target year `T+1`: `X̃ⱼₜ = (1+g)^(T+1−t) Xⱼₜ`. Then `X̃`
satisfies the thesis model exactly, with `μⱼ` replaced by the level in year
`T+1`, `(1+g)^(T+1) μⱼ`, and `σⱼₜ` by `(1+g)^(T+1) σⱼₜ`. So all of Core,
`Unequal`, the estimators (§2.8) and the moment layer apply to `X̃` as they
stand. Correlations `ρ` and `τ²/μ²` are unchanged.

If instead the noise does *not* grow with the trend (additive noise), the
detrended cell variance is `(1+g)^(2(T+1−t)) σⱼₜ²`: still a per-cell
variance, so `Unequal` covers it (older years get a smaller weight).

Lean (small, one file `Credibility/Trend.lean`): `Unequal.detrend`, the
rescaled data, and a theorem that its `K` is the old `K` times `(1+g)^(2(T+1))`
(constant-CV case), so `bestZ`, `b`, GLS weights are *unchanged* and the
premium just scales. One-line corollaries of `Unequal`. Handbook: one entry
("trend first, then blend; the weights do not move").

### Step 2: the common trend is estimated (`ĝ` from the portfolio).

Usual practice: fit `log` of the portfolio's yearly rate on `t`, or take an
external index. Facts worth stating:
- **Relativities are trend-free** (`Unequal.Noise.relativity_detrend`): restated
  with the true `g`, the blend's relativity `μ̂ⱼ / μ̂` does not depend on `g`
  (constant CV). `z`, `a`, `b` do not depend on `ĝ` at all. But an estimate
  `ĝ ≠ g` leaves a year-dependent factor that reweights years within a cohort,
  so relativities do move slightly (Finding 21, counterexample there); `ĝ` is a
  pure level shift only when all cohorts share one time profile.
- The error in `ĝ` is a common factor on every cohort's projection: a
  *common shock* on the prediction, i.e. an equal-correlation term.
  Year effects (hard winters, already our `ρ`) inflate the variance of `ĝ`;
  with `ρ > 0` the OLS slope on the portfolio is not the GLS slope.
- App study (no Lean): price of estimating `g`, plain OLS vs GLS with the
  year-shock covariance; the floor uses the true `g`.

### Step 3: cohort-specific trends (Hachemeister 1975).

Each cohort has a random level *and* a random slope:
`E[Xⱼₜ | θⱼ] = aⱼ + bⱼ (t − t̄ⱼ)`. The credibility factor becomes a 2 × 2
matrix. Known catch: with an uncentred time axis the matrix mixes level and
slope; Bühlmann & Gisler (1997) centre `t` at each cohort's volume-weighted
mean so the two decouple into two scalar credibilities.

What is new here: Hachemeister *with correlated cohorts*. Year shocks
correlate both the level and the slope estimates across cohorts, so `K`
becomes a block matrix over (cohort × {level, slope}). This needs a
**matrix Blend** in Core: vector-valued `μⱼ ∈ ℝᵖ`, covariance of the levels
`Λ` (`p × p`) instead of `τ²`, best predictor
`μ̂ⱼ = m + Z (μ̂ⱼ^data − m)` with `Z` a matrix. Rule of three: §2 below
needs the same generalisation, so build it once (`Credibility/CoreVector.lean`).
Target changes from `μⱼ` to next year's value `aⱼ + bⱼ (T+1 − t̄ⱼ)`.

### Step 4: evolving levels (later).

Random-walk or AR(1) levels (Gerber & Jones 1975; Bühlmann & Gisler, ch. 10,
evolutionary credibility / Kalman filter). Ties in with the "serial
correlation" item in the roadmap: recent years get more weight. Only after
step 3.

## 2. Frequency and severity

Cell `(j, t)`: exposure `eⱼₜ`, claim count `Nⱼₜ`, claim amount `Sⱼₜ`.
- frequency `Fⱼₜ = N/e`, weight `e`, level `φⱼ`;
- severity `Yⱼₜ = S/N`, weight `N` (condition on the counts, as usual),
  level `ψⱼ`;
- burning cost `Bⱼₜ = S/e = F·Y`, weight `e`, level `πⱼ = φⱼ ψⱼ`.

### Different trends are not by themselves a reason to blend separately.

If the trends are common to all cohorts, trend each component with its own
rate (`g_F`, `g_Y`), rebuild the projected burning cost
`B̃ⱼₜ = F̃ⱼₜ · Ỹⱼₜ`, and blend `B̃` once. By step 1 that is exactly the
thesis model, with trend `(1+g_F)(1+g_Y) − 1`. This is the recommended
first step (and the standard in ratemaking: Werner & Modlin trend frequency
and severity separately, then combine).

### When blending separately is better

1. **Different credibility.** Frequency is far less noisy than severity
   (one heavy claim moves `Y` a lot). Blending `B` forces one `z` on a mix
   of a well-measured and a badly measured factor; separate blends give a
   high `z_F` and a low `z_Y`.
2. **Different correlations — specific to our framework.** In the app's
   story a hard winter raises *frequency* in all regions of a year (high
   `ρ_F`) but hardly severity; severity is driven by repair costs, which
   move together through inflation (the trend) rather than through year
   shocks (low `ρ_Y`). So the two components have different `K`, and the
   GLS weights `b` and the balance correction differ. A single `K` for `B`
   averages them.
3. **Different trends by cohort** (step 3) are per component anyway.

### What separate blending costs

The premium is `φ̂ⱼ ψ̂ⱼ`, a product of two linear estimators:
- `φ̂ψ̂ − φψ = φ(ψ̂−ψ) + ψ(φ̂−φ) + (φ̂−φ)(ψ̂−ψ)`: unbiased and with an MSE that
  adds up only if the two estimation errors are uncorrelated with each other
  and with the other level. That holds when the levels `φⱼ`, `ψⱼ` are
  independent across components and the count and amount noises are
  conditionally independent (the compound model).
- **Correlated levels break it.** Urban regions: more claims, smaller ones
  (`cov(φⱼ, ψⱼ) < 0`). Then frequency data carry information about severity
  and the separate blends throw it away; the product is also biased by
  `cov(φ̂−φ, ψ̂−ψ)`.

### The principled answer: bivariate credibility = the matrix Blend

Treat `(φⱼ, ψⱼ)` as a vector level with covariance `Λ` (2 × 2, off-diagonal
= level correlation), data `(F̄ⱼ, Ȳⱼ)` with noise covariance across cohorts
`K_F`, `K_Y` (and `K_FY = 0` in the compound model). This is Jewell's
multidimensional credibility (Bühlmann & Gisler ch. 7) with our correlated
cohorts on top: **the same Core generalisation as Hachemeister** (step 3).
Separate blending is its special case `Λ` diagonal; blending `B` is the
other extreme. Theorem targets:
- the vector blend's MSE ≤ both separate blends and the single `B` blend
  (each is a restricted linear predictor);
- equality conditions: separate = vector iff `Λ` diagonal and `K_FY = 0`.
- precedent: Bühlmann (1974, ASTIN 7(3)) did this for one risk with independent
  levels (`literature.md` §7a): the two-statistic formula always wins, and the
  two restricted ones (claim count only, total only) are *not ordered*. Expect
  the same for separate vs single-`B` blends; don't try to prove an order.
For the premium `φψ` itself, a linear predictor is not optimal; the
first-order (delta-method) target `ψ̄ φ + φ̄ ψ` is linear and fits the
same machinery. State it as such, don't hide the approximation.

## 3. Order of work

1. Step 1 (Lean, small) + handbook entry + app switch "claim trend g"
   (today `growth` in `app/engine.js` is *volume* growth, not a claim
   trend). Default environment can do the app part; Lean needs **lean**.
2. Step 2: relativities-are-trend-free theorem (Lean) and the `ĝ` study (app).
3. App: split the world into frequency and severity (Poisson counts, gamma
   amounts, `ρ_F ≠ ρ_Y`, optional level correlation). Compare three fits on
   screen: blend `B̃`, separate blends, product. This shows whether the gap
   matters before proving anything (PLAN §5: a gap that makes no visible
   difference is dropped).
4. `CoreVector.lean`: the matrix Blend, PD of the block `K`, best `Z`,
   balance. Then Hachemeister with correlated cohorts and bivariate
   frequency–severity as its two corollaries.
   *Started 2026-11-19:* matrix eq. (7) (Loewner-optimal, unique for the
   trace, `P = Unit` is the scalar blend), matrix GLS weights (optimal) and
   matrix eq. (26) are proved. Open: block-diagonal `K` gives Bühlmann–Gisler
   ch. 7; balance; the moment layer; the two corollaries.
5. Step 4 (evolving levels) with serial correlation.

## 4. Literature to build on (see `studies/literature.md` §7)

Hachemeister (1975); Bühlmann & Gisler (1997, ASTIN 27(1)) for the centred
time axis; Jewell (1975) on regression credibility under inflation;
Jewell (1973) multidimensional credibility; Goulet, Forgues & Lu (2006,
NAAJ 10(1)), four frequency–severity credibility formulas from one
minimisation problem; Hewitt (1971) on severity credibility; Gerber & Jones
(1975) for evolving levels; Werner & Modlin, *Basic Ratemaking*, for
separate frequency and severity trending.
