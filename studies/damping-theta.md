# Damping θ and the common-covariance fit: a numerical study

2026-11-14. Script: `studies/damping-theta.js` (run `node studies/damping-theta.js 1000 tau`;
output in `damping-theta.out.txt`). It uses the app engine's world (motor by region, skewed draws,
σ = 6, 500 vehicle-years per region and year, volume spread 1) and its fits, with the same
1000 draws for every column (common random numbers). Entries: exposure-weighted MSE of the rates
relative to the floor (100 = best blend with known parameters).

The study findings are numbered S1–S29 (cited as "finding S19" in `studies/` and `app/`), so
they do not clash with the findings 1–16 of `FINDINGS.md`.

## Observations

- S1. **The best fixed θ grows with the correlation and with the data.** It is 0 at ρ = 0 and close
   to 1 at ρ = 0.9 or with T = 20 years. The curve is flat near its minimum: θ = 0.95 is within a
   few points of the best, *except* with a short history (T = 5) or a small τ (τ = 0.03 at ρ = 0:
   182 against 156 at θ = 0).
- S2. **θ = 1 (no damping) is risky.** With T = 5 years and 8 regions, `K̂` is not positive definite
   in up to 23% of draws. With a small τ, θ = 1 costs +60–100 points.
- S3. **A shrinkage rule from data is near the best fixed θ.**
   `θ̂ = ρ̄² / (ρ̄² + (1 − ρ̄²)²/(T − 1))`, with ρ̄ the average estimated correlation over the pairs:
   signal ρ̄² against the sampling variance of a correlation from T years. It lands within 0–2
   points of the best fixed θ in 23 of 24 worlds (worst: +7, at τ = 0.03, ρ = 0.6). It needs no
   tuning and goes to 0 by itself when there is no correlation.
- S4. **The common-covariance fit (G1 as stated) breaks down when volumes differ.** At θ = 0.95 it
   is 116–193 180 % of the floor. True covariances scale like `1/√(wᵢ* wⱼ*)`, so one common `c`
   exceeds the noise variance `vⱼ` of the large regions. Then `τ̂² + vⱼ − c` in
   `zⱼ = τ̂²/(τ̂² + vⱼ − c)` is near zero: |z| > 3 in 18% of draws at ρ = 0.6 (max |z| ≈ 1600).
   Equal covariances is the wrong one-parameter model unless the volumes are equal.
- S5. **A common *correlation* works best overall.** `Σ̂ᵢⱼ = ρ̄ √(Σ̂ᵢᵢ Σ̂ⱼⱼ)`, damped by θ̂: best or
   tied best in almost every world, often better than the best fixed θ of the full `K̂` (fewer
   parameters to estimate). Its Σ̂ is positive semidefinite for ρ̄ ≥ 0, so `dampedK_posDef`
   applies.
- S6. **At ρ = 0, BS is still slightly better** (111 against 114 for the full fit). That is the
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

- S7. **The best fixed θ depends on the distribution**, not only on two moments. At T = 5, ρ = 0.3
   it is 0 for normal or two-point noise and 0.75 for κ = 24. So no theorem with only first and
   second moments can give the optimal θ: fourth moments must enter, as given numbers.
- S8. **The θ̂ rule tracks the best θ under every law** (within 0–3 points in all 40 cases), although
   its variance term `(1 − ρ̄²)²/(T − 1)` is the normal-theory one. It adapts per draw, and the
   error curve is flat near its minimum.
- S9. **The fit can beat the floor under heavy tails** (93–99 at κ ≥ 6, ρ ≥ 0.6). The floor is the
   best blend with *fixed* weights `z, b`; the fitted weights depend on the data, so the fit is a
   non-linear estimator and is not bound by it. The app should call the floor "the best fixed
   blend", not "the best possible".
- S10. **Per-region variances are fragile with short histories.** Two-point noise, T = 5, ρ = 0: the
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

## A distribution-free θ̂ from the data (`damping-vhat.js`, `damping-oracle.js`)

Rule: `θ̂ = 1 − ΣV̂ᵢⱼ / Σŝᵢⱼ²` (Ledoit–Wolf form), with `V̂ᵢⱼ = T·s²(p)/Dᵢⱼ²` from the yearly
products `pₜ` (independent years, no normal-theory formula); raw and correlation scale agree.

- S11. **It is worse than the normal-theory rule**, by up to 10 points, at high ρ and with heavy
    tails: it damps too much (θ̂ ≈ 0.5 where the best θ is 0.95–1).
- S12. **The fault is the target, not V̂.** The oracle optimum of the stand-in loss
    `E Σ (θŝᵢⱼ − sᵢⱼ)²`, from the true variances: normal, ρ = 0.9: 0.80 (V̂ rule: 0.81, so V̂ is
    accurate there); κ = 24, ρ = 0.9: 0.29 (V̂ rule: 0.52; V̂ underestimates heavy tails from 10
    years). But the best θ *for the rates* is 0.99 there. Heavy tails make Σ̂ a worse estimate of
    the population K, yet the rates want *less* damping.
- S13. **Why (hypothesis H4):** Σ̂ is computed from the same years as the region means. A hard
    winter in this data set inflates Σ̂ in the same draw, and GLS then cancels that very shock.
    So Σ̂ is useful as a measurement of *this* history's common noise, not only as an estimate of
    K. Damping towards the population K throws that away. The same effect lets the fit beat the
    fixed-weight floor (finding S9).

**Consequence for G2.** The shrinkage lemma (θ* = S/(S + V)) is true and distribution-free but
optimises the wrong loss: it is not the θ the rates need. Use damping for safety (`K̂ ≻ 0`) with θ
near 1 once a correlation is clearly present, and θ → 0 only when ρ̄ ≈ 0. The normal-theory rule
does exactly that, which is why it works; its variance formula is not the reason.

## Towards a fit with no tuning (2026-11-14, owner: "the fit is determined by its own data only")

Scripts: `damping-cv.js`, `common-rho.js`, `common-rho-mom.js`, `common-rho-misspec.js`,
`variance-credibility.js` (outputs in the matching `.out.txt`).

- S14. **Cross-validation (leave one year out) is no help.** Data-only and in theory unbiased for
    ranking methods, but noisy, and too cautious: a held-out year's common shock cannot be
    cancelled, so it undervalues correlation modelling (finding S13). At ρ = 0.9 it scores
    120–129 where the fixed rules score 110.
- S15. **A common correlation needs no damping.** With one ρ ∈ [0, 1) the estimated table is
    `Σ = Λ((1 − ρ)D + ρG)Λ` (G the Gram matrix `Sᵢⱼ/(wᵢ*wⱼ*)`, D its diagonal, Λ = diag σⱼ), positive
    definite by `K_posDef` for a PSD ρ-table. θ̂ and its normal-theory formula disappear.
- S16. **Correlated BS** (one σ², one ρ, `ρσ²` by one moment equation over all pairs, unbiased, no
    ratio): best or within 1 point of best in all 64 worlds where its assumptions hold, and equal
    to BS at ρ = 0. Robust to a country structure in ρ. **But it fails with region-specific σⱼ**
    (139–146 against 121 for the full fit): the pooled σ̂² is its weak point.
- S17. **Credibility for the variances fixes that.** `σ̃ⱼ² = ζⱼσ̂ⱼ² + (1 − ζⱼ)σ̂²` with
    `ζⱼ = β²/(β² + Wⱼ)`: `Wⱼ` the variance of σ̂ⱼ² estimated from the yearly terms (independent
    years), `β²` the between-region variance of the σⱼ² by a moment equation. This is
    Bühlmann–Straub one level up. Then ρ by one moment equation on the standardised pairs. Over 45
    worlds (equal or spread σⱼ, ρ = 0 / 0.6 / countries, three noise laws, T = 5 / 10, J = 8 / 20)
    it is the most robust fit: best or near best almost everywhere, typically 5–30 points better
    than the full fit when σⱼ differ and ρ > 0. Weak spot: two-point noise with T = 5 at ρ = 0
    (182 against BS 116), the lattice case where a region's σ̂ⱼ² is often ≈ 0.

## Ansatz

**Correlated Bühlmann–Straub with credibility-weighted variances.** Parameters τ², σⱼ² (shrunk
towards the pooled σ², the shrinkage itself estimated), one ρ; every step a moment equation;
nothing to tune; `K̂ ≻ 0` by construction. Provable pieces, distribution-free:
1. `K ≻ 0` for a common ρ ∈ [0, 1) (corollary of `K_posDef`).
2. Equal σ: the pooled moment estimator of `ρσ²` is unbiased (linear in the data products).
3. The variance credibility factor ζⱼ is the best linear blend of σ̂ⱼ² and the pooled σ̂²: an
   instance of `bs_z` / `Core.bestZ_of_diag`, with the fourth moments as given numbers. Its
   unbiased estimators (`Wⱼ`, `β²`) need independent years.
4. Not unbiased end to end (estimates are plugged into z, as in classical BS). The quality of the
   whole stays numerical, like Prasad–Rao (1990) treat the EBLUP.
Literature to read for it: Ebrahimzadeh et al. (2012) (common-effects estimators), the
small-area work on shrinking means and variances (arXiv 1507.05179), Bühlmann–Gisler on
heterogeneous variances.

## Can the fit estimate its own error? (`msep.js`, output `msep.out.txt`)

Jackknife MSEP of Jiang, Lahiri & Wan (2002, Ann. Stat. 30), deleting one year at a time
(independent years): `MSEPⱼ = g₁₂ⱼ(θ̂) − (T−1)/T Σₜ (g₁₂ⱼ(θ̂₋ₜ) − g₁₂ⱼ(θ̂)) + (T−1)/T Σₜ (rateⱼ(θ̂₋ₜ) − rateⱼ(θ̂))²`,
with g₁₂ the known-parameter MSE (`blendMSE`) and θ̂₋ₜ the parameters re-estimated without year t
(region means kept). Data only, distribution-free, no tuning. 27 worlds, 1000 draws each.

- S18. **Plugging the estimates into the known-parameter MSE understates the error** by 13–50%
    (ratio 0.50–0.87): it misses the price of estimation.
- S19. **The jackknife MSEP is right on average within about ±15%.** With equal σ and T = 10 it is
    0.97–1.02 for normal and gamma noise; heavy tails (κ = 24) overstate by 11–17% (cautious);
    region-specific σⱼ understate by 10–15% (0.85–0.90), probably because the variance credibility
    shrinks the noisiest regions' σ̃ⱼ² towards the pool, a bias the jackknife does not see. T = 5
    is rougher (0.87–1.21). Per region the ratio spreads more (0.66–1.98 in the worst world).
- S20. The estimation part g₃ is 6–50% of the MSEP: large with few years or heavy tails, small with
    many regions. That is the "price of estimation" the app shows as fit − floor, now estimated
    from one data set.

Not measured yet: how noisy one data set's MSEP estimate is (its spread across draws), and
whether an interval `rate ± 2√MSEP` covers the true level as often as it should.

## The two extra terms, measured (`msep-terms.js`, output `msep-terms.out.txt`)

Fit error = e* + d with e* the floor's error and d = fitted rate − floor rate, so
MSE(fit) = MSE(floor) + C + g₃ with C = 2E[e*d], g₃ = E[d²]. In % of the floor MSE, 2000 draws:

- S21. **The cross term C follows the excess kurtosis, not the skewness.** ρ = 0.6, T = 10: two-point
    (κ = −2) +1.9, normal 0.0, gamma k = 2 (κ = 3) −2.5, gamma k = ¼ (κ = 24) −24.8, and its mirror
    image (skewness −4, same κ) −24.1. Reason: d = (ẑ − z)(μ̂ⱼ − μ̂) + …, a parameter error
    (quadratic in the noise) times a linear term, so e*·d is of fourth order in the noise. Under
    normality the fourth cumulants vanish and C = 0 (Kackar–Harville). Heavy tails make C negative:
    a large shock inflates the deviation μ̂ⱼ − μ̂ *and* the variance estimates, so ẑ shrinks harder
    exactly when the raw mean is most off. The fit corrects itself; that is why it can beat the
    floor.
- S22. **The jackknife g₃ is good with T = 10 (0.87–1.15 of the true E[d²]) and too large with T = 5
    (up to 2.7×)**, also at ρ = 0 (1.5–2.2×), where ρ̂ sits on its truncation at 0. Upward bias is
    expected (Efron–Stein inequality: the jackknife variance estimate is biased upwards for any
    statistic of independent units) and grows near the kinks (truncation of τ̂², ρ̂, β²).
- S23. **The jackknife MSEP has no C at all.** Jiang–Lahiri–Wan work with the best predictor, whose
    error is orthogonal to every function of the data; a linear credibility blend's error is only
    orthogonal to linear functions, so C ≠ 0 without normality. The earlier 11–17% overstatement
    under heavy tails is this missing negative C.

## SURE: choosing the shrinkage, and estimating the error (`sure.js`, output `sure.out.txt`)

SURE (Stein 1981) with Σ̂ from the moment fit plugged in for Σ; 27 worlds, 1000 draws each.

- S24. **SURE-chosen τ² (Xie–Kou–Brown style) is worse than the moment fit everywhere**: +3 to +25
    points (e.g. 108 → 118 at J = 8, T = 10, normal, ρ = 0.6), also under normal noise. Its τ² is
    too large on average (1.1–4.7× the truth, moment fit 1.0–1.5×) and noisy. Minimising one noisy
    risk estimate over τ² overfits it; Xie–Kou–Brown's gains are for hundreds of units, we have
    8–20. The moment estimator of τ² is the better choice here.
- S25. **SURE as an error estimate for the moment fit is right on average within −30% / +15%**
    (0.70–1.15), the jackknife within −15% / +28% (0.85–1.28). SURE is better under heavy tails
    (κ = 24: 0.81–1.15 against 1.12–1.28), the jackknife under normal and gamma(2) noise. SURE is
    only exact with Σ *known*; plugging in Σ̂ (from T − 1 degrees of freedom) makes it too small,
    most with T = 5 and with region-specific σⱼ (0.70).
- S26. **Neither predicts the error of one particular data set**: the per-draw correlation of SURE
    with the actual loss is −0.13 to 0.28. The loss of one data set depends on where the unknown
    levels happen to lie; an MSEP estimate is about the average over such data sets. For the app:
    show the MSEP as "typical error", not as an interval that covers the truth in this data set.

**Verdict on the distribution layer (so far).** For choosing the fit it does not pay: the
moment fit wins. For the error estimate, SURE and the jackknife are comparable, with opposite
strengths. A normal-noise refinement that accounts for Σ̂ (its Wishart distribution, independent of
the means under normality) could remove SURE's downward bias; that is the one place where a
distribution clearly helps. Not tried: Hudson's identity for a gamma family (needs a model where the
variance follows the mean, unlike our additive noise).

## corrBS flags and the cost of balance (`vc-balance.js`, output `vc-balance.out.txt`)

corrBS shows negative b in ≈70%, off-balance > 1% in ≈45%, z > 1 in ≈40% of draws at ρ = 0.6,
σⱼ spread (app world, gamma noise). Are these the fit's fault? Compared with the floor (true K, τ²)
and with three ways to force exposure balance Σⱼ wⱼ*μ̂ⱼᵇ = Σⱼ wⱼ*μ̂ⱼ, z kept: BS-style collective
μ̂ = Σ wⱼ*(1 − zⱼ)μ̂ⱼ / Σ wⱼ*(1 − zⱼ); every rate scaled; every rate shifted by the same amount
(benchmarking, Wang–Fuller–Qu 2008, the smallest change in our exposure-weighted loss). 19 worlds,
1000 draws each, errors in % of the floor.

- S27. **Negative b and off-balance are properties of the optimum, not of the fit.** The floor has a
    negative bⱼ in every world with ρ > 0 (min b −0.02 to −0.09), and is off-balance by more than
    1% in 54–80% of draws when σⱼ differ (5–57% with equal σ and ρ > 0). The blend is balanced, for
    all data, exactly for weights vⱼ ∝ bⱼ/(1 − zⱼ) (since Σ vⱼ(μ̂ⱼ − μ̂ⱼᵇ) = Σ vⱼ(1 − zⱼ)(μ̂ⱼ − μ̂));
    in BS that is vⱼ ∝ wⱼ*, with a diagonal K it is the precision wⱼ*/σⱼ² (checked to 10⁻⁶), and
    with ρ > 0 some vⱼ are negative, so no positive volume measure is balanced. Exposure balance
    is the right target only for BS.
- S28. **Forcing exposure balance is not cheap.** Best of the three (shift ≈ scale < BS-style): with σⱼ
    spread, +6 to +15 points of the floor at ρ = 0.3 and +14 to +32 at ρ = 0.6 (corrBS 112 → 126 at
    J = 8, T = 10; 116 → 148 at J = 20), i.e. up to about 30% more error, eating half or more of
    corrBS's gain over BS. Balancing the floor itself costs as much (100 → 122–152 at ρ = 0.6).
    Why: the exposure-weighted mean carries the common year shock; GLS removes it with the hedge
    weights, balance puts it back into every rate. At ρ = 0, equal σ, it costs 0–1 point. The
    BS-style collective is the worst and unstable when Σ wⱼ*(1 − zⱼ) is small (vc 109 → 208 with
    volume spread 2). So no balance switch in the app.
- S29. **z > 1 is harmless.** The floor never has z > 1 in these worlds, but its largest z is 0.94–0.99
    at ρ > 0 (the biggest region, partly hedged by the others); ẑ lands above 1 by estimation noise.
    Capping ẑ at 1 (thesis eq. (34)) changes the error by less than 0.5 point in every world.

App: corrBS moves these three flags from warnings to notes ("expected under correlation", or
"with region-specific σⱼ" when ρ̂ = 0 but β² > 0); τ̂² ≤ 0 stays a warning. Lean candidate (Core,
one line from `blend`): Σ vⱼ(μ̂ⱼ − μ̂ⱼᵇ) = 0 for all μ̂ iff vⱼ(1 − zⱼ) ∝ bⱼ; with diagonal K the
balanced weights are 1/(Kⱼⱼ − τ²). `bs_balance` is the BS case.
