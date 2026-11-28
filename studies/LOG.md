The log of all numbered simulation studies (S1–S82, index below); scripts and outputs are in
`runs/`. It began as the damping study (formerly `damping-theta.md`). Its first part was
absorbed into paper §7 and §8 on 2026-11-16.

# Damping θ and the common-covariance fit: a numerical study

2026-11-14. Script: `studies/runs/damping-theta.js` (run `node studies/runs/damping-theta.js 1000 tau`;
output in `runs/damping-theta.out.txt`). It uses the app engine's world (motor by region, skewed draws,
σ = 6, 500 vehicle-years per region and year, volume spread 1) and its fits, with the same
1000 draws for every column (common random numbers). Entries: exposure-weighted MSE of the rates
relative to the floor (100 = best blend with known parameters).

The study findings are numbered S1, S2, … (cited as "finding S19" in `studies/` and `app/`), so
they do not clash with the numbered findings of `FINDINGS.md`. Each carries a label for how far it
can be trusted if the simulated world changes:

- *[exact]*: follows from a formula in the second moments or a proved theorem; no simulation,
  holds for any noise law with those moments (the numbers still depend on the worlds chosen).
- *[theory]*: the direction or mechanism follows from a known result (cited in the finding);
  the size is numerical.
- *[numerical]*: observed in the simulated worlds only, within Monte Carlo error (1000–2000
  draws). It may change with the world model, the noise law or the fits.
- *[hypothesis]*: a proposed explanation, not checked separately.

A finding with two labels has parts of both kinds; the text says which part is which. Statements
about the floor (true `K` and `τ²`, fixed weights) are linear rules, so they can always be computed
exactly (`runs/exact-balance.js`) and should be, rather than simulated.

## Index (S1–S67)

One row per observation: number, script (output in the matching `.out.txt`), headline. Later chats
continue the numbering here; the full text and its trust label are below.

| S | Script | Headline |
|---|---|---|
| S1 | `runs/damping-theta.js` | The best fixed θ grows with the correlation and with the data |
| S2 | `runs/damping-theta.js` | θ = 1 (no damping) is risky |
| S3 | `runs/damping-theta.js` | A shrinkage rule from data is near the best fixed θ |
| S4 | `runs/damping-theta.js` | The common-covariance fit (G1 as stated) breaks down when volumes differ |
| S5 | `runs/damping-theta.js` | A common *correlation* works best overall |
| S6 | `runs/damping-theta.js` | At ρ = 0, BS is still slightly better |
| S7 | `runs/damping-dist.js` | The best fixed θ depends on the distribution |
| S8 | `runs/damping-dist.js` | The θ̂ rule tracks the best θ under every law |
| S9 | `runs/damping-dist.js` | The fit can beat the floor under heavy tails |
| S10 | `runs/damping-dist.js` | Per-region variances are fragile with short histories |
| S11 | `runs/damping-vhat.js` | It is worse than the normal-theory rule |
| S12 | `runs/damping-vhat.js` | The fault is the target, not V̂ |
| S13 | `runs/damping-vhat.js` | Why: Σ̂ from the same years as the means, so GLS cancels the shock (hypothesis H4) |
| S14 | `runs/damping-vhat.js` | Cross-validation (leave one year out) is no help |
| S15 | `runs/damping-vhat.js` | A common correlation needs no damping |
| S16 | `runs/damping-vhat.js` | Correlated BS |
| S17 | `runs/damping-vhat.js` | Credibility for the variances fixes that |
| S18 | `runs/msep.js` | Plugging the estimates into the known-parameter MSE understates the error |
| S19 | `runs/msep.js` | The jackknife MSEP is right on average within about ±15% |
| S20 | `runs/msep.js` | The estimation part g₃ is 6–50% of the MSEP |
| S21 | `runs/msep-terms.js` | The cross term C follows the excess kurtosis, not the skewness |
| S22 | `runs/msep-terms.js` | The jackknife g₃ is good with T = 10 (0.87–1.15 of the true E[d²]) and too large with T = 5 (up to 2.7×) |
| S23 | `runs/msep-terms.js` | The jackknife MSEP has no C at all |
| S24 | `runs/sure.js` | SURE-chosen τ² (Xie–Kou–Brown style) is worse than the moment fit everywhere |
| S25 | `runs/sure.js` | SURE as an error estimate for the moment fit is right on average within −30% / +15% |
| S26 | `runs/sure.js` | Neither predicts the error of one particular data set |
| S27 | `runs/vc-balance.js` | Negative b and off-balance are properties of the optimum, not of the fit |
| S28 | `runs/vc-balance.js` | Forcing exposure balance is not cheap |
| S29 | `runs/vc-balance.js` | z > 1 is harmless |
| S30 | `runs/blup-pairs.js` | BLUP on corrBS's `K̂` never loses to corrBS |
| S31 | `runs/blup-pairs.js` | The blend form is expensive with country structure |
| S32 | `runs/blup-pairs.js` | BLUP on the full `K̂` is high-variance |
| S33 | `runs/taper.js` | The taper does not beat damping for the blend |
| S34 | `runs/taper.js` | Not the rule's fault: the shape does not help even at its best fixed ρ |
| S35 | `runs/taper.js` | corrBS stays best |
| S36 | `runs/taper-blup.js` | With many ordered regions the taper pays, through the BLUP |
| S37 | `runs/taper-blup.js` | With few regions or one common ρ it does not |
| S38 | `runs/damping-cumulant.js` | The formula is right and the kurtosis term is large |
| S39 | `runs/damping-cumulant.js` | The covariance-form θ̂ damps more than S3, and that hurts at high ρ |
| S40 | `runs/damping-cumulant.js` | Why S3 works: its V is the correlation's, not the covariance's |
| S41 | `runs/damping-corr-exact.js` | Normal theory reproduces S3, and the true cumulants hardly move it |
| S42 | `runs/damping-corr-exact.js` | With infinite kurtosis the exact rule fails |
| S43 | `runs/ewma-decay.js` | EWMA loses because it sees only its own cohort |
| S44 | `runs/ewma-decay.js` | A size-dependent λ comes out of the model for free |
| S45 | `runs/ewma-decay.js` | Fitted, the plug-in BLUP stays best |
| S46 | `runs/taper-signal.js` | The signal is safe |
| S47 | `runs/taper-signal.js` | …but timid where the taper matters |
| S48 | `runs/taper-signal.js` | The regime matters as much as the method |
| S49 | `runs/taper-signal.js` | Leave-one-year-out is bolder but noisier, and not better overall |
| S50 | `runs/regime-check.js` | corrBS's lead holds in every regime |
| S51 | `runs/regime-check.js` | The thesis's own shape keeps the gaps large |
| S52 | `runs/regime-check.js` | The BLUP on corrBS's `K̂` beats corrBS wherever ρ ≥ 0.6, in every regime |
| S53 | `runs/price-formula.js` | The oracle part decides the sign |
| S54 | `runs/price-formula.js` | Estimating one correlation is free; estimating J variances is not |
| S55 | `runs/price-formula.js` | Why gaps shrink at high z |
| S56 | `runs/price-laws.js` | The laws hold for z ≥ 0.6, and reverse below |
| S57 | `runs/gain-price.js` | The verdict picks the better variances |
| S58 | `runs/gain-price.js` | The bound decides better than the exact form |
| S59 | `runs/obp-mean.js` | With known parameters the OBP mean pays only under a trend, and fails with a σⱼ spread |
| S60 | `runs/obp-mean.js` | Fitted, the OBP mean is a wash |
| S61 | `runs/obp-mean.js` | Never cut the sorted estimates by SURE |
| S62 | `runs/obp-mean.js` | A trend is a fixed effect |
| S63 | `runs/rho-channel.js` | Balance to the cross-fitted level, not to exposure |
| S64 | `runs/held-out-theta.js` | Choosing θ on a held-out year costs more than it can gain; take θ = 1 |
| S65 | `runs/vector-lambda.js` | With known `Λ` every correlation pays; fitted, the diagonal wins almost everywhere |
| S66 | `runs/vector-lambda-damp.js` | Weight the moment `Λ̂` by exposure and damp its off-diagonals |
| S67 | `runs/vector-lambda-shocks.js` | Model the shocks: corrected `Λ̂` and the joint BLUP |
| S68 | `runs/pretest-merge.js` | Merging when the gap looks small loses to both rules (exact, normal) |
| S69 | `runs/group-fit.js` | Fit `φτ²` by one GLS pass on the pairs; groups or not matters more |
| S70 | `runs/crossed-small.js` | Small crossed tables: REML on the cell means is never much worse than the default and often far better |
| S71 | `runs/crossed-fit.js` | REML holds on larger crossed tables (up to 6×4): the app's crossed default |
| S72 | `runs/recommended-fit.js` | Balanced, no fit wins: the BLUP gains with equal σⱼ and high ρ, loses with a wide σⱼ spread; g/p adds nothing |
| S82 | `runs/balance-volumes.js` | Volumes that vary by year: the cross-fitted level (any volumes now) removes the under-pricing (−166 → +25 bp); `auto` keeps it where that costs error (σⱼ spread) |
| S81 | `runs/rho-level.js` | ρ̂ is biased up (+0.06 to +0.13) by σ̃'s low level (0.63–0.97 of σ̂'s, every draw); ρ̂ from own σ̂ or rescaled σ̃: +0.4, +0.3 points, no default change |
| S80 | `runs/vcw-corr.js` | The corrected Wⱼ (unbiased, Finding 47) fixes Var σ̂ⱼ² and β̂² but worsens corrBS's rates: +4 mean, up to +44 points (T = 3, σⱼ spread 2) |
| S79 | `runs/volume-noise.js` | Volumes that vary by year: the fits and their ranking stand; the balance rule had silently always balanced (no cross-fitted level), up to +110 points; now prices the exposure-weighted level |
| S78 | `runs/psd-projection.js` | K̂ on the nearest PSD Σ̂⁺: the error moves ≤ 0.5 points; Σ̂ is PSD whenever volumes share one shape over the years, and fails at T = 3 with J > T otherwise; the gain is that K̂ ≻ 0 is a theorem in every draw |
| S77 | `runs/group-choice.js` | Groups or none on held-out years: regret 0.9 / max 4.0 though its picks barely follow φ; the stakes are small (−10 to +7 points) |
| S76 | `runs/balance-rule.js` | Balance iff the plug-in cost on K̂ is negative: regret 0.5 / max 6.9 (never 0.4 / 12.2, always 22.2 / 205.6, held-out 10.3 / 99.2) |
| S75 | `runs/balance-cost.js` | Cost of balancing = E(T − μ̄)² − E(r̄ − μ̄)², exact per draw; cross-fitted level 1.2–2.2× corrBS's own error with σⱼ spread 2 |
| S74 | `runs/blup-verdict.js` | The bootstrapped gain-against-price verdict for the BLUP adds nothing; S72's BLUP loss is the balance switch (corrBS itself +22 mean, up to +206 points balanced) |
| S73 | `runs/blup-price.js` | The BLUP's weight price over the blend on corrBS's `K̂`: +32 to +38 points with a σⱼ spread at app volume, ≤ +4 with equal σⱼ; no sign in general |

## Observations

- S1. *[numerical]* **The best fixed θ grows with the correlation and with the data.** It is 0 at ρ = 0 and close
   to 1 at ρ = 0.9 or with T = 20 years. The curve is flat near its minimum: θ = 0.95 is within a
   few points of the best, *except* with a short history (T = 5) or a small τ (τ = 0.03 at ρ = 0:
   182 against 156 at θ = 0).
- S2. *[numerical]* **θ = 1 (no damping) is risky.** With T = 5 years and 8 regions, `K̂` is not positive definite
   in up to 23% of draws. With a small τ, θ = 1 costs +60–100 points.
- S3. *[numerical]* **A shrinkage rule from data is near the best fixed θ.**
   `θ̂ = ρ̄² / (ρ̄² + (1 − ρ̄²)²/(T − 1))`, with ρ̄ the average estimated correlation over the pairs:
   signal ρ̄² against the sampling variance of a correlation from T years. It lands within 0–2
   points of the best fixed θ in 23 of 24 worlds (worst: +7, at τ = 0.03, ρ = 0.6). It needs no
   tuning and goes to 0 by itself when there is no correlation.
- S4. *[numerical]* **The common-covariance fit (G1 as stated) breaks down when volumes differ.** At θ = 0.95 it
   is 116–193 180 % of the floor. True covariances scale like `1/√(wᵢ* wⱼ*)`, so one common `c`
   exceeds the noise variance `vⱼ` of the large regions. Then `τ̂² + vⱼ − c` in
   `zⱼ = τ̂²/(τ̂² + vⱼ − c)` is near zero: |z| > 3 in 18% of draws at ρ = 0.6 (max |z| ≈ 1600).
   Equal covariances is the wrong one-parameter model unless the volumes are equal.
- S5. *[numerical]* **A common *correlation* works best overall.** `Σ̂ᵢⱼ = ρ̄ √(Σ̂ᵢᵢ Σ̂ⱼⱼ)`, damped by θ̂: best or
   tied best in almost every world, often better than the best fixed θ of the full `K̂` (fewer
   parameters to estimate). Its Σ̂ is positive semidefinite for ρ̄ ≥ 0, so `dampedK_posDef`
   applies.
- S6. *[numerical]* **At ρ = 0, BS is still slightly better** (111 against 114 for the full fit). That is the
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

## Does it depend on the noise distribution? (`runs/damping-dist.js`, output `runs/damping-dist.out.txt`)

Same study, J = 8, T ∈ {5, 10}, noise laws with mean 0, variance 1 and excess kurtosis
κ = −2 (two-point), 0 (normal), 3 (gamma k = 2), 6 (exponential), 24 (gamma k = 0.25).

- S7. *[numerical]* **The best fixed θ depends on the distribution**, not only on two moments. At T = 5, ρ = 0.3
   it is 0 for normal or two-point noise and 0.75 for κ = 24. So no theorem with only first and
   second moments can give the optimal θ: fourth moments must enter, as given numbers.
- S8. *[numerical]* **The θ̂ rule tracks the best θ under every law** (within 0–3 points in all 40 cases), although
   its variance term `(1 − ρ̄²)²/(T − 1)` is the normal-theory one. It adapts per draw, and the
   error curve is flat near its minimum.
- S9. *[numerical]* **The fit can beat the floor under heavy tails** (93–99 at κ ≥ 6, ρ ≥ 0.6). The floor is the
   best blend with *fixed* weights `z, b`; the fitted weights depend on the data, so the fit is a
   non-linear estimator and is not bound by it. The app should call the floor "the best fixed
   blend", not "the best possible".
- S10. *[numerical]* **Per-region variances are fragile with short histories.** Two-point noise, T = 5, ρ = 0: the
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

## A distribution-free θ̂ from the data (`runs/damping-vhat.js`, `runs/damping-oracle.js`)

Rule: `θ̂ = 1 − ΣV̂ᵢⱼ / Σŝᵢⱼ²` (Ledoit–Wolf form), with `V̂ᵢⱼ = T·s²(p)/Dᵢⱼ²` from the yearly
products `pₜ` (independent years, no normal-theory formula); raw and correlation scale agree.

- S11. *[numerical]* **It is worse than the normal-theory rule**, by up to 10 points, at high ρ and with heavy
    tails: it damps too much (θ̂ ≈ 0.5 where the best θ is 0.95–1).
- S12. *[numerical]* **The fault is the target, not V̂.** The oracle optimum of the stand-in loss
    `E Σ (θŝᵢⱼ − sᵢⱼ)²`, from the true variances: normal, ρ = 0.9: 0.80 (V̂ rule: 0.81, so V̂ is
    accurate there); κ = 24, ρ = 0.9: 0.29 (V̂ rule: 0.52; V̂ underestimates heavy tails from 10
    years). But the best θ *for the rates* is 0.99 there. Heavy tails make Σ̂ a worse estimate of
    the population K, yet the rates want *less* damping.
- S13. *[hypothesis]* **Why (hypothesis H4):** Σ̂ is computed from the same years as the region means. A hard
    winter in this data set inflates Σ̂ in the same draw, and GLS then cancels that very shock.
    So Σ̂ is useful as a measurement of *this* history's common noise, not only as an estimate of
    K. Damping towards the population K throws that away. The same effect lets the fit beat the
    fixed-weight floor (finding S9).

**Consequence for G2.** The shrinkage lemma (θ* = S/(S + V)) is true and distribution-free but
optimises the wrong loss: it is not the θ the rates need. Use damping for safety (`K̂ ≻ 0`) with θ
near 1 once a correlation is clearly present, and θ → 0 only when ρ̄ ≈ 0. The normal-theory rule
does exactly that, which is why it works; its variance formula is not the reason.

## Towards a fit with no tuning (2026-11-14, owner: "the fit is determined by its own data only")

Scripts: `runs/damping-cv.js`, `runs/common-rho.js`, `runs/common-rho-mom.js`, `runs/common-rho-misspec.js`,
`runs/variance-credibility.js` (outputs in the matching `.out.txt`).

- S14. *[numerical]* **Cross-validation (leave one year out) is no help.** Data-only and in theory unbiased for
    ranking methods, but noisy, and too cautious: a held-out year's common shock cannot be
    cancelled, so it undervalues correlation modelling (finding S13). At ρ = 0.9 it scores
    120–129 where the fixed rules score 110.
- S15. *[exact]* **A common correlation needs no damping.** With one ρ ∈ [0, 1) the estimated table is
    `Σ = Λ((1 − ρ)D + ρG)Λ` (G the Gram matrix `Sᵢⱼ/(wᵢ*wⱼ*)`, D its diagonal, Λ = diag σⱼ), positive
    definite by `K_posDef` for a PSD ρ-table. θ̂ and its normal-theory formula disappear.
- S16. *[theory + numerical]* **Correlated BS** (one σ², one ρ, `ρσ²` by one moment equation over all pairs, unbiased, no
    ratio): best or within 1 point of best in all 64 worlds where its assumptions hold, and equal
    to BS at ρ = 0. Robust to a country structure in ρ. **But it fails with region-specific σⱼ**
    (139–146 against 121 for the full fit): the pooled σ̂² is its weak point.
- S17. *[numerical]* **Credibility for the variances fixes that.** `σ̃ⱼ² = ζⱼσ̂ⱼ² + (1 − ζⱼ)σ̂²` with
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

## Can the fit estimate its own error? (`runs/msep.js`, output `runs/msep.out.txt`)

Jackknife MSEP of Jiang, Lahiri & Wan (2002, Ann. Stat. 30), deleting one year at a time
(independent years): `MSEPⱼ = g₁₂ⱼ(θ̂) − (T−1)/T Σₜ (g₁₂ⱼ(θ̂₋ₜ) − g₁₂ⱼ(θ̂)) + (T−1)/T Σₜ (rateⱼ(θ̂₋ₜ) − rateⱼ(θ̂))²`,
with g₁₂ the known-parameter MSE (`blendMSE`) and θ̂₋ₜ the parameters re-estimated without year t
(region means kept). Data only, distribution-free, no tuning. 27 worlds, 1000 draws each.

- S18. *[theory + numerical]* **Plugging the estimates into the known-parameter MSE understates the error** by 13–50%
    (ratio 0.50–0.87): it misses the price of estimation. The direction is theory under normal
    noise (Kackar–Harville: MSE = g₁ + g₂ + E[d²] with E[d²] ≥ 0); without normality the cross
    term C of S21 can be negative, so the direction is only numerical there.
- S19. *[numerical]* **The jackknife MSEP is right on average within about ±15%.** With equal σ and T = 10 it is
    0.97–1.02 for normal and gamma noise; heavy tails (κ = 24) overstate by 11–17% (cautious);
    region-specific σⱼ understate by 10–15% (0.85–0.90), probably because the variance credibility
    shrinks the noisiest regions' σ̃ⱼ² towards the pool, a bias the jackknife does not see. T = 5
    is rougher (0.87–1.21). Per region the ratio spreads more (0.66–1.98 in the worst world).
- S20. *[numerical]* The estimation part g₃ is 6–50% of the MSEP: large with few years or heavy tails, small with
    many regions. That is the "price of estimation" the app shows as fit − floor, now estimated
    from one data set.

Not measured yet: how noisy one data set's MSEP estimate is (its spread across draws), and
whether an interval `rate ± 2√MSEP` covers the true level as often as it should.

## The two extra terms, measured (`runs/msep-terms.js`, output `runs/msep-terms.out.txt`)

Fit error = e* + d with e* the floor's error and d = fitted rate − floor rate, so
MSE(fit) = MSE(floor) + C + g₃ with C = 2E[e*d], g₃ = E[d²]. In % of the floor MSE, 2000 draws:

- S21. *[theory + numerical]* **The cross term C follows the excess kurtosis, not the skewness.** ρ = 0.6, T = 10: two-point
    (κ = −2) +1.9, normal 0.0, gamma k = 2 (κ = 3) −2.5, gamma k = ¼ (κ = 24) −24.8, and its mirror
    image (skewness −4, same κ) −24.1. Reason: d = (ẑ − z)(μ̂ⱼ − μ̂) + …, a parameter error
    (quadratic in the noise) times a linear term, so e*·d is of fourth order in the noise. Under
    normality the fourth cumulants vanish and C = 0 (Kackar–Harville). Heavy tails make C negative:
    a large shock inflates the deviation μ̂ⱼ − μ̂ *and* the variance estimates, so ẑ shrinks harder
    exactly when the raw mean is most off. The fit corrects itself; that is why it can beat the
    floor.
- S22. *[theory + numerical]* **The jackknife g₃ is good with T = 10 (0.87–1.15 of the true E[d²]) and too large with T = 5
    (up to 2.7×)**, also at ρ = 0 (1.5–2.2×), where ρ̂ sits on its truncation at 0. Upward bias is
    expected (Efron–Stein inequality: the jackknife variance estimate is biased upwards for any
    statistic of independent units) and grows near the kinks (truncation of τ̂², ρ̂, β²).
- S23. *[theory + numerical]* **The jackknife MSEP has no C at all.** Jiang–Lahiri–Wan work with the best predictor, whose
    error is orthogonal to every function of the data; a linear credibility blend's error is only
    orthogonal to linear functions, so C ≠ 0 without normality. The earlier 11–17% overstatement
    under heavy tails is this missing negative C.

## SURE: choosing the shrinkage, and estimating the error (`runs/sure.js`, output `runs/sure.out.txt`)

SURE (Stein 1981) with Σ̂ from the moment fit plugged in for Σ; 27 worlds, 1000 draws each.

- S24. *[numerical]* **SURE-chosen τ² (Xie–Kou–Brown style) is worse than the moment fit everywhere**: +3 to +25
    points (e.g. 108 → 118 at J = 8, T = 10, normal, ρ = 0.6), also under normal noise. Its τ² is
    too large on average (1.1–4.7× the truth, moment fit 1.0–1.5×) and noisy. Minimising one noisy
    risk estimate over τ² overfits it; Xie–Kou–Brown's gains are for hundreds of units, we have
    8–20. The moment estimator of τ² is the better choice here.
- S25. *[numerical]* **SURE as an error estimate for the moment fit is right on average within −30% / +15%**
    (0.70–1.15), the jackknife within −15% / +28% (0.85–1.28). SURE is better under heavy tails
    (κ = 24: 0.81–1.15 against 1.12–1.28), the jackknife under normal and gamma(2) noise. SURE is
    only exact with Σ *known*; plugging in Σ̂ (from T − 1 degrees of freedom) makes it too small,
    most with T = 5 and with region-specific σⱼ (0.70).
- S26. *[numerical]* **Neither predicts the error of one particular data set**: the per-draw correlation of SURE
    with the actual loss is −0.13 to 0.28. The loss of one data set depends on where the unknown
    levels happen to lie; an MSEP estimate is about the average over such data sets. For the app:
    show the MSEP as "typical error", not as an interval that covers the truth in this data set.

**Verdict on the distribution layer (so far).** For choosing the fit it does not pay: the
moment fit wins. For the error estimate, SURE and the jackknife are comparable, with opposite
strengths. A normal-noise refinement that accounts for Σ̂ (its Wishart distribution, independent of
the means under normality) could remove SURE's downward bias; that is the one place where a
distribution clearly helps. Not tried: Hudson's identity for a gamma family (needs a model where the
variance follows the mean, unlike our additive noise).

## corrBS flags and the cost of balance (`runs/vc-balance.js`, output `runs/vc-balance.out.txt`)

corrBS shows negative b in ≈70%, off-balance > 1% in ≈45%, z > 1 in ≈40% of draws at ρ = 0.6,
σⱼ spread (app world, gamma noise). Are these the fit's fault? Compared with the floor (true K, τ²)
and with three ways to force exposure balance Σⱼ wⱼ*μ̂ⱼᵇ = Σⱼ wⱼ*μ̂ⱼ, z kept: BS-style collective
μ̂ = Σ wⱼ*(1 − zⱼ)μ̂ⱼ / Σ wⱼ*(1 − zⱼ); every rate scaled; every rate shifted by the same amount
(benchmarking, Wang–Fuller–Qu 2008, the smallest change in our exposure-weighted loss). 19 worlds,
1000 draws each, errors in % of the floor.

- S27. *[exact + numerical]* **Negative b and off-balance are properties of the optimum, not of the fit.** The floor has a
    negative bⱼ in every world with ρ > 0 (min b −0.003 to −0.09; exact, the floor's b is fixed by K),
    and is off-balance by more than 1% in 54–80% of draws when σⱼ differ (numerical: the share
    depends on the noise law) (5–57% with equal σ and ρ > 0). The blend is balanced, for
    all data, exactly for weights vⱼ ∝ bⱼ/(1 − zⱼ) (since Σ vⱼ(μ̂ⱼ − μ̂ⱼᵇ) = Σ vⱼ(1 − zⱼ)(μ̂ⱼ − μ̂));
    in BS that is vⱼ ∝ wⱼ*, with a diagonal K it is the precision wⱼ*/σⱼ² (checked to 10⁻⁶), and
    with ρ > 0 some vⱼ are negative, so no positive volume measure is balanced. Exposure balance
    is the right target only for BS.
- S28. *[exact + numerical]* **Forcing exposure balance is not cheap.** Best of the three (shift ≈ scale < BS-style): with σⱼ
    spread, +6 to +15 points of the floor at ρ = 0.3 and +14 to +32 at ρ = 0.6 (corrBS 112 → 126 at
    J = 8, T = 10; 116 → 148 at J = 20; numerical), i.e. up to about 30% more error, eating half or
    more of corrBS's gain over BS. Balancing the floor itself costs as much, and that part is exact
    (`runs/exact-balance.js`, no simulation): at ρ = 0.6 with σⱼ spread 100 → 121–141 by a shift and
    124–149 BS-style (the simulation gave 122–146 and 125–152); the best balanced blend (FINDINGS
    15) 147–196 over all worlds.
    Why: the exposure-weighted mean carries the common year shock; GLS removes it with the hedge
    weights, balance puts it back into every rate. At ρ = 0, equal σ, it costs 0–1 point. The
    BS-style collective is the worst and unstable when Σ wⱼ*(1 − zⱼ) is small (vc 109 → 208 with
    volume spread 2). So no balance switch in the app.
- S29. *[exact + numerical]* **z > 1 is harmless.** The floor never has z > 1 in these worlds (exact), but its largest z is 0.87–0.99
    at ρ > 0 (the biggest region, partly hedged by the others); ẑ lands above 1 by estimation noise.
    Capping ẑ at 1 (thesis eq. (34)) changes the error by less than 0.5 point in every world
    (numerical).

App: corrBS moves these three flags from warnings to notes ("expected under correlation", or
"with region-specific σⱼ" when ρ̂ = 0 but β² > 0); τ̂² ≤ 0 stays a warning. Lean candidate (Core,
one line from `blend`): Σ vⱼ(μ̂ⱼ − μ̂ⱼᵇ) = 0 for all μ̂ iff vⱼ(1 − zⱼ) ∝ bⱼ; with diagonal K the
balanced weights are 1/(Kⱼⱼ − τ²). `bs_balance` is the BS case.

## The plug-in BLUP under pair-specific correlation (`runs/blup-pairs.js`, output `runs/blup-pairs.out.txt`)

Finding 18 asks whether the best linear unbiased predictor survives estimating `K`. In the app's
own worlds (one common ρ) the BLUP on corrBS's `K̂` beat corrBS everywhere (PLAN 3c). Those worlds
favour it: corrBS's one-ρ̂ `K̂` is exactly right there. Here the noise has a factor structure
(countries with ρ 0.8 within and 0.2 or 0 between, heterogeneous loadings ρᵢⱼ = λᵢλⱼ, two factors
with some ρᵢⱼ < 0), so the one-ρ̂ `K̂` is misspecified. 18 worlds, 2000 draws each, MSE in % of the
blend floor. Two plug-in BLUPs: on corrBS's `K̂` (app fit "BLUP"), and on the thesis's full damped
`K̂` (every pair estimated).

- S30. *[numerical]* **BLUP on corrBS's `K̂` never loses to corrBS.** In all 18 worlds it is at most
    1 point worse (ties in the hard T = 5 worlds) and up to 23 points better (J = 20, common ρ:
    106 → 83; J = 20, 2 countries with σⱼ spread: 119 → 101). Under misspecification its gain
    is −1 to 18 points: it does not turn into a real loss. It costs nothing at ρ = 0 (PLAN 3c). So
    it is a safe upgrade of the blend on the same `K̂`.
- S31. *[exact]* **The blend form is expensive with country structure.** With true parameters the
    best blend is 6–18% above the BLUP in MSE with heterogeneous loadings or two factors, but 22–36% (J = 8) and
    61–73% (J = 20) with countries. The blend reaches the other regions only through one μ̂, so it
    cannot tell a same-country neighbour from a foreign one. This is the Finding 18 gap at its
    largest, and it grows with J.
- S32. *[numerical]* **BLUP on the full `K̂` is high-variance.** With strong structure and enough
    data it is the best fit (J = 20, countries: 78, 92, 84, below the blend floor). With T = 5 or
    unstructured loadings it is often the worst correlated fit (up to 141–144, against corrBS 116–126):
    J(J − 1)/2 noisy pairs. The gap of S31 calls for a `K̂` with few parameters that knows the
    groups (ρ within and between: the group-levels step of the PLAN, step 4), and the BLUP on it.

## Distance taper against damping (`runs/taper.js`, output `runs/taper.out.txt`, 2026-11-22)

App fit "corr taper": the thesis fit with every pair estimated, `K̂ = R ⊙ (Σ̂ + τ̂²I)` with
`Rᵢⱼ = ρ̂^|i−j|` over the region order (`posDef_distTaper_hadamard`). `ρ̂` minimises the plug-in
loss of S3 per distance, `Σ_d n_d [ρ^2d (r̄_d² + (1 − r̄_d²)²/(T−1)) − 2ρ^d r̄_d²]` (r̄_d the average
estimated correlation of the pairs at distance d); with every pair at distance 1 this is S3's θ̂.
New world switch "decays with distance": noise correlation `ρ^|i−j|` (an AR(1) along the region
order). 16 worlds, 1000 draws, MSE in % of the floor; damping by the app's grid rule (θ = 0.95
unless K̂ fails) and by S3's θ̂.

- S33. *[numerical]* **The taper does not beat damping for the blend.** With the plug-in rule it is
    within 0–4 points of S3 damping in the ordered worlds (e.g. J = 8, T = 10, ρ = 0.6: 113 against
    112) and worse in a short history with a common ρ (T = 5, ρ = 0.6: 138 against 128: it keeps too
    much of the noisy far pairs). Against the app's grid rule (θ = 0.95) it gains 1–9 points at
    ρ ≤ 0.6 in the ordered worlds and at ρ = 0 (the grid rule hardly damps), and loses 1–7 at
    ρ = 0.9 and up to 8 with a common ρ = 0.6.
- S34. *[numerical]* **Not the rule's fault: the shape does not help even at its best fixed ρ.**
    Sweeping fixed ρ and θ (600 draws, ordered worlds): the best taper and the best damping are within
    1 point (J = 8, T = 10, ρ = 0.6: 110 / 110; J = 20: 110 / 110; T = 5: 123 / 123), and at ρ = 0.9
    damping is better (111 at θ = 0.7–0.8 against 113 at ρ = 0.9). *[hypothesis]* The blend uses K̂ only
    through the GLS weights b and z, and reaches the other regions only through μ̂ (S31), so getting
    the far pairs right buys little; a predictor that uses each pair (the BLUP) might, and is the
    place to try the taper next.
- S35. *[numerical]* **corrBS stays best**: one common ρ̂, misspecified in the ordered worlds, still
    scores 108–122 in the ordered worlds against 109–138 for the taper, the gap largest with T = 5. Few parameters win
    over a better-shaped table of J(J − 1)/2 noisy pairs (as S5, S16).

For the app: keep "corr taper" as an option for ordered cohorts (its K̂ ≻ 0 is proved, ρ̂ comes
from the data), not as a recommendation. "corr" now damps by S3's θ̂ instead of the grid rule
(θ = 0.95 unless K̂ fails; kept as `thetaRule: 'grid'`): up to 12 points better at ρ ≤ 0.6, 0–3
worse at ρ = 0.9 (table above, columns "damp grid" and "damp S3").

## The taper on the BLUP (`runs/taper-blup.js`, output `runs/taper-blup.out.txt`, 2026-11-22)

S34's hypothesis tested: plug-in BLUP on the full `K̂` (every pair), damped by S3's θ̂ or tapered
by ρ̂^|i−j|, against the BLUP on corrBS's one-ρ̂ `K̂` (app "BLUP"). 11 worlds, 1000 draws, MSE in %
of the blend floor; "best fixed ρ" sweeps the taper as an oracle.

- S36. *[numerical]* **With many ordered regions the taper pays, through the BLUP.** J = 20, T = 10:
    BLUP taper 104 / 103 at ρ = 0.6 / 0.9, against BLUP on corrBS's `K̂` 113 / 131 and BLUP damped
    109 / 107; J = 20, T = 20, ρ = 0.9: 92 against 114 and 94, below the blend floor. BLUP on one
    common ρ̂ fails here because the far pairs are nearly uncorrelated (0.9^19 ≈ 0.14) while the
    near ones are strong: one ρ̂ fits neither. The fitted ρ̂ is within 1–4 points of the best fixed
    ρ in these worlds.
- S37. *[numerical]* **With few regions or one common ρ it does not.** J = 8 ordered, T = 10: about
    even (BLUP taper 112 / 110 / 123 against 114 / 106 / 125 at ρ = 0.6 / 0.9 / σⱼ spread); T = 5:
    worse (131 / 136 against 128 / 118): 28 noisy pairs are too many for 5 years. Common ρ (taper misspecified): 104–133 against 83–103.
    So the shape matters only once the BLUP can use each pair (S31) and there are enough pairs at
    each distance to average over (n_d grows with J).

App: fit "BLUP taper" (`fitBLUPTaper`), for ordered regions with many of them; not a default.

## The exact `V` in the damping rule (`runs/damping-cumulant.js`, output `runs/damping-cumulant.out.txt`, 2026-11-23)

G2 asked to plug the proved variance of `Σ̂ᵢⱼ` into `θ* = Σs²/(Σs² + ΣV)` (`Damping.bestTheta`) in
covariance form. The app's `Σ̂ᵢⱼ` (eq. (39)) carries `√(wᵢₜwⱼₜ)`, so its exact variance is
`Cumulants.variance_sum_mul_lin` with the residual coefficients `√wᵢₜ(δₜₛ − aᵢₛ)`; with unit
weights it is `variance_crossResid` (Node test). Engine: `sigmaHatVar`, `covTheta`,
`fitCorr(data, { thetaRule: 'cov', kappa })`. Plug-ins as S3 (one common r̄, σ̂ⱼ); `κ` the excess
kurtosis of the common year shock (`kₛᵢⱼᵢⱼ = κ covᵢⱼ²/(wᵢₛwⱼₛ)`), 0 or the world's true 3 (testing
only). Oracle: `θ*` from the true table. 32 worlds, 1000 draws, MSE in % of the floor.

- S38. *[exact + numerical]* **The formula is right and the kurtosis term is large.** Monte Carlo
    `Var Σ̂ᵢⱼ` (40 000 draws) agrees with `sigmaHatVar` within 1–3% with the true κ; normal theory
    (κ = 0) is 30–45% too small in the gamma worlds. Exact: for `i ≠ j` only the *shared* shock's
    kurtosis enters (region parts independent across regions), so the Lomax claims (α = 3, infinite
    kurtosis of the region part) leave `Var Σ̂ᵢⱼ` unchanged (MC: same within 2%).
- S39. *[numerical]* **The covariance-form θ̂ damps more than S3, and that hurts at high ρ.** Mean θ̂ at
    ρ = 0.9, T = 10: S3 0.99, cov κ = 0 0.79, cov κ true 0.64, oracle θ* 0.65. Rates: S3 106–110,
    cov κ = 0 107–114, cov κ true 110–117 (T = 5: 122 / 127 / 132). At ρ ≤ 0.6 all within ±2 points
    (cov sometimes 1–2 better with σⱼ spread). κ true lands on the oracle θ* everywhere, so the
    plug-ins are fine: the *target* is what is wrong, as in S12. Gamma and Lomax worlds behave the same.
- S40. *[exact + hypothesis]* **Why S3 works: its V is the correlation's, not the covariance's.**
    Balanced, normal: `Var ŝᵢⱼ/(σᵢσⱼ)² = (1 + ρ²)/(T−1)` (`variance_sampleCov`), `Var r̂ᵢⱼ ≈ (1 − ρ²)²/(T−1)`.
    At ρ = 0.9 that is 1.81 against 0.036: dividing by σ̂ᵢσ̂ⱼ removes the noise the pair shares with
    the variances. *[hypothesis]* GLS uses `K̂` through ratios (`b`, `z` are scale-free in `K̂`), so the
    correlation-scale error is the one that matters, and the extra damping the covariance V asks for
    throws away the in-sample shock (S13).

**Consequence.** Keep S3 as the app's rule; `thetaRule: 'cov'` stays a studies option. An estimate
`κ̂₄` from the residuals is *not* worth planning for G2: the true κ already makes the rule worse.
The next candidate is the exact `Var r̂ᵢⱼ` (a ratio; delta method, needs `Var`/`Cov` of all three
entries, which `variance_sum_mul_lin` gives) with κ, to see whether κ moves S3's θ̂ the right way.

## S3 with the exact correlation variance (`runs/damping-corr-exact.js`, output `runs/damping-corr-exact.out.txt`, 2026-11-23)

S40's next step: keep S3's correlation scale, `θ̂ = r̄²/(r̄² + V̄)`, but take `V̄` as the delta-method
`Var r̂ᵢⱼ` from the exact covariances of `(Σ̂ᵢⱼ, Σ̂ᵢᵢ, Σ̂ⱼⱼ)` (`variance_sum_mul_lin` in covariance
form; engine `sigmaHatMoments`, `corrVar`, `corrTheta`, `thetaRule: 'corr'`), with the fourth
cumulants of the shock and of the region part 0 or the world's true ones (testing only).
Oracle: true r, σⱼ and cumulants. 36 worlds, 1000 draws, MSE in % of the floor.

- S41. *[exact + numerical]* **Normal theory reproduces S3, and the true cumulants hardly move it.**
    With κ = 0 the delta method gives exactly `(1 − r²)²/(T − 1)` in a balanced world (Node test) and
    the same θ̂ and MSE as S3 in every world. The true cumulants raise `Var r̂` by about 55% (gamma;
    Monte Carlo agrees within 1–3%, 20% high with exponential noise), but θ̂ drops only 0.01–0.05 and
    the MSE changes by 0–1 point (gamma, Lomax α = 5). The oracle is 0–2 points better than S3. S3 is
    already within 0–3 points of the best fixed θ, so there is little left to gain.
- S42. *[exact + numerical]* **With infinite kurtosis the exact rule fails.** Lomax α = 3: the region
    part has no fourth moment, so the delta-method `Var r̂` is ∞ and θ̂ = 0, costing up to 40 points
    (161 against 121 at T = 5, ρ = 0.9). But `r̂ ∈ [−1, 1]` has a finite variance: the delta method,
    not the correlation, breaks down. S3's normal-theory V is the robust choice.

**Consequence for G2 (closes the κ̂₄ question).** No `κ̂₄` for the damping rule: with finite
cumulants it buys ≤ 1 point, and under heavy tails, where it would differ most, the estimate
would be unstable (literature §10l) and the rule breaks. S3 stays; `'cov'` and `'corr'` are studies
options.

## Temporal decay: EWMA years against the BLUP (`runs/ewma-decay.js`, output `runs/ewma-decay.out.txt`, 2026-11-24)

PLAN "Temporal decay" (literature §10l, Morris 2026) in the monthly card world (`app/monthly.js`:
AR(1) factor with φ per month, shock C, process noise s²/w, cohort × calendar-month season as fixed
effects; J = 4, Y = 5). EWMA weights each cohort's own annual means by λ^age (sum 1, so unbiased
under the season). At a fixed λ it is a predictor from aggregated data, so its excess over the BLUP
is exact: `(Ac − d*)ᵀK(Ac − d*)` (`Blup.predMse_aggregate_eq_blup_add`; Node test). "Own years" is
the best predictor from the same annual means (no hyperparameter); EWMA is a one-parameter family
inside it. Engine: `targetMoments`, `predMse`, `ewmaYears`, `ownYearsBest`; rolling-origin fit `ewma`.

- S43. *[exact]* **EWMA loses because it sees only its own cohort.** With the true tables and the
    best λ*, EWMA costs 0–4% over the BLUP when the factor forgets within a year (φ = 0.6, φ¹² ≈ 0)
    and 6–31% at φ = 0.9–0.97, growing with volume. The best own-years weights recover only 1–6 points
    of that. The BLUP's own-cohort weights stay nearly flat over years (0.23–0.49 on the last year),
    while the best own-years weights put up to 0.93 there (and negative weights on older years). The
    BLUP gets its recency from the other cohorts: the factor is common, and their month-by-month
    contrasts (weights summing to 0 per calendar month) estimate it.
- S44. *[exact]* **A size-dependent λ comes out of the model for free.** λ* falls with the cohort's
    noise s²ⱼ/wⱼ relative to the factor variance γ: at φ = 0.97, λ* = 0.50–0.69 at w0 = 100,
    0.16–0.29 at 1000 and 0.06–0.08 at 10 000; at φ = 0.9 it goes from 0.68–0.79 to 0.48. Within a
    portfolio the cohort with the lower s²/w (bigger, or less noisy) gets the shorter memory. At
    φ = 0.6 λ* ≈ 0.92 for every size: no decay to fit when the factor forgets within the year. So
    Morris's λ by account size is the trade of noise (more years) against drift (recent years), set
    by s²/w, γ and φ; it needs no extra parameter.
- S45. *[numerical]* **Fitted, the plug-in BLUP stays best** (2000 draws, MSE in % of the oracle
    BLUP): BLUP 110–123, EWMA λ̂ 110–136, own years 110–131, last year 127–166; EWMA ties the BLUP
    only at φ = 0.6 and nearly at w0 = 100 (117 against 115). λ̂ keeps the order of λ* by size but is
    pulled towards 0.5–0.6 where λ* is small (φ = 0.97, w0 = 1000: 0.49–0.56 against 0.16–0.29, from
    the noisy φ̂), and there the last-year mean (131) does as well as own years and better than EWMA (135).

**Consequence for the app.** EWMA years is a rolling-origin fit for comparison ("EWMA of own years,
λ fitted"), not a recommendation: it never beats the plug-in BLUP, and its exact loss at a fixed λ is
the aggregation excess. Morris's λ by size is explained by the second-moment model; a likelihood fit
of λ would belong in the distribution layer and is not needed for this.

## A data-side signal for the BLUP taper (`runs/taper-signal.js`, output `runs/taper-signal.out.txt`, 2026-11-24)

S36–S37 left open how a practitioner, who cannot see the world, knows when to taper. `Engine.taperSignal`
judges both candidate correlation tables by S3's plug-in loss per pair: the taper (each r̂ᵢⱼ times
ρ̂^d) by S3's own loss, one common r̄ (as corrBS) by `Σ_d n_d [(r̄ − r̄_d)² − V_d/n_d]₊`. It prefers the
smaller loss, with no tuning constant. `fitBLUPAuto` is the BLUP on the preferred table. First study with
the conventions of `PLAN.md` §1 (factorial grid, paired SEs, two regimes): structure (ordered or
common) × ρ ∈ {0.3, 0.6, 0.9} × J ∈ {8, 20} × T ∈ {5, 10} × regime, 48 worlds, 600 draws.

- S46. *[numerical]* **The signal is safe.** With one common ρ it tapers in 0–2% of draws, so auto
    equals BLUP on corrBS's `K̂` (whose lead there is 5–38 points). Over all 48 worlds auto is never
    more than 4 points worse than BLUP on corrBS (J = 8, T = 5: 134 against 130, ±3).
- S47. *[numerical]* **…but timid where the taper matters.** In the ordered worlds with ρ = 0.9 it
    tapers in only 13–61% of draws. The taper gains 7–29 points there with J = 20, and auto keeps 0–70% of
    that (J = 20, T = 10, app: 114 against taper 103 and corrBS 132). Regret against the better of the
    two: mean 1.4, at most 13 (± 12) points; within 2 SE of 0 in 36 of 48 worlds. *[hypothesis]* The
    common table's loss ignores how strongly the pairs' errors are correlated (they share the T years),
    so it is too optimistic. A sharper signal would score the two BLUPs directly, e.g. by
    leaving out one year.
- S48. *[numerical]* **The regime matters as much as the method.** In the thesis regime (z ≈ 0.7–1.0)
    the gap between BLUP taper and BLUP on corrBS averages 4.5 points (max 12), against 13.7 (max 42)
    at the app default. One ranking flips: J = 8, T = 10, ordered ρ = 0.9 gives corrBS 107 against taper
    109 (app), and 101 against 97 (thesis). Studies run only at the app default overstate every gap
    between fits about threefold for a portfolio with high volumes and equal σⱼ (corrected by S51:
    with the thesis's spread in σⱼ the gaps stay large).

**Consequence.** Keep "BLUP taper" as an option, and use `fitBLUPAuto` in studies. It goes on the page
once the recipe can show a conditional step. Earlier studies in this file ran at the app default only,
so their gaps are upper ends for high-volume portfolios with similar noise (not for the thesis's own
shape, S51). S36's "taper pays with many ordered regions"
holds in both regimes (J = 20, ρ = 0.9: 103 against 132 in the app regime, 96 against 103 in the thesis regime).

- S49. *[numerical]* **Leave-one-year-out is bolder but noisier, and not better overall.** Choosing by
    `Engine.loyoLoss` (refit without year s, score against year s; the noise term is the same for both
    fits, so the difference is unbiased for the MSE difference, with no tuning) picks the taper in
    41–68% of draws in the ordered worlds. It keeps more of the taper's gain there, at times beating both
    fits by choosing per draw (J = 20, T = 5, ρ = 0.9, app: 123 against 130 and 143). But it also picks the
    taper in 26–45% of draws with one common ρ, costing up to 13.5 ± 3.9 points (J = 20, T = 5,
    ρ = 0.6). Mean regret 2.0 against the plug-in signal's 1.4; within 2 SE of 0 in 27 against 36 of 48
    worlds. One held-out year per refit is too noisy a score next to the MSE gap it must detect.
    Keep the plug-in signal (S46). LOYO costs T refits per fit, for no gain.

## The headline recommendations across regimes (`runs/regime-check.js`, output `runs/regime-check.out.txt`, 2026-11-24)

Purpose: decide. Are S3, S5, S6 and S16 artefacts of the app's default world? BS, corrBS, the full `K̂`
damped by S3's θ̂ ("corr"), the BLUP on corrBS's `K̂` and own means, on the same draws. Grid: ρ ∈ {0, 0.3,
0.6, 0.9} × σⱼ spread × T ∈ {5, 10} × three regimes (`lib.regimes`: app; thesis = volume 4400; thesisShape
= volume 4400, volumes nearly equal, σⱼ² × 1/16–16 as the thesis's lognormal(16, √2)), J = 8, 40 worlds,
600 draws, paired differences against corrBS.

- S50. *[numerical]* **corrBS's lead holds in every regime.** BS is worse than corrBS in 36 of 40 worlds
    (by 4–86 points of the floor). It is better only at ρ = 0 with equal σⱼ: 10 ± 5 (T = 5) and 2 ± 1
    (T = 10) in the app regime, 2 ± 2 and 0 ± 1 in the thesis regime (S6, smaller). The full `K̂` damped
    by S3 is never better than corrBS beyond 2 SE, and worse in 28 of 40 worlds (S5, S16 hold).
- S51. *[numerical]* **The thesis's own shape keeps the gaps large.** Volume alone shrinks them (thesis
    regime: BS − corrBS 0–36 against 2–69 in the app regime), but the thesis's spread in σⱼ² brings z
    down to 0.27 for the noisiest cohorts, and the gaps return (BS − corrBS 43–86). S48's "about
    threefold smaller" holds for volume only. With the thesis's own σⱼ spread, the gaps are as large as
    at the app default, so S36–S47 are not overstated for that portfolio.
- S52. *[numerical]* **The BLUP on corrBS's `K̂` beats corrBS wherever ρ ≥ 0.6, in every regime**
    (by 3–37 points; e.g. ρ = 0.9, T = 5: 80 against 118 in the app regime, 110 against 138 with the
    thesis's shape). Elsewhere it is within 2 SE, or at most 1.1 ± 0.5 worse (ρ = 0). Better in 16,
    worse in 7 (all by ≤ 1.1), tied in 17 of 40 worlds. *For the owner:* on these numbers the BLUP is the
    better default for the rates. corrBS keeps the blend form `zμ̂ⱼ + (1 − z)μ̂` and its recipe. The
    balance and skew-bias trade-offs (Finding 35, "BLUP pooled") are not scored here.

## Predicting the gaps from moments: oracle part + price (`runs/price-formula.js`, output `runs/price-formula.out.txt`, 2026-11-24)

Purpose: conjecture and decide. Owner (2026-11-24): findings should depend less on simulation. Every
comparison splits as MSE(fitted F) = **oracle part** (exact: the MSE of F's weights at its limiting
parameters, `Core.linMse`; against the BLUP `CoreMoments.mse_blend_eq_blup_add`) + **price** (from
estimating the parameters; `PlugIn.lean`'s exact identity, whose cross term vanishes under normal noise,
`PlugInNormal`). With pooled variances, BS, corrBS and the BLUP on corrBS's `K̂` depend on the data only
through three quadratic statistics s = (P, Qn, B): the pooled within-region variance, the cross-region
residual products, and the spread of the means. Under normal data their means and covariances are
trace formulas (B is exactly uncorrelated with P and Qn). Two price formulas, both from moments only:
*first order* (Prasad–Rao g₃: Σ Cov(sₖ, sₗ) Gₖᵀ K Gₗ, Gₖ = ∂dⱼ/∂sₖ), and *integrated* (the exact
clipped weights averaged over s by a 3-D Gauss–Hermite rule, P and B on matched gamma scales via
Wilson–Hilferty; it ignores the dependence of s on μ̂, as g₃ does). Check: 2000 simulated draws of the
engine's fits (the re-implementation equals the engine on a draw). 16 normal worlds (ρ × T × regime,
J = 8, equal σⱼ).

- S53. *[exact + numerical]* **The oracle part decides the sign.** Wherever the simulated gap is
    outside 2 SE, the exact oracle gap has the same sign: 26 of 32 gaps, and none of the others has a
    clear sign. At ρ = 0 it is exactly 0 for both pairs, and the simulated gaps are ≤ 0.4 points. Its
    size is within a factor 0.7–1.5 in the app regime, but 2–4 times too small for BS − corrBS in the
    thesis regime, where BS's price matters. **The first-order price** closes that: BS − corrBS
    predicted at 0.7–0.85 of the simulated gap in the thesis regime and 1.1–1.2 at app T = 10, and the
    BLUP gap within 1–5 points. It overshoots 2–3-fold at app T = 5 (BS, ρ = 0.9: 208 against 63),
    where τ̂² is poorly determined and clipped. **The integrated price** fixes app T = 5 (72 against 63)
    and predicts the BLUP gap within 4 points everywhere. But it overstates BS's gap in the thesis
    regime (38 against 19): BS's τ̂² rises when the means spread, which helps it, and ignoring that
    dependence overstates the price.
- S54. *[numerical]* **Estimating one correlation is free; estimating J variances is not.** At ρ = 0,
    pooled corrBS − BS is 0.1 ± 0.3 (gamma, T = 5) and −0.2 ± 0.2 (T = 10), 3000 draws. S6's cost of
    corrBS at ρ = 0 is its variance-credibility step (σ̃ⱼ² per region when the σⱼ are equal): 8.0 ± 1.6
    (gamma) and 4.3 ± 0.9 (normal) at T = 5, 1.2 ± 0.6 and 0.4 ± 0.3 at T = 10. The skew link of
    Finding 35 doubles it. This is the price count of g₃: one ρ̂ pooled over J(J − 1)/2 pairs has a tiny
    variance, while each σ̂ⱼ² has only T − 1 degrees of freedom (relative variance ≈ 2/(T − 1)).
- S55. *[derived]* **Why gaps shrink at high z.** With z = τ²/(τ² + v), ∂z/∂log v = −z(1 − z)
    exactly. So the first-order price of a variance parameter, relative to the floor, is about
    z(1 − z)·CV² of its estimate. It is largest at z = ½ and vanishes at z → 0 or 1, consistent with
    S48 and S51. *Refined by S56:* this holds for each region's own variance. The price of τ̂² goes
    like (1 − z)/z instead, because τ̂²'s own CV grows as z falls.

**Consequence.** The *direction* of a comparison is a formula: the exact oracle gap. Its size needs the
price, and first order is reliable once each parameter has about 10 years of data or z is high. For
the app this gives a decision rule with no tuning: the oracle gap from the fitted `K̂`, against the
first-order price from the plug-in variances of the statistics (`PLAN.md` Pending, "gain against price").
Lean (2026-11-24, `Credibility/FitStatistics.lean`): the exact Var/Cov of P, Qn, B for any moment
tables (`Cumulants.covariance_stat`, `variance_stat`); cov(B, P) = cov(B, Qn) is the fourth-cumulant
term alone when the means are region-constant, the third cumulants vanish and the region means are
uncorrelated with the residuals, so 0 under normal cells (`covariance_statB_eq`, `_eq_zero`). The
last condition holds for ρ = 0 or proportional volumes (all worlds here), not in general (Finding 37).
The MSE gap between two blends with the same z is an exact quadratic in z
(`Core.linMse_lineWeight_sub`). The first-order price itself stays an approximation, checked here.

## Two price laws in closed form (`runs/price-laws.js`, output `runs/price-laws.out.txt`, 2026-11-24)

Purpose: conjecture. In a balanced world (equal volumes, ρ = 0, equal σ, normal noise) the BS factor
is exactly ẑ = 1 − v̂/S², with v̂ = σ̂²/(wT) and S² the sample variance of the J region means. To first
order, with z = τ²/(τ² + v) and the floor ≈ (1 − z)τ²:
  (a) **fitting BS** (τ̂², σ̂²): relative price ≈ (2/J)·T/(T − 1)·(1 − z)/z
      (Var ẑ ≈ (1 − z)²[2/(J − 1) + 2/(J(T − 1))], times (1 − 1/J)(τ² + v));
  (b) **own variances** σ̂ⱼ² instead of one σ̂²: extra relative price ≈ z(1 − z)·2/(T − 1)
      (∂zⱼ/∂log vⱼ = −z(1 − z), Var log σ̂ⱼ² ≈ 2/(T − 1)).
J ∈ {8, 20} × T ∈ {5, 10} × five volumes (z from 0.12 to 0.97), 4000 draws.

- S56. *[derived + numerical]* **The laws hold for z ≥ 0.6, and reverse below.** (a) is within 30% of the
    simulated price for z ≥ 0.58 (J = 8: 10.0 against 11.6 at z = 0.74, T = 10), within 10% at J = 20.
    It equals the exact first-order price (`runs/price-formula.js`) there. Below z ≈ 0.4 it overstates 2–6×
    (225 against 37 at z = 0.12): clipping τ̂² at 0 caps the loss at the pooled tariff's. (b) overstates
    1.1–2× for z ≥ 0.58 (4.3 against 2.0 at z = 0.74, J = 8, T = 10), so it leans toward pooling.
    It understates up to 5× below z ≈ 0.3 (5.4 against 25.8 at z = 0.12, J = 20, T = 5): with few years
    1/σ̂ⱼ² is strongly biased, which first order misses. Reading: the cost of fitting BS falls like
    (1 − z)/(Jz), more regions or more credibility both help. The cost of own variances is at most
    about z(1 − z)·2/(T − 1), i.e. ≤ 1/(2(T − 1)): 12% at T = 5, 6% at T = 10.
    *Lean (2026-11-24, `FitStatistics.lean`):* the balanced identity ẑ = 1 − v̂/S² is exact
    (`Cumulants.bsZ_bsTau2Hat_of_balanced`, with `statB_of_balanced` for S²). Law (a)'s first-order
    price, relative to (1 − z)τ², is exactly (2/J)(1 + (J − 1)/(J(T − 1)))(1 − z)/z, at most the
    study's (2/J)·T/(T − 1)·(1 − z)/z (`bsPrice_of_balanced`, `bsPrice_le_of_balanced`; inputs: the
    normal-theory CVs and cov(v̂, S²) = 0, `covariance_statB_eq_zero`). The exact blend floor in this
    world is (1 − z)τ² + (1 − z)²s/J, so "relative to the floor" is a further first-order step.
    The CV inputs are now derived from the cells (`variance_statP_of_balanced`: Var P = 2σ⁴/(J(T − 1));
    `variance_statB_of_balanced`: Var B = 2(wT)²s²(J − 1)), so `bsPrice_of_balanced_cells` takes only
    τ², σ², w, J, T (no third and fourth cumulants).
    *With fourth cumulants* (`bsPrice_of_balanced_cumulants`): levels κL, noise κN/w² per cell, no
    skew. Var P gains κN/(JT), Var B a term in κL + κN/(w²T³), and cov(B, P) = κN(J − 1)/(JT). The
    price relative to (1 − z)τ² becomes (1 − 1/J)(1 − z)/z·[2/(J(T − 1)) + 2/(J − 1) + κL/(Js²) +
    γN z²/(JT)], γN = κN/σ⁴.
    *Law (b) in Lean (2026-11-24, `ownPrice_sub_pooled_of_balanced`):* with τ² fixed, ∂z/∂log v =
    −z(1 − z), the curvature (1 − 1/J)s and the pooled v̂'s own CV² 2/(J(T − 1)), the extra price is
    exactly (1 − 1/J)²·z(1 − z)·2/(T − 1). The law as stated drops both factors 1 − 1/J: 1.31× at
    J = 8, 1.11× at J = 20, part of its overstatement at z ≥ 0.6 (J = 8: 4.3 → 3.3 against 2.0
    simulated). Against law (a) (`ownPrice_eq_sq_mul_bsPrice`): the same noise in v̂ costs an own
    factor at fixed τ² z² times what it costs BS's ẑ = 1 − v̂/S² at fixed S². So the share of noise kurtosis in the price grows like z² (at low z the positive
    covariance cancels most of it), and the levels' kurtosis adds κL/(Js²) however many years.

## Choosing the variances by gain against price (`runs/gain-price.js`, output `runs/gain-price.out.txt`, 2026-11-24)

Purpose: decide. `Engine.gainPrice(data)`: on corrBS's fitted `K̂`, the exact oracle gain of region
variances σ̃ⱼ² over one pooled σ̄² (same table, σ̄² in every region), against S56 (b)'s price. Verdict
'region' when the gain is larger. No tuning. It also returns the gains of corrBS over BS and of the BLUP
over the blend. Those carry no verdict: estimating ρ is nearly free (S54), and the BLUP uses the same `K̂`.
"auto" = corrBS pooled unless the verdict is 'region'. 24 worlds (σⱼ spread × ρ × T × regime, J = 8,
gamma noise), 600 draws, paired.

- S57. *[numerical]* **The verdict picks the better variances.** Regret against the better of corrBS and
    corrBS pooled: mean −0.5, at most 3.3 ± 4.9 points, within 2 SE of 0 in 16 of 24 worlds. It beats
    both fixed choices on average because it chooses per data set: with σⱼ spread 1, T = 5, it is 136
    against 144 and 145. With equal σⱼ it picks region variances in 1–23% of draws, with a spread in
    67–100%. Against today's default corrBS: 1.2 points better on average, from 7.5 better to 3.3 worse
    (within noise). Compared with S54: it recovers most of corrBS's cost at ρ = 0 (116 against 123 and
    113), without giving up region variances where they pay.

**Consequence.** The first decision rule built from formulas instead of a simulated threshold. Candidate
for the app's recommended fit: corrBS with the variance step chosen by `gainPrice`. It needs its own
recipe, a conditional step like "BLUP auto". `PLAN.md` Pending, "Gain against price".

## The exact law (b) in the verdict (`studies/runs/gain-price.js … exact`, 2026-11-24)

Purpose: decide. Law (b) is now proved in the balanced world: the exact first-order price is
(1 − 1/J)²·z(1 − z)·2/(T − 1) (`Cumulants.ownPrice_sub_pooled_of_balanced`), and the study's form is its
upper bound (`ownPrice_sub_pooled_le_of_balanced`), 1.31× at J = 8. Same 24 worlds and draws as S57, the
verdict priced with the exact form.

- S58. *[numerical]* **The bound decides better than the exact form.** Mean regret unchanged (−0.5), but
    the worst world gets worse: equal σⱼ, ρ = 0, T = 5 (z 0.13–0.76) goes from 2.8 ± 2.3 to 4.9 ± 2.6
    (region picked in 34% of draws against 23%); within 2 SE of 0 in 15 of 24 against 16. It helps only
    in the thesis regime with a σⱼ spread at T = 5 (1.2 → 0.5, 1.0 → 0.5). Against corrBS: −1.1 against
    −1.2. Why: below z ≈ 0.3 law (b) understates the true price up to 5× (S56, the bias of 1/σ̂ⱼ², not
    first order), and the bound's slack partly offsets it.

**Consequence.** `Engine.gainPrice` keeps the bound (now proved as a bound), `opts.lawB = 'exact'` for
comparison; the app labels (b) "proved in the balanced world". A price that tracks the low-z bias would be
the next improvement, not the exact first-order form.

## The OBP collective mean and grouping when levels trend with volume (`runs/obp-mean.js`, output `runs/obp-mean.out.txt`, 2026-11-25)

Purpose: decide (PLAN Pending, "OBP collective mean"). Does the observed best predictor's collective mean
(weights `∝ uⱼ(1 − zⱼ)²`, `Core.obpMean`, literature §10p) or grouping with a common `τ²` (Finding 41) beat
Bühlmann–Straub (`b ∝ z`) when the levels trend with volume? Grid: the three regimes × J ∈ {8, 20} ×
T ∈ {5, 10} × trend β ∈ {0, 0.5, 1, 2} (levels `1 + τηⱼ − βτsⱼ`, `sⱼ` the standardized volume rank), ρ = 0,
gamma levels and noise, 600 paired draws. Loss given the levels, exposure-weighted. Part A exact with the
true `σⱼ²`, `τ²`; Part B fitted, as paired differences to BS in % of its loss.

- S59. *[exact]* **With known parameters the OBP mean pays only under a trend, and fails with a σⱼ spread.**
    In the app and thesis regimes it is 0.4–1.8% worse than `b ∝ z` at β = 0, even at β ≈ 0.5, and 2–15%
    better at β = 1–2, where it is within 0.4 points of the best fixed `b`. In thesisShape (nearly equal
    volumes, `σⱼ²` × 1/16–16) it is 14–58% *worse* at β = 0 and still 5–15% worse at β = 1. Why: the
    theorem (`condRisk_obpMean_le`) holds the collective mean fixed; as an estimate its variance
    `Σ bⱼ²Dⱼ` is largest where `(1 − zⱼ)²` puts the weight, on the noisiest cohorts.
- S60. *[numerical]* **Fitted, the OBP mean is a wash.** BS's `ẑ` with the OBP mean: +0.3 to +1.4 at
    β = 0, −0.5 to −5.2 at β = 2 (app, J = 20 best). In thesisShape ±0.2: BS pools `σ̂²`, so the `ẑⱼ`
    are nearly equal and so are the weights (S59's failure needs per-cohort variances). The full OBP
    (`τ²` too by the observed criterion, Jiang–Nguyen–Rao) is worse than that: up to +5.3 (app, J = 8),
    like the SURE-chosen `τ²` in `runs/sure.js` (B). Neither is balanced (`res:balance` needs `b ∝ u(1 − z)`).
- S61. *[numerical]* **Never cut the sorted estimates by SURE.** Two groups, own means, one common `τ̂²`,
    the cut of the sorted estimates with the smallest SURE: +2.5 to +74 against BS in every world, worst
    at low credibility. SURE picks it over one group almost always (G-auto ≈ G2-est). Sorting puts the noise
    into the groups: the within-group spread and so `τ̂²` shrink, and SURE for fixed groups does not see
    that the groups were chosen on the same data. The same cut of the *true* level order (a reference)
    is −13 to +13; the cut of the volume order +27 to −3, small gains (≤ 3.3) only at β ≥ 1.
- S62. *[numerical]* **A trend is a fixed effect.** The BLUP with design columns `[1, log volume]`
    (`res:blup`, moment `τ̂²` from the weighted-LS residuals as eq. (13)): −3 to −35 at β ≥ 1, −4 to +5
    at β = 0.5, and +0.5 to +12 at β = 0 (the price of the column: largest at J = 8, T = 5, low z).
    It beats every other fit wherever a trend of τ or more is present.

**Consequence.** No OBP mean in the app, and no handbook recommendation for it: a "watch out" says why
(`res:bs`). Grouping cohorts by cuts of their sorted estimates must not choose the cut by SURE; the app's
planned grouping step (PLAN "Grouping cohorts") needs a selection-aware criterion (cross-fitting or the
gain against price with the selection in the price) before it is built. A trend in volume, if data show one, goes
in as a design column (an offset in log volume), chosen by gain against price (S57), with its price
visible at β = 0. Parked by the owner (2026-11-25): a size trend is niche, tariffs usually carry size.

### Finding 35's ρ̂ channel: cross-fitting (2026-11-26, `studies/runs/rho-channel.js`, `notes/blup-credibility-form.md` §3)
- S63. *[numerical]* **Balance to the cross-fitted level, not to exposure.** 4000 draws, ten worlds; MSE in %
    of the oracle / portfolio bias in % of the tariff (± 2 SE ≤ 0.15). Leave-one-year-out cross-fitting
    (`cfPool`: the weights for year `s`'s cells from corrBS's pooled parameters fitted without year `s`)
    removes the bias in every world (|bias| ≤ 0.09, all within 2 SE of 0; pooled BLUP −0.47 at `ρ = 0.6`,
    −0.84 at `ρ = 0.6, T = 5`), but costs 4–17 MSE points as a predictor. Keeping the BLUP's regional
    rates and moving only its exposure-weighted level to `cfPool`'s (`shiftBlup`, one common shift) is
    unbiased too and cheap: 112 / 119 / 128 against the exposure-balanced BLUP's 111 / 118 / 127 without
    correlation (default, `T = 4` shape 1, σⱼ spread 1), and 112 / 127 / 112 / 143 against 131 / 147 / 158
    / 145 under `ρ = 0.6` (plain, `T = 5`, `J = 20`, spread 1). So it matches exposure balance where that is
    free and beats it by 2–46 points where it is not, with no threshold on `ρ̂`. Attribution: the pooled
    BLUP with `ρ` fixed at the truth keeps about half the bias (−0.27 against −0.47; `T = 5`: −0.44 against
    −0.84), so `ρ̂` is half the channel, the rest through the pooled `σ̂²`/`τ̂²` ratio. P1 checked: equal
    volumes and `σⱼ`, the pooled BLUP has bias 0 exactly (symmetry), the region-specific one −0.18
    (its `σ̂ⱼ²` channel). The region-specific cross-fit alone over-corrects (+0.10 default, +0.33 `T = 4`),
    likely the level channel (`τ̂²` from the other years' means, skewed levels); not checked.

**Consequence (decided 2026-11-27: in the app, `balanceFit` with `target: 'crossFit'`, test "Balance to the cross-fitted level").** The balance switch could balance to the cross-fitted portfolio
level instead of the exposures. General target before building it (CLAUDE.md, general results first): with
year weights `πₛ` common to the regions (proportional volumes, as in the app) and weights `d̂⁽ˢ⁾` summing to 1
and independent of year `s`'s noise, `Σₛ πₛ d̂⁽ˢ⁾ᵀXₛ` has bias `Σₛ πₛ Σᵢ cov(d̂ᵢ⁽ˢ⁾, μᵢ)` (levels only;
0 for fixed levels), any distribution: a corollary of `Core.Estimates.integral_randomLin_sub`. With
region-specific year weights `aᵢₛ` the cross-fit is not exactly translation equivariant (`Σₛ Σᵢ aᵢₛd̂ᵢ⁽ˢ⁾ ≠ 1`).
*Proved 2026-11-26:* `Core.Estimates.integral_crossFit_sub` (`Credibility/RandomWeights.lean`), with independence of
`d̂ᵢ⁽ˢ⁾` and year `s`'s noise `Xᵢₛ - μᵢ` (uncorrelated would do); handbook `res:randomWeights` line, blueprint
`thm:Core_crossFit_bias`. The region-specific case stays a remark (no exact identity).

### The held-out θ̂ of the blend–BLUP path (2026-11-27, `studies/runs/held-out-theta.js`, output `runs/held-out-theta.out.txt`)
- S64. *[numerical + exact]* **Choosing θ on a held-out year costs more than it can gain; take θ = 1.**
    2000 draws, eleven worlds; rates from corrBS (blend, θ = 0) towards the BLUP on its `K̂` (θ = 1), MSE in %
    of the oracle (± 2 SE ≈ 3–14, paired differences far tighter). `hoT`: fit on years `1..T−1`, regress year
    `T`'s blend error on `Δ` across regions (weights `wⱼₜ`), clip to `[0, 1]`, apply to the fits on all
    `T` years; `loyo`: the same regression pooled over every held-out year. Without correlation `ρ̂` is often
    0 (`Δ = 0` in 60% of draws) and every θ ties (112–115). With a common year shock (`ρ = 0.3, 0.6`; `T = 5`;
    `J = 20`; thesis volumes; normal noise) the plug-in BLUP is at or within 0.7 points of the best fixed θ
    (`θ*` = 0.71–1.03), and `hoT` / `loyo` cost 1–15 points against it (`ρ = 0.6`: 114.8 / 114.4 against
    109.4; `J = 20`: 125.2 / 123.5 against 110.5); `θ = ½` is no worse than `θ̂` (112.1, 117.8). `θ̂` before
    clipping has quartiles about −4 / 1.2 / 6 and lands on 0 or 1 in ~90% of draws. Pooling the years
    narrows it (0.2 / 1.5 / 3.8) but does not help the loss. Bias: an iid year shock gives
    `E[Δε] = 0` (year `T` is independent of the fit on `1..T−1`), measured `|E[Δε]/EΔ²| ≤ 0.18`, within noise;
    a persistent shock (AR(1), `φ = 0.5, 0.8`) gives −0.80 and −2.25, pulling `θ̂` down while the best θ is
    2.0–4.2 (the plug-in BLUP on corrBS's `K̂`, which treats years as independent, is too timid there).
    **Why (exact, checked):** given the fit, `θ̂ = θ̃ + ΔᵀWε/ΔᵀWΔ` with `θ̃` the draw's own best θ, so its loss
    exceeds the draw's best by `price = ΔᵀWΣWΔ/ΔᵀWΔ` in mean (`Σ` year `T`'s noise table): a Rayleigh quotient
    of `W^½ΣW^½ = (σᵢσⱼρᵢⱼ)`, so at least `σ²(1 − ρ)` for equal `σⱼ`, *whatever the fits*. The study confirms
    the identity (realized 33 / 116 / 222 against predicted 36 / 104 / 241 at default / `ρ = 0.6` / `J = 20`,
    within 2 SE) and the bound (price/λmin ≥ 1 in every draw). The draw's possible gain over `θ = 1`,
    `S(1 − θ̃)²`, is 4–20 against a price of 36–241: 7–14 times smaller. The common shock also inflates the
    price beyond `λmin` (104 against 14.4): `Δ` lies largely along the shock's direction (the two fits differ
    mostly in their level). Same mechanism as the forecast combination puzzle (literature §10u).

**Consequence.** No θ̂ step in the app: the fitted BLUP stands (θ = 1), the path stays a display of `S`.
General targets (Lean, **lean** chat, `PlugInMix.lean`, moment layer):
1. *Done 2026-11-27* (`integral_heldOutTheta`, `integral_sq_heldOutTheta_sub`, `integral_wLoss_heldOutTheta`,
   `integral_wLoss_heldOutTheta_lt_iff`, `le_heldOutPrice`; handbook `res:heldOut_price`). *The price of one held-out year.* For fixed `e₀, Δ ∈ ℝᴶ`, `W = diag(w) ≻ 0`, `ΔᵀWΔ > 0` and a random
   `ε` with mean 0 and covariance table `Σ` (any distribution), `θ̂ = −ΔᵀW(e₀ − ε)/ΔᵀWΔ` has
   `E θ̂ = θ̃ = −ΔᵀWe₀/ΔᵀWΔ`, `Var θ̂ = ΔᵀWΣWΔ/(ΔᵀWΔ)²`, and
   `E[(e₀ + θ̂Δ)ᵀW(e₀ + θ̂Δ)] = (e₀ + θ̃Δ)ᵀW(e₀ + θ̃Δ) + ΔᵀWΣWΔ/ΔᵀWΔ`; hence `θ̂` beats a fixed `θ₀` in mean
   iff `ΔᵀWΔ(θ₀ − θ̃)² > ΔᵀWΣWΔ/ΔᵀWΔ`, and the price is ≥ `λmin(W^½ΣW^½)`. (Conditioning on the fit is
   the fixed `e₀, Δ`; `integral_quad_of_cov` gives the quadratic.) Clipping: `mixLoss_clip_le` per draw.
2. *Done 2026-11-27* (`FactorMoments.lean`: `Factor.HeldOut` with levels `μⱼ`, `ε = X_{(j,h)} − μⱼ`;
   `cov_X_noise`, `integral_wsum_noise`, `_eq_zero`, `_ar1`; handbook `res:heldOut_bias`). *The persistent-shock bias.* In `FactorMoments` with fixed weights: `E[Δε] = Σⱼ wⱼ Σᵢ (d − ŵ)ⱼᵢ
   cov(μ̂ᵢ, εⱼₜ)`, `cov(μ̂ᵢ, εⱼₜ) = λᵢλⱼ Σₛ aᵢₛ Γₛₜ` (0 iff the held-out month/year is uncorrelated with the
   fitted ones under `Γ`; AR(1): `Σₛ aᵢₛ φ^(T−s)`). A one-line corollary once the cross-covariance of
   `Cells` with a held-out cell is stated.

### Vector levels: which `Λ` to fit (2026-11-27, `studies/runs/vector-lambda.js`, owner's question)
Frequency × severity with a level and a slope per cohort (`P = 4`, Hachemeister centred as Bühlmann–Gisler),
independent cohorts, the matrix BLUP with three fitted structures for `Λ̂` (unbiased moment estimate,
projected PSD within the structure): diagonal, block per component, full. Grid: level–slope correlation
`rab ∈ {0, 0.7}`, frequency–severity correlation `rFY ∈ {0, −0.6}`, `J ∈ {10, 30}`, `T ∈ {5, 8}`, frequency
level credibility `z_F ∈ {0.5, 0.85}` (severity noise 4×); 2000 draws, MSE of next year's level in % above the
full oracle, ± 2 SE ≤ 6.
- S65. *[numerical]* **With known `Λ` every correlation pays; fitted, the diagonal wins almost everywhere.**
    Oracle: ignoring `rFY = −0.6` costs 1.5–3.3 (F) and 4–15 (Y), ignoring `rab = 0.7` 3–15 (F) and 1–9 (Y).
    Fitted: the diagonal `Λ̂` costs 9–69, the block one 9–92, the full one 13–115. Full is never better than
    block (full − block ≥ 0.3). Block beats diagonal only for the well-measured component with a level–slope
    correlation (`rab = 0.7`, F at `z_F = 0.85`: 1–15 points in 7 of those 8 worlds; Y only at `J = 30`, `T = 8`,
    by 3.5–4.6); everywhere else the off-diagonals' estimation noise exceeds their gain: block loses up to
    31 points to diagonal, full up to 59. The frequency–severity correlation never paid as fitted.
    Conditions: independent cohorts, normal levels, the unweighted moment estimator; a better `Λ̂` (weighted,
    REML, GEE) shrinks every price, and may move the edge. *Rerun 2026-11-27 with the app's generator: the
    first run's LCG had serially correlated draws (Λ̂'s slope variance biased about −100% at `T = 5`); the
    conclusions held, the numbers above are the rerun's.*

**Consequence (hypothesis).** The app's "cohort trend lines" step fits diagonal `Λ̂` by default (four
scalar credibilities after centring) and treats off-diagonal entries as an optional extra chosen by gain
against price (S57), not by their size. Candidates to test next: damp the off-diagonals of `Λ̂` with a
data-chosen θ (`OffDiagonal.lean` keeps PSD, `Damping.lean`'s `θ*`), a better `Λ̂`, and year shocks
(correlated cohorts, where `K` is not block diagonal). General target: with known moments the order
full ≤ block ≤ diagonal is a restricted-predictor statement (`blupW_optimal`); fitted, the plug-in
MSE `mse(d*) + E B² + 2E[AB]` (`PlugIn.lean`) is the place to state when an extra entry pays.

### Vector levels, part 2: damped, weighted, year shocks (2026-11-27, `studies/runs/vector-lambda-damp.js`)
S65's world and fits plus year shocks `ρ ∈ {0, 0.3}` (cell noises of one year correlate across cohorts; the
fits still assume independent cohorts, the oracle is the joint BLUP with the true `K`), the exposure-weighted
unbiased moment `Λ̂` (`…W`), and damping: the diagonal fit plus `θ̂ ×` the off-diagonals, projected PSD, with
`θ̂ = max(0, 1 − ΣV̂/Σr̂²)` (the plug-in `θ*` of `Damping.lean` on the correlation scale; `θ̂ = 0` is the
diagonal fit). 64 worlds, 1500 draws; differences against the (unweighted) diagonal fit, paired ± 2 SE.
- S66. *[numerical]* **Weight the moment `Λ̂` by exposure and damp its off-diagonals.** The weighted
    diagonal fit beats the unweighted one in all 128 world × component cells (1–14 points). The weighted
    damped fit (`dampW`) is never significantly worse than the diagonal fit (worst +0.3, within 2 SE) and
    better in 62 of 64 worlds for F and 50 for Y, by up to 26 points (the largest gains with a strong
    level–slope correlation, high credibility and `J = 30`, where `θ̄` reaches 0.64). Against the weighted
    diagonal fit it costs up to 5 (F) and 8 (Y) points (unpaired difference) in the worlds with no
    correlation, and wins up to 21. Undamped block and full fits stay erratic (−28 to +54). With year shocks
    the off-diagonals pay more (block's mean −2.5 for F at `ρ = 0.3` against +6.5 at 0); S67 checks why.
    `θ̂` averages 0.07–0.64, and 0.07–0.15 where `Λ` is diagonal. *Rerun with the app's generator (see S65).*

**Consequence (hypothesis).** Default for the app's "cohort trend lines" step: exposure-weighted moment
`Λ̂`, off-diagonals damped by `θ̂` (from data, no hyperparameter), PSD by projection. It replaces S65's
"diagonal by default": it keeps the diagonal fit's safety and takes most of the gain where correlations
exist. Open: the fits that model the year shocks (a `ρ̂`, joint `K̂`), and a general statement for the
plug-in `θ̂` (when it is within ε of the better of `θ = 0` and `θ = θ*`).

### Vector levels, part 3: modelling the year shocks (2026-11-27, `studies/runs/vector-lambda-shocks.js`)
S66's world with `ρ ∈ {0, 0.3, 0.6}`, `rFY = −0.6`, the other axes as S65 (48 worlds, 1000 draws). The fit
estimates the shocks: `ρ̂ᶜ` from same-year residual products of different cohorts (a "same column" pair
estimator, as `CrossedEstimation.lean`), scaled by `tr(I − H) = T − 2`, exact here since all cohorts' exposures
have one shape; `N̂` the noise covariance of the stacked line estimates from `ŝ²`, `ρ̂`; and the moment `Λ̂`
corrected for any noise covariance `N` between cohorts: `E Σⱼ ωⱼ eⱼeⱼᵀ = (1 − Σω²)Λ + Σⱼ ωⱼNⱼⱼ − ΣᵢΣₖ ωᵢωₖNᵢₖ`
(`eⱼ = β̂ⱼ − Σωᵢβ̂ᵢ`, `Σω = 1`). Fits against S66's `dampW` (shocks ignored): `dampWc` (corrected `Λ̂`, still an
independent-cohort predictor), `jointDiag` / `jointDamp` (corrected `Λ̂` diagonal / damped, joint BLUP with
`K̂ = I ⊗ Λ̂ + N̂`); oracle: the joint BLUP with the truth.
- S67. *[numerical]* **Model the shocks: corrected `Λ̂` and the joint BLUP.** `ρ̂` is 0.25–0.29 at `ρ = 0.3` and
    0.51–0.56 at 0.6 (10–15% low). Ignoring the shocks biases `Λ̂` down: the level variance by −23 to −31% at
    `ρ = 0.3` and −46 to −54% at 0.6 when `z_F = 0.5` (−2 to −10% at `z_F = 0.85`), the slope variance by −33% to
    −1150% (common shocks tilt every line alike, so the cohorts' slopes look alike); corrected, within a few
    percent (slope within its noise). This is S66's guess, but for the variances: the cross terms vanish
    for level–slope entries by centring, so the shocks do not enter the off-diagonals here; why
    off-diagonals paid more under shocks stays open. The correction alone gains little (`dampWc`: −0.1 to +0.4
    at `ρ = 0`, to −14 at 0.6). The joint damped BLUP is the fit: at `ρ = 0` it costs −0.2 to +1.9 (F) and +3.2
    (Y), at `ρ = 0.3` it gains up to 27 (F) and 38 (Y) (means −11, −13; worst +1.5 / +6.9, within 2 SE but for
    one Y world), at `ρ = 0.6` 20–112 (F) and 22–147 (Y), cutting `dampW`'s excess over the oracle there (means 67, 93) by three quarters.
    The damped and diagonal joint fits are within a few points of each other.

**Consequence (hypothesis).** The "cohort trend lines" step fits the joint damped BLUP: `ρ̂` per component from
same-year residual pairs, `Λ̂` exposure-weighted and corrected for `N̂`, off-diagonals damped by `θ̂`, PSD by
projection. Without shocks it costs at most 2–3 points against S66's default; with shocks it is the only fit
near the oracle. General target (**lean** chat): the corrected moment identity above, for any `N` and weights
`ω` (a matrix version of §2.8's expectation under correlated noise, `Expectation.lean` / `UnequalEstimation`),
so the corrected `Λ̂` is unbiased for any noise covariance between cohorts. *Proved 2026-11-27:*
`CoreVector.integral_spread` (`CoreVectorMoments.lean`, blueprint `thm:CV_spread`, handbook `res:vecSpread`),
for any weights with `Σω = 1` and estimates with a common mean; the corrected `Λ̂` is unbiased for any
`N̂` with `E N̂ = N` (`CoreVector.integral_correctedLambda`). *Proved 2026-11-27 (`LineResiduals.lean`):* `E Σₜ ẽᵢₜẽⱼₜ = σ²cᵢⱼ(T − 2p + tr(PᵢPⱼ))` for
weighted lines of `p` coefficients, so `ŝ²` (divisor `T − p`) is unbiased for any volumes, and S67's
`ρ̂ŝ²` (divisor `T − 2`) exactly when the hat matrices agree, as in S67's world (`wⱼₜ = wⱼ·1.05ᵗ`,
`hat_eq_of_shape`). There `N̂` is linear in `ŝ²` and `ρ̂ŝ²`, so `E N̂ = N` and the corrected `Λ̂` is
unbiased: composed with random lines in `LineResidualsMoments.lean`
(`integral_correctedLambda_lines`; pooled SUR version `integral_correctedLambda_pooled`). With unequal shapes S67's `ρ̂` is biased towards 0; the
divisor `T − 2p + tr(PᵢPⱼ)` (Zellner's SUR estimator, `unbiasedMean_cross`) fixes it.

### The winner's curse of merging a pair (2026-11-27, `studies/runs/pretest-merge.js`, Finding 43)
- S68. *[exact, numerical integration]* **Merging when the gap looks small loses to both rules.** Two cohorts,
    fixed gap `δ`, normal noise; each rule's excess is `a²R` with `R` the risk of estimating `δ` by `0`
    (merge) or `(1 − k)D` (separate), `D ~ N(δ, V)` (`PreTest.integral_sq_pretest`). Pre-test "merge iff
    `D² < c`", in units of `a²V`, at the tie of the fixed rules (`θ₀² = (1 − k)/(1 + k)`): positive for every
    `k ∈ {0, ¼, ½, ¾}` and every `t = √(c/V)` tried (largest `+0.26`, `k = 0`, `t = 2`; `+0.20` at `c = 2V`).
    It loses to both on 0–14% of the gaps `θ ∈ [0, 6]`, and its regret to the better rule reaches
    `0.65` (`k = 0`, `c = 2V`) and grows like `t²` for large thresholds. The plug-in threshold of
    `notes/merging-cohorts.md` §4 with the thesis blend: `+0.0004` (`τ²/V = 0.1`) to `+0.14` (`τ²/V = 5`) at
    the tie. **Consequence.** No threshold is safe (Finding 43, proved:
    `PreTest.lt_gapRisk_of_tie`); decide merges and cuts on held-out years (`CrossFit.integral_heldOutScore`).

### Fitting the group variance (2026-11-27, `studies/runs/group-fit.js`, PLAN G4)
- S69. *[numerical]* **Fit `φτ²` by one GLS pass on the pairs; groups or not matters more.** J = 12 cohorts in
    2 (8 + 4) or 4 (5 + 3 + 2 + 2) groups, T = 3 or 6, φ = 0.3 or 0.7, exponential or normal noise, volumes
    lognormal, 2000 draws per world. Fits of `θ = φτ²` and `λ = (1 − φ)τ²` from the pair estimators: volume
    weights (`phiTauPooled_unbiasedG`), Bühlmann–Gisler bottom-up, and Gauss–Markov on the pair table
    (`phiTauPool_blue_optimal`) with `V` from the volume-weighted pass under normal formulas (GLS1), once more
    (GLS2), or from the true parameters (GLS*). SD of `θ̂` in units of `θ`, mean over the 16 worlds: vol 4.18,
    BG 3.43, GLS1 3.43, GLS2 3.42, GLS* 3.34 (range 1.8–9): with 2–4 groups `φτ²` is barely identified.
    `λ̂`: GLS1 10–15% below vol and BG. Bias: BG's `θ̂` −0.1 to −0.85 (it clips `λ̂` in its noise term);
    the others within ±0.4 (Monte Carlo SE ≈ 0.1–0.2); GLS1's `λ̂` up to +0.8 in the hardest world
    (2 groups, T = 3, φ = 0.7, skewed). Blend MSE in % of the BLUP with true parameters: vol 125.6, BG 125.7,
    GLS1 124.6, GLS2 125.3, GLS* 123.1 (means; all within 1–4 points in each world). Ignoring the groups
    (one `τ̂²`): +4 to +15 at φ = 0.7, but −1 to −6 at φ = 0.3, T = 3. **Consequence.** The app's group fit is
    GLS1 (one pass, no hand-set choices); a second pass does not pay. The weights move the blend little; the
    decision that matters is whether to fit groups at all, which belongs to a held-out score
    (`CrossFit.integral_heldOutScore_sub`), not to the in-sample fit.

### Small crossed tables (2026-11-27, `studies/runs/crossed-small.js`; paper, open directions)
- S70. *[numerical]* **Small crossed tables: REML on the cell means is never much worse than the default and
    often far better.** Tables 2×2, 3×2, 3×3, 4×3, T = 10, effect mixes both / row only / weak / none
    (α, β, γ as `crossed-fit.js`, plus all zero), ρ ∈ {0, 0.5}, volume spread 0 or 1, regimes app and
    thesis (128 worlds, 1000 draws, common random numbers). Fits: the default (inverse-variance pools, clip),
    **REML** on the cell means `μ̂ ~ N(μ1, Σ̂ + L(θ))` with the default's noise table, `θ ≥ 0` by projected
    Fisher scoring, and **shrink** (each clipped variance times the plug-in `θ̂²/(θ̂² + V̂)`, `V̂` the
    normal-theory variance of the raw estimate on `K̂`). The raw default estimates are negative in 20–65% of
    draws even with real effects (2×2: α̂² 0.3–0.5, γ̂² 0.3–0.65). Observed cells' error in % of the floor,
    paired against the default: REML worse in 17 of 128 worlds (by at most +5.3 points, 2×2 weak, ρ = 0.5,
    spread 1, thesis regime), better in 69 (down to −60 in 2×2, −181 in 4×3 with no effects), mean −16.
    Shrink: worse in 53 (up to +26: real effects at high credibility, where it shrinks a well-estimated
    variance), better in 56, mean −24. Means by mix (default / REML / shrink / thesis fit / best blend):
    both 117 / 117 / 125 / 126 / 119, row only 124 / 123 / 125 / 135 / 129, weak 144 / 136 / 131 / 133 / 109,
    none 285 / 230 / 193 / 188 / 100. The default's loss with weak effects is the clip: a positive-part
    estimate stays positive in half the draws when the truth is about 0, and the predictor then splits
    noise into rows and columns. **Consequence.** REML is a candidate default for crossed fits at every table
    size visited (not proved; the worst case is small and inside 2 SE of zero in most worlds); shrinking wins
    only where the effects are near zero and costs where they are real, so it is not a default. Whether to fit
    rows and columns at all when effects may be absent belongs to a held-out score
    (`CrossFit.integral_heldOutScore_sub`), as for groups (S69).
- S71. *[numerical]* **REML holds on larger crossed tables: the app's crossed default.** `crossed-fit.js`'s
    grid (tables 3×2, 4×3, 6×4; mixes both / row only / no cell effect / weak; ρ ∈ {0, 0.5}; spread 0 or 1;
    regimes app and thesis; 96 worlds, 1000 draws, common random numbers), with REML as in S70 (now
    `app/crossed.js`, `method: 'reml'`, from the inverse-variance pools clipped at 0). Paired against those
    pools: REML worse in 9 of 96 worlds (at most +3.0 points of the floor, 6×4 with no cell effect, ρ = 0,
    equal volumes, where γ² = 0 and the pools' clip already sits on the truth), better in 48, even in 39;
    mean −3.9, down to −38.8. Mean over the grid: REML 125.9% of the floor, pools 129.7, thesis fit 157.0.
    The gain grows with unequal volumes (132.0 against 139.1) and with weak effects (136.7 against 144.8);
    at 6×4 the two are close (124.8 against 127.1). Variance RMSE after truncation 121% of τ² against 137.
    The rows of the earlier variants are unchanged (same seed). **Consequence.** With S70 (128 small-table
    worlds, worse by at most 5.3 points), REML is the app's crossed default from 2026-11-27, badge "not
    proved yet". A general target: a statement for REML's plug-in rates, or a bound on its loss against the
    pools, neither in hand.
- S72. *[numerical]* **Balanced, no recommended fit wins everywhere: the BLUP gains with equal σⱼ and high ρ,
    loses with a wide σⱼ spread, and g/p's variance verdict adds nothing.** S52's and S57's grids merged (regime
    app / thesis with σⱼ spread 0, 1, 2, thesisShape; ρ ∈ {0, 0.3, 0.6, 0.9}; T ∈ {5, 10}; J = 8; gamma noise;
    56 worlds, 600 draws), scored as the app prices: balance switch on (cross-fitted level). Fits: corrBS, corrBS
    g/p, the BLUP on corrBS's `K̂`, "BLUP g/p" (BLUP on the `K̂` g/p picks), and "held-out" (BLUP or corrBS by
    the leave-one-year-out score of the balanced fits). Paired against corrBS, in points of the floor:
    g/p worse in 5, better in 3, even in 48, range −3.7 to +1.2; BLUP g/p against BLUP the same (−3.6 to
    +1.2). The BLUP: worse in 16, better in 24, mean −0.6, range −15.5 to **+21.6**. By σⱼ spread: equal σⱼ
    never worse (better in 11 of 16, down to −15.5 at ρ = 0.9); spread 1 mixed (−5.6 to +3.6); spread 2
    worse in 14 of 24 (+15.8 and +21.6 at app volume, ρ = 0.3–0.6, T = 5; +3 to +5 in thesisShape at
    ρ = 0.3–0.6), better only at ρ = 0.9. Held-out: worse in 22, better in 24, range −13.6 to +10.1;
    regret against the better of corrBS and BLUP in each world: mean +1.7, at most +10.1 (it picks the BLUP
    in 23–86% of draws). Means over the grid are all 148.6–149.2% of the floor. **Without balancing** the
    BLUP wins broadly (mean −7.4, down to −65.4, worse in 10 of 56): S52 scored unbalanced fits and visited
    no app-volume world with σⱼ spread 2, so its "never much worse" does not carry over to the app's
    default (balance on). Portfolio bias before balancing: corrBS −56 bp, BLUP −72 bp (mean over worlds).
    **Consequence.** No switch of the recommended fit on this evidence: corrBS stays; the BLUP stays a choice
    with its watch-out (unequal noise variances); g/p is not worth a recommendation. General target: the
    price of the BLUP over the blend on the same `K̂`. `gainPrice` treats it as "none extra", but S72 shows
    it grows with the σⱼ spread at low volume (plug-in error of the off-diagonal `K̂` entries, which the
    BLUP uses and the blend does not).
- S73. *[numerical]* **The price of the BLUP over the blend on the same `K̂` (Finding 45).** Squared weight
    errors `(d̂ − d)ᵀK(d̂ − d)` of each family on corrBS's `K̂` against its own true-`K` weights (each fit's
    extra MSE over its oracle with the weights held fixed, `Core.linMse_eq_blupWeight_add`; no cross term),
    J = 8, T = 5, 300 draws, regimes app / thesis, σⱼ spread 0 / 2, ρ ∈ {0, 0.3, 0.6}. In points of the
    floor, BLUP − blend: app σⱼ×2 +32.1 ± 8.6 (ρ = 0.3) and +37.5 ± 7.7 (ρ = 0.6) against gains 2.9 and 11.8;
    app σⱼ×0 +0.6 to +3.9 against gains up to 9.2; thesis +0.0 to +5.4. At ρ = 0 (gain 0) +0.2 to +3.8: ρ̂ ≥ 0
    by clipping, so the BLUP's `K̂` is not diagonal. Part 2: random positive definite `K` and symmetric `ΔK`
    (J = 2–5, 20000 directions): the BLUP's first-order price is the lower one in 11.7%. **Consequence.** The
    first-order law (`Core.tendsto_blupPrice`, `tendsto_blendPrice`) is the general target S72 asked for;
    with a `Var θ̂` for corrBS it gives `gainPrice` a BLUP column (gain against price, as for the variances).
- S74. *[numerical]* **A data-side verdict for the BLUP by gain against bootstrapped price adds nothing, and
    S72's BLUP loss is the balance switch's.** S72's grid (56 worlds, 400 draws, gamma noise). Rule "price": the
    BLUP iff its exact gain on `K̂` exceeds its extra squared weight error over the blend, by a parametric
    bootstrap from the fit (60 normal draws from `K̂`, refit corrBS; Butar & Lahiri 2003; Finding 45's quantity
    with clipping and shrinkage kept). Balanced (cross-fitted level, as S72): price − corrBS mean −0.5, range
    −14.3 to +21.3, the same as always-BLUP (−0.5, −14.3 to +21.4); regret against the better of the two in each
    world 1.5 mean (held-out 1.6). It picks the BLUP in 38–99% of draws where the BLUP loses, so it does not
    find the draws that hurt. **Without balancing** the BLUP wins: raw BLUP − raw corrBS worse in 6 of 56, at
    most +6.2 (app ρ = 0.3, σⱼ×2, T = 5, ± 9.2), mean −8.0, down to −71.9. **The balance switch itself**:
    balanced corrBS − raw corrBS worse in 35 of 56, mean +21.8, up to +205.6 points (app ρ = 0.9, σⱼ×2, T = 5);
    +49.5 even at ρ = 0 (app σⱼ×2, T = 5); thesis volume +4 to +39; within ±12 with equal σⱼ. So S73's weight
    price (+32 at app ρ = 0.3, σⱼ×2) overstates the raw loss (+6): the cross term `2E[AB]` (gamma noise) is
    about −25 points there. **Consequence.** The BLUP-versus-corrBS question closes: unbalanced the BLUP is the
    better fit across the grid; balanced the comparison is dominated by the balance step's own cost, largest with
    unequal noise variances at low volume. Next general target: the MSE cost of balancing to the cross-fitted
    level (a common shift: its variance plus its bias, against the portfolio bias it removes).
- S75. *[numerical + exact]* **The cost of the balance switch is the target's portfolio error minus the fit's
    (Finding 46).** corrBS on S74's grid (56 worlds, 400 draws), balanced to the cross-fitted level. The identity
    `integral_sum_sq_shift` holds in every draw (gap ≤ 3.1e-14). `E(T − μ̄)²/E(r̄ − μ̄)²`: σⱼ×0 0.82–1.10,
    σⱼ×1 1.00–1.26, σⱼ×2 1.17–2.21; the plain exposure average `Σ uⱼμ̂ⱼ`: 0.86–1.60, 0.97–1.45, 1.14–2.01.
    Largest cost: app ρ = 0.9 σⱼ×2 T = 5, `E(T − μ̄)²` 375 against 169 points of the floor. **Consequence.** The
    switch replaces a good estimate of the portfolio level by a worse one when noise variances differ; it pays
    (slightly) only with equal σⱼ and high ρ. Next: a data-side estimate of `E(T − μ̄)² − E(r̄ − μ̄)²`, e.g. on
    held-out years, to decide the switch per portfolio.
- S76. *[numerical]* **A per-portfolio rule for the balance switch.** corrBS on S75's grid (56 worlds, 400 draws),
    against the better of always-on (cross-fitted level) and always-off in each world, points of the floor:
    always on regret 22.2 mean / 205.6 max (worse in 35); always off 0.4 / 12.2 (2); held-out (balance iff the
    leave-one-year-out score of the balanced fit is lower) 10.3 / 99.2 (29); plug-in (balance iff
    `mse(c̄) − mse(c)` on `K̂`, τ̂² is negative, `balance_cost_portLin`, `c̄` the cross-fit's mean weights)
    0.5 / 6.9 (4). The plug-in rule never balances with σⱼ spread 2 (0% of draws) and mostly balances with
    equal σⱼ and ρ ≥ 0.3 (79–98%), where it gains up to 13 points over never (app ρ = 0.9, T = 10: 91 against
    104). The held-out score is too noisy: one portfolio-level number per fold. Portfolio bias, bp of the tariff:
    on −15 to +80, off down to −190 (app σⱼ×2). **Consequence.** In MSE the plug-in rule is never-balance with
    the upside kept; a pricing actuary who must not under-price cannot get that from MSE alone (the bias is
    small in MSE but not in premium). Owner decision: app default, and whether to show the bias next to it.

### Groups or none (2026-11-27, `studies/runs/group-choice.js`; paper, open directions)
- S77. *[numerical]* **Groups or none on held-out years: low regret because little is at stake, not because the
    score sees φ.** The app's world with group levels (J = 8, regions j mod G), G ∈ {2, 4}, φ ∈ {0, 0.3, 0.7},
    T ∈ {5, 10}, ρ ∈ {0, 0.5}, regimes app / thesis; 48 worlds, 2000 draws. Rules: always groups
    (`fitGroupLevels`, S69's GLS pass), never (BLUP on corrBS's `K̂`), held-out (the app's `fitGroups`: groups iff
    the leave-one-year-out score is lower), and "θ̂ > 0" (groups iff the raw GLS `φτ²^` is positive, the plug-in
    gain on `K̂` with no price). Groups − none, points of the floor: −9.7 (app G = 2, φ = 0.7, T = 10) to +6.9
    (app G = 4, φ = 0, T = 5); with φ = 0 groups cost 0 to +7, at φ = 0.7 they gain up to 10 at app volume and
    0–4 at thesis volume. Regret against the better fixed rule in each world, mean / max (worse in): always
    1.4 / 6.9 (18 of 48), never 1.3 / 9.7 (11), held-out **0.9 / 4.0** (20), θ̂ > 0 1.4 / 4.7 (26). Held-out
    picks groups in 38–54% of draws whatever φ (φ = 0: 38–49%; φ = 0.7: 44–54%), so per draw it is close to a
    coin flip; it wins on regret by mixing the two rules, and in a few worlds lands below both. θ̂ > 0 follows φ
    (35–90%) but is too keen at φ = 0 (35–55%: a raw estimate is positive half the time when the truth is 0, as
    for the crossed clip, S70). **Consequence.** The app's rule stays: lowest mean and worst-case regret, no
    tuning. The stakes of the choice are small at J = 8 (at most 10 points of the floor either way), so a
    sharper rule is not worth chasing; parked. The general statement is the held-out score's unbiasedness
    (`CrossFit.integral_heldOutScore_sub`); its regret here holds only in these worlds.

- S78. *[numerical]* **The nearest PSD `Σ̂⁺` costs nothing and makes `K̂ ≻ 0` a theorem** (G2a, `studies/PLAN.md` §5
    step 1; 2026-11-28). The corr fits build `K̂` on `Σ̂⁺ = Σₖ max(λₖ, 0)uₖuₖᵀ`, the Frobenius projection of `Σ̂`
    onto the PSD tables (Higham 1988), never further from the true `Σ` (`ConeProjection.existsUnique_proj_posSemidef`);
    `τ̂²`, `ĉⱼ` and the rules for `θ̂`, `ρ̂` keep the unbiased `Σ̂`. Then `posDef_shrinkOffDiag` (θ < 1, positive
    diagonal) and `posDef_distTaper_hadamard` (τ̂² > 0) apply in every draw. **When Σ̂ is not PSD.** If every
    region's volumes have the same shape over the years (`wᵢₜ = aᵢgₜ`, as in all of the app's worlds), the divisor
    of eq. (37) is `dᵢⱼ = (T − 1)G√(aᵢaⱼ)`, rank one, so `Σ̂ = diag(c)·Q·diag(c)` with `Q` a Gram matrix: PSD by
    construction (a candidate lemma, not yet in Lean). With volumes of different shapes (each cell jittered,
    log-SD 0.1–0.3) and `T = 3`, `J ∈ {8, 12}`, `Σ̂` was not PSD in every draw (`Q` has rank `T − 1 = 2`); at `T = 5`
    in ≤ 2%; random panels: `J = 4, T = 3` about 27%, `T = 2` never. **Error.** Worlds `J ∈ {8, 12}`, `T ∈ {3, 5}`,
    `ρ ∈ {0, 0.3, 0.6}`, jitter 0.1, 0.3; 400 draws: damped and tapered fits on `Σ̂⁺` against the old fit on `Σ̂`
    differ by ≤ 0.5 points of the floor (`runs/psd-projection.out.txt`), and the old fit never had to lower `θ`:
    damping plus `τ̂²I` already gave `K̂ ≻ 0` numerically. **Consequence.** The app projects by default
    (`opts.project = false` is the old fit; not for one common covariance, whose closed-form `z` needs the common
    structure); the damped `K̂` badge is "proved" in every draw, the tapered one whenever `τ̂² > 0`. Seen on the
    side: at `T = 3` the corr fits score 145–177 (floor 100), worse than BS (117–122) at ρ ≤ 0.3; only at ρ = 0.6 does
    the damped fit beat BS (145–155 against 149–167): two degrees of freedom per covariance.

- S79. *[numerical]* **Volumes that vary by year: the fits stand, the balance rule did not** (2026-11-28; owner: "in
    reality the weights are noisy and not always trending"). Until now every world had one volume shape,
    `wⱼₜ = aⱼ(1.03)^t`. The world switch "Volumes vary by year" gives each region its own growth (SD 5% a year around
    3%) and year-to-year log-normal noise (log-SD 0.2), fixed per world (`volSeed`). Grid: `T ∈ {5, 10}`,
    `ρ ∈ {0, 0.3, 0.6}`, σⱼ spread 0 or 2, J = 8, gamma noise, 600 draws; switch off, and on with two volume patterns;
    each world against its own floor. **Fits.** Unbalanced, the mean errors move by ≤ 3.4 points of the floor
    (corrBS 161 → 165, BLUP 160 → 163, corr 156 → 155, BS and pooled BLUP unchanged); the best fit is the same in
    all 12 settings; gain against price (corrBS g/p) keeps its regret (0.8 → 0.9, max 5.8); the damping rule S3 stays
    1.7 points from the best fixed θ (max 6.0). One volume pattern can matter: `T = 5`, `ρ = 0.6`, σ spread 2,
    corrBS and BLUP 220 → 281 with pattern 1, 233 with pattern 2 (the corr fit unchanged): a draw of volumes, not
    a trend. **Balance.** The rule of S76 was silently off: `crossFitLevel` needs one volume shape (with
    region-specific year weights the cross-fitted level is not a function of the region means, so its error cannot
    be priced on `K̂`; `RandomWeights.integral_crossFit_sub`), and `balanceAuto` then balanced on exposures in every
    draw, S74's "always on", costing corrBS up to +110 points (T = 5, ρ = 0.6, σ spread 2: 233 → 341). Fixed: without
    a cross-fitted level the rule prices the exposure-weighted level `a = u` (`balance_cost_portLin` takes any
    `Σ aᵢ = 1`), which it then picks in 0% of draws: balanced = unbalanced. **Consequence.** The app's conclusions
    hold for uneven volumes except what rests on the cross-fitted level: on such data the skew under-pricing
    (Finding 35) is no longer removed. General target (PLAN Pending "Realistic volumes"): the balance cost for a
    target linear in the cells, then a cross-fitted level for any volumes. The switch stays off by default until the
    page's quoted checks are rerun under it.
- S80. *[numerical; the bias is exact]* **The unbiased `Wⱼ` worsens the rates.** Finding 47: the app's `Wⱼ` is
    low by a relative O(1/T) (`VcW.integral_vcW_equal`). `runs/vcw-corr.js`: J = 8, gamma noise, regimes app /
    thesis × σⱼ spread {0, 1, 2} × ρ {0, 0.6} × T {3, 5, 10}, 36 worlds, 600 paired draws. Mean W over the
    draws' Var σ̂ⱼ²: raw 0.40 / 0.66 / 0.84 (T = 3 / 5 / 10), corrected 0.79 (T = 3: only the normal part can
    be corrected) / 1.03 / 1.00. β̂²'s bias at ρ = 0 drops to about 0 from T = 5 (raw: +0.08 to +2.4 in units
    of β²); at ρ = 0.6 it stays low (−0.2 to −0.5 σ⁴ with equal σⱼ: the σ̂ⱼ² are correlated, so the cross
    terms are missing, `integral_betaHat`). corrBS's MSE, corrected − raw, points of the floor: mean +4.1,
    −9.0 to +43.7; 4 wins (equal σⱼ, app volume, T ≤ 5), 19 losses (every σⱼ spread with T ≤ 5, largest at
    T = 3). **Consequence.** The app keeps the raw `Wⱼ` (`opts.corrW` gives the corrected one). The bias in
    `Wⱼ` shrinks the σ̂ⱼ² less towards the pool, which pays when the σⱼ² differ. Hypothesis, not chased: the
    rates' loss in `ζ` is asymmetric, so the best plug-in `ζ` is not `β²/(β² + Var σ̂²)`.
- S81. *[numerical; the mechanism is exact]* **ρ̂'s bias comes from σ̃'s level, and the rates ignore it** (G1c,
    Finding 48). `runs/rho-level.js`: app's world, gamma noise, J = 8; part A at ρ = 0.6, σⱼ spread {0, 1, 2},
    T {5, 10}; part B the 24 worlds regime × spread × ρ {0, 0.6} × T; 600 paired draws. E ρ̂ − ρ by the σ in ρ̂'s
    denominator: true σⱼ ≈ 0 (as proved), own σ̂ⱼ −0.03 to −0.06, the app's σ̃ⱼ −0.05 (no spread) to +0.13 (spread
    2), pooled σ̄ −0.05 to −0.35. Σσ̃²/Σσ̂² = 0.63–0.97; below 1 in 100% of draws, while Wⱼ is fully ordered like
    σ̂ⱼ² in only 2–42% (so `sum_shrink_le_iff`, not Chebyshev, is the operative statement). corrBS's MSE: ρ̂ from
    own σ̂ⱼ +0.4 mean (−1.1 to +5.1), σ̃ rescaled to σ̂'s level +0.3 (−39.4 to +13.7: large gain at app volume, σⱼ
    spread 2, ρ = 0, losses with equal σⱼ). **Consequence.** No change to the app. Like S80: the plug-in variances'
    biases are exact and large, but correcting them does not help the rates.
- S82. *[numerical; the pricing is exact for fixed weights]* **Balancing with volumes that vary by year** (owner,
    2026-11-28: on uneven volumes nothing removed the skew under-pricing of Finding 35). `BalanceCost.balance_cost_cellLin`
    prices any target linear in the yearly cells, so `crossFitLevel` (common year shares πₛ, unbiased by
    `integral_crossFit_sub` for any volumes) no longer needs one volume shape, and `balanceAuto` prices it on the
    cells (`D̂ₛ` from `K̂ − L̂`; on one shape the fit's own term equals mse(c) on `K̂`, Node test).
    `runs/balance-volumes.js`: corrBS, volNoise 0.2, volTrend 0.05, σⱼ spread {0, 2} × ρ {0, 0.6} × T {5, 10},
    1500 draws. Portfolio bias raw −11 to −166 bp; always cross-fitted −3 to +39 (all within 2 SE of 0),
    exposures 0 to +45; MSE: cross-fitted ≈ raw with equal σⱼ (55.5 vs 55.9 at T = 5), +15 to
    +66% with σⱼ spread 2; `auto` follows the cheaper one (off with spread, partly on at ρ = 0.6: −70 → −48 bp,
    MSE 71.3 → 68.4). S79 rerun (`volume-noise.out.txt`): one shape, the exact cell pricing improves `auto`
    slightly (corrBS balanced 161.5 → 161.1, corr 155.9 → 155.5 % of the floor); varying volumes, balance on in
    18% of draws (was 0), MSE +0.1 to +0.4. S76's regret is unchanged (its rule is the script's own). **Consequence.**
    Varying volumes now behave as one shape: unbiased balance is available, at the Finding 46 price.

