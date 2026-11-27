# The BLUP in credibility form, and the ρ̂ channel of Finding 35

Discussion of 2026-11-26 (owner: is the BLUP more exposed to a winner's curse than the blend, and can it
be written like credibility so that the blend falls out of it?). Targets 1–3 of §2 are proved (2026-11-26); the
other Lean targets are marked. Plan entries: `studies/PLAN.md` Pending, "BLUP in credibility form" and "Finding 35: the ρ̂
channel".

## 1. Degrees of freedom

For a given `K`, `L` the BLUP fits nothing the blend does not: both are functions of the same table. The
extra parameters, and so the price of estimation, sit in `K̂`, not in the predictor:
`MSE = mse(d*) + E B² + 2E[AB]` (`Core.Target.integral_sq_plugIn`), and `E B²` grows with the number of
free entries of `K̂`. The app agrees (PLAN 3c): on corrBS's one-`ρ̂` table the plug-in BLUP is never
worse than the blend and wins under correlation; on the full damped `K̂` it wins only for `J = 20` with
strong structure and is worst at `T = 5`. So: keep `K̂` structured. The winner's curse proper is in
choosing BLUP or blend from the same data; that is the gain-against-price choice (S56, S57).

## 2. Credibility form

Residuals `r = μ̂ − 1 μ̂_GLS` (so `1ᵀK⁻¹r = 0`). From `d* = K⁻¹ℓ + (1 − 1ᵀK⁻¹ℓ) b`:

    μ̂ⱼᴮᴸᵁᴾ = μ̂_GLS + ℓⱼᵀ K⁻¹ r,    all cohorts at once:  μ̂ᴮᴸᵁᴾ = 1 μ̂_GLS + Z r,   Z = L K⁻¹.

For the thesis model `L = τ²I`, `K = τ²I + V`: `Z = τ²(τ²I + V)⁻¹`, the matrix form of
`z = τ²/(τ² + v)` and the shape of Jewell's multidimensional credibility `T(T + S)⁻¹`
(literature §10, Jewell 1973, Bühlmann–Gisler ch. 7). Reading: `Zⱼⱼ` is cohort `j`'s own credibility,
`Zⱼᵢ` what it borrows from cohort `i`'s residual.

Gauge: since `1ᵀK⁻¹r = 0`, row `j` of `Z` is defined only up to adding `c·1ᵀK⁻¹`. *Settled 2026-11-27*
(`Core.residualWeight_eq_iff`, `existsUnique_sum_eq_zero_row`, `quadForm_le_of_residualWeight_eq`): the
two candidates coincide, the row of least `K`-norm is the one with zero (plain) sum, `d* − b`, and
`d*ᵀKd* = s² + (d* − b)ᵀK(d* − b)`. The blend's is `z(eⱼ − b)`, diagonal `z(1 − bⱼ)`; report that.

The blend is the same form with row `j` restricted to `z eⱼᵀ` (plus the gauge): `μ̂ + z(μ̂ⱼ − μ̂)`.
Optimising that one number gives eq. (7). The blend is the BLUP iff `ℓⱼ − z K eⱼ` is constant, i.e.
`ℓⱼᵀK⁻¹ = z eⱼᵀ + c 1ᵀK⁻¹`: Finding 18's condition (`Core.blendWeight_eq_blupWeight_iff`).

Path between them: `d(θ) = w + θ(d* − w)`, `w` the best blend. Both are unbiased, so by Pythagoras
(`Core.errVar_eq_blupWeight_add`) `MSE(θ) = MSE(d*) + (1 − θ)²(w − d*)ᵀK(w − d*)`: with known `K`,
`θ = 1`. With `K̂`, the best `θ` should be about gain/(gain + price), the shape of
`Damping.lean`'s `θ*`, estimable from the data (no hand-set value). Report: `ẑ` as the headline, the
off-diagonal correction `θ̂(d̂* − ŵ)` next to it.

Lean targets (`Core.lean`, one chat; 1–3 done 2026-11-26: `Core.blupWeight_dotProduct`,
`Core.blendWeight_eq_residualWeight`, `Core.blendWeight_bestZ_optimal` (needs `b ≠ eⱼ`),
`Core.linMse_add_smul_blupWeight_sub`):
1. `blupWeight K L j ⬝ᵥ μ̂ = glsMean + (L K⁻¹ row j) ⬝ᵥ (μ̂ − glsMean • 1)`.
2. Row `j` restricted to `z eⱼ` gives `blendWeight`, its best `z` is `bestZ`.
3. `linMse` of `w + θ(d* − w)` equals `linMse d* + (1 − θ)²(w − d*)ᵀK(w − d*)`.
4. Later (needs the moment layer): the best `θ` for a plug-in, as for damping. *Done 2026-11-26*
   (`PlugInMix.lean`): `MSE(θ) = (1 − θ)M₀ + θM₁ − θ(1 − θ)S` for every distribution, `S` the spread of
   the two fitted predictions, `θ* = ½ + (M₀ − M₁)/(2S)`; not gain/(gain + price) but
   ½ + gain/(2·spread). Fitted `θ̂` (2026-11-26, same file): `θ* = −E[e₀Δ]/EΔ²`, the regression of
   the blend's error on the disagreement `Δ`; on a held-out proxy `Y' = Y + ε` it is off by exactly
   `E[Δε]/EΔ²`, so it is exact when the held-out noise is independent of the data (mean zero), and
   clipping to `[0, 1]` never hurts when `|M₀ − M₁| ≤ S`. *Studied 2026-11-27* (S64): one held-out year
   costs exactly `ΔᵀWΣWΔ/ΔᵀWΔ ≥ σ²(1 − ρ)` over the draw's best `θ`, 7–14× the gain; keep `θ = 1`. An iid year
   shock gives no bias; a persistent one does. Open: S64's Lean targets 1 (the price) and 2 (bias in the
   factor model).

## 3. Hypothesis for the ρ̂ channel (Finding 35, PLAN "Finding 35 remedies", open item)

*Outcome 2026-11-26 (S63 in `studies/damping-theta.md`, `studies/rho-channel.js`).* H2 and P3 were in fact
already in the app: `Engine.skewBias` (2026-11-23) predicts the `ρ̂` part to first order. H1 holds only by
half: with `ρ` fixed at the truth about half the bias stays (the pooled `σ̂²`/`τ̂²` ratio). P1 holds (bias 0
exactly). R1 removes the bias but costs 4–17 MSE points; its variant R1b, the BLUP shifted to the
cross-fitted portfolio level, is unbiased and beats exposure balance under correlation. Next: owner's
choice and the Lean corollary (S63 "Consequence"). The text below is the hypothesis as written before.

Seen: with the pooled `σ̂²` the portfolio bias is gone at `ρ = 0` (−0.05%) but not at `ρ = 0.6`
(−0.54%; spread 1: −0.38%). Balancing to exposure removes it but costs ~20 MSE points there.

**H1 (attribution).** With the pooled `σ̂²`, what is left runs through `ρ̂`, mostly via the GLS portfolio
weights `b̂` (the other regions' terms of `Σᵢ cov(d̂ᵢ, μ̂ᵢ)`, as for the `σ̂ⱼ²` channel), not through
`τ̂²`. Test: the pooled BLUP with `ρ` fixed at the truth (others estimated), and with `τ²` fixed at the
truth; `covDiag` split own / other.

**H2 (mechanism).** Because `Σᵢ d̂ᵢ = 1` in every draw, `Σᵢ cov(d̂ᵢ, μ̂ᵢ) = Σᵢ cov(d̂ᵢ, μ̂ᵢ − ν)` for any
common `ν`: a year that lifts every region alike costs nothing; only the region-differential part
counts. To first order the bias is `Σᵢ ∂dᵢ/∂ρ · cov(ρ̂, μ̂ᵢ − μ̂_b)`. `ρ̂` is a ratio of cross-products of
residuals, so `cov(ρ̂, μ̂ᵢ)` is a third *cross*-cumulant `κ(εₖ, εₗ, εᵢ)`, `k ≠ l`: zero without skew
(seen: 0 under normal noise) and zero without correlation (seen: pooled 0 at `ρ = 0`). Both are needed.
Direction (to check): a draw with large cross-products is one where the noisier (smaller) regions moved
most; `ρ̂` up moves `b̂` away from the noisier regions, so the regions that drew high lose weight:
under-pricing, as seen.

Predictions:
- P1. Equal exposures and equal `σ` (exchangeable regions): `b̂ = 1/J` for every `ρ̂`, so the `b̂` part
  vanishes; only a small own-weight part is left.
- P2. The bias grows with `ρ`, with skewness, and with the spread of the noise variances `σ²/wⱼ`; it
  vanishes under normal noise for every `ρ`.
- P3. The first-order formula with true cumulants matches the simulated `Σᵢ cov` to within noise.

**R1 (remedy candidate): leave-one-year-out cross-fitting of the residual parameters.**
`rate = Σₜ aₜ d̂₍₋ₜ₎ᵀ Xₜ`, with `d̂₍₋ₜ₎` built from `ρ̂`, `σ̂²` of the other years (these use
within-region residuals only, so no levels) and `τ̂²` from all years. Years are independent, so
`d̂₍₋ₜ₎` is independent of year `t`'s noise and the `ρ̂` (and `σ̂ⱼ²`) channel is exactly 0, for any
distribution; only the `τ̂²` channel stays (small at `ρ = 0`). Cost: weights from `T − 1` years, `T`
different weight vectors; expected small, since `ρ̂` is one number. Unlike exposure balance it does not
force the wrong balance under correlation (S28). Same idea as the cross-fitted power slope (PLAN "Noise
shape", literature §10j–k: Chernozhukov et al. 2018) and the cross-fitted learner (§10p).
Lean target (distribution-free, a corollary of `Core.Estimates.integral_randomLin_sub`): weights summing
to 1 and independent of the noise of the cells they weight give an unbiased predictor, given the levels.

**R2 (fallback): first-order bias correction** from k-statistic estimates of the cross-cumulants
(`noiseDiagnostics`). Likely too noisy (third moments, few years); try only if R1's price is high.

Study plan: a script `studies/rho-channel.js` on the app's worlds (default, `ρ = 0.6`, spread 1, `T = 4`
skew, `J = 20`): H1 attribution, P1–P3, and R1 against pooled and balanced (MSE / portfolio bias, 3000
draws). If R1 holds: a fit option "cross-fit ρ̂, σ̂²" and the Lean target above; the outcome is a
hypothesis until then (CLAUDE.md, general results first).
