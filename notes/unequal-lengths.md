# Cohort-dependent series lengths

README "Later goals → Cohort-dependent series length". Lean (all proved):
[`Credibility/Unequal.lean`](../Credibility/Unequal.lean). Not in the thesis.

**Short answer.** Everything carries over with sums restricted to the periods
a cohort (or a pair of cohorts) is observed in. `Kᵢⱼ = σ²ᵢⱼρᵢⱼ + τ²δᵢⱼ` still
holds, now with `σ²ᵢⱼ` summed over the *shared* periods only. `K` stays
positive definite for any overlap pattern, and under a weaker hypothesis on
`ρ` than before. The GLS weights and eq. (26) are unchanged (they only see
`K`). In the §2.8 estimator the `(T − 2)` of eq. (39) becomes a per-pair,
volume-weighted count `nᵢⱼ = |Tᵢⱼ| − ωᵢ − ωⱼ`, *not* `|Tᵢⱼ| − 2`.

## 1. Model

Periods `T` (finite), cohorts `J`. Cohort `j` is observed in `Tⱼ ⊆ T`,
`Tⱼ ≠ ∅`. Write `Tᵢⱼ = Tᵢ ∩ Tⱼ` (so `Tⱼⱼ = Tⱼ`) and, for each period,
`Jₜ = {j : t ∈ Tⱼ}`, the cohorts alive at `t`.

The model (15) is unchanged, only the index set of the data shrinks:

    μⱼₜ = μⱼ + σⱼₜ εⱼₜ,   t ∈ Tⱼ,     cov(εᵢₜ, εⱼₛ) = ρᵢⱼ δₜₛ.

So correlation acts only on pairs `(i, t), (j, t)` with `t ∈ Tᵢⱼ`, as wanted.

**Observation covariance (16).** Same formula, for `t ∈ Tᵢ`, `s ∈ Tⱼ`:

    K̄ᵢⱼᵗˢ = σᵢₜ σⱼₛ ρᵢⱼ δₜₛ + τ² δᵢⱼ.

**Cohort weights (23).** Inverse-variance on `Tⱼ`, zero elsewhere:

    aⱼₜ = σⱼₜ⁻² / Σ_{s∈Tⱼ} σⱼₛ⁻²   (t ∈ Tⱼ),   aⱼₜ = 0 otherwise.

The optimality proof of (23) is per cohort, so it applies verbatim to `Tⱼ`.

**`σ²ᵢⱼ` (18).** Only shared periods contribute:

    σ²ᵢⱼ = Σ_{t∈Tᵢⱼ} aᵢₜ aⱼₜ σᵢₜ σⱼₜ,    σ²ᵢⱼ = 0 if Tᵢ ∩ Tⱼ = ∅.

**`K` (21).** `Kᵢⱼ = Σ_{t∈Tᵢ} Σ_{s∈Tⱼ} aᵢₜ aⱼₛ K̄ᵢⱼᵗˢ`.

## 2. What carries over

| Result | Status | Change |
|---|---|---|
| `K_apply`: `Kᵢⱼ = σ²ᵢⱼρᵢⱼ + τ²δᵢⱼ` | carries over | `δₜₛ` collapses the double sum to `Tᵢⱼ`; the `τ²` term uses `Σ_{Tⱼ} aⱼₜ = 1`. No `T ≥ 1` hypothesis: `Tⱼ ≠ ∅` is part of the model. |
| `K_symm` | carries over | — |
| `K_posDef` | carries over, **weaker hypothesis** | see §3 |
| GLS weights (24)–(25), `b`, `s²` | verbatim | `Weights.lean` is generic in `K` |
| eqs. (22), (26) (`bestZ_eq`) | verbatim | the blend only sees `K`, `σ²ⱼⱼ`, `τ²` |
| equal covariances (Finding 5) | carries over | but pairs with no overlap have covariance `0`, so "all `σ²ᵢⱼρᵢⱼ = c`" with some disjoint pair forces `c = 0`, i.e. Bühlmann–Straub-like weights |
| §2.8 estimators | carry over with a new count | see §4 |
| balance (§2.9) | not looked at yet | |

Back to the thesis: with `Tⱼ = T` for all `j`, `a`, `σ²` and `K` are the
thesis ones (`Unequal.K_eq_of_full`).

## 3. Is `K` still positive definite? Yes.

As in `Model.K_posDef`: with `(yₜ)ⱼ = aⱼₜ σⱼₜ xⱼ`,

    xᵀ K x = Σₜ yₜᵀ R yₜ + τ² ‖x‖²,     R = (ρᵢⱼ).

Now `aⱼₜ = 0` for `t ∉ Tⱼ`, so `yₜ` is supported on `Jₜ`, and
`yₜᵀ R yₜ = yₜ|ᵀ R[Jₜ, Jₜ] yₜ|`. Hence `K ≻ 0` as soon as `τ² > 0` and
**every principal block `R[Jₜ, Jₜ]` is positive semidefinite**. That is
exactly the condition for the data covariance itself to be a covariance
matrix, and it is weaker than `R ⪰ 0`: entries `ρᵢⱼ` with `Tᵢ ∩ Tⱼ = ∅` never
enter, and need not even be completable to a correlation matrix.
Example: three cohorts, `T₁ = {1}`, `T₂ = {1, 2}`, `T₃ = {2}`,
`ρ₁₂ = ρ₂₃ = 0.9`, `ρ₁₃ = −0.9`. `R` is not PSD (`det R < 0`), but the two
blocks `{1,2}` and `{2,3}` are, so `K ≻ 0`.

So differing overlap sets do not break positive-definiteness; `τ² > 0` still
does all the work for strictness. Lean (proved): `Unequal.K_posDef` (blocks) and
`K_posDef_of_posSemidef` (full `R ⪰ 0`, the Model hypothesis).

## 4. Estimation (§2.8): the per-pair count

Special case `σⱼₜ = σⱼ/√wⱼₜ`. Per cohort: `wⱼ* = Σ_{t∈Tⱼ} wⱼₜ`,
`aⱼₜ = wⱼₜ/wⱼ*`, `μ̂ⱼ = Σ_{t∈Tⱼ} aⱼₜ μⱼₜ`, `w** = Σⱼ wⱼ*`. Per pair:

    Sᵢⱼ = Σ_{t∈Tᵢⱼ} √(wᵢₜ wⱼₜ),     ωᵢ⁽ʲ⁾ = Σ_{t∈Tᵢⱼ} wᵢₜ / wᵢ*

(`ωᵢ⁽ʲ⁾` is the share of cohort `i`'s volume that lies in the overlap).

**Eq. (37).** `σ²ᵢⱼρᵢⱼ = Sᵢⱼ/(wᵢ*wⱼ*) · σᵢσⱼρᵢⱼ`, with `Sᵢⱼ` over the overlap.

**Residual products.** For `t ∈ Tᵢⱼ` the display before (37) is unchanged:
`E[(μᵢₜ − μ̂ᵢ)(μⱼₜ − μ̂ⱼ)] = (1 − aᵢₜ − aⱼₜ)σᵢₜσⱼₜρᵢⱼ + σ²ᵢⱼρᵢⱼ`.

**The count.** Weighting by `√(wᵢₜwⱼₜ)` and summing over `Tᵢⱼ` gives
`σᵢσⱼρᵢⱼ · Σ_{Tᵢⱼ}(1 − wᵢₜ/wᵢ* − wⱼₜ/wⱼ*) + Sᵢⱼ σ²ᵢⱼρᵢⱼ`. In the thesis the
sum is `T − 2` because each cohort's shares add up to one over all of `T`.
Here they add up to `ωᵢ⁽ʲ⁾ ≤ 1` over the overlap, so

    nᵢⱼ = |Tᵢⱼ| − ωᵢ⁽ʲ⁾ − ωⱼ⁽ⁱ⁾,

and the unbiased estimator (39, first line) becomes

    σ²ᵢⱼρᵢⱼ^ = Σ_{t∈Tᵢⱼ} √(wᵢₜwⱼₜ)(μᵢₜ − μ̂ᵢ)(μⱼₜ − μ̂ⱼ)  /  (Sᵢⱼ + nᵢⱼ wᵢ*wⱼ*/Sᵢⱼ).

Checks: `Tᵢ = Tⱼ = T` gives `nᵢⱼ = T − 2` (the thesis). `i = j` gives
`nⱼⱼ = |Tⱼ| − 2` and denominator `(|Tⱼ| − 1)wⱼ*`: Bühlmann–Straub with the
cohort's own length (eq. (41)). Checked exactly against the covariance matrix
of the data for a random 3-cohort pattern (e.g. `|Tᵢⱼ| = 2`, `nᵢⱼ = 1.189`).
Using `|Tᵢⱼ| − 2` instead would bias the estimator whenever the two series
are not identical.

**When is the denominator positive?** Put `D = (Sᵢⱼ² /(wᵢ*wⱼ*)) + nᵢⱼ`
(the denominator times `Sᵢⱼ/(wᵢ*wⱼ*)`).
- `|Tᵢⱼ| ≥ 2`: `nᵢⱼ ≥ 2 − 1 − 1 = 0` and the first term is `> 0`, so `D > 0`.
- `|Tᵢⱼ| = 1`, `Tᵢⱼ = {t}`: `D = ωᵢωⱼ + 1 − ωᵢ − ωⱼ = (1 − ωᵢ)(1 − ωⱼ)`. So
  `D > 0` iff **both** cohorts also have a period outside the overlap. One
  shared period suffices to identify `ρᵢⱼ` when both series extend beyond
  it, because the deviations are from each cohort's own mean. This is the
  sharp form of the thesis's `T ≥ 2` (Finding 7): there `ωᵢ = ωⱼ = 1`.
- `Tᵢⱼ = ∅`: nothing to estimate, `σ²ᵢⱼρᵢⱼ = 0`; the estimator is the empty
  sum `0` (Lean's `x/0 = 0` also makes it `0`), which is unbiased.

**`τ̂²` and `K̂` (39).** Formally unchanged: `ĉⱼ = Σᵢ (δᵢⱼ − wᵢ*/w**)σ²ᵢⱼρᵢⱼ^`,
the `τ̂²` and `K̂ᵢⱼ` formulas are the thesis ones with the new `wⱼ*`, `μ̂ⱼ`,
`σ²ᵢⱼρᵢⱼ^`. The unbiasedness proof of `τ̂²` only uses `K = σ²ρ + τ²δ` and
`E[ℓᵀX mᵀX] = ℓᵀK̄m` for `Σℓ = 0`, so it goes through. Hypotheses: `J ≥ 2`
and `D > 0` for every pair with `Tᵢⱼ ≠ ∅` (in particular `|Tⱼ| ≥ 2` for all `j`).

**Only observed data.** Lean reuses `Model.Unbiased`, which puts a (latent)
value in every cell `(j, t) ∈ J × T`. To make sure no estimator peeks at a
cell outside `Tⱼ`, `Unequal.Observed f` says `f` depends only on the
observed cells, and `KHat_observed` checks it for `K̂`. The expectations then
only involve `K̄ᵢⱼᵗˢ` with `t ∈ Tᵢ`, `s ∈ Tⱼ`.

## 5. Open / next

- Which pairs need `ρᵢⱼ`: only overlapping ones. A natural follow-up is a
  model where `ρ` itself is only given on overlapping pairs (a partial
  correlation table), which the block hypothesis of §3 already allows.
- Balance (§2.9) with unequal lengths.
