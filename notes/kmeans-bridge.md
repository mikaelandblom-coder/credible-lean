# The k-means bridge: when are MSE-optimal cohorts intervals?

On paper, 2026-11-11 (roadmap §1). The aim is to use `kmeans_contiguous`
(`Credibility/KMeans.lean`) for choosing cohorts. Numbers are checked by
[`kmeans_bridge.py`](kmeans_bridge.py).

**Short answer.** Pooling with an exposure-weighted MSE is *exactly* weighted
k-means plus the number of cohorts. So optimal cohorts are intervals of the
sorted levels for any variances, and this is provable now. With a
credibility blend, or with an unweighted MSE, unequal variances break
contiguity: there are counterexamples. With a common variance `V`, no
counterexample exists for the blend either: optimal cohorts are intervals,
by a swap argument (Theorem below).

## Setting

Units `i` (e.g. rating classes) have fixed true levels `xᵢ` and unbiased,
uncorrelated estimates `Xᵢ` with `Var Xᵢ = vᵢ`; `wᵢ = 1/vᵢ` (exposure).
A labelling `c : ι → κ` puts them into at most `k = |κ|` cohorts. Cohort `a`
pools by inverse variance:

```
X̄ₐ = Σ_{c(i)=a} wᵢXᵢ / Wₐ,    E X̄ₐ = x̄ₐ (the w-weighted mean level),    Var X̄ₐ = 1/Wₐ.
```

Two rules for unit `i ∈ a`: **pool** predicts `X̄ₐ`; **blend** predicts
`μ + zₐ(X̄ₐ - μ)`, with `zₐ = τ²/(τ² + 1/Wₐ)` and `μ`, `τ²` known.

## Proposition (pooling = weighted k-means)

```
Σᵢ wᵢ E(X̄_{c(i)} - xᵢ)²  =  Σᵢ wᵢ (xᵢ - x̄_{c(i)})²  +  #(nonempty cohorts).
```

*Proof.* `E(X̄ₐ - xᵢ)² = (x̄ₐ - xᵢ)² + 1/Wₐ`, and `Σ_{i∈a} wᵢ · 1/Wₐ = 1`. ∎

The first term is `kmeansCost w x c x̄`, and `x̄` are the best centers for `c`.

**Corollary.** Among labellings into at most `k` cohorts, an MSE-optimal one
has interval cohorts: `xᵢ < xⱼ < xₗ` and `c i = c l` imply `c j = c i`.

*Proof.* Let `c*` be optimal with `m` nonempty cohorts, and restrict the
labels to those `m`. For any `c'` with those labels and any centers `μ'`:
`kmeansCost(c', μ') ≥ kmeansCost(c', x̄') = L(c') - m(c') ≥ L(c*) - m =
kmeansCost(c*, x̄*)`, since `L(c') ≥ L(c*)` and `m(c') ≤ m`. So `(c*, x̄*)`
is jointly k-means optimal, and `kmeans_contiguous` applies. ∎

So the optimal cohorts can be found exactly by dynamic programming over the
sorted levels. **Common `V`** is the special case `wᵢ = 1/V`: there the
unweighted total MSE is `kmeansCost(1, x, c, x̄) + mV`, the roadmap's
"constant plus a k-means cost". The exposure weighting makes the result hold
for unequal `vᵢ` too.

Not covered: correlated units (`ρ ≠ 0`). Then `Var X̄ₐ` depends on which
units share a cohort, and `W_a Var X̄_a` is no longer `1`.

## Counterexamples (unequal variances, at most 2 cohorts)

Levels are sorted; "best interval" is the best partition into intervals.

| rule, loss | `x` | `v` | `τ²` (`μ = 0`) | optimum | loss | best interval | loss |
|---|---|---|---|---|---|---|---|
| blend, unweighted | `(-½, 0, ½)` | `(16, ½, 16)` | `½` | `{1,3}{2}` | 0.680 | `{1,2}{3}` | 0.742 |
| blend, exposure-weighted | `(-½, 0, ½)` | `(16, 4, 16)` | `1` | `{1,3}{2}` | 0.0836 | `{1}{2,3}` | 0.0883 |
| pool, unweighted | `(-1, 0, 0.2, 0.25, 1.5)` | `(16, 1/16, ½, 4, 2)` | – | `{1,2,4}{3,5}` | 3.196 | `{1,2,3,4}{5}` | 3.347 |

*Check of the first row by hand.* `{1,3}`: `X̄ = (X₁+X₃)/2` has mean `0` and
variance `8`, so `z = ½/8.5 = 1/17`; each outer unit has MSE
`¼ + 8/17²`, total `0.555`. `{2}` alone: `z = ½`, mean level `0 = μ`, MSE
`¼·½ = 0.125`. Sum `0.680`.

*Why.* The noisy middle cohort sits next to `μ`, so the collective serves it
better than any neighbour; the outer noisy cohorts gain more from sharing
variance than they lose in bias. It is the pair-dependent scale of the
merge rule `1/d > 1/V + 1/τ²` (`notes/merging-cohorts.md`): with unequal
variances "close" is not a distance on the line.

The cap matters for the blend: with `k = 3` both blend examples pick
singletons, which are intervals. The pooled example fails with no cap at all:
for every `k ≤ 5` the optimum is `{1,2,4}{3,5}`. The cap is the practical
question anyway ("the best tariff with at most `k` cohorts").

## Common variance, blend: theorem (proved 2026-11-11)

With `vᵢ = V` the blend's total MSE is the k-means cost plus a cohort term
`nₐ(1-zₐ)²(x̄ₐ-μ)² + zₐ²V` that depends on the cohort's size and mean, so the
Proposition does not apply. Random search found no non-interval optimum
(20 000 cases with exactly `k` cohorts, 6000 with at most `k`). It is true,
by a swap argument instead of k-means.

**Theorem.** With a common variance `V ≥ 0`, `τ² > 0` and known `μ`, every
labelling that minimises the blend's total MSE (over all labellings into the
labels `κ`) has interval cohorts.

*Step 1: the loss depends on a cohort only through `(nₐ, Sₐ)`.* Put
`yᵢ = xᵢ - μ` and `Sₐ = Σ_{i∈a} yᵢ`, so `x̄ₐ - μ = Sₐ/nₐ`; here
`zₐ = nₐτ²/(nₐτ² + V)` and `Var X̄ₐ = V/nₐ`. Unit `i ∈ a` has MSE
`(zₐSₐ/nₐ - yᵢ)² + zₐ²V/nₐ`; summing over the cohort,

```
cohort loss = Σ_{i∈a} yᵢ²  -  fₐ Sₐ²  +  zₐ² V,     fₐ = zₐ(2 - zₐ)/nₐ > 0,
```

and `fₐ`, `zₐ` depend only on the size `nₐ`. So the total loss is
`Σᵢ yᵢ² - Σₐ (fₐSₐ² - zₐ²V)`.

*Step 2: swap.* Swapping two units `i ∈ A`, `j ∈ B` (`A ≠ B`) keeps all sizes,
hence all `f` and `z`, and changes only `S_A → S_A + d`, `S_B → S_B - d` with
`d = yⱼ - yᵢ = xⱼ - xᵢ`. The loss changes by

```
Δ = -(2d·D + (f_A + f_B) d²),     D = f_A S_A - f_B S_B.
```

*Step 3.* Let `c` be optimal and suppose `xᵢ < xⱼ < xₗ`, `c i = c l = A`,
`c j = B ≠ A`. Swapping `i, j` (`d = xⱼ - xᵢ > 0`) gives `Δ ≥ 0`, i.e.
`2dD ≤ -(f_A+f_B)d² < 0`, so `D < 0`. Swapping `l, j` (`d = xⱼ - xₗ < 0`)
gives `D > 0` the same way. Contradiction. ∎

*Remarks.* No cap is needed and none hurts: swaps keep the set of used labels,
so the result holds for "exactly `k`", "at most `k`" or any size constraint.
The same argument covers pooling with a common `V` (`f = 1/n`, cohort term
`V`). It fails for unequal variances because then `Var X̄ₐ`, hence `z` and
`f`, depend on *which* units share the cohort, not just how many (Finding
14). What made it work: for fixed sizes the loss is minus a strictly convex
function of the cohort sums, and convex maxima over the "swap moves" sit at
sorted assignments.

## For Lean (done 2026-11-11: `Credibility/KMeansBridge.lean`)

1. `pool_mse_eq_kmeansCost`: the Proposition, for `Fintype ι`, labels `κ`,
   `w > 0`, the pooled mean `x̄`. Purely algebraic (the levels are fixed; the
   variance term is `Σ_{i∈a} wᵢ/Wₐ = 1`). A moment-layer version (any random
   `Xᵢ` with these moments) can come later via `Core.Estimates`.
2. `pool_optimal_contiguous`: the Corollary, from item 1 and
   `kmeans_contiguous` with labels restricted to the used ones.
3. Finding 14 (below) as a blueprint remark in the k-means chapter.
