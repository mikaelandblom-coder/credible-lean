# Grouping cohorts with a τ² per group: are optimal groups intervals?

2026-11-25, numerical check (`notes/group_variances.py`, output `group_variances.out.txt`), asked
after reading the spatially clustered Fay–Herriot paper (literature §10p). Setting as in
`notes/kmeans-bridge.md`, with one change: cohorts are not pooled. Each cohort `j` keeps its own estimate
(fixed level `θⱼ`, noise variance `Dⱼ`, volume weight `uⱼ`) and is blended towards its group's
collective mean. Group `g` has its own mean `m_g` and either its own `τ²_g` or one common `τ²`. Oracle
loss, given the levels: `Σⱼ uⱼ[zⱼ²Dⱼ + (1 − zⱼ)²(m_g − θⱼ)²]`, `zⱼ = τ²/(τ² + Dⱼ)`, with the group parameters
at their best. The data-side twin is the normal likelihood `x̄ⱼ ~ N(m_g, τ²_g + Dⱼ)` that the paper
maximises. Brute force over all labellings into `k = 2` groups, `n = 7`.

## 1. Own `τ²` per group: no

Counterexample with **equal volumes** (`D = 1`): `θ = (−5, −0.2, −0.1, 0, 0.1, 0.2, 5)`.

| criterion | best | loss | best intervals | loss |
|---|---|---|---|---|
| oracle MSE | `{−5, 5}{middle}` | 2.021 | `{−5}{rest}` | 4.663 |
| normal likelihood (−log L) | `{−5, 5}{middle}` | 10.70 | `{−5}{rest}` | 13.18 |

*By hand.* With equal `D` a group of `n` with within-group variance `s²` costs `n·D·s²/(s² + D)`
(best `m` is the mean, best `z = s²/(s² + D)`). The outlier pair: `s² = 25`, cost `2·25/26 = 1.923`. The
middle five: `s² = 0.02`, cost `5·0.02/1.02 = 0.098`. Total 2.021. `{−5}` alone costs 0, and the other
six have `s² = 3.489`, cost `6·3.489/4.489 = 4.663`.

*Why.* The cost `n·D·s²/(s² + D)` is concave in the spread and never above `nD`, the cost of not
shrinking at all. A group with its own `τ²` can stop shrinking (`z → 1`), so however spread it is, it
costs at most `D` per member. The best use of such a group is to collect outliers from **both** tails,
which leaves the core tightly shrunk. That is a "don't-shrink" bin, not a regime. It is the nesting of Gaussian mixtures
with unequal variances: a wide component takes both tails.

*How often* (150 random cases per world, `k = 2`, share with a non-interval optimum):

| levels | volumes | oracle | likelihood |
|---|---|---|---|
| normal | equal | 1 | 0 |
| two regimes ±1.5 | equal | 0 | 0 |
| heavy tails (t₃) | equal | 12 (gap up to 30%) | 1 |
| normal | spread (`D` over e^±2) | 4 | 0 |

It is rare with normal levels and clear regimes, and appears with heavy-tailed levels. That is the case
where a "group of outliers" is tempting.

## 2. Own means, one common `τ²`: yes (0 of 300, volumes spread)

*Argument (in Lean: `KMeansBridge.groupLoss_eq`, `group_optimal_contiguous`).* For a fixed `τ²` every `zⱼ` is fixed, so the loss is the constant
`Σ uⱼzⱼ²Dⱼ` plus `Σⱼ uⱼ(1 − zⱼ)²(m_{c(j)} − θⱼ)²`. That is a **weighted k-means** cost with weights
`uⱼ(1 − zⱼ)² > 0` and centres `m_g`. So by `KMeans.kmeans_contiguous` an optimal labelling for that `τ²`
has interval groups, and the jointly optimal `(τ², c)` does too, since `c` is optimal for its own `τ²`. Ties as in
Finding 14: a cohort strictly between two members of a group joins it. The centres are the
`(1 − z)²`-weighted means of the levels, i.e. the collective mean of the observed best predictor
(literature §10p). The same weights appear for a different reason here.

*Lean (proved 2026-11-25):* `group_optimal_contiguous`. For fixed `τ² > 0` and `Dⱼ > 0`, the oracle loss is
`Σ uz²D + kmeansCost(u(1 − z)², θ, c, m)`. A minimiser over `(c, m)` has interval groups. This is a corollary
of `kmeans_contiguous`, like `pool_optimal_contiguous`.

## How this differs from Finding 14 (`notes/kmeans-bridge.md`)
Same engine (`kmeans_contiguous`), different problem. Finding 14 **pools** units into cohorts:
weights are the exposures and each cohort costs `+1`, so the number of cohorts is traded off
automatically. Here nothing is pooled: weights `uⱼ(1 − zⱼ)²`, so the noisy cohorts (which lean on
the group mean most) count most; the group means are the `(1 − z)²`-weighted means (the OBP
collective mean, `Core.obpMean`); `Dⱼ` may differ, `τ²` must be common. At the oracle more groups
never hurt (one group per cohort gives the constant `Σ uz²D`), so the number of groups `K` must
come from elsewhere: gain against price (S57).

## For the app and the plan
- A "group the cohorts" step should fit **own means with a common `τ²`**. The groups are then intervals of the sorted
  estimates, found exactly by dynamic programming (`notes/kmeans-bridge.md`, "Finding the cuts"),
  with the number of groups from gain against price and no contiguity weight.
- With a `τ²` per group, the cuts are not enough, and the optimum can be a bin of outliers rather than a regime.
  If the levels look heavy-tailed, treat outliers by robust credibility (literature §10l), not by a group.
- In data the levels are unknown and the sort is by the estimates. The theorem is about true
  levels, as in Finding 14.
- *Checked 2026-11-25 (`studies/obp-mean.js`, S61):* cutting the sorted estimates and choosing the cut by
  SURE is 2–74% worse than one group, in every world tried. Sorting puts the noise into the groups and
  SURE ignores the choice. The same cut of the true levels is −13 to +13%. So the step needs a
  selection-aware criterion first.
