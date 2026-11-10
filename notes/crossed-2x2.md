# Crossed levels: sport car Sweden vs sport car Norway

A note on a possible extension, not in the thesis and not yet in Lean. The
question: can cohorts in different groups share a level, so that Norway's
sport cars inform Sweden's? Numbers are checked by
[`crossed_2x2.py`](crossed_2x2.py).

**Short answer.** Yes, with *crossed* levels instead of nested ones. In the
balanced 2×2 example the best linear predictor is a two-way table with three
credibility factors, one per layer:

$$
\tilde\mu_{at} = \bar X
 + z_c\,(\bar X_{a\cdot}-\bar X)
 + z_t\,(\bar X_{\cdot t}-\bar X)
 + z_i\,(X_{at}-\bar X_{a\cdot}-\bar X_{\cdot t}+\bar X),
$$

country effect, car-type effect and what is left for the cell. The thesis
blend $z X_{at} + (1-z)\bar X$ is the same formula with one common $z$ for the
three layers. It is the best blend, and it is covered by Core already, but it
loses $\sum_k(\lambda_k+\sigma^2)(z-z_k)^2$ against the full predictor and
cannot say anything about a cell without data.

---

## 1. Setting

Four cohorts: the cells (country $a$, car type $t$) with
$a \in \{\text{SE}, \text{NO}\}$ and $t \in \{\text{sport}, \text{family}\}$.
As in §2.3, $X_{at} = \hat\mu_{at}$ is the cell's estimate, with error variance
$\sigma^2$. The levels are

$$
\mu_{at} = \mu + \alpha A_a + \beta B_t + \gamma C_{at},
\qquad \tau^2 = \alpha^2+\beta^2+\gamma^2 ,
$$

with $A_a$, $B_t$, $C_{at}$ uncorrelated, mean 0 and variance 1. Only first
and second moments are assumed, as in the thesis. The level covariance is

| pair of cells | $L_{ij} = \operatorname{cov}(\mu_i,\mu_j)$ |
|---|---|
| same cell | $\tau^2$ |
| same country, other type | $\alpha^2$ |
| same type, other country | $\beta^2$ |
| neither | $0$ |

so $L = \alpha^2[\text{same country}] + \beta^2[\text{same type}] + \gamma^2 I$
and $K = L + \Sigma$. Here $\Sigma = \sigma^2 I$: balanced, uncorrelated noise.

*Relation to the repo.* $\beta^2 = 0$ is Bridge 4 of `Hierarchical.lean` with
the countries as groups ($\varphi\tau^2 = \alpha^2$). $\alpha^2 = \beta^2 = 0$
is the thesis. With both positive the two groupings overlap, so $K$ is not
block diagonal for either.

## 2. The four directions

In a 2×2 table every vector splits into four orthogonal parts:

| part | pattern on (SE sport, SE family, NO sport, NO family) | variance of the level part $\lambda_k$ |
|---|---|---|
| grand mean | $(+,+,+,+)$ | $2\alpha^2+2\beta^2+\gamma^2$ |
| country $c$ | $(+,+,-,-)$ | $\lambda_c = 2\alpha^2+\gamma^2$ |
| type $t$ | $(+,-,+,-)$ | $\lambda_t = 2\beta^2+\gamma^2$ |
| cell (interaction) $i$ | $(+,-,-,+)$ | $\lambda_i = \gamma^2$ |

These are eigenvectors of $L$, and of $K$ with $\sigma^2$ added to each
eigenvalue. So the problem falls apart into four one-dimensional ones.

*GLS mean.* $\mathbf 1$ is an eigenvector of $K$, so $b_j = \tfrac14$ and
$\hat\mu = \bar X$.

*Each other part* is a signal of variance $\lambda_k$ seen with noise
$\sigma^2$, and $\mu$ does not enter it. Its best linear predictor is the
observed part times

$$
z_k = \frac{\lambda_k}{\lambda_k+\sigma^2},
\qquad k \in \{c, t, i\}.
$$

Adding the parts gives the formula in the short answer. It is the best linear
unbiased predictor $\hat\mu\mathbf 1 + LK^{-1}(X-\hat\mu\mathbf 1)$.

**Weights on the four cells.** For Sweden sport:

| cell | full predictor | thesis blend |
|---|---|---|
| SE sport (own) | $\tfrac14(1+z_c+z_t+z_i)$ | $\tfrac14(1+3z)$ |
| SE family | $\tfrac14(1+z_c-z_t-z_i)$ | $\tfrac14(1-z)$ |
| NO sport | $\tfrac14(1-z_c+z_t-z_i)$ | $\tfrac14(1-z)$ |
| NO family | $\tfrac14(1-z_c-z_t+z_i)$ | $\tfrac14(1-z)$ |

Norway sport gets more weight than Sweden family exactly when $z_t > z_c$,
i.e. $\beta^2 > \alpha^2$: car type matters more than country. The opposite
cell can get a *negative* weight. That is the relativity at work:
Sweden sport ≈ Sweden family + Norway sport − Norway family.

## 3. The thesis blend, and what it loses

The thesis form is $\tilde\mu_j = z_jX_j + (1-z_j)\hat\mu$. Core's eq. (26)
for a general level covariance (`Core.levelMoments_bestZ_eq`) gives

$$
z = \frac{L_{jj}-(Lb)_j}{K_{jj}-s^2}
  = \frac{D}{D+3\sigma^2},
\qquad D = \lambda_c+\lambda_t+\lambda_i = 2\alpha^2+2\beta^2+3\gamma^2 .
$$

So $z = \bar\lambda/(\bar\lambda+\sigma^2)$ with
$\bar\lambda = \gamma^2+\tfrac23(\alpha^2+\beta^2)$: the blend uses the
*average* of the three layer variances. Compare $\tau^2$ in the thesis: a
shared part counts for less, as in Bridge 2.

**Total MSE** over the four cells, $\sum_j\mathbb E(\tilde\mu_j-\mu_j)^2$.
The grand-mean part costs $\sigma^2$ for every rule. A layer shrunk by $z$
costs $z^2\sigma^2+(1-z)^2\lambda_k$, which is
$\lambda_k\sigma^2/(\lambda_k+\sigma^2)$ at $z = z_k$. Hence

$$
L_{\text{full}} = \sigma^2 + \sum_k \frac{\lambda_k\sigma^2}{\lambda_k+\sigma^2},
\qquad
L_{\text{blend}} = \sigma^2 + \frac{3\bar\lambda\sigma^2}{\bar\lambda+\sigma^2},
$$

$$
L_{\text{blend}} - L_{\text{full}} = \sum_{k}(\lambda_k+\sigma^2)\,(z-z_k)^2 \;\ge 0 .
$$

This is the same shape as the excess loss in
[`merging-cohorts.md`](merging-cohorts.md): a rule loses through the distance
between its credibility factors and the right ones. The loss is zero exactly
when $\lambda_c = \lambda_t = \lambda_i$, i.e. $\alpha^2 = \beta^2 = 0$: the
thesis.

## 4. Numbers

$\alpha^2 = 1$ (country), $\beta^2 = 4$ (car type), $\gamma^2 = 0.5$,
$\sigma^2 = 2$. Then $z_c = 0.556$, $z_t = 0.810$, $z_i = 0.200$ and the
blend has $z = 0.657$.

| weights for SE sport | SE sport | SE family | NO sport | NO family |
|---|---|---|---|---|
| full predictor | 0.641 | 0.137 | 0.263 | −0.041 |
| thesis blend | 0.743 | 0.086 | 0.086 | 0.086 |

| rule | total MSE |
|---|---|
| raw cell estimates $X_j$ | 8.000 |
| thesis blend, cross terms ignored ($z = \tau^2/(\tau^2+\sigma^2) = 0.733$) | 6.044 |
| thesis blend, best $z$ | 5.943 |
| full predictor | 5.130 |

Getting $z$ right gains little here (6.044 → 5.943). Using the row and column
means gains much more (→ 5.130).

**A cell without data.** Drop Sweden sport. The thesis form has no $X_j$ to
blend, so it can only return the collective mean of the other three (MSE
4.814 for that cell). The full predictor gives

$$
\tilde\mu_{\text{SE sport}}
 = 0.381\,X_{\text{SE family}} + 0.735\,X_{\text{NO sport}} - 0.115\,X_{\text{NO family}},
$$

with MSE 3.575. With no cell effect and no noise ($\gamma^2 = 0$,
$\sigma^2 \to 0$) the weights become $(1, 1, -1)$: the pure additive
relativity.

## 5. Beyond the balanced 2×2

- **Larger tables.** With $n_c$ countries and $n_t$ types, balanced, the same
  formula holds with $\lambda_c = n_t\alpha^2+\gamma^2$,
  $\lambda_t = n_c\beta^2+\gamma^2$, $\lambda_i = \gamma^2$ (checked for 3×4).
  More types make the country effect better known, and the other way round.
- **Equal noise correlation.** With the equicorrelated noise of the thesis
  simulation study, $\Sigma = \sigma^2((1-\rho)I+\rho\mathbf 1\mathbf 1^T)$, the
  four directions stay eigenvectors, and the three $z_k$ are as above with
  $\sigma^2(1-\rho)$ for $\sigma^2$. Positive correlation raises all three:
  common noise cancels in every contrast.
- **Unbalanced cells or general $\rho_{ij}$.** The four directions are no
  longer eigenvectors of $K$. The predictor
  $\hat\mu\mathbf 1 + LK^{-1}(X-\hat\mu\mathbf 1)$ still holds, without a
  closed form by layers.
- **Multiplicative relativities.** Tariffs usually multiply. The model above is
  additive in the key ratio; a multiplicative version is this model on the log
  scale, which the thesis does not treat.

## 6. Estimating the three variances

As in Bridge 5 (`pairHat_unbiasedG`), squared differences of pairs separate
the parts:

| pair | $\tfrac12\mathbb E(X_i-X_j)^2 - \sigma^2$ |
|---|---|
| same country | $\beta^2+\gamma^2$ |
| same type | $\alpha^2+\gamma^2$ |
| neither | $\alpha^2+\beta^2+\gamma^2$ |

Three equations for three unknowns, so $\alpha^2,\beta^2,\gamma^2$ are
identified once $\sigma^2$ is. In a 2×2 table there are only two pairs of each
kind, so the estimates are very noisy: a real
application needs more countries or more types.

## 7. What a formalization would need

1. **A full predictor in Core.** For positive definite $K$ and any level
   covariance $L$: among linear predictors with weights summing to one,
   $\hat\mu\mathbf 1 + LK^{-1}(X-\hat\mu\mathbf 1)$ has the least MSE for every
   cohort, and the excess of any other rule is a quadratic form (fact 1 of
   the merging note). This is new; everything in Core today is about the blend
   form. The setting is there: `Core.Estimates` (`CoreMoments.lean`) has
   estimates and levels with covariances `K` and `L` as random variables.
2. **When is the thesis blend already the full predictor?** For $J = 2$ always
   (merging note, §2). For the thesis $L = \tau^2I$ with correlated noise and
   $J \ge 3$, in general not (the script has an example). An exact condition would be a finding about the
   thesis itself, independent of crossed levels.
3. **The crossed model.** $L$ from two groupings, $K$ positive definite, and
   the layer formula of §2 in the balanced case.
4. **Estimation.** The pair identities of §6, in the style of Bridge 5.

Item 2 is the natural first step: it needs no new model.

*Literature (from memory, to be checked):* the crossed classification
credibility model of Dannenburg, Kaas and Goovaerts, *Practical Actuarial
Credibility Models* (1996); in statistics, mixed models with crossed random
effects.
