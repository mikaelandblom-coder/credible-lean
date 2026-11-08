# When does merging two cohorts lower the credibility MSE?

A note on the open question in FINDINGS item 6 and README "Later goals →
Choosing cohorts from the data". On paper only, no Lean yet. Numbers are
checked by [`merging_cohorts.py`](merging_cohorts.py).

**Short answer.** It depends on how far apart the pair's true levels are,
$d = \mathbb E(\mu_1-\mu_2)^2$, compared with how precisely the data measure
that gap, $V = \operatorname{Var}(\hat\mu_1-\hat\mu_2)$. It does not depend on
whether $z_1 = z_2$. For two cohorts on their own (the thesis setting of §2.7)
you should merge exactly when

$$
d \;<\; d^\ast = \frac{V\tau^2}{V+\tau^2},
\qquad\text{i.e.}\qquad
\frac1{d} > \frac1V + \frac1{\tau^2},
\qquad V = \sigma_1^2+\sigma_2^2-2\sigma_1\sigma_2\rho .
$$

Correlation enters only through $V$. Positive $\rho$ makes $V$ smaller, so
merging is harder: noise that moves both cohorts the same way cancels in
$\hat\mu_1-\hat\mu_2$, the gap is measured better, and even small true
differences are worth keeping. Negative $\rho$ makes merging easier. Under the
thesis model itself ($\mu_1,\mu_2$ uncorrelated, $d = 2\tau^2$) merging never
pays.

---

## 1. Setting: a two-level model

Notation follows §2.3–2.7: $\hat\mu_j$ is cohort $j$'s inverse-variance
estimate (eq. 23), $\sigma_j^2 = \sigma_{jj}^2$ its error variance (eq. 22), and
$c = \sigma_{12}^2\rho_{12}$ the error covariance. In the two-cohort case of
§2.7 this is $c = \sigma_1\sigma_2\rho$, with $\kappa_j = \sigma_j^2/\tau^2$.

The thesis's data model (eq. 16) has independent cohort levels,
$\mu_j = \mu + \tau\varepsilon_j$. Put the cohorts into groups, as in the
hierarchical model of Bühlmann & Gisler (ch. 6):

$$
\mu_j = \mu + \omega\,\varepsilon_{g(j)} + \tau_w\,\varepsilon_j,
\qquad \tau^2 = \omega^2 + \tau_w^2 ,
$$

where $g(j)$ is the group of cohort $j$. The total variance of a level is still
$\tau^2$. Two cohorts in the same group have

$$
\operatorname{cov}(\mu_1,\mu_2) = \omega^2 = \varphi\,\tau^2,
\qquad d = \mathbb E(\mu_1-\mu_2)^2 = 2\tau_w^2 = 2\tau^2(1-\varphi),
$$

where $\varphi \in [0,1]$ is the share of the level variance the pair has in
common. The two choices in item 6 are the two ends of this range:

| choice | working model | covariance of the levels | $d$ |
|---|---|---|---|
| keep **separate** (the thesis) | $\omega^2 = 0$ | $0$ | $2\tau^2$ |
| **merge** | $\tau_w^2 = 0$, so $\mu_1 = \mu_2$ | $\tau^2$ | $0$ |

The noise covariance $\Sigma = \begin{pmatrix}\sigma_1^2 & c\\ c & \sigma_2^2\end{pmatrix}$
is the same in both. Merging changes only the model for the levels; the data
and their correlation stay the same.

**Loss.** Write $X_j = \hat\mu_j$ and $\theta_j = \mu_j - \mu$. Each rule
predicts $\mu_j$ by a linear $\tilde\mu_j$, built as the best predictor under
its working model, with all second moments known. We compare the true total
MSE $L = \sum_j \mathbb E(\tilde\mu_j-\mu_j)^2$ under the true $\varphi$.

**Two facts that hold in all cases below.**

1. *$L$ is quadratic in the rule.* With $A^\ast$ the best rule for the true
   $\varphi$, $L(A) = L(A^\ast) + \lVert A - A^\ast\rVert^2$ in a positive
   definite norm. So a rule only loses through its distance from $A^\ast$.
2. *For a fixed rule, $L$ is linear in $\varphi$.* $\varphi$ enters only
   through $\operatorname{Cov}(\theta)$, and $L$ is linear in that matrix.

At $\varphi = 0$ the separate rule is the best one, and at $\varphi = 1$ the
merged rule is. By fact 2, $L_{\text{sep}} - L_{\text{merge}}$ is linear in
$\varphi$, so there is one threshold $\varphi^\ast \in (0,1)$:

$$
\text{merge} \iff \varphi > \varphi^\ast .
$$

What remains is to find $\varphi^\ast$. It depends on whether $\mu$ has to be
estimated from the pair (Case A) or is known from the rest of the portfolio
(Case B).

## 2. Case A: the pair on its own (§2.7, $\mu$ estimated)

This is the thesis setting: $J = 2$, and $\mu$ is estimated from the two
cohorts. An unbiased linear predictor of $\mu_1$ has weights summing to one:

$$
\tilde\mu_1 = X_1 - \beta_1\,(X_1 - X_2),
$$

where $\beta_1$ is the weight on the other cohort. The error is
$e_1 - \beta_1\big[(\theta_1-\theta_2) + (e_1-e_2)\big]$. The level gap and
the noise are uncorrelated, so

$$
\mathbb E(\tilde\mu_1-\mu_1)^2
= \sigma_1^2 - 2\beta_1(\sigma_1^2-c) + \beta_1^2\,(V + d).
$$

**Only $d$ enters**, not $\tau^2$ or $\varphi$ separately: with $\mu$
unknown, only the gap between the levels can be seen. The best weight is

$$
\beta_1^\ast(d) = \frac{\sigma_1^2 - c}{V + d}.
$$

*Check against the thesis.* With $d = 2\tau^2$, the weight eq. (32) gives
cohort 2 is $(1-z_1)\,b_2$. Eq. (31) gives
$b_2 = (\sigma_1^2+\tau^2-c)/(V+2\tau^2)$, and eq. (32) gives
$1-z_1 = (\sigma_1^2-c)/(\tau^2+\sigma_1^2-c)$. Their product is
$(\sigma_1^2-c)/(V+2\tau^2)$. So for two cohorts, the thesis estimator *is*
the best predictor under its own model: the one-parameter family $\beta_1$ is
every unbiased linear predictor.

*The merged rule* is $d = 0$: $\beta_1 = (\sigma_1^2-c)/V$, and both cohorts
get the same estimate

$$
\tilde\mu_1 = \tilde\mu_2 = \frac{(\sigma_2^2-c)X_1 + (\sigma_1^2-c)X_2}{V}.
$$

This is the GLS mean with the noise covariance $\Sigma$ alone. It matches
Finding 5: merging adds $\tau^2\mathbf 1\mathbf 1^T$ to $K$, and a rank-one
term along $\mathbf 1$ does not change the GLS weights.

**Excess loss.** By fact 1, a working value $d_w$ costs
$(V+d)\big(\beta_j(d_w) - \beta_j^\ast(d)\big)^2$ in cohort $j$. Summed over
both cohorts:

$$
\Delta L(d_w) = Q\,(V+d)\Big(\frac1{V+d_w} - \frac1{V+d}\Big)^2,
\qquad Q = (\sigma_1^2-c)^2 + (\sigma_2^2-c)^2 .
$$

The factor $Q$ is the same for both rules and for both cohorts, so it drops
out. Write $\zeta(x) = x/(V+x)$. This is the credibility of the observed
difference $X_1 - X_2$ as an estimate of $\mu_1 - \mu_2$ when the gap has
variance $x$. Since $1/(V+x) = (1-\zeta(x))/V$,

$$
\Delta L(d_w) \propto \big(\zeta(d_w) - \zeta(d)\big)^2,
\qquad \zeta_{\text{merge}} = 0,\quad
\zeta_{\text{sep}} = \frac{2\tau^2}{V+2\tau^2}.
$$

> **Result A (midpoint rule).** Merging lowers the total MSE iff
> $\zeta(d) < \tfrac12\zeta_{\text{sep}}$, that is
> $$ d < d^\ast = \frac{V\tau^2}{V+\tau^2}
> \iff \varphi > \varphi^\ast = \frac{V+2\tau^2}{2(V+\tau^2)}
> = \frac{k+2}{2(k+1)},\qquad k = \frac{V}{\tau^2} = \kappa_1+\kappa_2-2\rho\sqrt{\kappa_1\kappa_2}. $$

Assumptions: $\tau^2 > 0$, $V > 0$ (no exact cancellation, i.e. not
$\rho = 1$ with $\sigma_1 = \sigma_2$), and $Q > 0$. Remarks:

- **Both cohorts agree.** The common factor $Q$ means each cohort separately
  prefers the same choice. So the result holds for any positively weighted
  total MSE, e.g. weighted by exposure.
- **$\varphi^\ast \in (\tfrac12, 1)$.** A pair has to share more than half
  its level variance before merging pays. The thesis model ($\varphi = 0$)
  never merges, consistent with eq. (32) being optimal under it.
- **Without correlation:** $V = \sigma_1^2 + \sigma_2^2$, so
  $d^\ast = (\sigma_1^2+\sigma_2^2)\tau^2/(\sigma_1^2+\sigma_2^2+\tau^2)$.
- **With correlation:** $k$ decreases in $\rho$, so $\varphi^\ast$ increases
  in $\rho$ (proved, for fixed $\kappa_1,\kappa_2$). As $V \to 0$
  ($\rho \to 1$, $\sigma_1 = \sigma_2$), $\varphi^\ast \to 1$: if the gap is
  observed exactly, never merge.
- **Equal credibility is irrelevant** (answers item 6): the condition involves
  $V$, $\tau^2$ and $d$ only, not $z_1$ against $z_2$.
- **Finding 3's boundary** $\sigma_1^2 = c$ gives $\beta_1 = 0$ under every
  working model: cohort 1 keeps its own estimate, and only cohort 2 decides.
- **Caveat.** Here $\tau^2$ matters only through $d_{\text{sep}} = 2\tau^2$. If
  $\tau^2$ were estimated from this pair alone (§2.8), $\hat\tau^2$ would
  estimate $d/2$ and the separate rule would be right automatically. The
  question only makes sense when $\tau^2$ is the portfolio-wide variance,
  estimated from many cohorts, and the pair might be closer than a typical
  pair. That leads to Case B.

## 3. Case B: the pair inside a large portfolio ($\mu$ known)

Now there are many other groups, so $\mu$ is effectively known and the rule is
$\tilde\mu = \mu\mathbf 1 + A(X - \mu\mathbf 1)$ with
$A_w = T_w(T_w+\Sigma)^{-1}$, where $T_w$ is the working $\operatorname{Cov}(\theta)$.

- *Separate:* $A_{\text{sep}} = \tau^2(\tau^2 I + \Sigma)^{-1}$. At
  $\rho = 0$ this is $\operatorname{diag}(z_j^B)$, plain Bühlmann–Straub.
- *Merged:* by Sherman–Morrison,
  $$ A_{\text{merge}} = Z_M\,\mathbf 1 w^T,\quad
  w = \frac{\Sigma^{-1}\mathbf 1}{\mathbf 1^T\Sigma^{-1}\mathbf 1},\quad
  Z_M = \frac{\tau^2}{\tau^2 + v},\quad
  v = \frac{1}{\mathbf 1^T\Sigma^{-1}\mathbf 1} = \frac{\sigma_1^2\sigma_2^2 - c^2}{V}. $$
  The merged pair is one Bühlmann risk: the same GLS-pooled estimate $w^TX$
  as in Case A, with noise variance $v$, shrunk toward $\mu$.

By fact 2, $L(A) = L_0(A) + \varphi L_1(A)$ with
$L_0(A) = \operatorname{tr}\big[\tau^2(A-I)(A-I)^T + A\Sigma A^T\big]$ and
$L_1(A) = \tau^2\operatorname{tr}\big[(A-I)E(A-I)^T\big]$, where
$E = \begin{pmatrix}0&1\\1&0\end{pmatrix}$. So

$$
\varphi^\ast = \frac{L_0(A_{\text{merge}}) - L_0(A_{\text{sep}})}{L_1(A_{\text{sep}}) - L_1(A_{\text{merge}})}.
$$

**Closed form, equal $\sigma_j = \sigma$ and $\rho = 0$.** The problem splits
into the sum and difference directions, each a scalar credibility problem.
This gives

$$
\varphi^\ast_B = \frac{1+z^2}{2},\qquad z = \frac{\tau^2}{\tau^2+\sigma^2},
\qquad\text{against}\qquad \varphi^\ast_A = \frac1{2-z}.
$$

Since $(1+z^2)(2-z) - 2 = -z(1-z)^2 \le 0$, we get
$\varphi^\ast_B \le \varphi^\ast_A$: inside a portfolio, merging pays off
sooner. The reason is the pair's common deviation from $\mu$. In Case A it is
absorbed into the estimated $\mu$. In Case B it has to be predicted, and there
the merged model, which gives it variance $2\tau^2$ against the true
$\tau^2(1+\varphi)$, is closer than the separate model ($\tau^2$) as soon as
$\varphi > \tfrac12$.

**With correlation, numerically** (from `merging_cohorts.py`, $\tau^2 = 1$):

| $\kappa_1$ | $\kappa_2$ | $\rho$ | $\varphi^\ast$ pair alone (A) | $\varphi^\ast$ in portfolio (B) |
|---|---|---|---|---|
| 1 | 1 | −0.5 | 0.625 | 0.600 |
| 1 | 1 | 0 | 0.667 | 0.625 |
| 1 | 1 | 0.5 | 0.750 | 0.695 |
| 1 | 1 | 0.9 | 0.917 | 0.837 |
| 4 | 4 | −0.5 | 0.538 | 0.492 |
| 4 | 4 | 0.9 | 0.778 | 0.734 |
| 1 | 16 | 0 | 0.528 | 0.515 |
| 1 | 16 | 0.5 | 0.536 | 0.551 |
| 1 | 16 | 0.9 | 0.546 | 0.628 |

What the numbers show:

- Positive $\rho$ again makes merging harder, by the same mechanism.
- Unlike Case A, $\varphi^\ast_B$ can fall below $\tfrac12$ (down to about
  0.39 on the grid $\kappa_j \in [0.01, 100]$). It is also not always monotone
  in $\rho$: for $\kappa_1=\kappa_2=4$ it is 0.499 at $\rho=-0.9$ and 0.492 at
  $\rho=-0.5$ (35 of 625 grid pairs show such dips, all at negative $\rho$).
- $\varphi^\ast_B \le \varphi^\ast_A$ is not general. For unequal cohorts with
  strong positive correlation (1, 16, 0.5) it reverses. I have no clean
  explanation for this yet.

## 4. What this means for choosing cohorts

- **Merge and separate are the two ends of hierarchical credibility.** The
  best rule for the true $\varphi$ is the two-level (Bühlmann–Gisler)
  estimator, which estimates $\omega^2$ and $\tau_w^2$ and never has to
  choose. The thresholds above say which end is closer to it, in the loss's
  own metric (fact 1). Choosing only matters when a partition is required:
  tariff cells, or clustering as in van Rijn, Weber & Merz.
- **The right distance between cohorts is scaled by $V_{ij}$.** Estimating
  $d$ by $(X_1-X_2)^2 - V$ turns Result A into: merge iff
  $$ (X_1 - X_2)^2 < V + d^\ast = \frac{V(V+2\tau^2)}{V+\tau^2}. $$
  So the natural distance is $|X_i - X_j|/\sqrt{V_{ij}}$, with
  $V_{ij} = \sigma_i^2+\sigma_j^2-2\sigma_{ij}^2\rho_{ij}$. Euclidean
  k-means on credibility estimates uses one scale for all pairs and ignores
  that positively correlated cohorts have more precisely measured gaps. The
  two criteria agree only when all $V_{ij}$ are equal.
- **$d$ and the noise correlation can be told apart.** Noise correlation acts
  only within a period ($\delta_{ts}$ in eq. 16), while level covariance is
  constant over time. The §2.8 estimator of $\sigma_i\sigma_j\rho_{ij}$ uses
  same-period residuals, and $\mathbb E(X_1-X_2)^2 = d + V$ then gives $d$.
- **Winner's curse (open).** The plug-in rule is a pre-test estimator: it
  decides with the same data it then uses. Results A and B are for a choice
  fixed in advance, so they do not give its MSE. With one observation of the
  gap, $(X_1-X_2)^2$ is very noisy (one degree of freedom under normality),
  and pairs that look close by chance get merged. Quantifying this is the
  next step for the README goal.

## 5. Possible Lean targets later

Result A is pure algebra over the reals and fits next to `TwoCohorts.lean`
(e.g. a new `Credibility/Merging.lean`):

- the excess-loss identity
  $\mathbb E(\tilde\mu_1-\mu_1)^2 - \min = (V+d)(\beta-\beta^\ast)^2$;
- `merge_iff`: for $\tau^2 > 0$, $V > 0$, $Q > 0$ and $d \ge 0$,
  $\Delta L(0) < \Delta L(2\tau^2) \iff d\,(V+\tau^2) < V\tau^2$;
- monotonicity of $\varphi^\ast$ in $\rho$.

Case B's closed form for equal $\sigma$ is also short. The general Case B
threshold is better left as a definition plus fact 2 (linearity in $\varphi$).
