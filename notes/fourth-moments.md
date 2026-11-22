# A fourth-moment layer (draft, 2026-11-22; awaiting the owner's decision)

Status: proposal only. No `.lean` file yet. The owner decides first, because it settles the
open question of a third-moment layer (`κ̂ⱼ` in `Engine.noiseDiagnostics`) at the same time.

## Why

Open items need `Var` of quadratic estimators:
- G1: `Wⱼ`, `β²`, and the ratio `ρ̂` with `σ̃ⱼ` plugged in (delta method needs `Var`, `Cov`);
- G2: the `V` in `θ* = Σs²/(Σs² + ΣV)` is the variance of the off-diagonal `ĉᵢⱼ` (the app plugs in
  normal-theory `V`);
- G4: the best pair weights for `φτ²` minimise a variance;
- Wen & Liu (2026), Zhao & Poudyal (2026) (literature §10l) need the same.

The second-moment core gives `E` of any quadratic form (`Expectation.integral_quad_of_mean`).
`Var` needs moments up to order four, and the cross term needs order three.

## The lemma (one statement, then corollaries)

Random cells `x` with mean `μ`, covariance `Σ`, centred `e = x − μ`. Third and fourth cumulant
tensors
`κ₃(i,j,k) = E[eᵢeⱼeₖ]`,
`κ₄(i,j,k,l) = E[eᵢeⱼeₖeₗ] − ΣᵢⱼΣₖₗ − ΣᵢₖΣⱼₗ − ΣᵢₗΣⱼₖ`.
For a symmetric `A`:

    Var(xᵀAx) = 2 tr(AΣAΣ) + 4 μᵀAΣAμ + 4 Σᵢⱼₖ (Aμ)ᵢ Aⱼₖ κ₃(i,j,k) + Σᵢⱼₖₗ Aᵢⱼ Aₖₗ κ₄(i,j,k,l).

Idea: `xᵀAx − E = 2μᵀAe + (eᵀAe − tr AΣ)`. Square it and take the expectation: the linear part gives
the `μ` term, the cross term is a third moment, and the quadratic part is a fourth moment minus its
three Gaussian pairings. No independence is assumed. Gaussian data: both cumulant terms vanish
(Isserlis), which leaves the classical `2tr(AΣ)² + 4μᵀAΣAμ`.

**Corollary 1 (independent years).** If the year blocks `x₍·ₜ₎` are independent, `κ₃` and `κ₄`
vanish unless all indices are in the same year. Then the cumulant terms are sums over years.

**Corollary 2 (independent sources).** `x = μ + Bξ` with independent sources `ξₛ` (the levels,
each year's shock and each cell's noise), variances `vₛ`, cumulants `κ₃ₛ`, `κ₄ₛ`. With `M = BᵀAB`
and `a = BᵀAμ`:

    Var(xᵀAx) = 2 tr(AΣAΣ) + 4 μᵀAΣAμ + 4 Σₛ κ₃ₛ aₛ Mₛₛ + Σₛ κ₄ₛ Mₛₛ²,   Σ = B diag(v) Bᵀ.

This is the form the models use. It only needs one third and one fourth cumulant per source, for
example `κ₄ = 0` for Gaussian-like random effects and the variance function or compound Poisson
cumulants for the noise (PLAN "Cumulant layer"). Checked numerically by exact enumeration
(4 cells, 6 three-point sources, symmetric `A`): both sides 384.3165165313785.

## The third-moment pieces (same file, same tensors)

- `Cov(xᵀAx, bᵀx) = 2 μᵀAΣb + Σ κ₃(i,j,k) Aᵢⱼ bₖ`: the Finding 35 bias `Σᵢ cov(d̂ᵢ, μ̂ᵢ)` for quadratic
  weights, and its first-order skew correction (PLAN, noise shape step 2).
- `E` of a cubic form from `μ`, `Σ`, `κ₃`: proves `κ̂ⱼ` in `noiseDiagnostics` unbiased (only checked in
  Node now).
So one layer "cumulants up to order four" covers both the third-moment question and the
fourth-moment one. A separate third-moment layer would only be its first half.

## Proposed placement (if approved)

- `Credibility/Cumulants.lean` (moment layer, distribution-free: the cumulants are *defined* from
  the moments, nothing assumed about the family): the tensor statement as "`Vquad` is the actual
  variance of any random vector with `L⁴` cells", in the style of `integral_quad_of_mean`, then
  Corollaries 1 and 2, the `Cov` and cubic `E` pieces.
- Fits the core rule: still no distribution assumed, only more moments. A variance-function or
  compound Poisson choice of the `κₛ` stays in its own file (distribution/cumulant layer).
- First users: the exact `V` in G2 (`Damping.lean` takes it as a given number), the variance of
  `Q̂ᵢⱼ` for G1 and the best pair weights in G4 (a GLS problem in the pair covariances).

## Literature

Standard result. Gaussian case: Searle (1971), *Linear Models*, §2.5; Searle, Casella &
McCulloch (1992), *Variance Components*, Appendix S (from memory). Non-normal with independent
components: Atiqullah (1962, JRSS B 24) and Seber & Lee (2003), *Linear Regression Analysis*,
Thm 1.6 (equal moments), from memory. MINQUE variance under non-normality with kurtosis:
Rao & Kleffe (1988), *Estimation of Variance Components and Applications*, ch. 5 (from memory).
Cumulant expansions of products of quadratic forms: Bao & Ullah, *Expectation of quadratic forms
in normal and nonnormal variables with econometric applications* (found 2026-11-22). See
`studies/literature.md` §10l.
