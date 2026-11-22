# A fourth-moment layer (draft, 2026-11-22; awaiting the owner's decision)

Status: approved (owner, 2026-11-22), with option (b) below. Built so far in `Credibility/Cumulants.lean`:
the general lemma (`variance_quad_of_cumulants`). Next: the independent-sources corollary, the
third-moment pieces, and the conditional version (b). The owner decides first, because it settles the
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

**Corollary (independent sources).** `x = μ + Bξ` with independent sources `ξₛ`, variances `vₛ`,
cumulants `κ₃ₛ`, `κ₄ₛ`. With `M = BᵀAB` and `a = BᵀAμ`:

    Var(xᵀAx) = 2 tr(AΣAΣ) + 4 μᵀAΣAμ + 4 Σₛ κ₃ₛ aₛ Mₛₛ + Σₛ κ₄ₛ Mₛₛ²,   Σ = B diag(v) Bᵀ.

Checked numerically by exact enumeration (4 cells, 6 three-point sources, symmetric `A`): both
sides 384.3165165313785.

Independent *sources* are enough; independent *years* are not needed (an earlier draft had them as
a corollary, which is too narrow):
- **AR(1) factor.** `fₜ = φfₜ₋₁ + ηₜ` is linear in independent innovations `ηₜ`, so the sources are
  the `ηₜ` and `B` carries the recursion. The factor stays correlated across years. The stationary
  start `f₁` is one more source, with `κₙ(f₁) = κₙ(η)/(1 − φⁿ)`.
- **Within-year shock with a general `C`.** It splits into independent sources only if `C` has a
  factor structure (common plus idiosyncratic parts). Otherwise it is one J-vector source per
  year: give it `κ = 0` (Gaussian-like) or its own J-tensor.
- **Which sources enter.** A source drops out when `Mₛₛ = bₛᵀAbₛ = 0` and `aₛ = 0`, i.e. when the
  estimator cancels its loading. Within-cohort estimators difference out the levels, so level
  cumulants never enter them; between-cohort ones (`Ĉ`, `τ̂²`) do pick them up. So assuming the
  random effects Gaussian-like is weak for some estimators and a real assumption for others.

## Assumptions that cut the DoF (they stack)

The lemma needs none; each assumption only reduces the cumulant numbers to supply. Without any,
`C(n+2,3) + C(n+3,4)` for `n = JT` cells (`J = T = 10`: about 4.6M).
1. **Independent sources** (owner, 2026-11-22: fine in most cases). Cell noise independent across
   years and cells; the shock and the factor carry the common parts. Leaves one `(κ₃, κ₄)` per
   source, i.e. per cell for the noise. Stronger than the core's "uncorrelated": check it with
   the correlation of *squared* residuals across years (volatility clustering), which no
   second-moment check sees.
2. Volume scaling `κₙ = κₙ,unit / w^(n−1)`: one number per cohort and order (`2J`).
3. Common standardized shape `κ₃ⱼ = g σⱼ³`, `κ₄ⱼ = h σⱼ⁴`: 2 numbers.
4. Gaussian-like random effects (levels, shocks, factor): `κ = 0` for them.
5. Elliptical: `κ₃ = 0`, `κ₄ = h·(three pairings)`, 1 number even for a correlated shock; no skew.
6. **Variance function** `V(μ) = μᵖ` with dispersion `φ/w` (Tweedie; literature §10l):
   `κ₃ = (φ/w)² p μ^(2p−1)`, `κ₄ = (φ/w)³ p(2p−1) μ^(3p−2)`, from `κₙ₊₁ = (φ/w) V dκₙ/dμ`.
   No new numbers beyond `p`, since `φ/w` is the noise variance already fitted.
7. Compound Poisson with a severity family (Lomax `α, θ`): 2 numbers, heavy tails explicit;
   fourth moments need `α > 4`.

**Owner's choice (2026-11-22): 1 + 6.** Independent sources, with the noise cumulants from a
variance function, adds only `p`. Points to settle when it is built:
- **Noise and levels are no longer independent.** Under a variance function the noise cumulants
  depend on the cell's own mean `μⱼ`, which is random. Unconditionally the noise is still
  uncorrelated with the level, but not independent, so the independent-sources corollary does not
  apply as is. Either (a) evaluate `V` at the cohort's mean (first order; fine when `τ` is small
  next to `μ`), or (b) prove a conditional version through the law of total cumulance (one more
  lemma, exact). **Owner's choice: (b).**
- **`p` is weakly identified** from one portfolio: `noiseDiagnostics`' cross-fitted `p` has SE ≈ 1.4
  at `τ = 0.1` (PLAN, noise shape). Check `κ̂ⱼ` against the predicted `κ₃` first (PLAN, cumulant
  layer), and show the result for the normal value `p = 0` (`κ₃ = κ₄ = 0`) next to the fitted `p`.
- **No heavy tails.** No variance function gives them (literature §10l); the Lomax world shows
  where 6 breaks.
- Random effects still need 4 (or their own `V`); 6 covers only the noise.
- Fallback with no `κ` at all: a delete-a-year jackknife of the estimator's variance (uses the
  fourth moments implicitly; noisy for small `T`).

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
  the independent-sources corollary, the `Cov` and cubic `E` pieces.
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
