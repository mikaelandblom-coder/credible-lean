# Blending experience and exposure rating for an XoL layer

Discussion notes (owner and Claude, 2026-11-19). Nothing proved yet, and no
literature search done yet (owner: not needed at this stage). References
mentioned from memory, still to check: Patrik & Mashitz (1990), credibility
for treaty excess pricing; Clark, *Credibility for a tower of excess layers*
(Variance, 2011); Parodi & Bonche (2010), uncertainty-based credibility for XoL.

## 1. Setup: it is thesis eq. (7)

For one treaty and one layer the target is the true layer loss cost `μ`. There
are two estimates of it:

- **experience** `μ̂_exp`: the layer cost from an MLE fit to the claims. It is
  unbiased for this cedent but noisy, with variance `V` from Fisher
  information and the delta method through the layer-cost function;
- **exposure** `μ̂_expo`: from a rating tool (market curves and risk profile).
  It has little noise but misses this cedent's own deviation from the curve,
  with spread `τ²` across cedents.

The blend `z μ̂_exp + (1 − z) μ̂_expo` is minimised by eq. (7),
`BlendMoments.bestZ` (`Credibility/Blend.lean`), which is already proved for
any covariances. If the two estimates are independent, `z = τ² / (τ² + V)`.

Their covariance `c` is nonzero when both share an exposure base or
on-levelling, when the curve was calibrated partly on this cedent's claims,
or when an expert anchored on the claims (§2). Eq. (7) handles that; the
independent formula would count the same information twice.

How it maps onto the repo:
- **two estimators, one layer**: `Blend.bestZ`; a known bias of the tool is
  covered by `BlendMoments.shift`;
- **a tower of layers**: experience in adjacent layers shares claims, so the
  layers are correlated. The matrix blend covers this (`CoreVector.lean`:
  vector levels, matrix `Z`);
- **several years of experience**: trend and development make the years
  correlated. That is an off-diagonal `K` (`Core`);
- **estimating `τ²`**: cedents or treaties as cohorts, using the §2.8 moment
  estimators (§3).

What would be new: a small model file that builds these moments, with the
blend as a one-line corollary of `bestZ`. `V` from the MLE assumes a severity
family (e.g. Pareto), so it belongs in the optional distribution layer: its
own file, named "under Pareto severity". The core blend stays
distribution-free.

## 2. When the tool is pure expert judgment

The maths doesn't change: the blend needs only the exposure estimate's error
variance and its covariance with experience, not how the estimate was made.
Two things weigh more with an expert, though:

- **Shared bias.** Write the exposure error as `b + δᵢ`: `b` is common to the
  whole book (an expert is often off in the same direction on every treaty)
  and `δᵢ` is treaty-specific. `τ²` is `Var(δᵢ)` only. The bias `b` must be
  estimated and removed separately, as in the balance step (§2.9).
- **Anchoring on the claims.** An expert who has seen the claims makes
  `c > 0`, which moves `z` away from `τ²/(τ² + V)`.

## 3. Estimating `τ²` without a back-test of the tool

No history of the tool is needed, only many treaties that each have both
numbers now. Take the gap `dᵢ = μ̂_exp,i − μ̂_expo,i`. Then

    E[dᵢ] = b,    Var(dᵢ) = τ² + Vᵢ − 2cᵢ.

- **The cross-section of the current book.** `d̄` estimates `b`, and the
  average of `(dᵢ − d̄)² − Vᵢ + 2cᵢ` estimates `τ²`. This is the §2.8 moment
  estimator with unequal `Vᵢ` (`UnequalEstimation`). The only cost is running
  the tool, or the expert, on the treaties priced anyway; a sample of 20–30
  is a start.
- **Layers within one treaty.** A tower gives several gaps per treaty. They
  are correlated through shared claims, so they need a joint `K`
  (`CoreVector`). Thin on its own, but it adds to the cross-section.
- **Going forward.** Log the tool's output at every pricing. Each year of
  actual layer losses is then a further gap, where the variance subtracted is
  the process variance instead of `Vᵢ`.

## 4. When there is truly nothing

Then `τ²` can't come from data, and no `z` is optimal. A hand-set `τ²`
breaks the "no hand-set hyperparameters" rule (`studies/PLAN.md` §1), so
treat it as an explicit, temporary fallback, not part of the fitted model:

- **elicit the expert's uncertainty** (e.g. an 80% interval for the layer
  cost); experts are usually overconfident, so calibration methods from the
  expert-elicitation literature (e.g. Cooke) apply;
- **robust `z`**: choose `z` to minimise the worst-case MSE (or the worst
  relative loss) over a plausible range of `τ²`. Probably closed-form; a
  candidate small Lean extension;
- **updating**: the fallback gives way to the estimator of §3 as gaps
  accumulate.

## 5. Open questions (possible findings)

- Does plugging in an estimated `τ²` bias the blend? This is known in
  small-sample EBLUP work; check it for the XoL setting, especially when `τ̂²`
  and `μ̂_exp` use the same claims.
- The robust `z` of §4: its closed form and whether it is worth a Lean file.
- How to estimate `cᵢ` when an expert anchored on the claims.
- App: does it need an "experience against exposure" scenario? Not yet noted
  in `studies/PLAN.md`.
