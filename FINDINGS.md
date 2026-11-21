# Findings

Gaps, extra hypotheses and new results found while formalizing.

1. **Positive-definiteness of `K`.** After eq. (20) the thesis says "since
   `K` is a covariance matrix it is positive definite". A covariance matrix
   is only positive *semi*definite; `K` is positive definite here because
   `τ² > 0` and the correlations `ρ` form a positive-semidefinite matrix
   (`Model.K_posDef`).
2. **At least two cohorts.** With `J = 1` we get `b = 1` and `s² = τ² + σ²`,
   so eq. (26) is `0/0`. The thesis never assumes `J ≥ 2`, but the reduction
   to Bühlmann–Straub (`bs_z`, end of §2.6) needs it.
3. **Credibility above one (sharpened).** The thesis (§2.7) notes that
   `z₁ > 1` can happen and clips it in eq. (34), without saying when. In the
   two-cohort case `z₁ = τ² / (τ² + σ₁² - σ₁σ₂ρ)`, so below the singularity
   `z₁ > 1` exactly when `σ₁ < σ₂ρ` (`TwoCohorts.z1_gt_one_iff`).
   *Proved.* Below the singularity the denominator `τ² + σ₁² - σ₁σ₂ρ` is
   positive, so `z₁ > 1` iff `σ₁² < σ₁σ₂ρ`. The proof never uses `τ² > 0`:
   the condition is independent of the between-cohort variance.
4. **Weights from credibility factors (new, two cohorts only).** For two
   cohorts the GLS weight is `b₁ = z₁ / (z₁ + z₂)` (`TwoCohorts.b1_eq_z`,
   *proved*), the same form as Bühlmann–Straub's `b_j = z_j / z_*`. This is
   on the defence slides but not in the published thesis. So any binary
   split of a portfolio (two segments of a rating factor) keeps the classical
   weight formula under correlation. It fails for `J ≥ 3`: numerically with
   random `σⱼ`, `ρᵢⱼ` (e.g. `b = (0.536, 0.226, 0.238)` against
   `z/z_* = (0.564, 0.177, 0.259)`), and exactly for `τ² = 1`, one period,
   `σⱼ = 1`, `ρ₁₂ = 1/4`, `ρ₁₃ = ρ₂₃ = 0` (`Model.exists_b_ne_z`, *proved*).
   It also fails for equal correlations `ρᵢⱼ = ρ` when the `σⱼ` differ:
   `ρᵢⱼ = 1/2`, `σ = (1, 1, 2)` (`Model.exists_b_ne_z_equalCorr`, *proved*).
   Both via the converse of item 5. For `J ≥ 3` the right condition is
   item 5.
5. **Equal covariances (new, any `J`).** If all cohort pairs have the same
   covariance `σ²ᵢⱼρᵢⱼ = c`, then `bⱼ = zⱼ/z_*` and the proposed factor is
   `zⱼ = τ²/(τ² + σ²ⱼⱼ - c)`, i.e. eq. (32) with `σ₁σ₂ρ` replaced by `c`
   (`Model.b_eq_of_equalCov`, `Model.bestZ_of_equalCov`, *proved*). Reason:
   `K = diag(dⱼ) + c·11ᵀ`, and a rank-one term along `u` does not change the
   direction of `K⁻¹u`. Bühlmann–Straub is `c = 0`, two cohorts are
   `c = σ₁σ₂ρ`. Extra hypotheses: `τ² + σ²ⱼⱼ ≠ c` (the singularity of
   Finding 3, now per cohort) and `bⱼ ≠ 1` (`0/0`, as in Finding 2).
   *Converse.* `bⱼ = zⱼ/z_*` for all `j` iff some `λ`
   gives `Σᵢ≠ⱼ (Kᵢⱼ + λ) bᵢ = 0` for every `j` (⇒ in Lean,
   `Core.exists_shift_of_b_eq_z`, with `λ = τ²/z_* − s²`; ⇐ on paper). For
   `J = 3` with all `bⱼ ≠ 0` this forces equal covariances: the three
   conditions are a linear system in the `Kᵢⱼ + λ` with determinant
   `2b₁b₂b₃` (`Model.equalCov_of_b_eq_z`, *proved*). For `J ≥ 4` it does not
   (on paper, not in Lean): with equal `σⱼ`,
   any correlation matrix with equal row sums gives `b = z/z_* = u/J`
   (e.g. `J = 4`, off-diagonal covariances `0.5, -0.1, 0.2, 0.2, -0.1, 0.5`).
6. **Equal credibility is not grouping (discussion, no Lean).** Under
   equal covariances (item 5), `bⱼ = zⱼ/z_*`, so cohorts with the same `z`
   get the same weight. The collective estimate `μ̂ = Σ bⱼ μ̂ⱼ` then sees them
   only through the sum of their `μ̂ⱼ`: pooling them is lossless for `μ̂`.
   But this is not the grouping that clustering (e.g. arXiv:2611.07110) is
   after. (a) Equal `z` means equal reliability (`σ²ⱼⱼ`), not equal risk:
   cohorts with `μ̂ⱼ = 0.5` and `1.5` keep different premiums
   `zμ̂ⱼ + (1-z)μ̂`. (b) Putting `i`, `j` in one risk group means assuming
   `μᵢ = μⱼ`, so their covariance goes from `0` to `τ²`. That changes `K`,
   every `z` and `μ̂`. Open question: when does merging two cohorts
   lower the total MSE? Probably it depends on the data, not on `zᵢ = zⱼ`.
   Natural setting: two-level (hierarchical) credibility, cohorts nested in
   groups (Bühlmann & Gisler, ch. 6). See `notes/roadmap.md` §5.
   *Partly answered (`notes/merging-cohorts.md`; the pair-alone result is
   proved in `Credibility/Merging.lean`, `merge_iff`).* With
   `d = E(μ₁-μ₂)²` and `V = Var(μ̂₁-μ̂₂) = σ₁² + σ₂² - 2σ₁σ₂ρ`, for a pair
   on its own (§2.7, `μ` estimated) merging lowers the total MSE iff
   `d < Vτ²/(V+τ²)`, i.e. `1/d > 1/V + 1/τ²`. Correlation enters only via
   `V`: `ρ > 0` makes merging harder. Equal `z` plays no role, and under
   the thesis model (`d = 2τ²`) merging never pays. Inside a large
   portfolio (`μ` known) the threshold is lower (equal `σ`, `ρ = 0`:
   merge iff the shared share of level variance `φ > (1+z²)/2`, against
   `1/(2-z)` for the pair alone); it has no simple general form. Open: the
   winner's curse when the merge is decided from the same data.
7. **Estimation needs `T ≥ 2` and `J ≥ 2`; a typo in eq. (13).** The
   §2.8 estimators (eq. (39)) are unbiased (`Estimation.sigRhoHat_unbiased`,
   `tauHat_unbiased`, `KHat_unbiased`, *proved*), but the thesis never states
   the sample sizes they need. With `T = 1` the denominator of the
   `σ²ᵢⱼρᵢⱼ` estimator is `Sᵢⱼ - wᵢ*wⱼ*/Sᵢⱼ = 0` (`Sᵢⱼ = √(wᵢ₁wⱼ₁)`); with
   `J = 1` the denominator of `τ̂²` is `w** - w** = 0`. Bühlmann–Straub needs
   the same, so this is a gap in the statement, not in the method. On the
   diagonal the estimator is `σ̂ⱼ²/wⱼ*` (eq. (41), `sigRhoHat_self`).
   Unrelated typo: eq. (13) averages the Bühlmann–Straub `σ̂ⱼ²` with `1/T`,
   but there are `J` of them, so it should be `σ̂² = (1/J) Σⱼ σ̂ⱼ²`. Lean
   does not touch eq. (13); `sigRhoHat_self` only uses `σ̂ⱼ²`.

8. **Unequal lengths keep `K` positive definite (new).** With
   cohort `j` observed in `Tⱼ ⊆ T` (an open goal at the time; notes in
   `notes/unequal-lengths.md`), `Kᵢⱼ = σ²ᵢⱼρᵢⱼ + τ²δᵢⱼ` still holds with
   `σ²ᵢⱼ` summed over `Tᵢ ∩ Tⱼ`, and `K ≻ 0` for any overlap pattern as soon
   as, for each period `t`, the correlations of the cohorts observed at `t`
   form a PSD block (`Unequal.K_posDef`). That is weaker than `ρ ⪰ 0`: with
   `T₁ = {1}`, `T₂ = {1,2}`, `T₃ = {2}`, `ρ₁₂ = ρ₂₃ = 0.9`, `ρ₁₃ = −0.9`,
   `ρ` is not PSD but `K` is PD. *Proved* (`K_posDef`, `K_posDef_of_posSemidef`).
9. **The `T − 2` of eq. (39) becomes a volume-weighted per-pair count
   (new).** With unequal lengths the unbiased denominator of the
   `σ²ᵢⱼρᵢⱼ` estimator is `Sᵢⱼ + nᵢⱼwᵢ*wⱼ*/Sᵢⱼ` (sums over `Tᵢⱼ = Tᵢ ∩ Tⱼ`)
   with `nᵢⱼ = |Tᵢⱼ| − ωᵢ − ωⱼ`, `ωᵢ = Σ_{Tᵢⱼ} wᵢₜ/wᵢ*` the share of cohort
   `i`'s volume inside the overlap. The naive `|Tᵢⱼ| − 2` is biased unless
   `Tᵢ = Tⱼ`. Checked exactly against the data covariance for a random
   3-cohort pattern. One shared period `t` suffices if both cohorts are also
   observed elsewhere: the denominator is then
   `(wᵢ*wⱼ*/Sᵢⱼ)(1 − ωᵢ)(1 − ωⱼ) > 0`, which sharpens the `T ≥ 2` of item 7
   (`Unequal.den_of_overlap_singleton`, `sigRhoHat_unbiased`,
   `tauHat_unbiased`, `KHat_unbiased`, *proved*).

10. **Balance survives unequal lengths (new).** In the Bühlmann–Straub case
   (`σⱼₜ = σ/√wⱼₜ`, `ρᵢⱼ = δᵢⱼ`) with cohort `j` observed in `Tⱼ`, the
   proposed factor is `zⱼ = wⱼ*/(wⱼ* + σ²/τ²)` with `wⱼ* = Σ_{t∈Tⱼ} wⱼₜ`,
   `bⱼ = zⱼ/z*`, and `Σⱼ wⱼ*(1 − zⱼ)(μ̂ⱼ − μ̂) = 0` for all data: the
   thesis proof (§2.9) only uses `wⱼ*(1 − zⱼ) = κzⱼ` cohort by cohort.
   Equivalently, `Σⱼ Σ_{t∈Tⱼ} wⱼₜμⱼₜ = Σⱼ Σ_{t∈Tⱼ} wⱼₜμ̂ⱼᵇ`. Also, Finding 5
   for unequal lengths: equal covariances with one disjoint pair force
   `c = 0` (`Unequal.balance`, `balance_total`, `equalCov_eq_zero`,
   `bestZ_of_equalCov`, *proved*).

11. **The results are distribution-free, and `ρ ⪰ 0` is free too (new).**
   For any probability space and any square-integrable `ηⱼ`, `εⱼₜ` with
   the moments of eq. (15), eqs. (16) and (21) are the actual covariances,
   the weights (23)–(24) are optimal in actual variance, and `zⱼ` of eq.
   (7)/(26) minimises the actual mean squared error of the blend. Such
   random variables exist iff `ρ` is positive semidefinite, so the
   hypothesis Finding 1 adds for `K ≻ 0` is not an extra assumption: it
   holds whenever the model is consistent at all (`Model.Noise.mse_blend`,
   `bestZ_mse_optimal`, `exists_noise_iff`, *proved*).

12. **Unequal lengths: distribution-free, and the block condition is free (new).**
   With cohort `j` observed in `Tⱼ` and moments assumed only on observed
   cells, `K` (on `Tⱼ`) is the actual covariance of the `μ̂ⱼ`, the weights
   are optimal in actual variance, and `zⱼ` minimises the actual mean
   squared error. Such random variables exist iff, for every period `t`,
   the correlations of the cohorts observed at `t` are positive
   semidefinite: exactly the hypothesis of Finding 8. So `K ≻ 0` comes for
   free whenever the model is consistent, and correlations of cohorts that
   never share a period are unconstrained (Finding 8's example with
   `ρ₁₃ = −0.9` is realisable) (`Unequal.Noise.mse_blend`,
   `bestZ_mse_optimal`, `Unequal.exists_noise_iff`, *proved*).

13. **With group levels, `τ̂²` is biased by the within-group pairs (new).**
   Let the cohort levels share `φτ²` within groups and nothing across them
   (`cov(μᵢ, μⱼ) = τ²`, `φτ²` or `0`). Then the thesis estimator (39) has
   `E τ̂² = τ² − φτ²π`, with `π` the share of same-group pairs among pairs of
   distinct cohorts, weighted by `wᵢ*wⱼ*`. It lands between the non-shared
   part `(1−φ)τ²` (one group, `π = 1`) and `τ²` (singleton groups, `π = 0`).
   So the plug-in `K̂` estimates the `K` the within-group weights need
   exactly when there is one group (`φ ≠ 0`). With two or more groups it
   overstates the within-group level variance by `φτ²(1−π)`. Pairs fix it:
   `(μ̂ᵢ − μ̂ⱼ)²` minus its noise estimate is unbiased for `2(1−φ)τ²` within a
   group and `2τ²` across groups, so `φτ²` is identifiable from one pair of
   each kind. The one-group case is the shared level of Bridge 3, where `φ`
   is not identifiable (`tauHat_unbiasedG`, `KHat_unbiasedG_iff`,
   `pairHat_unbiasedG`, `phiTauHat_unbiasedG`, *proved*). Distribution-free:
   `Noise.integral_quad` makes `Unbiased` the actual expectation.

14. **Optimal cohorts are intervals for pooling, and for the blend with a
   common variance, but not in general (new; positive halves proved:
   `pool_optimal_contiguous`, `blend_optimal_contiguous`).** Units with fixed levels `xᵢ` and uncorrelated estimates of
   variance `vᵢ` are grouped into at most `k` cohorts, each pooled by inverse
   variance. The exposure-weighted total MSE `Σ wᵢ MSEᵢ` (`wᵢ = 1/vᵢ`) is
   exactly the weighted k-means cost of the levels plus the number of
   cohorts, so by `kmeans_contiguous` the optimal cohorts are intervals of
   the sorted levels, for any `vᵢ`. Common variance is the special case. With
   unequal `vᵢ` this fails for the unweighted MSE (`x = (-1, 0, 0.2, 0.25,
   1.5)`, `v = (16, 1/16, ½, 4, 2)`: optimum `{1,2,4}{3,5}`, with or without
   a cap on `k`) and for a credibility blend towards a known `μ`, weighted or
   not (`x = (-½, 0, ½)`, `μ = 0`, `τ² = ½`, `v = (16, ½, 16)`, at most two
   cohorts: `{1,3}{2}` has MSE 0.680, the best intervals 0.742). The noisy
   middle cohort sits at `μ` and is better served by the collective than by
   a neighbour. With a common variance the blend's optimal cohorts are
   intervals again (`blend_optimal_contiguous`, a swap argument: the loss
   depends on a cohort only through its size `n` and sum `S`, as
   `-f_n S² + z_n²V` with `f_n > 0`). Details: `notes/kmeans-bridge.md`.
15. **The best balanced blend: closed form, but a poor way to balance (new;
   `Core.bestBalanced_optimal`, `bestBalanced_cost`,
   `Estimates.bestBalanced_mse_optimal`).** Keep the GLS weights `b` and ask
   for the factors `z` that minimise `Σⱼ φⱼ MSEⱼ` subject to exposure balance
   `Σⱼ uⱼ(μ̂ⱼ − μ̂ⱼᵇ) = 0` (PLAN G7). By `balanced_iff` the balanced blends are
   the line `zⱼ = 1 − c·bⱼ/uⱼ`, and each `MSEⱼ` is the parabola
   `MSEⱼ(zⱼ*) + gⱼ(zⱼ − zⱼ*)²` (`gⱼ = Var(μ̂ⱼ − μ̂)`), so the optimum is a
   one-number weighted least squares: `c* = Σφg(1 − z*)a / Σφga²` with
   `aⱼ = bⱼ/uⱼ`, at a cost `S₀ − S₁²/S₂` over the unconstrained blend (zero iff
   that blend is already balanced). It needs no sign on `b`, so it covers
   correlation, and holds in true MSE for any distribution. But the line
   fixes the *shape* `1 − zⱼ ∝ bⱼ/uⱼ`: big cohorts are forced to `z ≈ 1`, small
   ones far from `zⱼ*` (even `z < 0`). In the 19 worlds of the app's study
   (`studies/vc-balance.js`) it costs up to 96% more error than the floor,
   where shifting all rates by the same amount (Wang–Fuller–Qu 2008) costs at
   most 41%; both cost nothing at `ρ = 0` with equal `σⱼ`. These numbers are
   exact, not simulated: both corrections are linear rules with the true `K`,
   so their MSE is a formula in the second moments (`studies/exact-balance.js`,
   tested in `app/engine.test.js`; the simulation gave 103% and 46%). They
   still depend on the worlds chosen. Balance should be
   restored by a common shift, not by bending `z`: the shift is outside the
   blend class.

16. **The common shift is the best balanced correction only without
   correlation (new; `Core.bestCorrection_optimal`, `commonShift_optimal`,
   `imbalanceCov_of_diag`, `Estimates.commonShift_mse_optimal`).** PLAN G7b
   asked whether shifting every blend by `D/Σuᵢ`, with imbalance
   `D = Σuᵢ(μ̂ᵢ − μ̂ᵢᵇ)`, is the best balanced correction of the form
   `θ̂ⱼ = μ̂ⱼᵇ + cⱼD` (balanced iff `Σuⱼcⱼ = 1`) for the loss `Σⱼ uⱼ MSE(θ̂ⱼ)`, as in
   Wang–Fuller–Qu. As stated it is false. `MSE(θ̂ⱼ) = MSEⱼ + 2cⱼκⱼ + cⱼ²V` with
   `κⱼ = cov(μ̂ⱼᵇ − μⱼ, D)` and `V = Var D`. The best `c` is
   `cⱼ* = (λuⱼ/φⱼ − κⱼ)/V`, and for `φ = u` it is the shift exactly when `κⱼ`
   is the same for all `j`. WFQ get this from `κ = 0`, which holds when the
   base predictor is the BLUP. Our blend is the BLUP for independent
   cohorts (`K` diagonal, `L = τ²I`), and then `κ = 0` (`imbalanceCov_of_diag`);
   in general only under the column condition of Finding 18.
   Counterexample under correlation: three cohorts, `τ² = 1`,
   `v = (0.5, 1, 3)`, `ρ = 0.5`, `u = (3, 2, 1)`, optimal `z`. Then
   `κ = (0.099, 0.183, 0.026)`, `c* = (0.177, 0.121, 0.227)` against `1/6`,
   loss `5.237` against `5.249` for the shift (checked by simulation). So the
   theorem is proved with the hypothesis "`κⱼ` constant". In 2000 random
   worlds (3–7 cohorts, `ρ ≤ 0.95`) the shift was never more than 2.2% worse
   than `c*`, and `c*` needs `κ`, i.e. fitted `K` and `L`. The shift stays the
   app's balance step.

17. **The blend is continuous through the two-cohort singularity
   (Lean: `TwoCohorts.bestZ_mul_one_sub_b1`,
   `Core.abs_bestZ_mul_norm_le`, `Core.abs_bestZ_mul_one_sub_le`).** Finding 3 and the thesis (§2.7,
   eq. (34)) treat the sign flip of `z₁` at `ρ* = (τ² + σ₁²)/(σ₁σ₂)` as a
   breakdown and clip `z₁` to `[0, 1]`. But the gap is
   `μ̂₁ − μ̂ = (1 − b₁)(μ̂₁ − μ̂₂)` and `τ² + σ₁² − s² = Var(μ̂₁ − μ̂) =
   (1 − b₁)²D` with `D = Var(μ̂₁ − μ̂₂) = σ₁² + σ₂² + 2τ² − 2σ₁σ₂ρ > 0`, so
   `z₁(μ̂₁ − μ̂) = (τ²/D)(μ̂₁ − μ̂₂)` and the best blend is
   `μ̂₁ᵇ = (b₁ + τ²/D) μ̂₁ + (b₂ − τ²/D) μ̂₂`, smooth in `ρ` on all of
   `|ρ| < 1`. At `ρ*` the GLS weight `b₁` passes through 1 (so `μ̂ = μ̂₁`)
   and the gap changes sign; `z₁` flips with it. Only at `ρ*` itself the blend
   family degenerates (every `z` gives `μ̂₁`), and the limit from both sides
   is not reached. Example (thesis §2.7.2: `κ₁ = 1`, `κ₂ = 16`, `τ² = 1`):
   `ρ = 0.49`, `0.51` give `z₁ = 25`, `−25` but coefficients on
   `(μ̂₁, μ̂₂)` of `(1.064, −0.064)`, `(1.070, −0.070)`; `ρ = 0.75` gives
   `z₁ = −1`, coefficients `(1.154, −0.154)`. So with the true parameters a
   negative `z₁` is the best blend, not an error; clipping it to 0 charges
   `μ̂`, which past `ρ*` already overshoots `μ̂₁`. In a fitted model an
   extreme `z` still signals a near-singular `K̂`. In Lean:
   `TwoCohorts.bestZ_mul_one_sub_b1`, `z₁(1 − b₁) = τ²/D` away from `ρ*`.
   *Reporting without the singularity (owner, 2026-11-16).* Keep `z` (the
   classical quantity, all results stated in it) and report next to it the
   own-data weight `cⱼ = bⱼ + zⱼ(1 − bⱼ)`, the coefficient of `μ̂ⱼ` in the
   blend. It is bounded for any `J`: `zⱼ(eⱼ − b)` has norm at most
   `τ²/λ_min(K)`, since `zⱼ = (1 − bⱼ)τ²/Var(gap)`, `|1 − bⱼ| ≤ |eⱼ − b|` and
   `Var(gap) = (eⱼ − b)ᵀK(eⱼ − b) ≥ λ_min|eⱼ − b|²` (checked in 20000 random
   worlds, `J = 2..6`: worst ratio 0.91). In Lean, with `xᵀKx ≥ m‖x‖²` for a
   given `m > 0` in place of `λ_min`: `Core.abs_bestZ_mul_norm_le`, and
   `|cⱼ − bⱼ| ≤ τ²/m` as `Core.abs_bestZ_mul_one_sub_le`; with `m = λ_min(K)`
   (Rayleigh bound from the spectral theorem):
   `Core.abs_bestZ_mul_norm_le_eigenvalues`, `Core.abs_bestZ_mul_one_sub_le_eigenvalues`. Example above:
   `c₁ = 1.000, 1.038, 1.064, 1.070, 1.154` at `ρ = 0.25, 0.4, 0.49, 0.51,
   0.75`. For `J = 2` also `ζ₁ = z₁(1 − b₁) = τ²/D`, the factor on
   `μ̂₁ − μ̂₂`; for `J ≥ 3` comparing with the reweighted rest
   `Σᵢ≠ⱼ bᵢμ̂ᵢ/(1 − bⱼ)` moves the singularity to `bⱼ = 1`, so `cⱼ` is the
   general choice. `zⱼ` is singular only at `b = eⱼ` (`K ≻ 0`), which for
   `J ≥ 3` needs all other weights zero. `cⱼ` differs from `zⱼ` in meaning:
   at `ρ = 0` in the example `z₁ = 0.5`, `c₁ = 0.947`. Restrict the blend,
   not `z`, if anything.

18. **The blend against the best linear unbiased predictor (new;
   `Core.blupWeight_optimal`, `Core.errVar_eq_blupWeight_add`,
   `Core.exists_blendWeight_eq_blupWeight_iff`,
   `Core.Estimates.blup_mse_optimal`, `Core.Estimates.mse_blend_eq_blup_add`).**
   The thesis optimises `z` inside the family `z μ̂ⱼ + (1 − z) μ̂`. The
   classical benchmark is wider: all `Σᵢ dᵢ μ̂ᵢ` with `Σᵢ dᵢ = 1` (unbiased
   for any common mean), the homogeneous credibility estimator, i.e. the BLUP
   of Goldberger (1962). With `ℓᵢ = cov(μⱼ, μ̂ᵢ)` (row `j` of `L`) its weights
   are `d* = K⁻¹ℓ + (1 − 1ᵀK⁻¹ℓ) b`, and any unbiased weights `d` have
   `MSE(d) = MSE(d*) + (d − d*)ᵀK(d − d*)`. So the blend with weights
   `w = z eⱼ + (1 − z) b` pays exactly `(w − d*)ᵀK(w − d*)`. The blend *is*
   the BLUP iff `Lⱼᵢ − z Kᵢⱼ` is the same for every `i`
   (`Core.blendWeight_eq_blupWeight_iff`). For the thesis's `L = τ²I`: iff
   cohort `j` has the same covariance `c ≠ Kⱼⱼ` with every other cohort
   estimate, and then `z = τ²/(Kⱼⱼ − c)`. That holds always for two cohorts
   (so §2.7 loses nothing), for equal covariances (Finding 5) and for
   independent cohorts; it corrects the "only for independent cohorts" of
   Finding 16. Otherwise the blend is strictly worse. Example (as in
   Finding 16: `τ² = 1`, `v = (0.5, 1, 3)`, `ρ = 0.5`, optimal `z`): MSE of
   the blend `0.4961, 0.8668, 1.5492` against `0.4827, 0.8404, 1.5470` for
   the BLUP, i.e. 2.8%, 3.1%, 0.1% above. The BLUP weights for cohort 1 are
   `(0.974, 0.079, −0.052)` against the blend's `(0.960, 0.032, 0.008)`: it
   uses the other cohorts individually, some with negative weight. With the
   true `K` the price of the blend is small here; whether the BLUP survives
   estimation of `K` (it needs every `K̂ᵢⱼ`, the blend only `b̂` and `ẑ`) is
   a question for the app (PLAN, Pending). All statements are
   distribution-free, in true MSE.

19. **What ignoring correlation can cost (new; `Core.linMse_blupWeight_working_le`,
   `Core.linMse_ignoreCorr_le`, `Core.linMse_ignoreCorr_le_of_offDiag`,
   `Core.Estimates.ignoreCorr_mse_le`).** Bühlmann–Straub on correlated cohorts
   is the best linear unbiased predictor of a wrong model, `K̃ = diag(τ² + vᵢ)`
   (`Core.blupWeight_diag_eq_blendWeight`: the blend with `z = τ²/(τ² + vⱼ)` and
   inverse-variance weights). With `K = τ²I + V`, `L = τ²I` and `δ` the spectral
   norm of the noise correlation matrix minus `I`
   (`|yᵀVy − Σ vᵢyᵢ²| ≤ δ Σ vᵢyᵢ²`), its mean squared error is at most
   `1/(1 − δ²)` times the smallest, whatever `τ²` and the `vᵢ`. The proof is
   Kantorovich's: the true and working variances of every `Σ dᵢμ̂ᵢ − tμⱼ`
   are within factors `1 ∓ δ`, and Wielandt's inequality turns that into
   `(a + A)²/(4aA)` for the predictor (`linMse_blupWeight_working_le`, any working
   model). If every correlation is at most `r`, `δ ≤ (J − 1)r`; for two cohorts
   the factor is `1/(1 − ρ²)` and nearly attained (`ρ = 0.5`: bound 1.333, worst
   of 20000 random worlds 1.316). Checked in 15689 random worlds with `δ < 1`
   (`J = 2..7`): never violated, worst ratio of excess to bound 0.81. The
   bound is weak for many equicorrelated cohorts (`J = 3`, `ρ = 0.5` gives
   `δ = 1`). Exact cost in the Finding 16 example (`τ² = 1`,
   `v = (0.5, 1, 3)`, `ρ = 0.5`): 14.3%, 9.2%, 0.4% above the minimum, against
   2.8%, 3.1%, 0.1% for the blend restriction (Finding 18). So with true
   parameters the correlation matters more than the blend form; whether
   estimating it pays is the fitted-model question of the studies (S6 in `studies/damping-theta.md`).

20. **Equal correlations: the sharp price of ignoring or damping them (new;
   `Core.linMse_damped_le`, `Core.linMse_ignoreCorr_le_two_sided`,
   `Core.linMse_damped_equicorr_le`, `Core.linMse_ignoreCorr_equicorr_le`,
   `Core.Estimates.damped_mse_le`).**
   Question (owner): the proof of Finding 19 only uses directions `(d̃* + uh, 1)`
   with `Σ hᵢ = 0`, so is the large eigenvalue `1 + (J − 1)r` of an equicorrelated
   noise correlation needed, or does `δ = r` (bound `1/(1 − r²)`) suffice? **No**:
   the correlation acts on `√vᵢ hᵢ`, which need not sum to zero, and as `τ² → 0`
   nothing else dampens it. Counterexample: `J = 3`, `r = 0.5`, `τ² = 0.001`,
   `v = (1, 1000, 30)`: ratio 1.561 > 4/3. What does hold, and is sharp: Kantorovich
   with the two eigenvalues separately, `a = 1 − δ₋`, `A = 1 + δ₊`, giving
   `(2 + δ₊ − δ₋)²/(4(1 − δ₋)(1 + δ₊))`; for equal correlations `δ₋ = r`,
   `δ₊ = (J − 1)r`, so `(2 + (J − 2)r)²/(4(1 − r)(1 + (J − 1)r))`, finite for every
   `r < 1` (`J = 3`, `r = 0.5`: 1.5625; `J = 2`: `1/(1 − r²)` again). Numerically the
   worst case over `τ²`, `v`, `j` equals this bound to four digits (`J = 2..7`,
   `r` up to 0.9; attained as `τ² → 0`). A working model that damps the noise
   correlations by `θ ∈ [0, 1]` (`shrinkOffDiag`) has `a = (1 − δ₋)/(1 − θδ₋)`,
   `A = (1 + δ₊)/(1 + θδ₊)`; checked on 80000 random cases (equicorrelated and
   general correlation matrices), never violated, attained. Halfway damping at
   `J = 3`, `r = 0.5` cuts the worst case from 56% to 12.5%.

21. **A known trend moves no weight, but an estimated one moves relativities (new;
   `Unequal.K_detrend`, `Unequal.bestZ_detrend`, `Unequal.Noise.relativity_detrend`).**
   Planning claim (`notes/time-trends.md` §1 step 2): "relativities `μ̂ⱼ/μ̂` do not
   depend on `g`, so `ĝ` only moves the overall level, never the ranking or `z`".
   True for the world's `g` when the data are restated with that same `g`
   (constant CV): `K̃ = (1+g)^(2n) K`, so `a`, `b`, `z` are unchanged and every
   estimate is `(1+g)^n` times the untrended one. **False for an estimate
   `ĝ ≠ g`**: the leftover factor `((1+g)/(1+ĝ))^t` varies with the year, so it
   reweights old against recent data within each cohort. Counterexample: two
   cohorts, two years, equal `σ`, `ρ = 0`, data `(2, 1)` and `(1, 2)`; restated
   with `r = 1+ĝ`, `μ̂₁/μ̂₂ = (2r+1)/(r+2)`: 1 at `ĝ = 0`, 1.032 at `ĝ = 10%`.
   What survives for any `ĝ`: `a`, `b`, `z` do not depend on it (`bestZ_detrend`
   holds for every `g`), and the target year never matters. `ĝ` is a pure level
   shift only when all cohorts' data have the same time profile.

22. **Vector credibility beats separate credibility only as a predictor, not as a blend
   (new; `CoreVector.blupW_optimal`, `CoreVector.errVar_eq_blupW_add`,
   `CoreVector.trace_linMse_blupW_le_separate`).** Planning target
   (`notes/time-trends.md` §2): "the vector blend's MSE ≤ the separate blends' (each is a
   restricted linear predictor), via `bestZ_optimal` restricted to diagonal `Z`". The route
   fails: separate blends use their own portfolio estimate per component (scalar GLS on
   `K_F`, `K_Y`), not the matrix GLS `μ̂` of the vector blend, so they are not a diagonal-`Z`
   vector blend. They coincide only if `K` has no covariance between components, and in the
   compound model `K = L + N` that forces `Λ` diagonal, where the two are equal anyway. **The
   statement is false with correlated cohorts.** Counterexample: three cohorts, independent
   levels `L = I ⊗ Λ`, `Λ = [[2, 1], [1, 4]]` (frequency, severity), compound noise
   (no frequency–severity covariance) correlated across cohorts,
   `N_F = [[5, 2, 1], [2, 1, 1], [1, 1, 5]]`, `N_Y = [[2, 1, 2], [1, 1, 1], [2, 1, 3]]`,
   `K = L + N`, cohort 2. Summed MSE: vector blend (matrix GLS, `Z*`)
   `819884/414757 ≈ 1.9768`, separate blends (scalar GLS and best `z` per component)
   `649/329 ≈ 1.9726`: the frequency MSE is `0.9768` against `0.9726`. What is true is the
   classical statement one level up: the matrix best linear unbiased predictor
   `A* = K⁻¹LEⱼ + W(I − UᵀK⁻¹LEⱼ)` beats every unbiased linear predictor in the Loewner
   order, so both blends (here `2455/1351 ≈ 1.8172`), and the matrix blend loses exactly
   `(A − A*)ᵀK(A − A*)` against it (the matrix Finding 18). Numerically (random search, not
   proved): with independent cohorts or two cohorts the vector blend never lost (there it is
   the predictor, as in Finding 18), so the gap needs correlated cohorts and three or more
   of them; with `L = I ⊗ Λ` it is small. As Bühlmann (1974) found for one risk, restricted
   predictors are not ordered: don't claim an order between the vector and separate blends.

23. **A common period shock does not shrink with volume; the thesis's fixed `ρᵢⱼ` makes it
   shrink (new; modelling remark, no Lean statement affected).** Eq. (16) gives
   `cov(μᵢₜ, μⱼₜ) = σᵢₜσⱼₜρᵢⱼ` with `ρᵢⱼ` fixed over periods, and §2.8 (eqs. (37)–(41)) takes
   `σⱼₜ² = σⱼ²/wⱼₜ`. Then the covariance between cohorts falls like `1/√(wᵢₜwⱼₜ)`: doubling
   both volumes halves it. The motivating shock (travel demand, thesis §2.2) hits a cohort's
   rate whatever its size, so its covariance should not fall. The natural model is a shock
   plus process noise, `cov(μᵢₜ, μⱼₛ) = δₜₛ(Cᵢⱼ + δᵢⱼ sᵢ²/wᵢₜ) + τ²δᵢⱼ`, with `C ⪰ 0` (rank one,
   `λᵢλⱼ`, for one shock with loadings); its correlation *rises* with volume. It equals eq. (16)
   only if the correlation may depend on the period, `ρᵢⱼₜ = Cᵢⱼ/(σᵢₜσⱼₜ)`, with
   `σⱼₜ² = Cⱼⱼ + sⱼ²/wⱼₜ`. Counterexample (no fixed `ρ` fits): two cohorts, two periods,
   `C = 11ᵀ`, `s = 1`, `w₁ = (1, 4)`, `w₂ = (1, 1)`: `σ₁ₜ² = (2, 1.25)`, `σ₂ₜ² = (2, 2)`,
   implied `ρ₁₂ₜ = (0.5, 0.632)`; and `σ₁₁²/σ₁₂² = 1.6`, not the `w₁₂/w₁₁ = 4` of §2.8.
   What is unaffected: every result stated for a general positive definite `K` (Core), and
   the Lean model, whose `σⱼₜ` are free numbers (only `ρᵢⱼ` is period-free). What changes:
   the §2.8 estimators assume `σⱼ²/wⱼₜ` with a fixed `ρ`, so with growing or shifting volumes
   they misweight the cross products. Equivalent if each cohort's volume is constant over
   time. The shock model is a new `obsCov` table: its `K`, positive definiteness
   (`C ⪰ 0` plus a positive diagonal) and unbiased estimators of `C` and `s²` are the work;
   the expectation layer (`Ecov`, `UnbiasedCov` for a general table) already applies.
   Econometrics names it a common factor with loadings (`studies/literature.md` §9).
   **In Lean (2026-11-19, `Credibility/Shock.lean`).** For any cohort weights summing to one,
   `Kᵢⱼ = (Σₜ aᵢₜaⱼₜ)Cᵢⱼ + δᵢⱼ(sᵢ²Σₜ aᵢₜ²/wᵢₜ + τ²)` and `K ≻ 0` (`Shock.K_apply`,
   `Shock.K_posDef`); `bestZ` is the Core formula (`Shock.bestZ_eq`). Same-period residual
   cross products estimate `Cᵢⱼ`, `i ≠ j`, without bias (`Shock.crossHat_unbiased`). On the
   diagonal a squared residual mixes `Cⱼⱼ` and `sⱼ²`; two weightings of the squared residuals
   separate them by Cramer's rule (`Shock.CdiagHat_unbiased`, `Shock.s2Hat_unbiased`) when a
   2×2 determinant is nonzero. That needs volume variation: with a constant volume no
   estimator is unbiased for `sⱼ²` (`Shock.not_unbiased_s2_of_const`), and with `T = 2` the
   residuals of a cohort are proportional, so the determinant is `0` for any weightings.
   With exposure weights and weightings `1` and `w`, the determinant is negative once
   `T ≥ 3` and the volumes vary (`Shock.det_expo_neg`, 2026-11-20): `Δⱼwⱼ*² = -F`, and
   `2F = Σᵢₖ (wᵢ-wₖ)²/(wᵢwₖ)((W-wᵢ-wₖ)² + Q-wᵢ²-wₖ²)` is a sum of nonnegative terms
   (`two_mul_detGap_eq`, `detGap_pos`); comparing pair by pair fails, the identity does not.
   Moment layer (`Credibility/ShockMoments.lean`): for any random cells with this table, `K` is
   the actual covariance, `zⱼ` minimises the true MSE and `E K̂ = K` (`Shock.Cells.toEstimates`,
   `Shock.Cells.bestZ_mse_optimal`, `Shock.Cells.integral_KHat`).

24. **The season does not drop out of the 12-month predictor, even with whole years (new;
   `notes/card-data.md` Step 2).** Expected at first: for a 12-month target and cards observed
   in whole years, an estimated additive season (one fixed effect per calendar month) leaves
   the predictor unchanged. False. The seasonal predictor equals the one-mean predictor iff the
   one-mean `d*` already puts weight `cₘ` (here `1`) on each month (`Season.blup_eq_iff`, from
   `Core.blup_eq_blup_iff_of_nested`). Counterexample (`Season.blup_ne_of_volume`): one card,
   two years of two months, independent noise with twice the volume in the first month,
   `K = diag(1, 2, 1, 2)`, `ℓ = 0`: the one-mean `d* = (2/3, 1/3, 2/3, 1/3)` puts `4/3` on the
   first month. With a real season `β` it is biased by `Σₘ (Sₘ(d*) - cₘ)βₘ = (β₁ - β₂)/3`
   (`Core.Target.integral_bias`). What holds: the season drops out when the months are
   interchangeable, some relabelling of the cells maps any month onto any other and leaves `K`
   and `ℓ` unchanged (`Season.blup_eq_of_interchangeable`); seasonal volume, an AR(1) factor
   that favours recent months, or a card entering mid-year all break that. So with a season,
   fit it (or a known index, `Unequal.a_eq_of_volume`); the one-mean predictor leans on the
   high-volume months.

25. **Positive autocorrelation does not keep the weights positive (new; `notes/card-data.md`
   Step 3).** Common factor model `cov(Xᵢₜ, Xⱼₛ) = λᵢλⱼΓₜₛ + δₜₛCᵢⱼ + δₜₛδᵢⱼsᵢ²/wᵢₜ + τ²δᵢⱼ`
   (`Credibility/Factor.lean`, `K ≻ 0` for any observed cells: `Factor.K_posDef`). Expected:
   per-month weights can be negative under an AR(1) factor. True, and already with positive
   autocorrelation and a balanced panel (`Factor.blup_neg_of_ar1`): two cards observed in
   months `0, 1`, AR(1) `Γₜₛ = φ^|t-s|` with `φ = 1/2`, loadings `1`, `C = 0`, `s²/w = 1/2`,
   `τ² = 1`, one common mean. The best predictor of card 0 in month 2 has weights
   `(11/30, 8/15, -1/30, 2/15)` on `(0,0), (0,1), (1,0), (1,1)` (`Factor.blup_exAR1`). Why:
   card 1's change `X₁₁ - X₁₀` tracks the factor's latest value, which persists into month 2,
   without card 1's own level. With one card the weights stayed positive in our numerical
   checks (AR(1) plus noise, `φ = ±1/2`), so the negative weight comes from borrowing the
   factor from other cards. Pinquet (2020) gives nonnegative partial autocorrelations as
   sufficient for nonnegative weights for per-risk AR effects; with a common factor across
   cards that condition does not carry over. Practice: negative weights are a feature of the
   best predictor here, not a fitting error; a predictor restricted to nonnegative weights
   (like the thesis blend) gives this up.

26. **The shock fit absorbs only part of a persistent factor (new; `notes/card-data.md`
   Step 5, literature §10h item 3).** Fitting `Shock` (`Ĉ` from within-card residuals
   `rⱼₜ = Xⱼₜ - Σₛaⱼₛ Xⱼₛ`) to data from the factor model: each residual product picks up
   `λᵢλⱼ(eₜ - aᵢ)ᵀΓ(eₜ - aⱼ)` (`Factor.res_unbiased`), so for `i ≠ j` `Shock.crossHat` is
   unbiased for `Cᵢⱼ + λᵢλⱼΣₜ(eₜ - aᵢ)ᵀΓ(eₜ - aⱼ)/Σₜdᵢⱼₜ` (`Factor.crossHat_factor_unbiased`).
   Expected: biased for `C`. Found: also biased for the lag-0 covariance `C + γλλᵀ`
   whenever the factor persists. Two months, equal weights, AR(1) `γφ^|t-s|`: `Ĉᵢⱼ`
   estimates `Cᵢⱼ + (1 - φ)γλᵢλⱼ` (`Factor.crossHat_ar1_two`). The two ends: `φ = 0` gives
   `C + γλλᵀ` (the factor is a rank-one shock, as in `obsCov_eq_shock_loadings`), and a
   constant factor (`φ = 1`) gives `C` (demeaning removes it). Why: subtracting each card's
   own mean removes the part of the factor shared by all its months. Practice: a shock fit
   on data with a persistent demand factor gives a `K̂` that is neither the shock nor the
   lag-0 covariance, and its lagged covariances (`ℓ` for the next year) are `0` where the
   truth has `λλᵀΓ(h)`. Fit the factor (`FactorEstimation`, year-on-year cross-products)
   rather than reading it off the shock. The level estimate is affected too: the
   between-cohort spread gains `ΣⱼxⱼvⱼᵀΓvⱼ`, `vⱼ = λⱼaⱼ - Σᵢxᵢλᵢaᵢ`, which with equal weights
   `aⱼ = α` is `Σⱼxⱼ(λⱼ - λ̄)²·αᵀΓα` (`Factor.between_factor_equal_weights`): unequal loadings
   look like heterogeneity `τ²`, as do per-card dynamics (`Σₖxₖ(1 - xₖ)αᵀGₖα`).
   The diagonal (2026-11-21): each `Σₜuⱼₜrⱼₜ²` gains
   `Fⱼ(u) = Σₜuⱼₜ(λⱼ²(eₜ - aⱼ)ᵀΓ(eₜ - aⱼ) + (eₜ - aⱼ)ᵀGⱼ(eₜ - aⱼ))`, so `Ĉⱼⱼ` and `ŝⱼ²` are off by
   the Cramer combinations of `Fⱼ(u)`, `Fⱼ(v)` (`Factor.CdiagHat_factor_unbiased`,
   `s2Hat_factor_unbiased`), and `τ̂²` by the spread's term minus the plugged-in biases of `Σ̂`
   (`Factor.tauHat_factor_unbiased`). A persistent factor is not constant in `t` after
   demeaning, so it leaks into `ŝ²` too (it is told apart from the shock only by the
   volume pattern, which the factor does not follow). With independent months the factor is
   a rank-one shock: `Ĉⱼⱼ` reads `Cⱼⱼ + γλⱼ²`, `ŝⱼ²` stays unbiased (`Factor.CdiagHat_s2Hat_indep`).

Equation numbers refer to `thesis/original/main.tex` as compiled.
