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
   (`studies/runs/vc-balance.js`) it costs up to 96% more error than the floor,
   where shifting all rates by the same amount (Wang–Fuller–Qu 2008) costs at
   most 41%; both cost nothing at `ρ = 0` with equal `σⱼ`. These numbers are
   exact, not simulated: both corrections are linear rules with the true `K`,
   so their MSE is a formula in the second moments (`studies/runs/exact-balance.js`,
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
   estimating it pays is the fitted-model question of the studies (S6 in `studies/LOG.md`).

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
   `notes/card-data.md` Step 2).** Expected at first: for a 12-month target and cohorts observed
   in whole years, an estimated additive season (one fixed effect per calendar month) leaves
   the predictor unchanged. False. The seasonal predictor equals the one-mean predictor iff the
   one-mean `d*` already puts weight `cₘ` (here `1`) on each month (`Season.blup_eq_iff`, from
   `Core.blup_eq_blup_iff_of_nested`). Counterexample (`Season.blup_ne_of_volume`): one cohort,
   two years of two months, independent noise with twice the volume in the first month,
   `K = diag(1, 2, 1, 2)`, `ℓ = 0`: the one-mean `d* = (2/3, 1/3, 2/3, 1/3)` puts `4/3` on the
   first month. With a real season `β` it is biased by `Σₘ (Sₘ(d*) - cₘ)βₘ = (β₁ - β₂)/3`
   (`Core.Target.integral_bias`). What holds: the season drops out when the months are
   interchangeable, some relabelling of the cells maps any month onto any other and leaves `K`
   and `ℓ` unchanged (`Season.blup_eq_of_interchangeable`); seasonal volume, an AR(1) factor
   that favours recent months, or a cohort entering mid-year all break that. So with a season,
   fit it (or a known index, `Unequal.a_eq_of_volume`); the one-mean predictor leans on the
   high-volume months.

25. **Positive autocorrelation does not keep the weights positive (new; `notes/card-data.md`
   Step 3).** Common factor model `cov(Xᵢₜ, Xⱼₛ) = λᵢλⱼΓₜₛ + δₜₛCᵢⱼ + δₜₛδᵢⱼsᵢ²/wᵢₜ + τ²δᵢⱼ`
   (`Credibility/Factor.lean`, `K ≻ 0` for any observed cells: `Factor.K_posDef`). Expected:
   per-month weights can be negative under an AR(1) factor. True, and already with positive
   autocorrelation and a balanced panel (`Factor.blup_neg_of_ar1`): two cohorts observed in
   months `0, 1`, AR(1) `Γₜₛ = φ^|t-s|` with `φ = 1/2`, loadings `1`, `C = 0`, `s²/w = 1/2`,
   `τ² = 1`, one common mean. The best predictor of cohort 0 in month 2 has weights
   `(11/30, 8/15, -1/30, 2/15)` on `(0,0), (0,1), (1,0), (1,1)` (`Factor.blup_exAR1`). Why:
   cohort 1's change `X₁₁ - X₁₀` tracks the factor's latest value, which persists into month 2,
   without cohort 1's own level. With one cohort the weights stayed positive in our numerical
   checks (AR(1) plus noise, `φ = ±1/2`), so the negative weight comes from borrowing the
   factor from other cohorts. Pinquet (2020) gives nonnegative partial autocorrelations as
   sufficient for nonnegative weights for per-risk AR effects; with a common factor across
   cohorts that condition does not carry over. Practice: negative weights are a feature of the
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
   constant factor (`φ = 1`) gives `C` (demeaning removes it). Why: subtracting each cohort's
   own mean removes the part of the factor shared by all its months. Practice: a shock fit
   on data with a persistent demand factor gives a `K̂` that is neither the shock nor the
   lag-0 covariance, and its lagged covariances (`ℓ` for the next year) are `0` where the
   truth has `λλᵀΓ(h)`. Fit the factor (`FactorEstimation`, year-on-year cross-products)
   rather than reading it off the shock. The level estimate is affected too: the
   between-cohort spread gains `ΣⱼxⱼvⱼᵀΓvⱼ`, `vⱼ = λⱼaⱼ - Σᵢxᵢλᵢaᵢ`, which with equal weights
   `aⱼ = α` is `Σⱼxⱼ(λⱼ - λ̄)²·αᵀΓα` (`Factor.between_factor_equal_weights`): unequal loadings
   look like heterogeneity `τ²`, as do per-cohort dynamics (`Σₖxₖ(1 - xₖ)αᵀGₖα`).
   The diagonal (2026-11-21): each `Σₜuⱼₜrⱼₜ²` gains
   `Fⱼ(u) = Σₜuⱼₜ(λⱼ²(eₜ - aⱼ)ᵀΓ(eₜ - aⱼ) + (eₜ - aⱼ)ᵀGⱼ(eₜ - aⱼ))`, so `Ĉⱼⱼ` and `ŝⱼ²` are off by
   the Cramer combinations of `Fⱼ(u)`, `Fⱼ(v)` (`Factor.CdiagHat_factor_unbiased`,
   `s2Hat_factor_unbiased`), and `τ̂²` by the spread's term minus the plugged-in biases of `Σ̂`
   (`Factor.tauHat_factor_unbiased`). A persistent factor is not constant in `t` after
   demeaning, so it leaks into `ŝ²` too (it is told apart from the shock only by the
   volume pattern, which the factor does not follow). With independent months the factor is
   a rank-one shock: `Ĉⱼⱼ` reads `Cⱼⱼ + γλⱼ²`, `ŝⱼ²` stays unbiased (`Factor.CdiagHat_s2Hat_indep`).

27. **Cohort-specific means hide the cohort level from invariant estimators (new; `notes/card-data.md`
   Step 5).** Expected: Henderson III / MINQUE given the shape (`Factor.henderson_factor_unbiased`)
   estimates `τ²` with the other parameters whenever the basis tables are independent and the
   design has full rank. Found: no. The cohort-level table `I ⊗ 11ᵀ` is `DEDᵀ` for the cohort season
   `D` (`Factor.shapeBasis_tau_eq_cohortSeason`), and a table in the span of the design gets weight
   `0` from every form with `QD = 0` (`Model.hendersonMat_det_eq_zero_of_design`), so every
   invariant system is singular (`Factor.hendersonMat_cohortSeason_det_eq_zero`). The right
   condition for MINQUE is independence of the projected tables `RVₖR`
   (`Model.minque_det_ne_zero_iff`); minimal counterexample: one cohort, two months, a common mean,
   tables `I` and `11ᵀ` (`Factor.exists_independent_singular`). Practice: under cohort-specific
   means fit `(A, C, s², g)` without `τ²`; `τ²` is the spread of what the design already
   estimates, so it is not needed for prediction with those fixed effects.

28. **Under a cohort season the covariance is seen only through repeated calendar months (new;
   `notes/card-data.md` Step 5).** Expected: dropping `τ²` (Finding 27) leaves a nonsingular
   Henderson III / MINQUE system for `(A, C, s², g)` given volume variation and `Γ₀ ≠ I`.
   Found: further collapses. Invariant forms see tables only modulo `{YDᵀ}`
   (`Model.hendersonMat_det_eq_zero_of_mod_design`), and under the cohort season the tables that
   see only cohort and calendar month are `DFDᵀ` (`Factor.classTable_eq_cohortSeason`). (a) One
   year of data (one cell per cohort and calendar month): every unbiased quadratic estimator has
   expectation `0`, nothing is estimable (`Factor.unbiasedMean_cohortSeason_eq_zero`). (b) A
   factor shape `Γ₀ = aI + g(mon t, mon s)`, e.g. AR(1) at `φ = 1` (a constant factor, which
   demeaning removes, as in Finding 26) or at `φ = 0` (against `C`, as before), or any shape
   that repeats with the calendar: `A_z - aC_z` is invisible, singular for every invariant form
   (`Factor.hendersonMat_cohortSeason_det_eq_zero_of_shape`). (c) Per-card dynamics `G₀` of that
   form: `gⱼ` against `aCⱼⱼ` (`Factor.hendersonMat_cohortSeason_det_eq_zero_of_shapeG`). Practice:
   fit second moments under a cohort season only with at least two years per cohort, and with
   factor shapes that decay within the year; check the rank of the projected tables
   (`Model.minque_det_ne_zero_iff`) rather than hoping for a general condition. A general
   sufficient condition for nonsingularity: see Finding 29.

29. **With two years, `s²` needs volumes that vary over the calendar, not only across years
   (new; `notes/card-data.md` Step 5).** Expected: under a cohort season, two years, AR(1) with
   `0 < φ < 1` and volume variation make MINQUE for `(A, C, s²)` nonsingular. Found: true with
   the right kind of volume variation. Sufficient (`Factor.minque_cohortSeason_det_ne_zero`, any
   number of cohorts, any prior `W ≻ 0`): one nonzero year-on-year double difference of `Γ₀`
   (for AR(1): `2φ - φ¹¹ - φ¹³ > 0`, `Factor.minque_ar1_two_years_det_ne_zero`), and for every
   cohort `1/wⱼ,₍₀,ₘ₎ + 1/wⱼ,₍₁,ₘ₎` not constant over the calendar month `m`. The second condition
   is needed: if it is constant for one cohort (e.g. its volume changes only from one year to
   the next, or is the same each year in every month), `2Vₛⱼ - hV_Cⱼⱼ` is `YDᵀ + DYᵀ`, within
   each calendar month `diag(x, -x)`, and MINQUE is singular for every prior and every shape
   (`Factor.minque_cohortSeason_det_eq_zero_of_volume`). The reason: with two years the only
   contrasts are the year-on-year differences, which see the process noise only through
   `1/wⱼ,₍₀,ₘ₎ + 1/wⱼ,₍₁,ₘ₎`. With three or more years the diagonal `diag(1/wⱼ)` within a
   calendar month is no longer of the form `u1ᵀ + 1uᵀ` (argued, not formalized). Dropping `τ²`
   costs nothing: the estimators stay unbiased whatever `τ²` (`Factor.henderson_season_unbiased`,
   `Model.UnbiasedMean.add_design`). Practice: with two years, check that each cohort's volume
   has a within-year pattern; otherwise report `Cⱼⱼ + sⱼ²h/2` for that cohort.
30. **Valid fitted tables need `ŝ² > 0` for `K̂ ≻ 0`, and are not a factor model (new;
   `studies/PLAN.md`, valid tables).** Expected: the app's constrained tables (`Â ⪰ 0`, `Ĉ ⪰ 0`,
   `ŝ² ≥ 0`) give `K̂ ≻ 0` by `Factor.K_posDef`. Found: that theorem does not apply, for two
   reasons. The projection of `γλλᵀ` onto the positive semidefinite cone need not be rank one,
   and the premium leaves `τ²` out. The general table `Aᵢⱼ Φₜₛ + δₜₛCᵢⱼ + δ sᵢ²/wᵢₜ` is positive
   definite for any `A ⪰ 0`, `Φ ⪰ 0`, `C ⪰ 0` and every `sⱼ² > 0`, without `τ²`
   (`Factor.tableK_posDef`, AR(1): `tableK_ar1_posDef`); `Factor.K_posDef` is now its corollary.
   But the projection only gives `ŝ² ≥ 0`: a cohort whose `Âⱼⱼ`, `Ĉⱼⱼ`, `ŝⱼ²` are all clipped to
   `0` has cells of variance zero and `K̂` is singular (`Factor.tableK_not_posDef`). Practice:
   check `ŝⱼ² > 0` after the projection (the app's Cholesky fails otherwise and gives no premium).

31. **Equal loadings and the same months do not make the factor drop out of relativities; the
   month weights must match (new; `notes/card-data.md` Step 4).** Expected: with equal loadings
   and cohorts observed in the same months the common factor cancels from cohort relativities.
   Found: any linear statistic (or predictor error) `Σ aX` has, under the factor model, the
   factor-free variance plus exactly `gᵀΓg`, `gₜ = Σⱼ λⱼaⱼₜ` (`Factor.quadTab_eq`; true variance:
   `Factor.Cells.variance_lin_eq`). For the relativity `z(μ̂ⱼ - Σᵢ bᵢμ̂ᵢ)` with `μ̂ᵢ = Σₜ αᵢₜXᵢₜ`,
   `gₜ = z(λⱼαⱼₜ - Σᵢ bᵢλᵢαᵢₜ)` (`Factor.quadTab_relCoef`). It vanishes for equal loadings **and the
   same weight profile** `αᵢₜ = αₜ` (`Factor.relCoef_factor_free`), e.g. exposure weights with
   proportional volumes (`Shock.expo_eq_of_proportional`). Same months with different weights do
   not suffice: two months, AR(1) `γφ^|t-s|`, weights `(3/4, 1/4)` against `(1/4, 3/4)` leave
   `γ(1 - φ)/2` (`Factor.extra_profile`), as does a cohort entering in month 2
   (`Factor.extra_entry`); unequal loadings `(1, 2)` leave `Γₜₜ` in one month
   (`Factor.extra_loadings`). Only a factor constant over the window (`φ = 1`) always cancels.
   Practice: rank cards on a common window with common month weights, or keep the factor in the
   fit; ignoring it understates the error (`Factor.quadTab_shock_le`).

32. **Separate equals joint frequency × severity without block diagonality (new;
   `notes/card-data.md` Step 6).** Expected: separate and joint prediction coincide iff there is
   no cross-component covariance. Found: only "if" holds
   (`CoreVector.blupW_eq_sepW_of_componentBlockDiag`; for a factor table per component:
   `FreqSev.blupW_eq_separate`). With the same cohort structure in both components, `K = K_c ⊗ S`,
   `L = L_c ⊗ S`, the best predictor is the separate one whatever the cross-covariance `S`
   (`CoreVector.blupW_kronecker`; Zellner's SUR with identical regressors). So cross-correlated
   residuals are necessary for a gain from joint prediction, not sufficient. With frequency
   weighted by cards and severity by claim counts the cohort structures differ, so the gain is
   expected in practice; measure it rather than infer it from the correlation.

33. **The bias of the product of frequency and severity predictions is exact, no delta method
   (new; `notes/card-data.md` Step 6).** Expected: the bias of `φ̂ψ̂` needs a delta-method
   approximation. Found: for unbiased linear predictions it is exactly
   `(AᵀKA)_FY - L₍ⱼF₎₍ⱼY₎`, the covariance of the two predictions minus that of the two levels,
   for every distribution (`CoreVector.VecEstimates.integral_mul_pred_sub`; only
   `E[XY] = EX·EY + cov(X, Y)`). For separate weights with no cross-component covariance it is `0`
   (`FreqSev.prodBias_sepW_eq_zero`); with cross-correlation separate predictions give
   `Σ a_Fᵢ a_Yₖ K₍ᵢF₎₍ₖY₎ - T_FY`, so ignoring a level correlation `T_FY > 0` underprices. The MSE
   of the product needs third and fourth moments (argued, not formalized): it lives in the
   optional distribution layer.

34. **`K̂ ≻ 0` iff `(Â + Ĉ)_ZZ ≻ 0` needs `Φ ≻ 0` and a common month (new; `studies/PLAN.md`,
   valid tables).** Expected: valid tables (`Â, Ĉ ⪰ 0`, `ŝ² ≥ 0`) give `K̂ ≻ 0` iff
   `Â_ZZ + Ĉ_ZZ ≻ 0`, `Z = {j : ŝⱼ² = 0}` (the app's `degenerateTable`). Found: true for distinct
   cells when `Φ ≻ 0` and the cohorts in `Z` share an observed month (`Factor.tableK_posDef_iff`;
   the directions separately: `tableK_posDef_of_zero`, `posDef_zero_of_tableK`), false without
   either. `Φ = 0`, `Â = I`, `Ĉ = 0`, `ŝ² = 0`: `(Â + Ĉ)_ZZ = I` but `K̂ = 0`
   (`Factor.tableK_counter_phi`; any singular `Φ` lets a month contrast escape the factor). Two
   cohorts with `ŝ² = 0` in different months, `Ĉ = (1, -1)(1, -1)ᵀ`, `Φ = I`: `K̂ = I ≻ 0` but `Ĉ` is
   singular (`Factor.tableK_counter_month`). The app meets both conditions (AR(1) with
   `φ̂ ∈ (0.001, 0.999)`, full panel), so its check is exact there (`Factor.tableK_ar1_posDef_iff`,
   with `Factor.ar1_posDef`); with entry and exit it is only
   sufficient.

35. **Under skewed claims, fits with region-specific estimated variances under-price (new; app,
   `studies/PLAN.md` "Plug-in bias").** Expected: the plug-in BLUP on corrBS's `K̂` is unbiased, as
   under symmetric noise (`Core.Target.blup_plugIn_unbiased_of_symmetric`). Found (simulated,
   4000 draws, gamma noise): portfolio mean error −0.37% of the tariff in the default world
   (z ≈ −10), −2.4% with `T = 4` and shape 1; corrBS alike; BS, own, pool and the oracle (true `K`)
   0; all 0 under normal noise. With the pooled `σ̂²` in place of the region-specific `σ̃ⱼ²` the bias
   is gone (−0.06%, z −1.5); with `ρ = 0.6` a second channel through `ρ̂` remains (−0.5%).
   Why: (a) exact, any distribution (proved, `Core.Estimates.integral_randomLin_sub`): for
   square-integrable weights with `d̂ᵀ1 = 1`, `E(d̂ᵀμ̂ − μⱼ) = Σᵢ cov(d̂ᵢ, μ̂ᵢ)`, so the fit is biased
   exactly when its weights covary with the estimates they weight; fixed weights (the oracle) never
   are. (b) exact (proved, `Core.Estimates.integral_portfolio_sub_of_balanced`): an
   exposure-balanced fit (`Σⱼ wⱼ*rateⱼ = Σⱼ wⱼ*μ̂ⱼ` in every draw, `bs_balance`; the G7
   corrections, `Core.Estimates.correct_balanced`) has portfolio bias 0 in every world.
   (c) first order (argued; its ingredient proved): `d̂ = d(θ̂)` with `θ̂` quadratic in the data, so `cov(d̂ᵢ, μ̂ᵢ) ≈ Σₖ ∂ₖdᵢ·cov(θ̂ₖ, μ̂ᵢ)`,
   a third moment (exact for any weights, `Cumulants.covariance_resVar_mean`, 2026-11-23:
   `cov(Σₜcₜrₜ², μ̂) = Σₛ aₛκₛ Σₜ cₜ(δₜₛ − aₛ)²`; for iid cells `κ₃/T`): 0 under symmetry,
   and with right skew (`κ₃ > 0`, every claims world) a region with high draws gets a high mean
   and a high `σ̂ⱼ²` together, so less weight (`∂dᵢ/∂σᵢ² < 0`; in the app mostly through the GLS
   portfolio weights `bᵢ`, i.e. the other regions' terms of `Σᵢ cov`, not the own weight): under-pricing of order
   skewness × `σⱼ/√(T wⱼ*)` × the shrinkage `ζⱼ`. A common `σ̂²` dilutes this by `1/J`. Same
   mechanism as inverse-variance weighting with estimated variances in meta-analysis
   (Hamman et al. 2018; Doncaster et al. 2017; `studies/literature.md` §10j). The core (two moments) cannot exclude it: it
   promises unbiasedness for known `K` only. Remedies in the app (`blupPool`, the balance switch, on by default;
   `studies/PLAN.md`): without correlation the common shift to exposure balance removes the bias at
   no MSE cost, and the pooled `σ̂²` also removes it but gives up real variance differences; under
   correlation the shift costs about 20% more MSE, and the pooled `σ̂²` leaves the `ρ̂` channel. Adopted 2026-11-27 (owner; S63, app's balance switch):
   shift to the leave-one-year-out cross-fitted portfolio level instead of the exposure-balanced one: unbiased in every
   world studied, and under `ρ = 0.6` 2–46 MSE points cheaper than exposure balance; its bias is the level channel only
   (`Core.Estimates.integral_crossFit_sub`, 0 for weights blind to the levels: `integral_crossFit_sub_eq_zero`). Exposure
   balance stays the fallback when year shares differ by region.
36. **Clipping `z` to `[0, 1]` is harmless exactly when the best `z` lies in `[0, 1]` (new; PLAN G3;
   Lean: `BlendMoments.errVar_clipZ_le_iff`, `errVar_clipZ_le`, `errVar_clipZ_bestZ`).** The thesis
   clips in eq. (34) without saying what it costs. The error variance is the parabola
   `E(z) = E(z*) + g(z − z*)²`, `g = Var(μ̂ⱼ − μ̂) > 0`, and clipping moves any `z` towards every point
   of `[0, 1]`. So if `z* ∈ [0, 1]`, clipping never increases the error, whatever `z` was; if not, it
   already hurts at `z = z*`, by exactly `g·dist(z*, [0, 1])²`. With two cohorts `z₁* > 1` below the
   singularity iff `σ₁ < σ₂ρ` (Finding 3), and `z₁* < 0` past it (Finding 17): there clipping costs.
   Caveat: this is for a fixed `z` against the true error curve; for an estimated `ẑ` that depends on
   the same data the error in a draw is a different parabola, and nothing is claimed.

37. **The spread of the means `B` is uncorrelated with `P` and `Qn` only under three conditions (new;
   `studies/LOG.md` S53; Lean: `Cumulants.covariance_statB_eq`, `covariance_statB_eq_zero`,
   `meanCoef_dotProduct_resCoef_eq_zero`, all in `FitStatistics.lean`).** Expected (S53, Lean candidate):
   `cov(B, P) = cov(B, Qn) = 0` when the third cumulants vanish. Found: exactly,
   `cov(B, R) = Σ A_B A_R κ₄` for `R = P` or `Qn` whenever (i) the cell means are constant within
   regions, (ii) there are no third cumulants, and (iii) the region means are uncorrelated with the
   residuals; so `0` needs also (iv) no fourth cumulants. Neither (iii) nor (iv) can be dropped.
   (iv): `J = T = 2`, unit volumes, independent cells with fourth cumulant `κ₄`: `cov(B, P) = κ₄/4`
   (checked by simulation with Exp(1) cells, `κ₄ = 6`: 1.505 against 1.5). (iii) holds for a level
   covariance plus year noise `Dₜ` with `aᵢₜDₜᵢⱼ` constant in `t`: uncorrelated regions with
   `Dₜᵢᵢ = σᵢ²/wᵢₜ`, or `Dₜᵢⱼ = Vᵢⱼ/√(wᵢₜwⱼₜ)` with proportional volumes `wᵢₜ = Wᵢvₜ`, as in every
   world of `studies/runs/price-formula.js` (so S53's numbers stand). With correlated regions and
   non-proportional volumes it fails: `ρ = 0.6`, app world with volumes × (1 + ½((j + t) mod 3)),
   normal cells: corr(P, B) = 0.007, corr(Qn, B) = 0.006 (0 at `ρ = 0`). Why: `P` and `Qn` are
   functions of the residuals, `B` of the region means; normal theory makes them independent only
   when the means and residuals are uncorrelated, and the fourth cumulant links any two quadratic
   forms sharing cells. Consequence for the price formula: the zero is exact in the study's worlds,
   small elsewhere, and under heavy tails the `κ₄` term is the one to add (`covariance_stat` gives it).
   In the balanced world it is exactly `cov(B, P) = κN(J − 1)/(JT)` for noise of fourth cumulant `κN/w²`;
   the levels' cumulant does not enter (`covariance_statB_statP_of_balanced_cumulants`, 2026-11-24).

38. **Estimating the noise variance flips the sign of the noise kurtosis in the plug-in's cross term
   (new; `studies/literature.md` §10m; Lean: `Cumulants.crossTerm_of_balanced_cumulants`,
   `crossTerm_of_balanced_cumulants_known`, in `FitCrossTerm.lean`).** Expected (Chen, Lahiri &
   Rao 2025, `D` known): the first-order cross term `2E[AB]` of the Bühlmann–Straub plug-in, relative
   to `(1 − z)τ²`, has the level part `−2z(1 − z)γL/J`. Found, balanced world, levels and noise with
   fourth cumulants `κL`, `κN/w²` (`γL = κL/τ⁴`, `γN = κN/σ⁴`), `ẑ = 1 − v̂/S²` linearized:
   - `D` estimated by `v̂`: `2E[AB] = −2(1 − 1/J) z(1 − z)(γL + γN/T)/J`.
   - `D` known: `2(1 − 1/J)(1 − z)/J · (−zγL + (1 − z)γN/T)`, their `2g₄` up to `1 − 1/J` (`κ_e = γN/T`).
   So the level part matches; the noise part changes sign and takes the form of the level part. Why:
   `A = (1 − z)m̄ − uⱼ` (`m` the centred region means, `uⱼ = Lⱼ − zmⱼ` uncorrelated with the data)
   meets `ẑ − z` only through fourth cumulants. Through `S²` the levels enter with `−(1 − z)` and the
   mean noise with `+z`; through `v̂` (only with `D` estimated) the noise enters again with `−z/s` times
   a larger weight, and the sum is negative. Consequence: adding law (a)'s kurtosis terms
   (`bsPrice_of_balanced_cumulants`, `+(1 − 1/J)z(1 − z)(γL + γN/T)/J` relative), the total first-order
   effect of kurtosis on the plug-in's MSE is `−(1 − 1/J)z(1 − z)(γL + γN/T)/J`: heavy tails of either
   kind *lower* it at this order, and law (a) with its kurtosis terms alone has the sign wrong. This
   agrees in sign with the app's simulations (`2E[AB]` −6% under gamma noise). Caveat: proved only for
   equal volumes `wⱼₜ = w` (the one case where `ẑ = 1 − v̂/S²` is the same for every region and the
   result has a closed form), first order in the delta method; no third cumulants enter at this order.
   *Unequal volumes, checked numerically (2026-11-24, `studies/runs/cross-term.js`, not proved):* the same
   first-order term for any `wⱼₜ`, exact from the moment tables (`integral_lin_lin_sumSq` holds for any
   weights), reproduces the closed form to all digits when balanced. With region sizes 16× apart and
   years 1–2×, it is negative in every world and every region, for levels and for noise, and the
   simulated exact `2E[AB]` (100 000 draws, fitBS with truncation) agrees: noise part −1.98% against
   −1.96 ± 0.16% (J = 8, T = 5), −0.58% against −0.61 ± 0.04% (J = 30). The level part's first order
   overstates at small J (−9.0% against −6.6 ± 0.2% at J = 8; −2.5% against −2.3% at J = 30), as a
   delta method should; gamma (skewed) and Laplace (symmetric) shapes of equal kurtosis give nearly
   the same. So the sign and the size carry over to unequal volumes. *Proved for any volumes
   (2026-11-25, `Cumulants.crossTerm_bs_of_cumulants`, with `bsAlpha_hasDerivAt`):* BS's weights depend
   on `(σ̂², τ̂²)` only through `k = σ²/τ²`, so the first-order error is `ε̂·(λ·x̄)`, `ε̂ = σ̂²/σ² − τ̂²/τ²`,
   `λ = dα/d log k`; then `2E[AB] = 2((1/σ² + (J − 1)/(cτ²))T_P − T_B/(cτ²))` with
   `T_P = κN/(J(T − 1)) Σᵢ αᵢλᵢ(1 − hᵢ)/Wᵢ`, `T_B = Σᵢ λᵢ(1 − Wᵢ/W)(κL Wᵢ(αᵢ − δᵢⱼ) + κN hᵢαᵢ/Wᵢ)`,
   `hᵢ = Σₜ aᵢₜ²`. It matches `firstOrder` in the study to all printed digits. The sign is not general
   (Finding 39). The balanced theorems are now its equal-volumes corollaries (2026-11-25).

39. **Heavy-tailed noise can raise the Bühlmann–Straub plug-in's MSE: Finding 38's sign fails when a
   region's volume sits in one year (new; Lean: `Cumulants.crossTerm_bs_pos_example`, with
   `crossTerm_bs_noise_pos_value`, in `FitCrossTerm.lean`; `studies/runs/cross-term.js` for the general
   term).** Expected (Finding 38, numerics with even years): the first-order cross term `2E[AB]` is
   ≤ 0 whenever `κL, κN ≥ 0`. Found: the *level* part is ≤ 0 in every world tried (random volumes,
   J = 2–11, T = 2–11, 300 000 worlds × regions; *proved 2026-11-25 for any volumes*,
   `Cumulants.crossTerm_bs_level_nonpos`: Chebyshev's sum inequality, as `mᵢzᵢ = Wᵢ(1 − Wᵢ/W)zᵢ`
   increases with `zᵢ`), but the *noise* part is not.
   Counterexample (proved): J = T = 2, volumes `(1, 8)` and `(10, 10)`, `τ² = 1`, `σ² = 20`
   (`z = 0.31, 0.5`), `κL = 0`: region 0's noise part is `+0.46(1 − z₀)τ²` per unit `γN`. Realistic
   size (J = 8, T = 5, region sizes ×4 apart, one region with 90% of its volume in one year, `z₀ = 0.5`,
   `γN = 3`): first order +19%, simulated exact `2E[A₀B₀]` **+7.5 ± 0.5%** with Laplace noise (0.0 ± 0.3%
   normal; 400 000 draws); with the year shares even (f = 0.2) it is −3.3% first order, −2.9 ± 0.4%
   simulated. Why: a region whose volume is concentrated in one year (`hᵢ = Σₜaᵢₜ²` near 1) has a mean
   that is nearly one cell, so its noise kurtosis passes in full to `S²`, while the pooled `σ̂²` hardly
   sees it (the residual weight of that cell is `w(1 − a)`, small). The negative channel through `σ̂²`
   then no longer outweighs the positive one through `S²`. With even years inside every region the
   noise part was ≤ 0 except at `z ≈ 0` (J = 2, `z < 0.01`), where the first order means little.
   Exposure-weighted portfolio totals can turn positive too (up to +2% at `z ≥ 0.5`, J = 8, T = 5,
   uneven years). Consequence: the sign of the kurtosis correction to the price of fitting BS depends
   on the volumes; use the general formula (`crossTerm_bs_of_cumulants`), not the balanced one.

40. **The level part of the cross term has no sign for the BLUP on corrBS's K̂ (new; exact check
   `studies/runs/blup-level-sign.py`, search `studies/runs/blup-level-sign.js`; not in Lean).** Expected: like BS
   (`Cumulants.crossTerm_bs_level_nonpos`), the level part of the first-order cross term `2E[AⱼBⱼ]` is ≤ 0
   when `κL ≥ 0`. Formula, for any pooled fit (data only through `P`, `Qn`, `B`): a level `Lₚ` enters only
   `B`, with weight `mₚ = Wₚ(1 − Wₚ/W)`, so the level part is `2κL Σₚ mₚ(dⱼₚ − δₚⱼ)∂dⱼₚ/∂B
   = (κL/c) d/dτ² ‖dⱼ − eⱼ‖²ₘ`. The sign asks whether more `τ̂²` pulls the weights towards the region's own
   mean in the `m`-norm. BS: always (Chebyshev). Found for the BLUP: ≤ 0 in 28 000 random cells
   (J = 2–10, T = 2–9, ρ < 0.95), and with J = 2 in every search, but not in general. Counterexample (exact,
   rational): J = 3, T = 2, σ² = 1, ρ = 0.99, τ² = 1/20, volumes `(0.2², 0.23²)`, `(0.13², 0.14²)`, `(35², 44²)`,
   region 1: `d/dτ² ‖d − e₁‖²ₘ = +0.0125`, level part `+0.12%` of the region's BLUP MSE per unit `γL`.
   Largest found: `+0.38%` (J = 10, T = 3, ρ = 0.9, sizes ≤ 16× apart, one region's volume 5× uneven over
   its years); with ρ ≤ 0.6 at most `+0.015%`, and none with ρ ≤ 0.9 when year shares are within 10×.
   Why: with strong cross-region correlation a large region's mean reveals a small region's noise, so the
   BLUP weight of a small region sits mostly on the large one (weights −0.04, 0.03, 1.02 above), and more
   `τ̂²` need not move it towards `eⱼ`. Consequence: for the BLUP plug-in the level part is negative for
   practical purposes but not a theorem; the per-region sign of BS does not carry over.
   *Where it holds (2026-11-25):* J = 2 always. The weights sum to 1, so `dⱼ − eⱼ = d₂(e₂ − e₁)` with
   `d₂ = (a − c)/(a + b − 2c + 2τ²)`, `a, b` the noise variances of the two means and `c` their covariance,
   and `d/dτ² 2m d₂² = −8m(a − c)²/Var(x̄₁ − x̄₂)³ ≤ 0`. No condition on ρ or the years suffices for J ≥ 3:
   with even year shares it fails at ρ = 0.1 (exact: J = 4, T = 3, per-year volumes
   `0.01², 37.1², 5.03², 5.01²`, τ² = 30, region 1: `+2.5·10⁻⁷` per unit γL), and the size grows with ρ
   (even years: at most `+0.002%` for ρ ≤ 0.5, `+0.2%` at 0.8, `+2.5%` at 0.999 with sizes 10⁶ apart).

41. **With its own `τ²` per group, optimal groups need not be intervals, even with equal volumes (new;
   numerical, `notes/group_variances.py`; not in Lean).** Question from the spatially clustered Fay–Herriot
   model (literature §10p): cohorts with fixed levels `θⱼ` and noise `Dⱼ` are split into groups, and each
   group gets its own collective mean and its own `τ²_g`. Counterexample, `D = 1`, two groups:
   `θ = (−5, −0.2, −0.1, 0, 0.1, 0.2, 5)`. The best grouping is `{−5, 5}{middle}`: oracle MSE 2.021 against
   4.663 for the best intervals, and normal likelihood −log L 10.70 against 13.18. Why: with equal `D` a group costs
   `n·D·s²/(s² + D)`, concave in its spread and at most `nD`. A group can stop shrinking, so it pays at most
   `D` per member and collects the outliers of both tails. Frequency (150 random cases, `n = 7`): 12 with
   heavy-tailed levels, 0–4 otherwise. With own means and **one common `τ²`** the groups are intervals for any volumes (0 of 300).
   For fixed `τ²` the loss is a weighted k-means cost with weights `uⱼ(1 − zⱼ)²`, so `kmeans_contiguous`
   applies (proved: `group_optimal_contiguous`, via `groupLoss_eq`). Consequence: a grouping should use a common `τ²`. But choosing the cut of
   the sorted *estimates* by SURE on the same data is 2–74% worse than one group (S61, `studies/LOG.md`):
   the fit needs a selection-aware criterion first. Details: `notes/group-variances.md`.

42. **The analysis-of-variance estimators of crossed-classification credibility are biased when the
   noise is correlated across cells (new; proved: `Model.anovaStat_row_unbiasedX`).** Goulet (1998,
   eqs. (67)–(69), from Dannenburg 1995) estimates the crossed variances from volume-weighted sums of
   squares of the cell means minus `(n − 1)ŝ²/U`. Exactly (`sum_mul_sq_sub_noise_eq_pairs`): such a
   statistic is the pool of the pairs `(μ̂ₖ − μ̂ₗ)² − v̂ₖ − v̂ₗ` with weights `uₖuₗ/(2U²)`. Its noise
   correction has each cell's own noise variance but not the cross term `+2σ²ₖₗρₖₗ` that the pair
   estimator `P̂ₖₗ` carries. For cells in one row (`anovaStat_row_unbiasedX`):
   `E G = (β² + γ²)(1 − Σ(uₖ/U)²) − Σ_{k≠l} (uₖuₗ/U²) σ²ₖₗρₖₗ`. The first term is Goulet's (67) (exact,
   `anovaStat_row_unbiasedX_of_uncorr`, when the noise is uncorrelated across the cells); the second is
   the bias. With positive correlation within a period, the classical estimators understate the
   variance components. Example: `n` cells of equal volume `u` in a row, noise variance `σ²/u` per cell
   estimate and correlation `ρ` between cells: `E G = (1 − 1/n)(β² + γ² − ρσ²/u)`, so Goulet's estimate
   of `β² + γ²` is short by `ρσ²/u`, a fraction `ρ` of a cell's noise variance.
   General form for any set of cells: `anovaStat_unbiasedX`; about the grand mean
   (`anovaStat_grand_unbiasedX`): `E G = α²(1 − Σ(U_a/U)²) + β²(1 − Σ(U_b/U)²) + γ²(1 − Σ(uₖ/U)²)` minus
   the same cross term, Goulet's (69) exactly when the noise is uncorrelated. So the whole two-way
   system (67)–(69) is reproduced, and each equation loses the same cross term. Use the pair estimators with the
   cross-covariance estimate (`crossed_unbiasedX`) instead; they are unbiased for any correlations.

43. **Merging when the gap looks small loses to both fixed rules, for every threshold (new; under
   normal noise; proved: `PreTest.integral_sq_pretest`, `PreTest.lt_gapRisk_of_tie`,
   `PreTest.pretest_mse_gt`).** Item 6 and `Merging.merge_iff` rank
   merging against keeping two cohorts separate for a choice made in advance. The plug-in version,
   merge iff `(X₁ − X₂)² < c` (`notes/merging-cohorts.md` §4), decides with the same data. For fixed
   levels with gap `δ`, `D = X₁ − X₂ ~ N(δ, V)` and `a = (v₁ − c₁₂)/V`, every such rule's error is
   `u + a·G(D)` with `u` independent of `D`, so its MSE is `E u² + a²R`, where `R = E G(D)²` is the
   risk of estimating the gap by `0` (merged) or `(1 − k)D` (separate, `k = V/(V + 2τ²)` for the
   thesis blend, `0` for own estimates): the pre-test merge is hard thresholding of the gap (with
   shrinkage). Always merging has `R = δ²`, never merging `m²V + (1 − m)²δ²`, `m = 1 − k`; they tie at
   `δ²(2 − m) = mV`. **There the pre-test rule is strictly worse than both, for every `c > 0`**, in
   every cohort (the factor `a²` is common). So no threshold is safe; this is the classical pre-test
   result (Bancroft 1944, Judge & Bock 1978) in credibility form. Size (`studies/runs/pretest-merge.js`,
   S68): own estimates, `c = 2V`: `+0.20·a²V` at the tie (the separate rule's whole excess is `a²V`);
   the plug-in threshold of §4 with `τ²/V = 1`: `+0.04·a²V`; it loses to both on up to 14% of the gaps,
   and, at `c = 2V`, to the better of the two by up to `0.65·a²V`. Proof idea: with `p(x) = δ² − (mx − δ)²`,
   `R − δ² = −E[p(D); D² ≥ c]`, `E p(D) = 0` at the tie; folding `x ↦ −x`, the integrand on `x > 0`
   has the sign of `sinh y/(y cosh y) − mV/(2δ²)`, `y = δx/V` (`fold_eq`), strictly decreasing in `y`
   (`sinh_div_strictAntiOn`), so positive then negative. Remedy: choose on a held-out year,
   whose score is unbiased for the chosen rule's error for every distribution
   (`CrossFit.integral_heldOutScore`).

44. **A 2×2 crossed table cannot estimate its variances, at any volume (new; proved:
   `CrossedSmall.sq_le_trace_row`, `_col`, `_cell`, `two_mul_sq_le_variance_cell`).** The four cell means
   of a 2×2 table span the mean, one row contrast, one column contrast and one interaction contrast, so
   each of `α²`, `β²`, `γ²` has one degree of freedom. Every estimator `μ̂ᵀAμ̂ − c` that does not depend on
   the common mean (`A1 = 0`) and is unbiased for one of them whatever the three are (noise covariance
   `Σ ⪰ 0` known, any volumes, any correlations) has Gaussian variance `2 tr(AKAK) ≥ 2θ²`; with Gaussian
   third and fourth cumulants that is its actual variance. So its standard deviation is at least `√2`
   times its value, more exposure shrinks only `Σ` and never this bound, and the MSE-best multiple
   `θ²/(θ² + V)` is at most `1/3` (`bestMultiple_le_third`). Sharp: for `γ²` with `Σ = 0` the interaction
   contrast `D = v·μ̂/2` gives `D² − 0` with variance exactly `2γ⁴`. The pair pools of `crossed_unbiasedX`
   with fixed weights are such estimators. Consequence: the raw estimates are negative in 20–65% of draws
   even with real effects (S70), clipping keeps most of the error, and only more rows or columns help;
   in practice merge small classifications or fit without the crossed layer, decided on held-out years.
   Not covered: estimated noise (adds its own variance under normal noise, independent of the means for
   noise independent over time; not proved) and kurtosis below the Gaussian.

45. **The price of the BLUP over the blend on the same `K̂` is not "none extra", and has no sign (new; proved:
   `Core.blupWeight_sub_eq`, `blendWeight_sub_eq`, `tendsto_blupPrice`, `tendsto_blendPrice`).** On a fitted
   `K'`, `L'` the BLUP's weights err by exactly `Q'(L'ⱼ − Lⱼ − (K' − K)d*)` and the blend's by
   `(z' − z)(eⱼ − b') − (1 − z)Q'((K' − K)b)`, with `Q r = K⁻¹r − (1ᵀK⁻¹r)b` the zero-sum solve. At first order
   the extra MSE (by `linMse_eq_blupWeight_add`, the squared weight error in the `K`-norm) is `rᵀQr`,
   `r = ΔLⱼ − ΔK d*`, against `Δz²·gap − 2Δz(1 − z)(eⱼ − b)ᵀΔK b + (1 − z)²(ΔK b)ᵀQ(ΔK b)`: Das, Jiang & Rao's `g₃`
   (2004, eq. (3.4)) for each family. The BLUP reads `ΔK` through the whole vector `ΔK d*`, the blend through
   `Δz` and `ΔK b` only. Neither dominates: for random positive definite `K` and symmetric `ΔK` the BLUP's
   price is the lower one in 11.7% of directions (S73), so the sign of the difference depends on `Var θ̂`.
   Size (S73, J = 8, T = 5, weights on corrBS's `K̂`): at app volume with σⱼ spread 2 and ρ = 0.3–0.6 the
   BLUP's extra price is +32 to +38 points of the floor against a gain of 3–12; with equal σⱼ it is at most
   +4. So `Engine.gainPrice`'s "none extra" understates the BLUP's price exactly where S72 saw it lose.
   Not covered: the cross term `2E[AB]` of `PlugIn.lean`, and the second-order terms. These matter: under
   gamma noise the raw BLUP loses only +6 there (S74), so the cross term is about −25 points, and a
   bootstrapped gain-against-price verdict picks no better than always-BLUP (S74). S72's loss of the
   balanced BLUP is mostly the balance switch's own cost (S74).

46. **Balancing trades the fit's portfolio level for the target's, and with unequal noise variances the
   app's target is the worse one (new; proved: `integral_sum_sq_shift`, `Core.Estimates.balance_blup_cost`).**
   A common shift `D = T − r̄` to a portfolio level `T` changes the exposure-weighted MSE by exactly
   `E(T − μ̄)² − E(r̄ − μ̄)²` (`μ̄`, `r̄` the exposure-weighted level and rate), for any rates, target and
   distribution; the regions' relative rates are untouched. So a constraint is not costly as such: balancing
   pays exactly when `T` estimates `μ̄` better than the fit does. With known moments the BLUP's `r̄ = cᵀμ̂`,
   `c = Σ uⱼd*ⱼ`, is the best unbiased linear estimate of `μ̄`, so balancing it to the exposure average costs
   `(u − c)ᵀK(u − c) ≥ 0`. In the fitted worlds (S75, corrBS, 56 worlds; identity exact to 3e-14 per draw):
   the cross-fitted level's `E(T − μ̄)²` is 0.82–1.10 times corrBS's own with equal σⱼ, 1.00–1.26 with
   spread 1, 1.17–2.21 with spread 2; the exposure average 0.86–2.01. Bias (Finding 35) is part of
   `E(r̄ − μ̄)²` and is small next to its variance there. Consequence for the app: the balance switch should
   be on only where its target is the better estimate of `μ̄`. Data-side (S76): the closed form for fixed
   weights (`balance_cost_portLin`) on corrBS's `K̂`, τ̂², "balance iff the plug-in cost is negative", has regret
   0.5 mean, 6.9 max (never: 0.4, 12.2; always: 22.2, 205.6; held-out scores: 10.3, 99.2). It ignores the
   portfolio bias, which the unbalanced fit keeps (down to −190 bp at app volume, σⱼ spread 2).

47. **The app's `Wⱼ` underestimates `Var σ̂ⱼ²` by a relative `O(1/T)`, and correcting it worsens the
   rates (new; proved: `VcW.integral_vcW`, `integral_vcW_equal`, `integral_vcWCorr_equal`,
   `integral_vcWCorr`, `integral_betaHat`).** `Wⱼ = Σₜ(uⱼₜ − σ̂ⱼ²)²/(T(T−1))` estimates the variance of
   `σ̂ⱼ²` from the yearly terms, but `uⱼₜ` uses the fitted `μ̂ⱼ`, so the `uⱼₜ` are dependent. Exactly, for
   independent years with equal volumes, variance `σ²` and fourth cumulant `κ` per unit of volume, any
   level and any distribution with four moments:
   `E Wⱼ = 2σ⁴(T−2)/(T−1)² + κ(T−2)²/(T(T−1)²)` against `Var σ̂ⱼ² = 2σ⁴/(T−1) + κ/T`. So `Wⱼ` is low by
   the factors `(T−2)/(T−1)` (normal part) and `(T−2)²/(T−1)²` (kurtosis part): 50% at `T = 3`, 25% at
   `T = 5`, 11% at `T = 10` under normal noise; 62%, 35%, 17% under the app's gamma(2) noise (`κ = 3σ⁴`).
   The absolute bias is `O(1/T²)`, as expected, but `Var σ̂²` is itself `O(1/T)`. For any volumes the
   exact `E Wⱼ` is a sum over the forms of `uₜ − σ̂²` (`integral_vcW`). Correction:
   `W̃ = (T−1)³/(T(T−2)(T−3)) W − 2σ̂⁴/(T(T−3))` is unbiased for `T ≥ 4` (equal volumes); for any volumes,
   if variances and fourth cumulants are known up to two scales (fixed-shape noise: `∝ 1/wₜ`, `∝ 1/wₜ²`),
   two coefficients solved from the exact moments make `λW + μσ̂⁴` unbiased (`Engine.vcWCoef`). No
   unbiased quadratic correction exists at `T = 3` (the two equations are singular). Then `β̂²` (G1b) is
   unbiased as Bühlmann–Straub's `τ̂²` one level up (`integral_betaHat`), but only for uncorrelated regions:
   correlated noise (`ρ ≠ 0`) correlates the `σ̂ⱼ²` and needs the cross terms `Ŵᵢⱼ` (S80: with `ρ = 0.6` and
   equal σⱼ the corrected `β̂²` is still low by 0.2–0.5 σ⁴). In the fitted worlds (S80, 36 worlds) the
   correction fixes its own targets (`W̃/Var σ̂² ≈ 1.0` from `T = 5`; `β̂²` bias ≈ 0 at `ρ = 0`) but raises
   corrBS's rate error by 4 points of the floor on average (up to 44 at `T = 3`, σⱼ spread 2); it gains
   only with equal σⱼ and short histories (−5 to −9 at app volume). Unbiased inputs to `ζⱼ = β²/(β² + Wⱼ)`
   do not give the better `ζⱼ` for the rates: the downward bias of `Wⱼ` shrinks the σⱼ² less, which pays
   when they differ. The app keeps the raw `Wⱼ` (corrected one: `opts.corrW`). Open (hypothesis): the
   rates' loss is asymmetric in `ζ`, so the target for `ζ` is not `β²/(β² + Var σ̂²)`.

Equation numbers refer to `thesis/original/main.tex` as compiled.
