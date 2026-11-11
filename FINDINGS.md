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
   `z/z_* = (0.564, 0.177, 0.259)`). It also fails for equal correlations
   `ρᵢⱼ = ρ` when the `σⱼ` differ. For `J ≥ 3` the right condition is
   item 5.
5. **Equal covariances (new, any `J`).** If all cohort pairs have the same
   covariance `σ²ᵢⱼρᵢⱼ = c`, then `bⱼ = zⱼ/z_*` and the proposed factor is
   `zⱼ = τ²/(τ² + σ²ⱼⱼ - c)`, i.e. eq. (32) with `σ₁σ₂ρ` replaced by `c`
   (`Model.b_eq_of_equalCov`, `Model.bestZ_of_equalCov`, *proved*). Reason:
   `K = diag(dⱼ) + c·11ᵀ`, and a rank-one term along `u` does not change the
   direction of `K⁻¹u`. Bühlmann–Straub is `c = 0`, two cohorts are
   `c = σ₁σ₂ρ`. Extra hypotheses: `τ² + σ²ⱼⱼ ≠ c` (the singularity of
   Finding 3, now per cohort) and `bⱼ ≠ 1` (`0/0`, as in Finding 2).
   *Converse (on paper, not in Lean).* `bⱼ = zⱼ/z_*` for all `j` iff some `λ`
   gives `Σᵢ≠ⱼ (Kᵢⱼ + λ) bᵢ = 0` for every `j`. For `J = 3` with all `bⱼ ≠ 0`
   this forces equal covariances. For `J ≥ 4` it does not: with equal `σⱼ`,
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
   groups (Bühlmann & Gisler, ch. 6). See README "Later goals".
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
   cohort `j` observed in `Tⱼ ⊆ T` (README "Later goals"; notes in
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

14. **Optimal cohorts are intervals only for exposure-weighted pooling (new,
   on paper).** Units with fixed levels `xᵢ` and uncorrelated estimates of
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
   a neighbour. Open: the blend with a common variance (no counterexample in
   26 000 random cases). Details: `notes/kmeans-bridge.md`.

Equation numbers refer to `thesis/original/main.tex` as compiled.
