import Credibility.Estimation
import Credibility.OffDiagonal

/-!
# Bridge to hierarchical credibility: a shared group level

Not in the thesis; first step towards two-level credibility (FINDINGS item 6,
`notes/merging-cohorts.md`). In the thesis the cohort levels `μⱼ` are
uncorrelated with variance `τ²`. Here they share a fraction `φ` of that
variance: `cov(μᵢ, μⱼ) = τ²` if `i = j` and `φτ²` otherwise, i.e. the level
covariance is `τ²·(11ᵀ)^φ` with `(·)^φ` the damping of `OffDiagonal.lean`.
The cohort estimates then have covariance `K_φ = τ²·(11ᵀ)^φ + Σ`, where
`Σᵢⱼ = σ²ᵢⱼρᵢⱼ` is the error covariance.

* `φ = 0` is the thesis: `K_0 = K` (`Kφ_zero`);
* `φ ∈ [0,1)` keeps `K_φ` positive definite (`Kφ_posDef`);
* `φ = 1` (one common level) gives `Σ + τ²·11ᵀ`: the error covariance plus
  a rank-one term along `1`, the structure behind Finding 5 (`Kφ_one`).

Bridge 2: `K_φ` is the thesis `K` with `τ²` replaced by `(1-φ)τ²` (the model
`M.withLevel φ`), plus `φτ²·11ᵀ` (`Kφ_eq`). A rank-one term along `1` does not
move the GLS weights and adds its size to `s²` (`glsWeight_add_rankOne`,
`invTotal_inv_add_rankOne`). The shared level then adds `φτ²` to all six
moments of the blend, which changes neither its error variance nor `bestZ`
(`BlendMoments.shift`): credibility only sees the non-shared part `(1-φ)τ²`.

Bridge 3: the §2.8 estimators see the same part. With observation covariance
`σᵢₜσⱼₛρᵢⱼδₜₛ + τ²(11ᵀ)^φᵢⱼ`, `τ̂²` has expectation `(1-φ)τ²` and `K̂` estimates
`K_φ - φτ²·11ᵀ` (`tauHat_unbiasedφ`, `KHat_unbiasedφ`), for every `φ`: no
inverse is involved, so `φ = 1` needs no separate case. The shared level acts
like the unknown mean `μ`, which the estimators are built to ignore.

Bridge 4: several groups `g = grp j`, each with its own shared level:
`cov(μᵢ, μⱼ) = τ²` if `i = j`, `φτ²` within a group, `0` across groups. Then
`L_G = (1-φ)τ²·I + φτ²·Σ_g 1_g1_gᵀ` and `K_G = K(M_φ) + φτ²·Σ_g 1_g1_gᵀ`
(`KG_eq`): one rank-one term per group, no longer along `1`, so it does not
drop out. With errors uncorrelated across groups, `K_G` is block diagonal with
blocks `K(M_φ)_g + φτ²·11ᵀ` (`block_KG`), and the Core fact for block-diagonal
`K` (`glsWeight_blockDiag`: GLS within each group, then inverse-variance
weights (23) across groups) plus Bridge 2 per block give: within a group the
thesis weights for `(1-φ)τ²`; across groups, inverse-variance weights with
group variance `s'²_g + φτ²` (`glsWeight_KG`, `s2_KG`). The between-group
variance flattens the group weights, and `zⱼ` gains `φτ²(1 - B_g)`, with
`B_g` the weight of `j`'s group (`bestZ_G_eq`).

Bridge 5: the §2.8 estimators with group levels. A thesis-unbiased estimator
`f` gets expectation `θ - φτ²(Σⱼ f(1_{j}) - Σ_g f(1_g))`, with `1_g` the
noise-free data equal to `1` on group `g` (`unbiasedG_of`). So `E τ̂² = τ² - φτ²π`,
`π` the weighted share of same-group pairs (`tauHat_unbiasedG`), and `K̂`
estimates `K_G - φτ²·[g(i) = g(j)]` only with one group (`KHat_unbiasedG_iff`).
Pairs separate the parts: `(μ̂ᵢ - μ̂ⱼ)²` minus its noise estimates `2τ²` across
groups and `2(1-φ)τ²` within one (`pairHat_unbiasedG`), so `φτ²` is identified
(`phiTauHat_unbiasedG`).
-/

open Matrix

namespace Credibility

/-! ### A rank-one term along `1` (Core level) -/

section RankOne

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- If `K` and `K + c·11ᵀ` are positive definite, then
`(K + c·11ᵀ)⁻¹1 = K⁻¹1 / (1 + c·1ᵀK⁻¹1)`, with `1 + c·1ᵀK⁻¹1 > 0`:
`(K + c·11ᵀ) K⁻¹1 = (1 + c·1ᵀK⁻¹1)·1`. -/
theorem Kinv_one_add_rankOne {K : Matrix J J ℝ} (hK : K.PosDef) (c : ℝ)
    (hK' : (K + c • vecMulVec 1 1).PosDef) :
    0 < 1 + c * invTotal K ∧
      (K + c • vecMulVec 1 1)⁻¹ *ᵥ 1 = (1 + c * invTotal K)⁻¹ • (K⁻¹ *ᵥ 1) := by
  set w := K⁻¹ *ᵥ 1
  set S := invTotal K
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).mp hK'.isUnit
  have hKw : (K + c • vecMulVec 1 1) *ᵥ w = (1 + c * S) • (1 : J → ℝ) := by
    rw [add_mulVec, smul_mulVec, vecMulVec_mulVec, mulVec_mulVec, mul_nonsing_inv K hdet,
      one_mulVec]
    ext i; simp [S, invTotal, w]
  have hw : w = (1 + c * S) • ((K + c • vecMulVec 1 1)⁻¹ *ᵥ 1) := by
    rw [← mulVec_smul, ← hKw, mulVec_mulVec, nonsing_inv_mul _ hdet', one_mulVec]
  -- `wᵀ(K + c·11ᵀ)w = (1 + cS)·S > 0` with `S > 0`.
  have hpos : 0 < 1 + c * S := by
    rcases isEmpty_or_nonempty J with hJ | hJ
    · simp [S, invTotal]
    have hS : 0 < S := invTotal_pos hK
    have hw0 : w ≠ 0 := by
      intro h0
      have : S = 0 := by
        simp only [S, invTotal]; rw [show K⁻¹ *ᵥ 1 = w from rfl, h0, dotProduct_zero]
      linarith
    have := hK'.dotProduct_mulVec_pos hw0
    rw [star_trivial, hKw, dotProduct_smul, dotProduct_one, smul_eq_mul] at this
    have hS' : ∑ i, w i = S := by simp [S, invTotal, w, one_dotProduct]
    rw [hS'] at this
    exact pos_of_mul_pos_left this hS.le
  refine ⟨hpos, ?_⟩
  rw [eq_inv_smul_iff₀ hpos.ne']; exact hw.symm

/-- A rank-one term along `1` does not change the GLS weights:
`b(K + c·11ᵀ) = b(K)`, since `(K + c·11ᵀ)⁻¹1 ∝ K⁻¹1`. -/
theorem glsWeight_add_rankOne {K : Matrix J J ℝ} (hK : K.PosDef) (c : ℝ)
    (hK' : (K + c • vecMulVec 1 1).PosDef) :
    glsWeight (K + c • vecMulVec 1 1) = glsWeight K := by
  obtain ⟨hpos, hinv⟩ := Kinv_one_add_rankOne hK c hK'
  ext j
  rw [glsWeight, glsWeight, invTotal, hinv, dotProduct_smul, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, mul_div_mul_left _ _ (inv_ne_zero hpos.ne'), invTotal]

/-- …and it adds `c` to the portfolio variance: `s²(K + c·11ᵀ) = s²(K) + c`. -/
theorem invTotal_inv_add_rankOne [Nonempty J] {K : Matrix J J ℝ} (hK : K.PosDef) (c : ℝ)
    (hK' : (K + c • vecMulVec 1 1).PosDef) :
    (invTotal (K + c • vecMulVec 1 1))⁻¹ = (invTotal K)⁻¹ + c := by
  obtain ⟨hpos, hinv⟩ := Kinv_one_add_rankOne hK c hK'
  have hS := (invTotal_pos hK).ne'
  rw [invTotal, hinv, dotProduct_smul, smul_eq_mul, ← invTotal]
  field_simp

end RankOne

/-! ### Shifting all moments of the blend by a constant -/

namespace BlendMoments

/-- Add `c` to all six second moments of the blend: what a common component of
variance `c` in the cohort estimates, the portfolio estimate and the target does. -/
def shift (m : BlendMoments) (c : ℝ) : BlendMoments where
  varCohort := m.varCohort + c
  varPortfolio := m.varPortfolio + c
  varTarget := m.varTarget + c
  covEst := m.covEst + c
  covCohortTarget := m.covCohortTarget + c
  covPortfolioTarget := m.covPortfolioTarget + c

/-- A common component cancels in the error of the blend:
`z + (1 - z) - 1 = 0`, so the error variance is unchanged. -/
theorem errVar_shift (m : BlendMoments) (c z : ℝ) : (m.shift c).errVar z = m.errVar z := by
  simp only [errVar, shift]; ring

/-- …and so is `Var(μ̂ⱼ - μ̂)`. -/
theorem gap_shift (m : BlendMoments) (c : ℝ) : (m.shift c).gap = m.gap := by
  simp only [gap, shift]; ring

/-- …and so is the best credibility factor. -/
theorem bestZ_shift (m : BlendMoments) (c : ℝ) : (m.shift c).bestZ = m.bestZ := by
  rw [bestZ, gap_shift, bestZ]; simp only [shift]; ring_nf

end BlendMoments

namespace Model

variable {J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
variable (M : Model J T)

/-- Covariance of the cohort levels when they share a fraction `φ` of the
level variance: `τ²` on the diagonal, `φτ²` off it. -/
noncomputable def levelCov (τ2 φ : ℝ) : Matrix J J ℝ :=
  τ2 • shrinkOffDiag φ (of fun _ _ => (1 : ℝ))

/-- The error covariance `Σᵢⱼ = σ²ᵢⱼρᵢⱼ` of the cohort estimates. -/
noncomputable def errCov : Matrix J J ℝ := of fun i j => M.σ2 i j * M.ρ i j

/-- `K_φ = τ²·(11ᵀ)^φ + Σ`, the covariance of the cohort estimates when the
levels share a fraction `φ` of their variance. -/
noncomputable def Kφ (φ : ℝ) : Matrix J J ℝ := levelCov M.τ2 φ + M.errCov

omit [Fintype J] [Fintype T] [DecidableEq T] in
lemma levelCov_apply (τ2 φ : ℝ) (i j : J) :
    levelCov τ2 φ i j = if i = j then τ2 else φ * τ2 := by
  by_cases h : i = j <;> simp [levelCov, shrinkOffDiag, h, mul_comm]

omit [Fintype J] in
/-- `φ = 0` is the thesis model: `K_0 = K`. -/
theorem Kφ_zero [Nonempty T] : M.Kφ 0 = M.K := by
  ext i j
  rw [Kφ, Matrix.add_apply, levelCov_apply, M.K_apply]
  by_cases h : i = j <;> simp [errCov, h, add_comm]

omit [Fintype J] [DecidableEq T] in
/-- `φ = 1` (one common level): `K_1 = Σ + τ²·11ᵀ`, the error covariance plus
a rank-one term along `1`. -/
theorem Kφ_one : M.Kφ 1 = M.errCov + M.τ2 • vecMulVec 1 1 := by
  ext i j
  rw [Kφ, Matrix.add_apply, levelCov_apply, add_comm]
  by_cases h : i = j <;> simp [h]

omit [Fintype J] in
/-- The error covariance is `K - τ²·I`, so `K_1 = K - τ²·I + τ²·11ᵀ`. -/
theorem errCov_eq [Nonempty T] : M.errCov = M.K - M.τ2 • (1 : Matrix J J ℝ) := by
  ext i j
  rw [Matrix.sub_apply, M.K_apply]
  by_cases h : i = j <;> simp [errCov, h]

/-- The error covariance is positive semidefinite when `ρ` is: for every
`ε > 0`, `Σ + εI` is the `K` of the model with `τ² = ε`, positive definite by
`K_posDef`. -/
theorem errCov_posSemidef [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) :
    M.errCov.PosSemidef := by
  -- The model with `τ² = ε`.
  let Mε : (ε : ℝ) → 0 < ε → Model J T := fun ε hε => { M with τ2 := ε, τ2_pos := hε }
  have hK : ∀ ε (hε : 0 < ε), (Mε ε hε).K = M.errCov + ε • (1 : Matrix J J ℝ) := by
    intro ε hε
    ext i j
    rw [Matrix.add_apply, (Mε ε hε).K_apply]
    by_cases h : i = j <;> simp [Mε, errCov, h, σ2, a]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · have hE : M.errCov = (Mε 1 one_pos).K - 1 := by rw [hK, one_smul, add_sub_cancel_right]
    rw [hE]
    exact ((Mε 1 one_pos).K_posDef hρ).isHermitian.sub isHermitian_one
  · -- `xᵀΣx + ε‖x‖² ≥ 0` for every `ε > 0`.
    have h : ∀ ε, 0 < ε → 0 ≤ star x ⬝ᵥ (M.errCov *ᵥ x) + ε * (star x ⬝ᵥ x) := by
      intro ε hε
      have := ((hK ε hε) ▸ (Mε ε hε).K_posDef hρ).posSemidef.dotProduct_mulVec_nonneg x
      simpa [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul] using this
    by_contra hneg
    rw [not_le] at hneg
    have hxx : 0 ≤ star x ⬝ᵥ x := by
      simp only [dotProduct, star_trivial]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    set q := star x ⬝ᵥ (M.errCov *ᵥ x)
    set n := star x ⬝ᵥ x
    have := h (-q / (2 * (n + 1))) (div_pos (by linarith) (by linarith))
    have hn1 : 0 < n + 1 := by linarith
    have : -q / (2 * (n + 1)) * n ≤ -q / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith
    linarith

/-- For `φ ∈ [0,1)`, `K_φ` is positive definite: `τ²·(11ᵀ)^φ ≻ 0` by
`posDef_shrinkOffDiag` (`11ᵀ ⪰ 0` with unit diagonal), and `Σ ⪰ 0`. -/
theorem Kφ_posDef [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) : (M.Kφ φ).PosDef := by
  have h11 : (of fun _ _ => (1 : ℝ) : Matrix J J ℝ).PosSemidef := by
    simpa [vecMulVec] using posSemidef_vecMulVec_self_star (1 : J → ℝ)
  exact PosDef.add_posSemidef
    ((posDef_shrinkOffDiag h11 h0 h1 fun _ => one_pos).smul M.τ2_pos)
    (M.errCov_posSemidef hρ)

/-! ### Bridge 2: `K_φ` is a thesis `K` plus a rank-one term -/

/-- The thesis model with the non-shared level variance `(1-φ)τ²`. -/
def withLevel (φ : ℝ) (h1 : φ < 1) : Model J T :=
  { M with τ2 := (1 - φ) * M.τ2, τ2_pos := mul_pos (sub_pos.mpr h1) M.τ2_pos }

omit [Fintype J] [Fintype T] [DecidableEq T] in
/-- `τ²(11ᵀ)^φ = (1-φ)τ²·I + φτ²·11ᵀ`. -/
lemma levelCov_eq (τ2 φ : ℝ) :
    levelCov τ2 φ = ((1 - φ) * τ2) • (1 : Matrix J J ℝ) + (φ * τ2) • vecMulVec 1 1 := by
  ext i j
  rw [levelCov_apply]
  by_cases h : i = j <;> simp [h]; ring

omit [Fintype J] in
/-- `K_φ` is the thesis `K` with `τ²` replaced by `(1-φ)τ²`, plus `φτ²·11ᵀ`. -/
theorem Kφ_eq [Nonempty T] {φ : ℝ} (h1 : φ < 1) :
    M.Kφ φ = (M.withLevel φ h1).K + (φ * M.τ2) • vecMulVec 1 1 := by
  have he : M.errCov = (M.withLevel φ h1).errCov := rfl
  have hτ : (M.withLevel φ h1).τ2 = (1 - φ) * M.τ2 := rfl
  rw [Kφ, levelCov_eq, he, errCov_eq, hτ]
  abel

/-- For `φ ∈ [0,1)`, the GLS weights of `K_φ` are the thesis weights with
`τ²` replaced by `(1-φ)τ²`. -/
theorem glsWeight_Kφ [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) : glsWeight (M.Kφ φ) = (M.withLevel φ h1).b := by
  have hK' := M.Kφ_posDef hρ h0 h1
  rw [M.Kφ_eq h1] at hK' ⊢
  exact glsWeight_add_rankOne ((M.withLevel φ h1).K_posDef hρ) _ hK'

/-- …and the portfolio variance is that model's `s²` plus the shared `φτ²`. -/
theorem s2_Kφ [Nonempty T] [Nonempty J] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) : (invTotal (M.Kφ φ))⁻¹ = (M.withLevel φ h1).s2 + φ * M.τ2 := by
  have hK' := M.Kφ_posDef hρ h0 h1
  rw [M.Kφ_eq h1] at hK' ⊢
  exact invTotal_inv_add_rankOne ((M.withLevel φ h1).K_posDef hρ) _ hK'

/-! ### The blend with a shared level -/

/-- The moments entering the blend for cohort `j` when the levels share `φτ²`
(§2.4 with `cov(μᵢ, μⱼ) = φτ²`): the GLS weights `b` of `K_φ`, and
`cov(μ̂, μⱼ) = Σᵢ bᵢ cov(μᵢ, μⱼ)`. -/
noncomputable def momentsφ (φ : ℝ) (j : J) : BlendMoments where
  varCohort := M.τ2 + M.σ2 j j
  varPortfolio := (invTotal (M.Kφ φ))⁻¹
  varTarget := M.τ2
  covEst := (M.Kφ φ *ᵥ glsWeight (M.Kφ φ)) j
  covCohortTarget := M.τ2
  covPortfolioTarget := (levelCov M.τ2 φ *ᵥ glsWeight (M.Kφ φ)) j

/-- The shared level adds `φτ²` to every moment of the thesis blend with
non-shared level variance `(1-φ)τ²`. -/
theorem momentsφ_eq [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) (j : J) :
    M.momentsφ φ j = ((M.withLevel φ h1).moments j).shift (φ * M.τ2) := by
  have : Nonempty J := ⟨j⟩
  set M' := M.withLevel φ h1
  have hb := M.glsWeight_Kφ hρ h0 h1
  have hs := M.s2_Kφ hρ h0 h1
  have hcov : (M.Kφ φ *ᵥ glsWeight (M.Kφ φ)) j = (invTotal (M.Kφ φ))⁻¹ := by
    rw [mulVec_glsWeight (M.Kφ_posDef hρ h0 h1)]
  have hcov' : (M'.K *ᵥ M'.b) j = M'.s2 := by
    rw [Model.b, mulVec_glsWeight (M'.K_posDef hρ)]; rfl
  -- `cov(μ̂, μⱼ) = φτ² + (1-φ)τ² bⱼ`, using `Σ b = 1`.
  have hlev : (levelCov M.τ2 φ *ᵥ glsWeight (M.Kφ φ)) j
      = φ * M.τ2 + (1 - φ) * M.τ2 * M'.b j := by
    rw [levelCov_eq, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, hb]
    have hsum : 1 ⬝ᵥ M'.b = 1 := by rw [one_dotProduct, Model.b, sum_glsWeight (M'.K_posDef hρ)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    erw [hsum]; simp; ring
  have hτ : M'.τ2 = (1 - φ) * M.τ2 := rfl
  have hσ : M'.σ2 = M.σ2 := rfl
  simp only [momentsφ, Model.moments, BlendMoments.shift, hcov, hcov', hlev, hs, hτ, hσ,
    BlendMoments.mk.injEq]
  exact ⟨by ring, rfl, by ring, rfl, by ring, by ring⟩

/-- The error variance of the blend with a shared level is that of the thesis
model with `τ²` replaced by `(1-φ)τ²`, for every `z`. -/
theorem errVar_momentsφ [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) (j : J) (z : ℝ) :
    (M.momentsφ φ j).errVar z = ((M.withLevel φ h1).moments j).errVar z := by
  rw [M.momentsφ_eq hρ h0 h1, BlendMoments.errVar_shift]

/-- …so the best credibility factor is too. -/
theorem bestZ_momentsφ [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) (j : J) :
    (M.momentsφ φ j).bestZ = ((M.withLevel φ h1).moments j).bestZ := by
  rw [M.momentsφ_eq hρ h0 h1, BlendMoments.bestZ_shift]

/-- Eq. (26) with a shared level: `zⱼ = (1 - bⱼ)(1-φ)τ² / ((1-φ)τ² + vⱼ - (s² - φτ²))`,
with `b` and `s²` the GLS weights and portfolio variance of `K_φ`. -/
theorem bestZ_φ_eq [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) (j : J) :
    (M.momentsφ φ j).bestZ = (1 - glsWeight (M.Kφ φ) j) * ((1 - φ) * M.τ2)
      / ((1 - φ) * M.τ2 + M.σ2 j j - ((invTotal (M.Kφ φ))⁻¹ - φ * M.τ2)) := by
  have : Nonempty J := ⟨j⟩
  rw [M.bestZ_momentsφ hρ h0 h1, Model.bestZ_eq _ ((M.withLevel φ h1).K_posDef hρ) j,
    M.glsWeight_Kφ hρ h0 h1, M.s2_Kφ hρ h0 h1, add_sub_cancel_right]
  rfl

/-! ### Bridge 3: the §2.8 estimators with a shared level -/

/-- `cov(μᵢₜ, μⱼₛ)` when the levels share `φτ²`: eq. (16) with the level
covariance `τ²(11ᵀ)^φ` in place of `τ²δᵢⱼ`. -/
noncomputable def obsCovφ (φ : ℝ) (i j : J) (t s : T) : ℝ :=
  M.σ i t * M.σ j s * M.ρ i j * (if t = s then 1 else 0) + levelCov M.τ2 φ i j

/-- Expectation of the quadratic form `quad Q` when the levels share `φτ²`
(as `Model.E`, with `obsCovφ` in place of `obsCov`). -/
noncomputable def Eφ (φ μ : ℝ) (Q : J × T → J × T → ℝ) : ℝ :=
  ∑ p, ∑ q, Q p q * (M.obsCovφ φ p.1 q.1 p.2 q.2 + μ ^ 2)

/-- `f` is unbiased for `θ` when the levels share `φτ²`: a quadratic form in the
data with expectation `θ` for every mean `μ`. -/
def Unbiasedφ (φ : ℝ) (f : (J × T → ℝ) → ℝ) (θ : ℝ) : Prop :=
  ∃ Q : J × T → J × T → ℝ, (∀ X, quad Q X = f X) ∧ ∀ μ, M.Eφ φ μ Q = θ

/-- The part of an expectation coming from the sampling noise. -/
noncomputable def errPart (Q : J × T → J × T → ℝ) : ℝ :=
  ∑ p, ∑ q, Q p q * (M.σ p.1 p.2 * M.σ q.1 q.2 * M.ρ p.1 q.1 * if p.2 = q.2 then 1 else 0)

/-- Splitting an expectation: noise, level variance on same-cohort pairs, and
the mean on all pairs. -/
lemma E_split (μ : ℝ) (Q : J × T → J × T → ℝ) :
    M.E μ Q = M.errPart Q
      + M.τ2 * ∑ p, ∑ q, Q p q * (if p.1 = q.1 then 1 else 0) + μ ^ 2 * ∑ p, ∑ q, Q p q := by
  simp only [E, mom2, obsCov, errPart, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- …and with a shared level: the level adds `(1-φ)τ²` on same-cohort pairs
and `φτ²` on all pairs, like the mean. -/
lemma Eφ_split (φ μ : ℝ) (Q : J × T → J × T → ℝ) :
    M.Eφ φ μ Q = M.errPart Q
      + (1 - φ) * M.τ2 * ∑ p, ∑ q, Q p q * (if p.1 = q.1 then 1 else 0)
      + (φ * M.τ2 + μ ^ 2) * ∑ p, ∑ q, Q p q := by
  simp only [Eφ, obsCovφ, errPart, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [levelCov_apply]
  split_ifs <;> ring

/-- An estimator unbiased in the thesis model is unbiased with a shared level,
for the value obtained by affine extrapolation in `φ`: if `f` is unbiased for
`θ` in `M` and for `θ'` in `M_ψ` (`ψ ≠ 0`), then under `K_φ` it is unbiased for
`θ + (φ/ψ)(θ' - θ)`, for every `φ`. -/
theorem unbiasedφ_of {f : (J × T → ℝ) → ℝ} {θ θ' ψ : ℝ} (hf : M.Unbiased f θ) (h1 : ψ < 1)
    (hψ : ψ ≠ 0) (hf' : (M.withLevel ψ h1).Unbiased f θ') (φ : ℝ) :
    M.Unbiasedφ φ f (θ + φ / ψ * (θ' - θ)) := by
  obtain ⟨Q, hQ, hE⟩ := hf
  obtain ⟨Q', hQ', hE'⟩ := hf'
  refine ⟨Q, hQ, fun μ => ?_⟩
  have h0 := hE 0
  have h1' := hE 1
  -- In `M_ψ` the expectation of `f` is `θ'`, whatever matrix represents it.
  have hW : (M.withLevel ψ h1).E 0 Q = θ' :=
    ((M.withLevel ψ h1).E_congr 0 fun X => (hQ X).trans (hQ' X).symm).trans (hE' 0)
  rw [E_split] at h0 h1' hW
  rw [Eφ_split]
  have hA : (M.withLevel ψ h1).errPart Q = M.errPart Q := rfl
  have hτ : (M.withLevel ψ h1).τ2 = (1 - ψ) * M.τ2 := rfl
  rw [hA, hτ] at hW
  set A := M.errPart Q
  set D := ∑ p, ∑ q, Q p q * (if p.1 = q.1 then (1 : ℝ) else 0)
  set S := ∑ p, ∑ q, Q p q
  norm_num at h0 h1' hW
  -- The thesis estimator does not see the mean: `S = 0`.
  have hS : S = 0 := by linarith
  have key : M.τ2 * D = (θ - θ') / ψ := by
    field_simp
    linear_combination h0 - hW
  rw [hS, show φ / ψ * (θ' - θ) = -φ * ((θ - θ') / ψ) by ring, ← key]
  linear_combination h0

variable {w : J → T → ℝ} (sig : J → ℝ) (hw : ∀ j t, 0 < w j t)
  (hσ : ∀ j t, M.σ j t = sig j / √(w j t))
include hw hσ

/-- With a shared level, `σ²ᵢⱼρᵢⱼ^` is still unbiased for `σ²ᵢⱼρᵢⱼ`: it uses
only deviations within a cohort, where the level cancels. -/
theorem sigRhoHat_unbiasedφ (hT : 2 ≤ Fintype.card T) (φ : ℝ) (i j : J) :
    M.Unbiasedφ φ (fun X => sigRhoHat w X i j) (M.σ2 i j * M.ρ i j) := by
  have h := M.unbiasedφ_of (M.sigRhoHat_unbiased sig hw hσ hT i j)
    (ψ := 1 / 2) (by norm_num) (by norm_num)
    ((M.withLevel (1 / 2) (by norm_num)).sigRhoHat_unbiased sig hw hσ hT i j) φ
  have hσ2 : (M.withLevel (1 / 2) (by norm_num)).σ2 = M.σ2 := rfl
  have hρ : (M.withLevel (1 / 2) (by norm_num)).ρ = M.ρ := rfl
  rw [hσ2, hρ] at h
  simpa using h

/-- Bridge 3: with a shared level, `τ̂²` (eq. (39)) is unbiased for the non-shared
part `(1-φ)τ²`, for every `φ`. At `φ = 1` its expectation is `0`: a common
level is invisible to the data, like the mean `μ`. -/
theorem tauHat_unbiasedφ (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) (φ : ℝ) :
    M.Unbiasedφ φ (tauHat w) ((1 - φ) * M.τ2) := by
  have h := M.unbiasedφ_of (M.tauHat_unbiased sig hw hσ hT hJ)
    (ψ := 1 / 2) (by norm_num) (by norm_num)
    ((M.withLevel (1 / 2) (by norm_num)).tauHat_unbiased sig hw hσ hT hJ) φ
  have hτ : (M.withLevel (1 / 2) (by norm_num)).τ2 = (1 - 1 / 2) * M.τ2 := rfl
  rw [hτ] at h
  convert h using 1
  ring

/-- With a shared level, `K̂ᵢⱼ` is unbiased for `(K_φ - φτ²·11ᵀ)ᵢⱼ`, the thesis
`K` with `τ²` replaced by `(1-φ)τ²`: by Bridge 2, all that credibility needs. -/
theorem KHat_unbiasedφ (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) (φ : ℝ)
    (i j : J) : M.Unbiasedφ φ (fun X => KHat w X i j) (M.Kφ φ i j - φ * M.τ2) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have h := M.unbiasedφ_of (M.KHat_unbiased sig hw hσ hT hJ i j)
    (ψ := 1 / 2) (by norm_num) (by norm_num)
    ((M.withLevel (1 / 2) (by norm_num)).KHat_unbiased sig hw hσ hT hJ i j) φ
  have hτ : (M.withLevel (1 / 2) (by norm_num)).τ2 = (1 - 1 / 2) * M.τ2 := rfl
  have hσ2 : (M.withLevel (1 / 2) (by norm_num)).σ2 = M.σ2 := rfl
  have hρ : (M.withLevel (1 / 2) (by norm_num)).ρ = M.ρ := rfl
  rw [K_apply, K_apply, hτ, hσ2, hρ] at h
  convert h using 1
  rw [Kφ, Matrix.add_apply, levelCov_apply]
  by_cases hij : i = j <;> simp [hij, errCov]; ring

end Model

/-! ### Bridge 4: several groups, each with its own shared level -/

section Blocks

variable {J G : Type*} [Fintype J] [DecidableEq J] [Fintype G] [DecidableEq G] (grp : J → G)

/-- The block of `K` on group `g`. -/
def block (K : Matrix J J ℝ) (g : G) : Matrix {j // grp j = g} {j // grp j = g} ℝ :=
  K.submatrix Subtype.val Subtype.val

/-- `K` is block diagonal with respect to `grp`. -/
def IsBlockDiag (K : Matrix J J ℝ) : Prop := ∀ i j, grp i ≠ grp j → K i j = 0

variable {grp}

omit [Fintype J] [DecidableEq J] [Fintype G] [DecidableEq G] in
lemma block_posDef {K : Matrix J J ℝ} (hK : K.PosDef) (g : G) : (block grp K g).PosDef :=
  hK.submatrix Subtype.val_injective

omit [DecidableEq J] [Fintype G] in
/-- A sum over `J` of a function vanishing outside group `g` is a sum over the group. -/
lemma sum_eq_sum_block (g : G) (f : J → ℝ) (hf : ∀ j, grp j ≠ g → f j = 0) :
    ∑ j, f j = ∑ j : {j // grp j = g}, f j := by
  rw [← Finset.sum_subtype (Finset.univ.filter (grp · = g)) (by simp), Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> simp [hf j, h]

omit [Fintype G] in
/-- For block-diagonal `K`, `K⁻¹1` is assembled from the blocks: `(K⁻¹1)ⱼ = (K_g⁻¹1)ⱼ`
with `g` the group of `j`. -/
theorem Kinv_one_blockDiag {K : Matrix J J ℝ} (hK : K.PosDef) (hb : IsBlockDiag grp K)
    (j : J) : (K⁻¹ *ᵥ 1) j = ((block grp K (grp j))⁻¹ *ᵥ 1) ⟨j, rfl⟩ := by
  set x : J → ℝ := fun j => ((block grp K (grp j))⁻¹ *ᵥ 1) ⟨j, rfl⟩
  have hx : ∀ g (j : J) (h : grp j = g), x j = ((block grp K g)⁻¹ *ᵥ 1) ⟨j, h⟩ := by
    intro g j h; subst h; rfl
  have hKx : K *ᵥ x = 1 := by
    ext i
    simp only [mulVec, dotProduct, Pi.one_apply]
    rw [sum_eq_sum_block (grp := grp) (grp i) _ fun j hj => by rw [hb i j (Ne.symm hj), zero_mul]]
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (block_posDef (grp := grp) hK (grp i)).isUnit
    have := congrFun (mul_nonsing_inv _ hdet) ⟨i, rfl⟩
    have h1 : ((block grp K (grp i)) *ᵥ ((block grp K (grp i))⁻¹ *ᵥ 1)) ⟨i, rfl⟩ = 1 := by
      rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]; rfl
    rw [← h1]
    simp only [mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [hx _ _ j.2]; rfl
  have hdet := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  rw [← hKx, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]

/-- The precision `1ᵀK⁻¹1` of a block-diagonal `K` is the sum of the block precisions. -/
theorem invTotal_blockDiag {K : Matrix J J ℝ} (hK : K.PosDef) (hb : IsBlockDiag grp K) :
    invTotal K = ∑ g, invTotal (block grp K g) := by
  rw [invTotal, one_dotProduct, ← Finset.sum_fiberwise Finset.univ grp]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [invTotal, one_dotProduct, Finset.sum_subtype _ (p := (grp · = g)) (by simp)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Kinv_one_blockDiag hK hb]
  obtain ⟨j, h⟩ := a
  subst h; rfl

/-- Two-stage GLS: for block-diagonal `K`, the GLS weight of `j` is its GLS weight
within its group `g`, times the inverse-variance weight (eq. (23)) of the group,
whose variance is the group's `s²_g = 1/1ᵀK_g⁻¹1`. -/
theorem glsWeight_blockDiag {K : Matrix J J ℝ} (hK : K.PosDef) (hb : IsBlockDiag grp K)
    (j : J) : glsWeight K j = glsWeight (block grp K (grp j)) ⟨j, rfl⟩
      * invVarWeight (fun g => (invTotal (block grp K g))⁻¹) (grp j) := by
  have : Nonempty {i // grp i = grp j} := ⟨⟨j, rfl⟩⟩
  have hg := (invTotal_pos (block_posDef (grp := grp) hK (grp j))).ne'
  simp only [glsWeight, invVarWeight, inv_inv, ← invTotal_blockDiag hK hb,
    Kinv_one_blockDiag hK hb]
  field_simp

end Blocks

namespace Model

variable {J T G : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
  [Fintype G] [DecidableEq G]
variable (M : Model J T) (grp : J → G)

/-- Indicator `1_g` of group `g`. -/
def grpOne (g : G) : J → ℝ := fun j => if grp j = g then 1 else 0

/-- Total weight `B_g = Σ_{grp i = g} bᵢ` that `b` gives to group `g`. -/
def groupWeight (b : J → ℝ) (g : G) : ℝ := ∑ i, if grp i = g then b i else 0

/-- Level covariance with several groups, each with its own shared level:
`τ²` on the diagonal, `φτ²` within a group, `0` across groups. -/
def levelCovG (τ2 φ : ℝ) : Matrix J J ℝ :=
  of fun i j => if i = j then τ2 else if grp i = grp j then φ * τ2 else 0

/-- The covariance of the cohort estimates with group levels: `K_G = L_G + Σ`. -/
noncomputable def KG (φ : ℝ) : Matrix J J ℝ := levelCovG grp M.τ2 φ + M.errCov

omit [Fintype J] [Fintype G] in
lemma levelCovG_apply' (τ2 φ : ℝ) (i j : J) :
    levelCovG grp τ2 φ i j
      = (1 - φ) * τ2 * (if i = j then 1 else 0) + φ * τ2 * (if grp i = grp j then 1 else 0) := by
  by_cases h : i = j
  · subst h; simp [levelCovG]; ring
  · by_cases hg : grp i = grp j <;> simp [levelCovG, h, hg]

omit [Fintype J] in
/-- `L_G = (1-φ)τ²·I + φτ²·Σ_g 1_g1_gᵀ`: one rank-one term per group. -/
lemma levelCovG_eq (τ2 φ : ℝ) :
    levelCovG grp τ2 φ = ((1 - φ) * τ2) • (1 : Matrix J J ℝ)
      + (φ * τ2) • ∑ g, vecMulVec (grpOne grp g) (grpOne grp g) := by
  ext i j
  rw [levelCovG_apply']
  simp [Matrix.sum_apply, vecMulVec, grpOne, Matrix.one_apply, eq_comm]

omit [Fintype J] [Fintype G] in
/-- One group is Bridge 2: `L_G = τ²(11ᵀ)^φ`. -/
lemma levelCovG_const (h : ∀ i j, grp i = grp j) (τ2 φ : ℝ) :
    levelCovG grp τ2 φ = levelCov τ2 φ := by
  ext i j; rw [levelCov_apply]; simp [levelCovG, h i j]

omit [Fintype J] in
/-- `K_G` is the thesis `K` with `τ²` replaced by `(1-φ)τ²`, plus `φτ²·1_g1_gᵀ` per group. -/
theorem KG_eq [Nonempty T] {φ : ℝ} (h1 : φ < 1) :
    M.KG grp φ = (M.withLevel φ h1).K + (φ * M.τ2) • ∑ g, vecMulVec (grpOne grp g) (grpOne grp g) := by
  have he : M.errCov = (M.withLevel φ h1).errCov := rfl
  have hτ : (M.withLevel φ h1).τ2 = (1 - φ) * M.τ2 := rfl
  rw [KG, levelCovG_eq, he, errCov_eq, hτ]
  abel

/-- For `φ ∈ [0,1)`, `K_G` is positive definite. -/
theorem KG_posDef [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) : (M.KG grp φ).PosDef := by
  have hR : (∑ g, vecMulVec (grpOne grp g) (grpOne grp g)).PosSemidef :=
    posSemidef_sum _ fun g _ => by simpa using posSemidef_vecMulVec_self_star (grpOne grp g)
  rw [KG, levelCovG_eq]
  exact (PosDef.add_posSemidef (PosDef.one.smul (mul_pos (sub_pos.mpr h1) M.τ2_pos))
    (hR.smul (mul_nonneg h0 M.τ2_pos.le))).add_posSemidef (M.errCov_posSemidef hρ)

omit [Fintype J] [DecidableEq T] [Fintype G] in
/-- Errors uncorrelated across groups make `K_G` block diagonal. -/
theorem KG_isBlockDiag (hρ0 : ∀ i j, grp i ≠ grp j → M.ρ i j = 0) (φ : ℝ) :
    IsBlockDiag grp (M.KG grp φ) := by
  intro i j h
  have hij : i ≠ j := fun e => h (e ▸ rfl)
  simp [KG, levelCovG, errCov, hij, h, hρ0 i j h]

omit [Fintype J] [Fintype G] in
/-- …and each block is a thesis `K` plus a rank-one term: `(K_G)_g = K'_g + φτ²·11ᵀ`,
with `K'` the thesis `K` for `(1-φ)τ²`. -/
theorem block_KG [Nonempty T] {φ : ℝ} (h1 : φ < 1) (g : G) :
    block grp (M.KG grp φ) g = block grp (M.withLevel φ h1).K g + (φ * M.τ2) • vecMulVec 1 1 := by
  ext ⟨a, ha⟩ ⟨b, hb⟩
  have hτ : (M.withLevel φ h1).τ2 = (1 - φ) * M.τ2 := rfl
  have hσ : (M.withLevel φ h1).σ2 = M.σ2 := rfl
  have hρ : (M.withLevel φ h1).ρ = M.ρ := rfl
  simp only [block, submatrix_apply, Matrix.add_apply, KG, levelCovG_apply', K_apply, hτ, hσ, hρ,
    errCov, of_apply]
  simp [ha, hb]
  split_ifs <;> ring

variable {grp}

/-- GLS weights with group levels (errors uncorrelated across groups, every group
non-empty): two-stage GLS. Within group `g`, the thesis weights for `(1-φ)τ²`;
across groups, inverse-variance weights with group variance `s'²_g + φτ²`. -/
theorem glsWeight_KG [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) (hρ0 : ∀ i j, grp i ≠ grp j → M.ρ i j = 0) (hgrp : Function.Surjective grp)
    (j : J) :
    glsWeight (M.KG grp φ) j = glsWeight (block grp (M.withLevel φ h1).K (grp j)) ⟨j, rfl⟩
      * invVarWeight (fun g => (invTotal (block grp (M.withLevel φ h1).K g))⁻¹ + φ * M.τ2)
        (grp j) := by
  have hK := M.KG_posDef grp hρ h0 h1
  have hK' := (M.withLevel φ h1).K_posDef hρ
  have hblk : ∀ g, (block grp (M.withLevel φ h1).K g + (φ * M.τ2) • vecMulVec 1 1).PosDef :=
    fun g => M.block_KG grp h1 g ▸ block_posDef hK g
  have hs : (fun g => (invTotal (block grp (M.KG grp φ) g))⁻¹)
      = fun g => (invTotal (block grp (M.withLevel φ h1).K g))⁻¹ + φ * M.τ2 := by
    funext g
    obtain ⟨i, hi⟩ := hgrp g
    have : Nonempty {i // grp i = g} := ⟨⟨i, hi⟩⟩
    rw [M.block_KG grp h1]
    exact invTotal_inv_add_rankOne (block_posDef hK' g) _ (hblk g)
  rw [glsWeight_blockDiag hK (M.KG_isBlockDiag grp hρ0 φ), hs, M.block_KG grp h1,
    glsWeight_add_rankOne (block_posDef hK' _) _ (hblk _)]

/-- …and the portfolio variance is the harmonic combination of the group
variances `s'²_g + φτ²`: the between-group variance no longer just adds. -/
theorem s2_KG [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) (hρ0 : ∀ i j, grp i ≠ grp j → M.ρ i j = 0) (hgrp : Function.Surjective grp) :
    (invTotal (M.KG grp φ))⁻¹
      = (∑ g, ((invTotal (block grp (M.withLevel φ h1).K g))⁻¹ + φ * M.τ2)⁻¹)⁻¹ := by
  have hK := M.KG_posDef grp hρ h0 h1
  have hK' := (M.withLevel φ h1).K_posDef hρ
  rw [invTotal_blockDiag hK (M.KG_isBlockDiag grp hρ0 φ)]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  obtain ⟨i, hi⟩ := hgrp g
  have : Nonempty {i // grp i = g} := ⟨⟨i, hi⟩⟩
  have hb := M.block_KG grp h1 g
  rw [← invTotal_inv_add_rankOne (block_posDef hK' g) _ (hb ▸ block_posDef hK g), ← hb, inv_inv]

/-- The moments entering the blend for cohort `j` with group levels: as
`momentsφ`, with the level covariance `L_G`. -/
noncomputable def momentsG (grp : J → G) (φ : ℝ) (j : J) : BlendMoments where
  varCohort := M.τ2 + M.σ2 j j
  varPortfolio := (invTotal (M.KG grp φ))⁻¹
  varTarget := M.τ2
  covEst := (M.KG grp φ *ᵥ glsWeight (M.KG grp φ)) j
  covCohortTarget := M.τ2
  covPortfolioTarget := (levelCovG grp M.τ2 φ *ᵥ glsWeight (M.KG grp φ)) j

/-- Eq. (26) with group levels: with `b`, `s²` the GLS weights and portfolio
variance of `K_G` and `B_g` the total weight of the group `g` of `j`,
`zⱼ = ((1-φ)τ²(1 - bⱼ) + φτ²(1 - B_g)) / (τ² + vⱼ - s²)`. Each part of the
level variance counts with the weight the portfolio puts outside what it
shares with `j`. -/
theorem bestZ_G_eq [Nonempty T] (hρ : (Matrix.of M.ρ).PosSemidef) {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < 1) (j : J) :
    (M.momentsG grp φ j).bestZ
      = ((1 - φ) * M.τ2 * (1 - glsWeight (M.KG grp φ) j)
          + φ * M.τ2 * (1 - groupWeight grp (glsWeight (M.KG grp φ)) (grp j)))
        / (M.τ2 + M.σ2 j j - (invTotal (M.KG grp φ))⁻¹) := by
  have : Nonempty J := ⟨j⟩
  have hK := M.KG_posDef grp hρ h0 h1
  set b := glsWeight (M.KG grp φ)
  have hL : (levelCovG grp M.τ2 φ *ᵥ b) j
      = (1 - φ) * M.τ2 * b j + φ * M.τ2 * groupWeight grp b (grp j) := by
    have hx : ∀ x, levelCovG grp M.τ2 φ j x * b x = (1 - φ) * M.τ2 * (if j = x then b x else 0)
        + φ * M.τ2 * (if grp x = grp j then b x else 0) := by
      intro x
      rw [levelCovG_apply']
      by_cases h : j = x
      · subst h; simp; ring
      · by_cases hg : grp x = grp j
        · simp only [h, hg, ite_true, ite_false]; ring
        · have hg' : ¬grp j = grp x := fun e => hg e.symm
          simp only [h, hg, hg', ite_false]; ring
    simp only [mulVec, dotProduct, hx, Finset.sum_add_distrib, ← Finset.mul_sum, groupWeight,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [BlendMoments.bestZ, BlendMoments.gap, momentsG]
  rw [show (levelCovG grp M.τ2 φ *ᵥ glsWeight (M.KG grp φ)) j = _ from hL, mulVec_glsWeight hK]
  congr 1 <;> ring

/-! ### Bridge 5: the §2.8 estimators with group levels -/

variable (grp)

/-- `cov(μᵢₜ, μⱼₛ)` with group levels: eq. (16) with `L_G` in place of `τ²δᵢⱼ`. -/
noncomputable def obsCovG (φ : ℝ) (i j : J) (t s : T) : ℝ :=
  M.σ i t * M.σ j s * M.ρ i j * (if t = s then 1 else 0) + levelCovG grp M.τ2 φ i j

/-- Expectation of `quad Q` with group levels (as `Model.E`, with `obsCovG`). -/
noncomputable def EG (φ μ : ℝ) (Q : J × T → J × T → ℝ) : ℝ :=
  ∑ p, ∑ q, Q p q * (M.obsCovG grp φ p.1 q.1 p.2 q.2 + μ ^ 2)

/-- `f` is unbiased for `θ` with group levels, whatever the mean `μ`. -/
def UnbiasedG (φ : ℝ) (f : (J × T → ℝ) → ℝ) (θ : ℝ) : Prop :=
  ∃ Q : J × T → J × T → ℝ, (∀ X, quad Q X = f X) ∧ ∀ μ, M.EG grp φ μ Q = θ

/-- The noise-free data `1_g`: `1` on every cell of a cohort in group `g`, `0` elsewhere. -/
def grpData (g : G) : J × T → ℝ := fun p => grpOne grp g p.1

omit [DecidableEq J] [DecidableEq T] in
/-- Summing a quadratic form over the group patterns picks the same-group pairs. -/
lemma sum_quad_grpData (Q : J × T → J × T → ℝ) :
    ∑ g, quad Q (grpData grp g) = ∑ p, ∑ q, Q p q * (if grp p.1 = grp q.1 then 1 else 0) := by
  simp only [quad, grpData, grpOne]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : grp p.1 = grp q.1
  · simp [h, eq_comm]
  · simp only [h, ite_false, mul_zero]
    refine Finset.sum_eq_zero fun g _ => ?_
    by_cases hp : grp p.1 = g
    · have : ¬grp q.1 = g := fun e => h (hp.trans e.symm)
      simp [this]
    · simp [hp]

/-- The group level moves an expectation by `φτ²` times the estimator at the
group patterns minus at the cohort patterns: within a group the shared part
`φτ²` acts like a common mean. -/
lemma EG_eq (φ μ : ℝ) (Q : J × T → J × T → ℝ) :
    M.EG grp φ μ Q = M.E μ Q - φ * M.τ2 * ∑ j, quad Q (grpData id j)
      + φ * M.τ2 * ∑ g, quad Q (grpData grp g) := by
  rw [sum_quad_grpData, sum_quad_grpData]
  simp only [EG, E, mom2, obsCovG, obsCov, levelCovG_apply', Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, id]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring

/-- Bridge 5: an estimator unbiased for `θ` in the thesis model has, with group
levels, expectation `θ - φτ²(Σⱼ f(1_{j}) - Σ_g f(1_g))`: evaluate it on the
noise-free cohort and group patterns. -/
theorem unbiasedG_of {f : (J × T → ℝ) → ℝ} {θ : ℝ} (hf : M.Unbiased f θ) (φ : ℝ) :
    M.UnbiasedG grp φ f
      (θ - φ * M.τ2 * ∑ j, f (grpData id j) + φ * M.τ2 * ∑ g, f (grpData grp g)) := by
  obtain ⟨Q, hQ, hE⟩ := hf
  exact ⟨Q, hQ, fun μ => by simp only [EG_eq, hE, hQ]⟩

variable {M grp} in
/-- An estimator has one expectation: `UnbiasedG` fixes the value. -/
theorem UnbiasedG.unique {φ : ℝ} {f : (J × T → ℝ) → ℝ} {θ θ' : ℝ}
    (h : M.UnbiasedG grp φ f θ) (h' : M.UnbiasedG grp φ f θ') : θ = θ' := by
  obtain ⟨Q, hQ, hE⟩ := h
  obtain ⟨Q', hQ', hE'⟩ := h'
  rw [← hE 0, ← hE' 0, EG_eq, EG_eq, M.E_congr 0 fun X => (hQ X).trans (hQ' X).symm]
  simp only [hQ, hQ']

omit [Fintype G] in
variable {M grp} in
/-- Linearity of `UnbiasedG`: sums. -/
lemma UnbiasedG.add {φ : ℝ} {f g : (J × T → ℝ) → ℝ} {θ θ' : ℝ} (hf : M.UnbiasedG grp φ f θ)
    (hg : M.UnbiasedG grp φ g θ') : M.UnbiasedG grp φ (fun X => f X + g X) (θ + θ') := by
  obtain ⟨Q, hQ, hE⟩ := hf
  obtain ⟨Q', hQ', hE'⟩ := hg
  refine ⟨fun p q => Q p q + Q' p q, fun X => ?_, fun μ => ?_⟩
  · beta_reduce; rw [← hQ, ← hQ']; simp only [quad, add_mul, Finset.sum_add_distrib]
  · rw [← hE μ, ← hE' μ]; simp only [EG, add_mul, Finset.sum_add_distrib]

omit [Fintype G] in
variable {M grp} in
/-- Linearity of `UnbiasedG`: scalar multiples. -/
lemma UnbiasedG.const_mul {φ : ℝ} {f : (J × T → ℝ) → ℝ} {θ : ℝ} (c : ℝ)
    (hf : M.UnbiasedG grp φ f θ) : M.UnbiasedG grp φ (fun X => c * f X) (c * θ) := by
  obtain ⟨Q, hQ, hE⟩ := hf
  refine ⟨fun p q => c * Q p q, fun X => ?_, fun μ => ?_⟩
  · beta_reduce; rw [← hQ]; simp only [quad, Finset.mul_sum, mul_assoc]
  · rw [← hE μ]; simp only [EG, Finset.mul_sum, mul_assoc]

omit [Fintype G] in
variable {M grp} in
lemma UnbiasedG.congr {φ : ℝ} {f g : (J × T → ℝ) → ℝ} {θ θ' : ℝ} (h : M.UnbiasedG grp φ f θ)
    (hf : ∀ X, f X = g X) (hθ : θ = θ') : M.UnbiasedG grp φ g θ' := by
  obtain ⟨Q, hQ, hE⟩ := h
  exact ⟨Q, fun X => (hQ X).trans (hf X), fun μ => (hE μ).trans hθ⟩

/-! #### Weighted share of same-group pairs -/

lemma groupWeight_id (b : J → ℝ) (j : J) : groupWeight id b j = b j := by
  simp [groupWeight]

omit [DecidableEq J] in
lemma sum_groupWeight (b : J → ℝ) : ∑ g, groupWeight grp b g = ∑ i, b i := by
  simp only [groupWeight]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq J] in
/-- `Σ_g W_g² = Σ_{g(i) = g(j)} WᵢWⱼ`. -/
lemma sum_groupWeight_sq (W : J → ℝ) :
    ∑ g, groupWeight grp W g ^ 2 = ∑ i, ∑ j, if grp i = grp j then W i * W j else 0 := by
  have h : ∀ g, groupWeight grp W g ^ 2
      = ∑ i, ∑ j, if grp i = g ∧ grp j = g then W i * W j else 0 := fun g => by
    simp only [groupWeight, sq, Finset.sum_mul_sum, ite_mul, mul_ite, zero_mul, mul_zero]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      by_cases hi : grp i = g <;> by_cases hj : grp j = g <;> simp [hi, hj]
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : grp i = grp j
  · simp [hij]
  · simp only [hij, ite_false]
    exact Finset.sum_eq_zero fun g _ => by
      rw [ite_eq_right_iff]; exact fun hg => absurd (hg.1.trans hg.2.symm) hij

omit [DecidableEq J] in
/-- `(Σ Wᵢ)² - Σ_g W_g² = Σ_{g(i) ≠ g(j)} WᵢWⱼ`: the pairs across groups. -/
lemma sq_sum_sub_sum_groupWeight_sq (W : J → ℝ) :
    (∑ i, W i) ^ 2 - ∑ g, groupWeight grp W g ^ 2
      = ∑ i, ∑ j, if grp i = grp j then 0 else W i * W j := by
  rw [sum_groupWeight_sq, sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- The weighted share of same-group pairs among pairs of distinct cohorts,
`π = Σ_{i≠j, g(i)=g(j)} WᵢWⱼ / Σ_{i≠j} WᵢWⱼ` (`withinShare_eq_pairs`). -/
noncomputable def withinShare (W : J → ℝ) : ℝ :=
  (∑ g, groupWeight grp W g ^ 2 - ∑ j, W j ^ 2) / ((∑ j, W j) ^ 2 - ∑ j, W j ^ 2)

lemma withinShare_eq_pairs (W : J → ℝ) :
    withinShare grp W = (∑ i, ∑ j, if i ≠ j ∧ grp i = grp j then W i * W j else 0)
      / ∑ i, ∑ j, if i ≠ j then W i * W j else 0 := by
  have hd := sq_sum_sub_sum_groupWeight_sq (id : J → J) W
  have hn := sq_sum_sub_sum_groupWeight_sq grp W
  simp only [groupWeight_id, id] at hd
  rw [withinShare]
  congr 1
  · have : ∑ g, groupWeight grp W g ^ 2 - ∑ j, W j ^ 2
        = ((∑ i, W i) ^ 2 - ∑ j, W j ^ 2) - ((∑ i, W i) ^ 2 - ∑ g, groupWeight grp W g ^ 2) := by
      ring
    rw [this, hd, hn, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i = j
    · subst h; simp
    · by_cases hg : grp i = grp j <;> simp [h, hg]
  · rw [hd]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      by_cases h : i = j <;> simp [h]

omit [Fintype G] [DecidableEq G] in
/-- With positive weights and two cohorts, the pairs of distinct cohorts have positive weight. -/
lemma sq_sum_sub_sum_sq_pos {W : J → ℝ} (hW : ∀ j, 0 < W j) (hJ : 2 ≤ Fintype.card J) :
    0 < (∑ j, W j) ^ 2 - ∑ j, W j ^ 2 := by
  have hd := sq_sum_sub_sum_groupWeight_sq (id : J → J) W
  simp only [groupWeight_id, id] at hd
  rw [hd]
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card J)
  have hnn : ∀ i j, 0 ≤ (if i = j then 0 else W i * W j) := fun i j => by
    split_ifs
    · exact le_rfl
    · exact (mul_pos (hW i) (hW j)).le
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => hnn i j) ⟨a, Finset.mem_univ _, ?_⟩
  refine Finset.sum_pos' (fun j _ => hnn a j) ⟨b, Finset.mem_univ _, ?_⟩
  simp [hab, mul_pos (hW a) (hW b)]

/-- `π = 1` (no pairs across groups) exactly when there is one group. -/
lemma withinShare_eq_one_iff {W : J → ℝ} (hW : ∀ j, 0 < W j) (hJ : 2 ≤ Fintype.card J) :
    withinShare grp W = 1 ↔ ∀ i j, grp i = grp j := by
  have hD := sq_sum_sub_sum_sq_pos hW hJ
  have hn := sq_sum_sub_sum_groupWeight_sq grp W
  have hnn : ∀ i j, 0 ≤ (if grp i = grp j then 0 else W i * W j) := fun i j => by
    split_ifs
    · exact le_rfl
    · exact (mul_pos (hW i) (hW j)).le
  rw [withinShare, div_eq_one_iff_eq hD.ne']
  constructor
  · intro h i j
    have h0 : ∑ i, ∑ j, (if grp i = grp j then 0 else W i * W j) = 0 := by
      rw [← hn]; linarith
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hnn i j).mp h0 i (Finset.mem_univ _)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn i j).mp hi j (Finset.mem_univ _)
    by_contra hg
    simp only [hg, ite_false] at hij
    exact (mul_pos (hW i) (hW j)).ne' hij
  · intro h
    have h0 : ∑ i, ∑ j, (if grp i = grp j then 0 else W i * W j) = 0 :=
      Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by simp [h i j]
    linarith

/-! #### The estimators on the noise-free patterns -/

omit [Fintype J] [DecidableEq J] [DecidableEq T] [Fintype G] [DecidableEq G] in
lemma wtot_pos' [Nonempty T] {w : J → T → ℝ} (hw : ∀ j t, 0 < w j t) (j : J) : 0 < wtot w j :=
  Finset.sum_pos (fun t _ => hw j t) Finset.univ_nonempty

omit [Fintype J] [DecidableEq J] [DecidableEq T] [Fintype G] in
lemma muHat_grpData [Nonempty T] {w : J → T → ℝ} (hw : ∀ j t, 0 < w j t) (g : G) (j : J) :
    muHat w (grpData grp g) j = grpOne grp g j := by
  simp only [muHat, grpData]
  have : (∑ t, w j t) / wtot w j = 1 := div_self (wtot_pos' hw j).ne'
  rw [← Finset.sum_mul, ← Finset.sum_div, this, one_mul]

omit [Fintype J] [DecidableEq J] [DecidableEq T] [Fintype G] in
lemma sigRhoHat_grpData [Nonempty T] {w : J → T → ℝ} (hw : ∀ j t, 0 < w j t) (g : G) (i j : J) :
    sigRhoHat w (grpData grp g) i j = 0 := by
  simp [sigRhoHat, muHat_grpData grp hw, grpData]

omit [DecidableEq T] [Fintype G] in
lemma tauHat_grpData [Nonempty T] [Nonempty J] {w : J → T → ℝ} (hw : ∀ j t, 0 < w j t) (g : G) :
    tauHat w (grpData grp g)
      = (groupWeight grp (wtot w) g - groupWeight grp (wtot w) g ^ 2 / wall w)
        / (wall w - ∑ i, wtot w i ^ 2 / wall w) := by
  have hS : 0 < wall w := Finset.sum_pos (fun j _ => wtot_pos' hw j) Finset.univ_nonempty
  have hc : ∀ j, cHat w (grpData grp g) j = 0 := fun j => by
    simp [cHat, sigRhoHat_grpData grp hw]
  simp only [tauHat, hc, muHat_grpData grp hw, sub_zero]
  congr 1
  set Wg := groupWeight grp (wtot w) g
  have h1 : ∑ i, wtot w i / wall w * grpOne grp g i = Wg / wall w := by
    rw [show Wg = ∑ i, if grp i = g then wtot w i else 0 from rfl, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by simp only [grpOne]; split_ifs <;> ring
  have h2 : ∀ j, wtot w j * (grpOne grp g j - Wg / wall w) ^ 2
      = (if grp j = g then wtot w j else 0) * (1 - 2 * (Wg / wall w))
        + wtot w j * (Wg / wall w) ^ 2 := fun j => by
    simp only [grpOne]; split_ifs <;> ring
  rw [h1]
  simp only [h2, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [show (∑ j, if grp j = g then wtot w j else 0) = Wg from rfl,
    show (∑ j, wtot w j) = wall w from rfl]
  field_simp
  ring

omit [DecidableEq T] in
/-- The estimator `τ̂²` at the group patterns minus at the cohort patterns is `-π`. -/
lemma sum_tauHat_grpData (hJ : 2 ≤ Fintype.card J) [Nonempty T] {w : J → T → ℝ}
    (hw : ∀ j t, 0 < w j t) :
    ∑ j, tauHat w (grpData id j) - ∑ g, tauHat w (grpData grp g) = withinShare grp (wtot w) := by
  have : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  have hS : 0 < wall w := Finset.sum_pos (fun j _ => wtot_pos' hw j) Finset.univ_nonempty
  have hD := sq_sum_sub_sum_sq_pos (wtot_pos' hw) hJ
  rw [show (∑ j, wtot w j) = wall w from rfl] at hD
  simp only [tauHat_grpData grp hw, tauHat_grpData (id : J → J) hw, groupWeight_id, ← Finset.sum_div,
    Finset.sum_sub_distrib, sum_groupWeight]
  rw [withinShare, show (∑ j, wtot w j) = wall w from rfl]
  have hden : wall w - (∑ i, wtot w i ^ 2) / wall w = (wall w ^ 2 - ∑ i, wtot w i ^ 2) / wall w := by
    field_simp
  rw [hden]
  field_simp
  ring

/-- The pair estimator `(μ̂ᵢ - μ̂ⱼ)² - (σ²ᵢᵢρᵢᵢ^ + σ²ⱼⱼρⱼⱼ^ - 2σ²ᵢⱼρᵢⱼ^)`: the
squared difference of two cohort estimates, minus its estimated noise. -/
noncomputable def pairHat (w : J → T → ℝ) (X : J × T → ℝ) (i j : J) : ℝ :=
  (muHat w X i - muHat w X j) ^ 2 - (sigRhoHat w X i i + sigRhoHat w X j j - 2 * sigRhoHat w X i j)

/-! #### Expectations with group levels -/

variable {w : J → T → ℝ} (sig : J → ℝ) (hw : ∀ j t, 0 < w j t)
  (hσ : ∀ j t, M.σ j t = sig j / √(w j t))
include hw hσ

/-- With group levels, `σ²ᵢⱼρᵢⱼ^` is still unbiased: it uses only deviations
within a cohort. -/
theorem sigRhoHat_unbiasedG (hT : 2 ≤ Fintype.card T) (φ : ℝ) (i j : J) :
    M.UnbiasedG grp φ (fun X => sigRhoHat w X i j) (M.σ2 i j * M.ρ i j) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have h := M.unbiasedG_of grp (M.sigRhoHat_unbiased sig hw hσ hT i j) φ
  simpa [sigRhoHat_grpData _ hw] using h

/-- Bridge 5: with group levels, `E τ̂² = τ² - φτ²·π`, with `π` the weighted
share of same-group pairs (`withinShare`, weights `wⱼ*`). `τ̂²` averages
`½E(μ̂ᵢ - μ̂ⱼ)²` over pairs, and a pair in one group shares `φτ²`. One group:
`π = 1`, Bridge 3; singleton groups: `π = 0`, the thesis. -/
theorem tauHat_unbiasedG (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) (φ : ℝ) :
    M.UnbiasedG grp φ (tauHat w) (M.τ2 - φ * M.τ2 * withinShare grp (wtot w)) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have h := M.unbiasedG_of grp (M.tauHat_unbiased sig hw hσ hT hJ) φ
  convert h using 1
  rw [← sum_tauHat_grpData grp hJ hw]
  ring

/-- With group levels, `E K̂ᵢⱼ = σ²ᵢⱼρᵢⱼ + (τ² - φτ²π)δᵢⱼ`. -/
theorem KHat_unbiasedG (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) (φ : ℝ) (i j : J) :
    M.UnbiasedG grp φ (fun X => KHat w X i j)
      (M.σ2 i j * M.ρ i j
        + (M.τ2 - φ * M.τ2 * withinShare grp (wtot w)) * (if i = j then 1 else 0)) :=
  ((M.sigRhoHat_unbiasedG grp sig hw hσ hT φ i j).add
    ((M.tauHat_unbiasedG grp sig hw hσ hT hJ φ).const_mul (if i = j then 1 else 0))).congr
    (fun X => by simp only [KHat]; ring) (by ring)

/-- `K̂` estimates `K_G - φτ²·[g(i) = g(j)]`, the thesis `K` for the non-shared
part `(1-φ)τ²` (all the within-group weights need, by Bridge 4), exactly when
there is one group, as in Bridge 3. With two or more groups `τ̂²` picks up
`φτ²(1-π)` from the pairs across groups. -/
theorem KHat_unbiasedG_iff (hT : 2 ≤ Fintype.card T) (hJ : 2 ≤ Fintype.card J) {φ : ℝ}
    (hφ : φ ≠ 0) :
    (∀ i j, M.UnbiasedG grp φ (fun X => KHat w X i j)
        (M.KG grp φ i j - φ * M.τ2 * (if grp i = grp j then 1 else 0)))
      ↔ ∀ i j, grp i = grp j := by
  have hK : ∀ i j, M.KG grp φ i j - φ * M.τ2 * (if grp i = grp j then 1 else 0)
      = M.σ2 i j * M.ρ i j + (1 - φ) * M.τ2 * (if i = j then 1 else 0) := fun i j => by
    rw [KG, Matrix.add_apply, levelCovG_apply']; simp only [errCov, of_apply]; ring
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have hπ := withinShare_eq_one_iff grp (wtot_pos' (T := T) hw) hJ
  constructor
  · intro h
    rw [← hπ]
    obtain ⟨j⟩ : Nonempty J := Fintype.card_pos_iff.mp (by omega)
    have e := (h j j).unique (M.KHat_unbiasedG grp sig hw hσ hT hJ φ j j)
    rw [hK] at e
    simp only [ite_true, mul_one] at e
    have : φ * M.τ2 * (withinShare grp (wtot w) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (mul_ne_zero hφ M.τ2_pos.ne')
    · linarith
  · intro h i j
    rw [hK]
    exact (M.KHat_unbiasedG grp sig hw hσ hT hJ φ i j).congr (fun _ => rfl)
      (by rw [hπ.mpr h]; ring)

/-! #### Identifying `φτ²`: pairs within and across groups -/

/-- In the thesis model the pair estimator is unbiased for `2τ²` (`i ≠ j`):
`E(μ̂ᵢ - μ̂ⱼ)² = Kᵢᵢ + Kⱼⱼ - 2Kᵢⱼ`. -/
theorem pairHat_unbiased (hT : 2 ≤ Fintype.card T) {i j : J} (hij : i ≠ j) :
    M.Unbiased (fun X => pairHat w X i j) (2 * M.τ2) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have ha := M.a_special sig hw hσ
  have hW : ∀ k, (∑ t, w k t) / wtot w k = 1 := fun k => div_self (wtot_pos' hw k).ne'
  let ℓ : J × T → ℝ := fun p =>
    (if p.1 = i then M.a i p.2 else 0) - (if p.1 = j then M.a j p.2 else 0)
  have pull : ∀ (k : J) (g : J → T → ℝ),
      ∑ x, ∑ s, (if x = k then g x s else 0) = ∑ s, g k s := fun k g => by
    rw [Finset.sum_comm]; simp [Finset.sum_ite_eq']
  have hlin : ∀ X : J × T → ℝ, ∑ p, ℓ p * X p = muHat w X i - muHat w X j := fun X => by
    simp only [ℓ, Fintype.sum_prod_type, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
      pull, muHat, ha]
  have hsum : ∑ p, ℓ p = 0 := by
    simp only [ℓ, Fintype.sum_prod_type, Finset.sum_sub_distrib, Finset.sum_ite_irrel,
      Finset.sum_const_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ha, ← Finset.sum_div, hW, sub_self]
  have hcov : ∑ p, ∑ q, ℓ p * ℓ q * M.obsCov p.1 q.1 p.2 q.2
      = M.K i i + M.K j j - M.K i j - M.K j i := by
    simp only [ℓ, Fintype.sum_prod_type, sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, K]
    ring
  have hsq : M.Unbiased (fun X => (muHat w X i - muHat w X j) ^ 2)
      (M.K i i + M.K j j - M.K i j - M.K j i) :=
    (M.unbiased_mul ℓ ℓ hsum).congr (fun X => by rw [hlin, sq]) hcov
  have hs : ∀ k l, M.Unbiased (fun X => sigRhoHat w X k l) (M.σ2 k l * M.ρ k l) :=
    M.sigRhoHat_unbiased sig hw hσ hT
  refine (hsq.add ((((hs i i).add (hs j j)).add ((hs i j).const_mul (-2))).const_mul (-1))).congr
    (fun X => by simp only [pairHat]; ring) ?_
  have hσ2 : M.σ2 j i = M.σ2 i j := by
    simp only [Model.σ2]; exact Finset.sum_congr rfl fun t _ => by ring
  rw [M.K_apply, M.K_apply, M.K_apply, M.K_apply, hσ2, M.ρ_symm j i]
  simp [hij, Ne.symm hij]
  ring

omit [Fintype J] [DecidableEq J] [DecidableEq T] hσ in
lemma sum_pairHat_grpData [Nonempty T] (i j : J) :
    ∑ g, pairHat w (grpData grp g) i j = if grp i = grp j then 0 else 2 := by
  simp only [pairHat, muHat_grpData grp hw, sigRhoHat_grpData grp hw, grpOne]
  by_cases h : grp i = grp j
  · simp [h]
  · simp only [h, ite_false, add_zero, mul_zero, sub_zero]
    have : ∀ g : G, ((if grp i = g then (1 : ℝ) else 0) - if grp j = g then 1 else 0) ^ 2
        = (if grp i = g then 1 else 0) + (if grp j = g then 1 else 0) := fun g => by
      by_cases hi : grp i = g <;> by_cases hj : grp j = g
      · exact absurd (hi.trans hj.symm) h
      all_goals simp [hi, hj]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    norm_num

/-- Bridge 5: with group levels the pair estimator is unbiased for
`2τ² - 2φτ²·[g(i) = g(j)]`: a pair across groups sees the whole level variance,
a pair within a group only the non-shared part. -/
theorem pairHat_unbiasedG (hT : 2 ≤ Fintype.card T) (φ : ℝ) {i j : J} (hij : i ≠ j) :
    M.UnbiasedG grp φ (fun X => pairHat w X i j)
      (2 * M.τ2 - 2 * (φ * M.τ2) * (if grp i = grp j then 1 else 0)) := by
  have : Nonempty T := Fintype.card_pos_iff.mp (by omega)
  have h := M.unbiasedG_of grp (M.pairHat_unbiased sig hw hσ hT hij) φ
  rw [sum_pairHat_grpData grp hw, sum_pairHat_grpData (id : J → J) hw] at h
  convert h using 1
  simp only [id, hij, ite_false]
  split_ifs <;> ring

/-- `φτ²` is identifiable from one pair within a group (`i`, `j`) and one pair
across groups (`i`, `k`): half the difference of the two pair estimators is
unbiased for `φτ²`. -/
theorem phiTauHat_unbiasedG (hT : 2 ≤ Fintype.card T) (φ : ℝ) {i j k : J} (hij : i ≠ j)
    (hg : grp i = grp j) (hk : grp i ≠ grp k) :
    M.UnbiasedG grp φ (fun X => (pairHat w X i k - pairHat w X i j) / 2) (φ * M.τ2) := by
  have hik : i ≠ k := fun e => hk (congrArg grp e)
  refine (((M.pairHat_unbiasedG grp sig hw hσ hT φ hik).add
    ((M.pairHat_unbiasedG grp sig hw hσ hT φ hij).const_mul (-1))).const_mul (1 / 2)).congr
    (fun X => by ring) ?_
  have hk' : grp j ≠ grp k := hg ▸ hk
  simp only [hg, hk', ite_true, ite_false]
  ring

end Model
end Credibility
