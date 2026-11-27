import Credibility.Core

/-!
# The price of the BLUP over the blend on the same `K̂` (extension, distribution-free)

The plug-in BLUP and the plug-in blend use the same fitted `K̂` (and `L̂`), but not in the same
way. Their weights move differently when `K̂` errs, and so do their prices. In the mixed-model
literature this price is Prasad–Rao's `g₃`; Das, Jiang & Rao (2004, eq. (3.4)) write it as
`tr{(∂d)ᵀ K (∂d) · Var θ̂}`. That trace is the expected value of the quantity below when the
fitted moments `θ̂` vary around the truth. This file states the price for the two families on
the same `K̂`, exactly and at first order.

* `zeroSumSolve K r = K⁻¹r - (1ᵀK⁻¹r) b`: the zero-sum vector `δ` with `Kδ - r` constant
  (`eq_zeroSumSolve`), and `δᵀKδ = rᵀδ` (`zeroSumSolve_quad`).
* **Exact weight errors.** With `K'`, `L'` in place of `K`, `L`:
  `d*' - d* = Q'(L'ⱼ - Lⱼ - (K' - K)d*)` (`blupWeight_sub_eq`), with `Q' = zeroSumSolve K'`;
  `b' - b = -Q'((K' - K)b)` (`glsWeight_sub_eq`); and the blend's
  `w' - w = (z' - z)(eⱼ - b') - (1 - z)Q'((K' - K)b)` (`blendWeight_sub_eq`).
  Their `K'`-norms are `rᵀQ'r` (`blupWeight_sub_quad`) and
  `(z' - z)²·gap' - 2(z' - z)(1 - z)(eⱼ - b')ᵀ(K' - K)b + (1 - z)²·((K' - K)b)ᵀQ'((K' - K)b)`
  (`blendWeight_sub_quad`).
* **First order.** Along `K + tΔK`, `L + tΔL` and a factor `z(t)` with `z'(0) = Δz`, the
  squared weight error divided by `t²` tends to `blupPrice` (`tendsto_blupPrice`) and
  `blendPrice` (`tendsto_blendPrice`):
  `blupPrice = rᵀQr` with `r = ΔLⱼ - ΔK d*`;
  `blendPrice = Δz²·gap - 2Δz(1 - z)(eⱼ - b)ᵀΔK b + (1 - z)²·(ΔK b)ᵀQ(ΔK b)`.
  By `linMse_eq_blupWeight_add`, the squared weight error is exactly the extra MSE of fixed
  weights `d` over `d*`, so the extra first-order price of the BLUP over the blend is
  `blupPrice - blendPrice`.

The BLUP reacts to `ΔK` through the whole vector `ΔK d*`, its own part `K⁻¹Lⱼ` spread over
correlated cohorts; the blend through the scalar `Δz` and the GLS weights only. Neither price
dominates the other in general (Finding 45). Nothing about the distribution is assumed: these are
statements about weights, and the moments enter only as `K`, `L`.
-/

open Finset Matrix Filter Topology

namespace Credibility
namespace Core

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- `Qr = K⁻¹r - (1ᵀK⁻¹r) b`: the zero-sum vector `δ` with `Kδ - r` constant. -/
noncomputable def zeroSumSolve (K : Matrix J J ℝ) (r : J → ℝ) : J → ℝ :=
  K⁻¹ *ᵥ r - (1 ⬝ᵥ (K⁻¹ *ᵥ r)) • glsWeight K

variable {K : Matrix J J ℝ}

/-- `Qr` has zero sum. -/
theorem sum_zeroSumSolve [Nonempty J] (hK : K.PosDef) (r : J → ℝ) :
    ∑ i, zeroSumSolve K r i = 0 := by
  simp only [zeroSumSolve, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sum_sub_distrib, ← mul_sum,
    sum_glsWeight hK, one_dotProduct]
  ring

/-- `KQr = r - (1ᵀK⁻¹r) s² 1`. -/
theorem mulVec_zeroSumSolve (hK : K.PosDef) (r : J → ℝ) (i : J) :
    (K *ᵥ zeroSumSolve K r) i = r i - (1 ⬝ᵥ (K⁻¹ *ᵥ r)) * (invTotal K)⁻¹ := by
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  rw [zeroSumSolve, mulVec_sub, mulVec_mulVec, mul_nonsing_inv K hdet, one_mulVec, mulVec_smul,
    mulVec_glsWeight hK]
  simp

omit [DecidableEq J] in
/-- For zero-sum `u` and `Kδ - r` constant, `uᵀKδ = uᵀr`. -/
lemma dotProduct_of_mulVec_sub_const {u δ r : J → ℝ} {c : ℝ} (hs : ∑ i, u i = 0)
    (hc : ∀ i, (K *ᵥ δ) i - r i = c) : u ⬝ᵥ (K *ᵥ δ) = u ⬝ᵥ r := by
  have : u ⬝ᵥ (K *ᵥ δ) - u ⬝ᵥ r = c * ∑ i, u i := by
    simp only [dotProduct, ← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun i _ => by rw [← hc i]; ring
  rw [hs, mul_zero, sub_eq_zero] at this
  exact this

omit [DecidableEq J] in
/-- For zero-sum `δ` and `Kδ - r` constant, `δᵀKδ = rᵀδ`. -/
lemma quad_of_mulVec_sub_const {δ r : J → ℝ} {c : ℝ} (hs : ∑ i, δ i = 0)
    (hc : ∀ i, (K *ᵥ δ) i - r i = c) : δ ⬝ᵥ (K *ᵥ δ) = r ⬝ᵥ δ := by
  rw [dotProduct_of_mulVec_sub_const hs hc, dotProduct_comm]

/-- `(Qr)ᵀK(Qr) = rᵀQr`. -/
theorem zeroSumSolve_quad [Nonempty J] (hK : K.PosDef) (r : J → ℝ) :
    zeroSumSolve K r ⬝ᵥ (K *ᵥ zeroSumSolve K r) = r ⬝ᵥ zeroSumSolve K r :=
  quad_of_mulVec_sub_const (c := -((1 ⬝ᵥ (K⁻¹ *ᵥ r)) * (invTotal K)⁻¹))
    (sum_zeroSumSolve hK r) fun i => by rw [mulVec_zeroSumSolve hK]; ring

/-- `Qr` is the only zero-sum `δ` with `Kδ - r` constant. -/
theorem eq_zeroSumSolve [Nonempty J] (hK : K.PosDef) {δ r : J → ℝ} {c : ℝ}
    (hs : ∑ i, δ i = 0) (hc : ∀ i, (K *ᵥ δ) i - r i = c) : δ = zeroSumSolve K r := by
  set e := δ - zeroSumSolve K r
  have hes : ∑ i, e i = 0 := by
    simp only [e, Pi.sub_apply, sum_sub_distrib, hs, sum_zeroSumSolve hK, sub_zero]
  have hec : ∀ i, (K *ᵥ e) i - (0 : J → ℝ) i = c + (1 ⬝ᵥ (K⁻¹ *ᵥ r)) * (invTotal K)⁻¹ :=
    fun i => by
      have := hc i
      simp only [e, mulVec_sub, Pi.sub_apply, mulVec_zeroSumSolve hK, Pi.zero_apply] at this ⊢
      linarith
  have h0 : e ⬝ᵥ (K *ᵥ e) = 0 := by
    rw [quad_of_mulVec_sub_const hes hec, zero_dotProduct]
  by_contra hne
  have := hK.dotProduct_mulVec_pos (x := e) (sub_ne_zero.mpr hne)
  simp only [star_trivial] at this
  linarith

/-! ### Exact weight errors on a fitted `K'` -/

variable {K' : Matrix J J ℝ}

/-- **The BLUP's weight error.** With `K'`, `L'` in place of `K`, `L`:
`d*(K', L') - d*(K, L) = Q'(L'ⱼ - Lⱼ - (K' - K) d*)`, `Q' = zeroSumSolve K'`. Exact. -/
theorem blupWeight_sub_eq (hK : K.PosDef) (hK' : K'.PosDef) (L L' : Matrix J J ℝ) (j : J) :
    blupWeight K' L' j - blupWeight K L j
      = zeroSumSolve K' (L' j - L j - (K' - K) *ᵥ blupWeight K L j) := by
  have : Nonempty J := ⟨j⟩
  refine eq_zeroSumSolve hK' (c := (1 - 1 ⬝ᵥ (K'⁻¹ *ᵥ L' j)) * (invTotal K')⁻¹
    - (1 - 1 ⬝ᵥ (K⁻¹ *ᵥ L j)) * (invTotal K)⁻¹) ?_ fun i => ?_
  · simp only [Pi.sub_apply, sum_sub_distrib, sum_blupWeight hK, sum_blupWeight hK', sub_self]
  · have h' := mulVec_blupWeight hK' L' j i
    have h := mulVec_blupWeight hK L j i
    simp only [mulVec_sub, sub_mulVec, Pi.sub_apply] at h h' ⊢
    linarith

/-- **The GLS weights' error**: `b(K') - b(K) = -Q'((K' - K) b)`. Exact. -/
theorem glsWeight_sub_eq (hK : K.PosDef) (hK' : K'.PosDef) [Nonempty J] :
    glsWeight K' - glsWeight K = -zeroSumSolve K' ((K' - K) *ᵥ glsWeight K) := by
  have h := eq_zeroSumSolve hK' (δ := glsWeight K - glsWeight K')
    (r := (K' - K) *ᵥ glsWeight K) (c := (invTotal K)⁻¹ - (invTotal K')⁻¹)
    (by simp only [Pi.sub_apply, sum_sub_distrib, sum_glsWeight hK, sum_glsWeight hK', sub_self])
    fun i => by
      simp only [mulVec_sub, sub_mulVec, Pi.sub_apply, mulVec_glsWeight hK,
        mulVec_glsWeight hK']
      ring
  rw [← h]; abel

/-- `(Q'r)ᵀK'(Q'r) = rᵀQ'r`: the BLUP's squared weight error in the `K'`-norm. -/
theorem blupWeight_sub_quad (hK : K.PosDef) (hK' : K'.PosDef) (L L' : Matrix J J ℝ) (j : J) :
    (blupWeight K' L' j - blupWeight K L j) ⬝ᵥ (K' *ᵥ (blupWeight K' L' j - blupWeight K L j))
      = (L' j - L j - (K' - K) *ᵥ blupWeight K L j)
          ⬝ᵥ zeroSumSolve K' (L' j - L j - (K' - K) *ᵥ blupWeight K L j) := by
  have : Nonempty J := ⟨j⟩
  rw [blupWeight_sub_eq hK hK', zeroSumSolve_quad hK']

/-- **The blend's weight error.** With `K'` and the factor `z'` in place of `K` and `z`:
`w(K', z') - w(K, z) = (z' - z)(eⱼ - b') - (1 - z)Q'((K' - K) b)`. Exact. -/
theorem blendWeight_sub_eq (hK : K.PosDef) (hK' : K'.PosDef) (j : J) (z z' : ℝ) :
    blendWeight K' j z' - blendWeight K j z
      = (z' - z) • (Pi.single j 1 - glsWeight K')
        - (1 - z) • zeroSumSolve K' ((K' - K) *ᵥ glsWeight K) := by
  have : Nonempty J := ⟨j⟩
  have h := glsWeight_sub_eq hK hK'
  rw [eq_neg_iff_add_eq_zero] at h
  funext i
  have hi := congrFun h i
  simp only [blendWeight, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] at hi ⊢
  linear_combination (1 - z) * hi

/-- The `K`-norm of `a(eⱼ - b) - cQ(ΔK b)`: `a²·gap - 2ac(eⱼ - b)ᵀΔK b + c²(ΔK b)ᵀQ(ΔK b)`,
with `gap = (eⱼ - b)ᵀK(eⱼ - b) = Kⱼⱼ - s²`. -/
theorem blendDir_quad [Nonempty J] (hK : K.PosDef) (j : J) (a c : ℝ) (y : J → ℝ) :
    (a • (Pi.single j 1 - glsWeight K) - c • zeroSumSolve K y)
        ⬝ᵥ (K *ᵥ (a • (Pi.single j 1 - glsWeight K) - c • zeroSumSolve K y))
      = a ^ 2 * (K j j - (invTotal K)⁻¹)
        - 2 * a * c * ((Pi.single j 1 - glsWeight K) ⬝ᵥ y) + c ^ 2 * (y ⬝ᵥ zeroSumSolve K y) := by
  set u := Pi.single j 1 - glsWeight K
  set s := zeroSumSolve K y
  have hsymm := dotProduct_mulVec_comm_of_isHermitian hK.isHermitian u s
  have hu1 : ∑ i, u i = 0 := by
    simp [u, sum_sub_distrib, sum_glsWeight hK]
  -- `uᵀKs = uᵀy`: `Ks - y` is constant and `u` has zero sum.
  have hus : u ⬝ᵥ (K *ᵥ s) = u ⬝ᵥ y :=
    dotProduct_of_mulVec_sub_const (c := -((1 ⬝ᵥ (K⁻¹ *ᵥ y)) * (invTotal K)⁻¹)) hu1
      fun i => by rw [mulVec_zeroSumSolve hK]; ring
  have huu : u ⬝ᵥ (K *ᵥ u) = K j j - (invTotal K)⁻¹ := by
    have := quadForm_single_sub_glsWeight hK j
    simpa [u] using this
  have hss : s ⬝ᵥ (K *ᵥ s) = y ⬝ᵥ s := zeroSumSolve_quad hK y
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  rw [huu, hus, hss, ← hsymm, hus]
  ring

/-- `(w' - w)ᵀK'(w' - w)` for the blend:
`(z' - z)²·gap' - 2(z' - z)(1 - z)(eⱼ - b')ᵀ(K' - K)b + (1 - z)²·rᵀQ'r`, `r = (K' - K)b`. -/
theorem blendWeight_sub_quad (hK : K.PosDef) (hK' : K'.PosDef) (j : J) (z z' : ℝ) :
    (blendWeight K' j z' - blendWeight K j z) ⬝ᵥ (K' *ᵥ (blendWeight K' j z' - blendWeight K j z))
      = (z' - z) ^ 2 * (K' j j - (invTotal K')⁻¹)
        - 2 * (z' - z) * (1 - z)
            * ((Pi.single j 1 - glsWeight K') ⬝ᵥ ((K' - K) *ᵥ glsWeight K))
        + (1 - z) ^ 2 * (((K' - K) *ᵥ glsWeight K)
            ⬝ᵥ zeroSumSolve K' ((K' - K) *ᵥ glsWeight K)) := by
  have : Nonempty J := ⟨j⟩
  rw [blendWeight_sub_eq hK hK', blendDir_quad hK']

/-! ### First order: the prices along a direction of the fit's error -/

/-- **The first-order price of the BLUP's weights** in the direction `(ΔK, ΔL)`:
`rᵀQr` with `r = ΔLⱼ - ΔK d*` (`tendsto_blupPrice`). -/
noncomputable def blupPrice (K L : Matrix J J ℝ) (j : J) (ΔK ΔL : Matrix J J ℝ) : ℝ :=
  (ΔL j - ΔK *ᵥ blupWeight K L j) ⬝ᵥ zeroSumSolve K (ΔL j - ΔK *ᵥ blupWeight K L j)

/-- **The first-order price of the blend's weights** in the direction `ΔK`, with the factor moving
at rate `Δz`: `Δz²·gap - 2Δz(1 - z)(eⱼ - b)ᵀΔK b + (1 - z)²·(ΔK b)ᵀQ(ΔK b)`
(`tendsto_blendPrice`). -/
noncomputable def blendPrice (K : Matrix J J ℝ) (j : J) (z Δz : ℝ) (ΔK : Matrix J J ℝ) : ℝ :=
  Δz ^ 2 * (K j j - (invTotal K)⁻¹)
    - 2 * Δz * (1 - z) * ((Pi.single j 1 - glsWeight K) ⬝ᵥ (ΔK *ᵥ glsWeight K))
    + (1 - z) ^ 2 * ((ΔK *ᵥ glsWeight K) ⬝ᵥ zeroSumSolve K (ΔK *ᵥ glsWeight K))

omit [Fintype J] [DecidableEq J] in
lemma continuous_mulVec_left (y : J → ℝ) [Fintype J] :
    Continuous fun M : Matrix J J ℝ => M *ᵥ y :=
  continuous_id.matrix_mulVec continuous_const

/-- `t ↦ (K + tΔK)⁻¹` is continuous at `0`. -/
lemma continuousAt_inv_line (hK : K.PosDef) (ΔK : Matrix J J ℝ) :
    ContinuousAt (fun t : ℝ => (K + t • ΔK)⁻¹) 0 := by
  have hdet : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK.isUnit
  have hinv : ContinuousAt Inv.inv K :=
    continuousAt_matrix_inv K (by
      obtain ⟨u, hu⟩ := hdet
      rw [← hu]; exact NormedRing.inverse_continuousAt u)
  have hline : Continuous fun t : ℝ => K + t • ΔK := continuous_const.add (continuous_id.smul continuous_const)
  have : ContinuousAt (fun t : ℝ => K + t • ΔK) 0 := hline.continuousAt
  have h0 : K + (0 : ℝ) • ΔK = K := by simp
  exact ContinuousAt.comp (g := Inv.inv) (by rw [h0]; exact hinv) this

/-- The GLS weights and `Qy` on `K + tΔK` are continuous at `t = 0`. -/
lemma continuousAt_gls_zeroSumSolve_line [Nonempty J] (hK : K.PosDef) (ΔK : Matrix J J ℝ)
    (y : J → ℝ) :
    ContinuousAt (fun t : ℝ => glsWeight (K + t • ΔK)) 0
      ∧ ContinuousAt (fun t : ℝ => zeroSumSolve (K + t • ΔK) y) 0 := by
  have hi := continuousAt_inv_line hK ΔK
  have hu : ContinuousAt (fun t : ℝ => (K + t • ΔK)⁻¹ *ᵥ 1) 0 :=
    (continuous_mulVec_left 1).continuousAt.comp hi
  have hy : ContinuousAt (fun t : ℝ => (K + t • ΔK)⁻¹ *ᵥ y) 0 :=
    (continuous_mulVec_left y).continuousAt.comp hi
  have htot : ContinuousAt (fun t : ℝ => invTotal (K + t • ΔK)) 0 :=
    (continuous_const.dotProduct continuous_id).continuousAt.comp hu
  have h0 : invTotal (K + (0 : ℝ) • ΔK) ≠ 0 := by simpa using (invTotal_pos hK).ne'
  have hg : ContinuousAt (fun t : ℝ => glsWeight (K + t • ΔK)) 0 := by
    simp only [glsWeight_eq_smul]
    exact (htot.inv₀ h0).smul hu
  refine ⟨hg, ?_⟩
  simp only [zeroSumSolve]
  exact hy.sub (((continuous_const.dotProduct continuous_id).continuousAt.comp hy).smul hg)

omit [DecidableEq J] in
lemma tendsto_quad {v : ℝ → J → ℝ} {v₀ : J → ℝ} {l : Filter ℝ} (h : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun t => v t ⬝ᵥ (K *ᵥ v t)) l (𝓝 (v₀ ⬝ᵥ (K *ᵥ v₀))) :=
  ((continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)).tendsto v₀).comp h

omit [DecidableEq J] in
lemma quad_smul_div (t : ℝ) (ht : t ≠ 0) (v : J → ℝ) :
    (t • v) ⬝ᵥ (K *ᵥ (t • v)) / t ^ 2 = v ⬝ᵥ (K *ᵥ v) := by
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp

lemma zeroSumSolve_smul (K : Matrix J J ℝ) (t : ℝ) (r : J → ℝ) :
    zeroSumSolve K (t • r) = t • zeroSumSolve K r := by
  simp only [zeroSumSolve, mulVec_smul, dotProduct_smul, smul_eq_mul, smul_sub, smul_smul]

/-- **The BLUP's price at first order.** Along `K + tΔK`, `L + tΔL` (eventually positive
definite), the squared weight error in the true `K`-norm, `(d*(t) - d*)ᵀK(d*(t) - d*)`, divided
by `t²`, tends to `blupPrice K L j ΔK ΔL`. By `linMse_eq_blupWeight_add` that squared error is the
extra MSE of the weights `d*(t)` over `d*`. -/
theorem tendsto_blupPrice (hK : K.PosDef) (L ΔK ΔL : Matrix J J ℝ) (j : J)
    (hKt : ∀ᶠ t in 𝓝 (0 : ℝ), (K + t • ΔK).PosDef) :
    Tendsto (fun t : ℝ => (blupWeight (K + t • ΔK) (L + t • ΔL) j - blupWeight K L j)
        ⬝ᵥ (K *ᵥ (blupWeight (K + t • ΔK) (L + t • ΔL) j - blupWeight K L j)) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (blupPrice K L j ΔK ΔL)) := by
  have : Nonempty J := ⟨j⟩
  set r := ΔL j - ΔK *ᵥ blupWeight K L j
  have hc := (continuousAt_gls_zeroSumSolve_line hK ΔK r).2
  have hlim : Tendsto (fun t : ℝ => zeroSumSolve (K + t • ΔK) r) (𝓝[≠] 0)
      (𝓝 (zeroSumSolve K r)) := by
    have := hc.tendsto; simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hq := tendsto_quad (K := K) hlim
  rw [zeroSumSolve_quad hK] at hq
  refine hq.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hKt, self_mem_nhdsWithin] with t hKt' ht
  have harg : (L + t • ΔL) j - L j - (K + t • ΔK - K) *ᵥ blupWeight K L j = t • r := by
    funext i
    simp [r, smul_mulVec, mul_sub]
  rw [blupWeight_sub_eq hK hKt', harg, zeroSumSolve_smul, quad_smul_div t ht]

/-- **The blend's price at first order.** Along `K + tΔK` (eventually positive definite), with a
factor `z(t)` differentiable at `0` with `z'(0) = Δz` (e.g. `bestZ` of the plug-in moments), the
squared weight error `(w(t) - w)ᵀK(w(t) - w)` divided by `t²` tends to
`blendPrice K j (z 0) Δz ΔK`. -/
theorem tendsto_blendPrice (hK : K.PosDef) (ΔK : Matrix J J ℝ) (j : J) {z : ℝ → ℝ} {Δz : ℝ}
    (hz : HasDerivAt z Δz 0) (hKt : ∀ᶠ t in 𝓝 (0 : ℝ), (K + t • ΔK).PosDef) :
    Tendsto (fun t : ℝ => (blendWeight (K + t • ΔK) j (z t) - blendWeight K j (z 0))
        ⬝ᵥ (K *ᵥ (blendWeight (K + t • ΔK) j (z t) - blendWeight K j (z 0))) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (blendPrice K j (z 0) Δz ΔK)) := by
  have : Nonempty J := ⟨j⟩
  set y := ΔK *ᵥ glsWeight K
  obtain ⟨hg, hc⟩ := continuousAt_gls_zeroSumSolve_line hK ΔK y
  have tw : ∀ {f : ℝ → J → ℝ} {a : J → ℝ}, ContinuousAt f 0 → f 0 = a →
      Tendsto f (𝓝[≠] 0) (𝓝 a) := fun h e => by
    rw [← e]; exact h.tendsto.mono_left nhdsWithin_le_nhds
  have hslope : Tendsto (fun t : ℝ => t⁻¹ * (z t - z 0)) (𝓝[≠] 0) (𝓝 Δz) := by
    simpa using hz.tendsto_slope_zero
  set v : ℝ → J → ℝ := fun t => (t⁻¹ * (z t - z 0)) • (Pi.single j 1 - glsWeight (K + t • ΔK))
    - (1 - z 0) • zeroSumSolve (K + t • ΔK) y
  have hv : Tendsto v (𝓝[≠] 0)
      (𝓝 (Δz • (Pi.single j 1 - glsWeight K) - (1 - z 0) • zeroSumSolve K y)) :=
    (hslope.smul (tendsto_const_nhds.sub (tw hg (by simp)))).sub
      (tendsto_const_nhds.smul (tw hc (by simp)))
  have hq := tendsto_quad (K := K) hv
  rw [blendDir_quad hK] at hq
  refine hq.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hKt, self_mem_nhdsWithin] with t hKt' ht
  have hd : blendWeight (K + t • ΔK) j (z t) - blendWeight K j (z 0) = t • v t := by
    rw [blendWeight_sub_eq hK hKt', show K + t • ΔK - K = t • ΔK by abel, smul_mulVec,
      zeroSumSolve_smul]
    simp only [v, smul_sub, smul_smul]
    rw [mul_inv_cancel_left₀ ht, mul_comm t (1 - z 0)]
  rw [hd, quad_smul_div t ht]

end Core
end Credibility
