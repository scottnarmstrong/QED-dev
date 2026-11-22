/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.ContinuationParam
public import QED.DimReg.CubeSplit
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Mellin integrals over the unit cube

The leaf integrals of a sector decomposition have the form

  `M H a = ∫_{(0,1]^N} ∏ₖ yₖ ^ (aₖ - 1) · H(y) dy`

with `H` continuous on the closed cube (`QED.DimReg.cubeMellin`). This module proves the two
analytic facts behind their continuation in `a`:

* **Analyticity in a parameter** (`QED.DimReg.analyticAt_cubeMellin_param`): if `H` and `a`
  depend on `z ∈ ℂ`, `H` jointly continuous and holomorphic in `z`, `a` holomorphic, then
  `z ↦ M (H z) (a z)` is analytic wherever all `re aₖ > 0`. The proof is differentiation under
  the integral with the `z`-derivative dominated by a Cauchy estimate, stated once for a general
  measure (`QED.DimReg.differentiableAt_integral_of_holomorphic`).
* **Partial integration in one coordinate** (`QED.DimReg.cubeMellin_step`): if `∂ᵢ H = H'`, then
  `aᵢ · M H a = M (H|_{yᵢ = 1}) (a with aᵢ = 1) - M H' (a + eᵢ)`, by Fubini and the one-variable
  step `QED.DimReg.mul_mellinUnit_of_hasDerivAt`. The first term is again a cube integral: the
  exponent `1` makes the integrand constant in `yᵢ`, and `(0, 1]` has measure `1`.

## Main results

* `QED.DimReg.integrableOn_cubeMellin`: the integrand is integrable when all `re aₖ > 0`.
* `QED.DimReg.cubeMellin_fubini`: the integral as an iterated integral, coordinate `i` inside.
* `QED.DimReg.cubeMellin_step`, `QED.DimReg.analyticAt_cubeMellin_param`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology Metric

namespace QED.DimReg

/-! ### Holomorphy of parametric integrals -/

/-- **Holomorphic parametric integrals.** If `F w` is a.e.-measurable for `w` in a disc, bounded
there by an integrable `b`, and holomorphic in `w` for a.e. `t`, then `w ↦ ∫ F w t dμ` is complex
differentiable at the centre. -/
theorem differentiableAt_integral_of_holomorphic {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : ℂ → α → ℂ} {z₁ : ℂ} {R : ℝ} (hR : 0 < R) {b : α → ℝ}
    (hb : Integrable b μ) (hFm : ∀ w ∈ ball z₁ R, AEStronglyMeasurable (F w) μ)
    (hFb : ∀ᵐ t ∂μ, ∀ w ∈ ball z₁ R, ‖F w t‖ ≤ b t)
    (hFd : ∀ᵐ t ∂μ, DifferentiableOn ℂ (fun w => F w t) (ball z₁ R)) :
    DifferentiableAt ℂ (fun w => ∫ t, F w t ∂μ) z₁ := by
  set r := R / 3 with hrdef
  have hr : 0 < r := div_pos hR (by norm_num)
  have hF'b : ∀ᵐ t ∂μ, ∀ w ∈ ball z₁ r, ‖deriv (fun w => F w t) w‖ ≤ b t / r := by
    filter_upwards [hFb, hFd] with t hb' hd' w hw
    have hsub : closedBall w r ⊆ ball z₁ R := by
      intro u hu
      rw [mem_ball] at hw ⊢
      rw [mem_closedBall] at hu
      calc dist u z₁ ≤ dist u w + dist w z₁ := dist_triangle _ _ _
        _ < R := by linarith
    refine norm_deriv_le_of_forall_mem_sphere_norm_le hr (hd'.diffContOnCl_ball hsub) ?_
    intro u hu
    exact hb' u (hsub (sphere_subset_closedBall hu))
  have hz₁ : z₁ ∈ ball z₁ R := mem_ball_self hR
  have hFint : Integrable (F z₁) μ := by
    refine hb.mono' (hFm z₁ hz₁) ?_
    filter_upwards [hFb] with t ht using ht z₁ hz₁
  have hF'm : AEStronglyMeasurable (fun t => deriv (fun w => F w t) z₁) μ := by
    set δ : ℕ → ℂ := fun n => ((r * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) with hδ
    have hδmem : ∀ n : ℕ, z₁ + δ n ∈ ball z₁ R := by
      intro n
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hδ, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      rw [hrdef] at ⊢
      nlinarith
    have hδt : Tendsto δ atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r
        rw [mul_zero] at h1
        have h2 := (continuous_ofReal.tendsto 0).comp h1
        rw [ofReal_zero] at h2
        exact h2
      · simp only [hδ, mem_compl_iff, mem_singleton_iff, ofReal_eq_zero]
        positivity
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n t => (δ n)⁻¹ • (F (z₁ + δ n) t - F z₁ t)) (fun n => ?_) ?_
    · exact (((hFm _ (hδmem n)).sub (hFm z₁ hz₁)).const_smul (δ n)⁻¹ :)
    · filter_upwards [hFd] with t ht
      have hd := (ht.differentiableAt (isOpen_ball.mem_nhds hz₁)).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope_zero] at hd
      exact hd.comp hδt
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F)
    (F' := fun w t => deriv (fun w => F w t) w) (x₀ := z₁)
    (bound := fun t => b t / r) (s := ball z₁ r) (ball_mem_nhds z₁ hr)
    (eventually_of_mem (isOpen_ball.mem_nhds hz₁) hFm) hFint hF'm hF'b (hb.div_const r)
    (by
      filter_upwards [hFd] with t ht x hx
      exact (ht.differentiableAt (isOpen_ball.mem_nhds
        (ball_subset_ball (by rw [hrdef]; linarith) hx))).hasDerivAt)
  exact hmain.2.differentiableAt

variable {N : ℕ}

/-! ### The cube Mellin integral -/

/-- The closed unit cube `[0, 1]^N`. -/
def closedCube (N : ℕ) : Set (Fin N → ℝ) := univ.pi fun _ => Icc 0 1

theorem isCompact_closedCube (N : ℕ) : IsCompact (closedCube N) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem unitCube_subset_closedCube : unitCube N ⊆ closedCube N :=
  pi_mono fun _ _ => Ioc_subset_Icc_self

theorem mem_closedCube {y : Fin N → ℝ} : y ∈ closedCube N ↔ ∀ k, 0 ≤ y k ∧ y k ≤ 1 := by
  simp only [closedCube, mem_univ_pi, mem_Icc]

/-- The monomial weight `∏ₖ yₖ ^ (aₖ - 1)`. -/
noncomputable def cubeWeight (a : Fin N → ℂ) (y : Fin N → ℝ) : ℂ := ∏ k, (y k : ℂ) ^ (a k - 1)

/-- The cube Mellin integral `M H a = ∫_{(0,1]^N} ∏ₖ yₖ ^ (aₖ - 1) H(y) dy`. -/
noncomputable def cubeMellin (H : (Fin N → ℝ) → ℂ) (a : Fin N → ℂ) : ℂ :=
  ∫ y in unitCube N, cubeWeight a y * H y

theorem norm_cubeWeight (a : Fin N → ℂ) {y : Fin N → ℝ} (hy : y ∈ unitCube N) :
    ‖cubeWeight a y‖ = ∏ k, y k ^ ((a k).re - 1) := by
  rw [cubeWeight, norm_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [norm_cpow_eq_rpow_re_of_pos ((mem_unitCube.mp hy) k).1, sub_re, one_re]

theorem norm_cubeWeight_le {a : Fin N → ℂ} {σ : ℝ} (ha : ∀ k, σ ≤ (a k).re) {y : Fin N → ℝ}
    (hy : y ∈ unitCube N) : ‖cubeWeight a y‖ ≤ ∏ k, y k ^ (σ - 1) := by
  rw [norm_cubeWeight a hy]
  refine Finset.prod_le_prod₀ (fun k _ => Real.rpow_nonneg ((mem_unitCube.mp hy) k).1.le _)
    fun k _ => ?_
  exact Real.rpow_le_rpow_of_exponent_ge ((mem_unitCube.mp hy) k).1 ((mem_unitCube.mp hy) k).2
    (by linarith [ha k])

theorem continuousOn_cubeWeight (a : Fin N → ℂ) : ContinuousOn (cubeWeight a) (unitCube N) := by
  refine continuousOn_finsetProd _ fun k _ y hy => ?_
  have h1 : ContinuousAt (fun y : Fin N → ℝ => (y k : ℂ)) y :=
    (continuous_ofReal.comp (continuous_apply k)).continuousAt
  exact (h1.cpow continuousAt_const
    (ofReal_mem_slitPlane.mpr ((mem_unitCube.mp hy) k).1)).continuousWithinAt

/-- The monomial `∏ₖ yₖ ^ cₖ` is integrable on the unit cube when all `cₖ > -1`. -/
theorem integrableOn_unitCube_prod_rpow {c : Fin N → ℝ} (hc : ∀ k, -1 < c k) :
    IntegrableOn (fun y : Fin N → ℝ => ∏ k, y k ^ c k) (unitCube N) := by
  unfold IntegrableOn unitCube
  rw [volume_pi, Measure.restrict_pi_pi]
  refine Integrable.fintype_prod_dep (f := fun k (t : ℝ) => t ^ c k) fun k => ?_
  rw [← IntegrableOn, integrableOn_Ioc_iff_integrableOn_Ioo]
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (hc k)

theorem exists_pos_lt_re {a : Fin N → ℂ} (ha : ∀ k, 0 < (a k).re) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ k, σ < (a k).re := by
  induction N with
  | zero => exact ⟨1, one_pos, fun k => k.elim0⟩
  | succ n ih =>
    obtain ⟨σ, hσ, hk⟩ := ih (a := fun k => a k.succ) fun k => ha k.succ
    refine ⟨min σ ((a 0).re / 2), lt_min hσ (by linarith [ha 0]), fun k => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) k
    · exact (min_le_right _ _).trans_lt (by linarith [ha 0])
    · exact (min_le_left _ _).trans_lt (hk j)

/-- **Integrability.** For `H` continuous on the closed cube and all `re aₖ > 0`, the cube Mellin
integrand is integrable. -/
theorem integrableOn_cubeMellin {H : (Fin N → ℝ) → ℂ} (hH : ContinuousOn H (closedCube N))
    {a : Fin N → ℂ} (ha : ∀ k, 0 < (a k).re) :
    IntegrableOn (fun y => cubeWeight a y * H y) (unitCube N) := by
  obtain ⟨σ, hσ, hσa⟩ := exists_pos_lt_re ha
  obtain ⟨C, hC⟩ := (isCompact_closedCube N).exists_bound_of_continuousOn hH
  refine Integrable.mono' ((integrableOn_unitCube_prod_rpow (c := fun _ => σ - 1)
    (fun _ => by linarith)).mul_const C) ?_ ?_
  · exact ((continuousOn_cubeWeight a).mul (hH.mono unitCube_subset_closedCube))
      |>.aestronglyMeasurable (measurableSet_unitCube N)
  · filter_upwards [ae_restrict_mem (measurableSet_unitCube N)] with y hy
    rw [norm_mul]
    exact mul_le_mul (norm_cubeWeight_le (fun k => (hσa k).le) hy)
      (hC y (unitCube_subset_closedCube hy)) (norm_nonneg _)
      (Finset.prod_nonneg fun k _ => Real.rpow_nonneg ((mem_unitCube.mp hy) k).1.le _)

/-! ### Analyticity in a parameter -/

/-- **Analyticity of a parametric cube Mellin integral.** If `H` is jointly continuous on
`U × [0, 1]^N` and holomorphic in `z ∈ U` for each `y`, and each `aₖ` is holomorphic on the open
set `U`, then `z ↦ M (H z) (a z)` is analytic at every `z₀ ∈ U` with all `re aₖ(z₀) > 0`. -/
theorem analyticAt_cubeMellin_param {H : ℂ → (Fin N → ℝ) → ℂ} {a : ℂ → Fin N → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hc : ContinuousOn (fun p : ℂ × (Fin N → ℝ) => H p.1 p.2) (U ×ˢ closedCube N))
    (hh : ∀ y ∈ closedCube N, DifferentiableOn ℂ (fun z => H z y) U)
    (ha : ∀ k, DifferentiableOn ℂ (fun z => a z k) U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (ha₀ : ∀ k, 0 < (a z₀ k).re) :
    AnalyticAt ℂ (fun z => cubeMellin (H z) (a z)) z₀ := by
  set V := U ∩ ⋂ k, (U ∩ (fun z => a z k) ⁻¹' {w | 0 < w.re}) with hV
  have hVo : IsOpen V := hU.inter (isOpen_iInter_of_finite fun k =>
    (ha k).continuousOn.isOpen_inter_preimage hU (isOpen_lt continuous_const continuous_re))
  refine DifferentiableOn.analyticAt (s := V) (fun z₁ hz₁ => ?_)
    (hVo.mem_nhds ⟨hz₀, mem_iInter.mpr fun k => ⟨hz₀, ha₀ k⟩⟩)
  refine DifferentiableAt.differentiableWithinAt ?_
  have hz₁U : z₁ ∈ U := hz₁.1
  obtain ⟨σ, hσ, hσa⟩ := exists_pos_lt_re fun k => (mem_iInter.mp hz₁.2 k).2
  set W := U ∩ ⋂ k, (U ∩ (fun z => a z k) ⁻¹' {w | σ < w.re}) with hW
  have hWo : IsOpen W := hU.inter (isOpen_iInter_of_finite fun k =>
    (ha k).continuousOn.isOpen_inter_preimage hU (isOpen_lt continuous_const continuous_re))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hWo z₁
    ⟨hz₁U, mem_iInter.mpr fun k => ⟨hz₁U, hσa k⟩⟩
  have hcl : closedBall z₁ (ε / 2) ⊆ W := (closedBall_subset_ball (by linarith)).trans hball
  have hbW : ball z₁ (ε / 2) ⊆ W := ball_subset_closedBall.trans hcl
  have hWU : W ⊆ U := inter_subset_left
  have hWσ : ∀ w ∈ W, ∀ k, σ ≤ (a w k).re := fun w hw k => (mem_iInter.mp hw.2 k).2.le
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall z₁ (ε / 2)).prod (isCompact_closedCube N)).exists_bound_of_continuousOn
    (hc.mono (prod_mono (hcl.trans hWU) subset_rfl))
  have hHy : ∀ w ∈ U, ContinuousOn (H w) (closedCube N) := fun w hw =>
    hc.comp (continuousOn_const.prodMk continuousOn_id) fun _ hy => ⟨hw, hy⟩
  refine differentiableAt_integral_of_holomorphic (μ := volume.restrict (unitCube N))
    (F := fun w y => cubeWeight (a w) y * H w y) (half_pos hε)
    (b := fun y => (∏ k, y k ^ (σ - 1)) * C)
    ((integrableOn_unitCube_prod_rpow (c := fun _ => σ - 1) fun _ => by linarith).mul_const C)
    (fun w hw => ((continuousOn_cubeWeight (a w)).mul ((hHy w (hWU (hbW hw))).mono
      unitCube_subset_closedCube)).aestronglyMeasurable (measurableSet_unitCube N)) ?_ ?_
  · filter_upwards [ae_restrict_mem (measurableSet_unitCube N)] with y hy w hw
    rw [norm_mul]
    exact mul_le_mul (norm_cubeWeight_le (hWσ w (hbW hw)) hy)
      (hC (w, y) ⟨ball_subset_closedBall hw, unitCube_subset_closedCube hy⟩) (norm_nonneg _)
      (Finset.prod_nonneg fun k _ => Real.rpow_nonneg ((mem_unitCube.mp hy) k).1.le _)
  · filter_upwards [ae_restrict_mem (measurableSet_unitCube N)] with y hy
    refine DifferentiableOn.mul ?_ ((hh y (unitCube_subset_closedCube hy)).mono
      (hbW.trans hWU))
    have : (fun w => cubeWeight (a w) y) = ∏ k, fun w => (y k : ℂ) ^ (a w k - 1) := by
      funext w; simp [cubeWeight, Finset.prod_apply]
    rw [this]
    refine DifferentiableOn.finsetProd fun k _ => ?_
    exact (((ha k).mono (hbW.trans hWU)).sub_const 1).const_cpow
      (Or.inl (ofReal_ne_zero.mpr ((mem_unitCube.mp hy) k).1.ne'))

/-! ### Fubini in one coordinate -/

theorem preimage_piFinSuccAbove_unitCube {n : ℕ} (i : Fin (n + 1)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i) ⁻¹'
      (Ioc 0 1 ×ˢ unitCube n) = unitCube (n + 1) := by
  ext x
  simp only [mem_preimage, mem_prod, mem_unitCube, mem_Ioc,
    MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply, Fin.removeNth]
  exact (Fin.forall_iff_succAbove (P := fun j => 0 < x j ∧ x j ≤ 1) i).symm

theorem insertNth_mem_closedCube {n : ℕ} (i : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {y : Fin n → ℝ} (hy : y ∈ closedCube n) : Fin.insertNth i t y ∈ closedCube (n + 1) := by
  rw [mem_closedCube] at hy ⊢
  refine (Fin.forall_iff_succAbove i).mpr ⟨?_, fun j => ?_⟩
  · rw [Fin.insertNth_apply_same]; exact ht
  · rw [Fin.insertNth_apply_succAbove]; exact hy j

theorem cubeWeight_insertNth {n : ℕ} (i : Fin (n + 1)) (a : Fin (n + 1) → ℂ) (t : ℝ)
    (y : Fin n → ℝ) :
    cubeWeight a (Fin.insertNth i t y) =
      (t : ℂ) ^ (a i - 1) * cubeWeight (fun j => a (i.succAbove j)) y := by
  rw [cubeWeight, Fin.prod_univ_succAbove _ i]
  simp [cubeWeight]

/-- **Fubini for the cube Mellin integral**, coordinate `i` inside:
`M H a = ∫_{(0,1]^n} ∏_{j} y_j ^ (a_{i.succAbove j} - 1) · M_1 (H(insert t at i)) (aᵢ) dy`. -/
theorem cubeMellin_fubini {n : ℕ} (i : Fin (n + 1)) {H : (Fin (n + 1) → ℝ) → ℂ}
    {a : Fin (n + 1) → ℂ} (hint : IntegrableOn (fun y => cubeWeight a y * H y) (unitCube (n + 1))) :
    IntegrableOn (fun y => cubeWeight (fun j => a (i.succAbove j)) y *
        mellinUnit (fun t => H (Fin.insertNth i t y)) (a i)) (unitCube n) ∧
      cubeMellin H a = ∫ y in unitCube n, cubeWeight (fun j => a (i.succAbove j)) y *
        mellinUnit (fun t => H (Fin.insertNth i t y)) (a i) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hp : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ => ℝ) i
  have he : ∀ z : ℝ × (Fin n → ℝ), e.symm z = Fin.insertNth i z.1 z.2 := fun _ => rfl
  set f : (Fin (n + 1) → ℝ) → ℂ := fun y => cubeWeight a y * H y with hf
  have hinner : ∀ y : Fin n → ℝ, ∫ t in Ioc (0 : ℝ) 1, f (e.symm (t, y)) =
      cubeWeight (fun j => a (i.succAbove j)) y *
        mellinUnit (fun t => H (Fin.insertNth i t y)) (a i) := by
    intro y
    rw [mellinUnit, intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hf, he, cubeWeight_insertNth]
    ring
  rw [← preimage_piFinSuccAbove_unitCube i] at hint
  have A1 : IntegrableOn ((fun z => f (e.symm z)) ∘ e) (e ⁻¹' (Ioc 0 1 ×ˢ unitCube n)) := by
    convert hint using 1
    funext x
    simp [hf]
  have h2 := (hp.integrableOn_comp_preimage e.measurableEmbedding).mp A1
  have hint' : cubeMellin H a = ∫ z in Ioc 0 1 ×ˢ unitCube n, f (e.symm z) := by
    have hS : e ⁻¹' (Ioc 0 1 ×ˢ unitCube n) = unitCube (n + 1) :=
      preimage_piFinSuccAbove_unitCube i
    rw [← hp.setIntegral_preimage_emb e.measurableEmbedding, hS]
    simp only [e.symm_apply_apply, hf, cubeMellin]
  unfold IntegrableOn at h2
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h2 hint'
  refine ⟨?_, ?_⟩
  · exact h2.integral_prod_right.congr (Eventually.of_forall hinner)
  · rw [hint', integral_prod_symm _ h2]
    exact integral_congr_ae (Eventually.of_forall hinner)

/-! ### Partial integration in one coordinate -/

theorem mellinUnit_const_one (c : ℂ) : mellinUnit (fun _ => c) 1 = c := by
  simp [mellinUnit]

/-- **Partial integration in coordinate `i`.** If `H` and `H'` are continuous on the closed cube,
`∂ᵢ H = H'` at the points of the closed cube with `0 < yᵢ < 1`, and all `re aₖ > 0`, then
`aᵢ · M H a = M (H|_{yᵢ = 1}) (a with aᵢ = 1) - M H' (a with aᵢ + 1)`. -/
theorem cubeMellin_step {i : Fin N} {H H' : (Fin N → ℝ) → ℂ} (hH : ContinuousOn H (closedCube N))
    (hH' : ContinuousOn H' (closedCube N))
    (hd : ∀ y ∈ closedCube N, y i ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (fun t => H (Function.update y i t)) (H' y) (y i))
    {a : Fin N → ℂ} (ha : ∀ k, 0 < (a k).re) :
    a i * cubeMellin H a = cubeMellin (fun y => H (Function.update y i 1)) (Function.update a i 1) -
      cubeMellin H' (Function.update a i (a i + 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i.pos; omega⟩
  have hupd : ∀ c : ℂ, ∀ j : Fin n, Function.update a i c (i.succAbove j) = a (i.succAbove j) :=
    fun c j => Function.update_of_ne (i.succAbove_ne j) _ _
  have hcont1 : ContinuousOn (fun y => H (Function.update y i 1)) (closedCube (n + 1)) := by
    refine hH.comp (continuous_id.update i continuous_const).continuousOn fun y hy => ?_
    rw [mem_closedCube] at hy ⊢
    intro k
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk]; exact hy k
  have ha1 : ∀ k, 0 < (Function.update a i 1 k).re := by
    intro k; by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk]; exact ha k
  have ha2 : ∀ k, 0 < (Function.update a i (a i + 1) k).re := by
    intro k; by_cases hk : k = i
    · subst hk; simp; linarith [ha k]
    · rw [Function.update_of_ne hk]; exact ha k
  obtain ⟨-, F1⟩ := cubeMellin_fubini i (integrableOn_cubeMellin hH ha)
  obtain ⟨I2, F2⟩ := cubeMellin_fubini i (integrableOn_cubeMellin hcont1 ha1)
  obtain ⟨I3, F3⟩ := cubeMellin_fubini i (integrableOn_cubeMellin hH' ha2)
  simp only [hupd, Function.update_self, Fin.update_insertNth, mellinUnit_const_one] at F2 F3 I2 I3
  rw [F1, F2, F3, ← integral_const_mul, ← integral_sub I2 I3]
  refine setIntegral_congr_fun (measurableSet_unitCube n) fun y hy => ?_
  have hyc : y ∈ closedCube n := unitCube_subset_closedCube hy
  have hc : ∀ {G : (Fin (n + 1) → ℝ) → ℂ}, ContinuousOn G (closedCube (n + 1)) →
      ContinuousOn (fun t => G (Fin.insertNth i t y)) (Icc 0 1) := fun hG =>
    hG.comp (Continuous.finInsertNth (A := fun _ => ℝ) i (f := fun t : ℝ => t)
      (g := fun _ => y) continuous_id continuous_const).continuousOn
      fun t ht => insertNth_mem_closedCube i ht hyc
  have hstep := mul_mellinUnit_of_hasDerivAt (hc hH) (hc hH') (fun t ht => by
    have h := hd (Fin.insertNth i t y) (insertNth_mem_closedCube i (Ioo_subset_Icc_self ht) hyc)
      (by rwa [Fin.insertNth_apply_same])
    simp only [Fin.insertNth_apply_same, Fin.update_insertNth] at h
    exact h) (ha i)
  rw [← mul_sub, ← hstep]
  ring

end QED.DimReg
