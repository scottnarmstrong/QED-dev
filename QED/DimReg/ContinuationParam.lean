/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Continuation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# The unit Mellin continuation with a complex parameter

The continuation `QED.DimReg.mellinUnitCont` of `M f s = ∫₀¹ t ^ (s - 1) f(t) dt` is the
one-variable step of the continuation of a sector integral. In a sector the integrand and the
exponent both depend on the other exponents and on the dimension. Along a complex line through
parameter space one complex parameter `z` suffices, and this module proves that the continuation
is analytic (or meromorphic) in `z`.

The `t`-derivatives of the integrand are given as a family `g : ℕ → ℂ → ℝ → ℂ`
(`g (j + 1) z = ∂ₜ g j z` on `(0, 1)`), rather than computed with `deriv`: the derivatives of a
sector integrand are explicit, and `deriv` at the endpoints of `[0, 1]` would carry junk values.
`QED.DimReg.mellinCont k g s` is the `k`-fold partial-integration continuation built from such a
family; it agrees with `mellinUnitCont` for `g j = deriv^[j] f`
(`QED.DimReg.mellinUnitCont_eq_mellinCont`).

## Main results

* `QED.DimReg.mul_mellinUnit_of_hasDerivAt`: the partial-integration step with derivatives on
  `(0, 1)` only.
* `QED.DimReg.mellinCont_eq`: the continuation equals the integral on `re s > 0`.
* `QED.DimReg.analyticAt_mellinUnit_param`: **base case.** If `h` is jointly continuous on
  `U × [0, 1]` and holomorphic in `z` for each `t`, and `s` is holomorphic on `U`, then
  `z ↦ M (h z) (s z)` is analytic wherever `re s z > 0` (differentiation under the integral, the
  derivative dominated by a Cauchy estimate).
* `QED.DimReg.analyticAt_mellinCont_param`, `QED.DimReg.meromorphicAt_mellinCont_param`: the
  continuation `z ↦ mellinCont k (g · z) (s z)` is meromorphic where `re s z > -k`, and analytic
  there unless `s z ∈ {0, -1, …, -(k - 1)}`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology Metric

namespace QED.DimReg

/-! ### Partial integration with derivatives on the open interval -/

/-- **The partial-integration step.** If `f` and `f'` are continuous on `[0, 1]` and `f' = ∂f`
on `(0, 1)`, then `s · M f s = f(1) - M f' (s + 1)` for `re s > 0`. -/
theorem mul_mellinUnit_of_hasDerivAt {f f' : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1))
    (hf' : ContinuousOn f' (Icc 0 1)) (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' t) t)
    {s : ℂ} (hs : 0 < s.re) : s * mellinUnit f s = f 1 - mellinUnit f' (s + 1) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hv : ∀ t ∈ Ioo (min (0 : ℝ) 1) (max 0 1),
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ s / s) ((t : ℂ) ^ (s - 1)) t := by
    intro t ht
    have ht0 : 0 < t := by simpa using ht.1
    have h := ((hasDerivAt_id (t : ℂ)).cpow_const (c := s)
      (ofReal_mem_slitPlane.mpr ht0)).comp_ofReal.div_const s
    simp only [id] at h
    convert h using 1
    field_simp
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := f) (u' := f') (v := fun t : ℝ => (t : ℂ) ^ s / s)
    (v' := fun t : ℝ => (t : ℂ) ^ (s - 1)) (a := 0) (b := 1)
    (by rwa [uIcc_of_le zero_le_one])
    ((continuous_ofReal_cpow_const hs).div_const s).continuousOn
    (fun t ht => hd t (by simpa using ht)) hv (hf'.intervalIntegrable_of_Icc zero_le_one)
    (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith))
  have h0 : ((0 : ℝ) : ℂ) ^ s = 0 := by rw [ofReal_zero, zero_cpow hs0]
  rw [mellinUnit, mellinUnit, add_sub_cancel_right]
  simp only [ofReal_one, one_cpow, h0, zero_div, mul_zero, sub_zero] at hparts
  have e1 : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ (s - 1) * f t =
      ∫ t in (0 : ℝ)..1, f t * (t : ℂ) ^ (s - 1) := by
    congr 1; funext t; ring
  have e2 : ∫ t in (0 : ℝ)..1, f' t * ((t : ℂ) ^ s / s) =
      s⁻¹ * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ s * f' t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; field_simp
  rw [e1, hparts, e2]
  field_simp

/-! ### The continuation built from a family of derivatives -/

/-- The `k`-fold partial-integration continuation built from a family `g` of `t`-derivatives
(`g j` playing the role of `∂ₜʲ g 0`): `Cont₀ g = M (g 0)` and
`Cont_{k+1} g s = (g 0 1 - Cont_k (g (· + 1)) (s + 1)) / s`. -/
noncomputable def mellinCont : ℕ → (ℕ → ℝ → ℂ) → ℂ → ℂ
  | 0, g, s => mellinUnit (g 0) s
  | k + 1, g, s => (g 0 1 - mellinCont k (fun j => g (j + 1)) (s + 1)) / s

/-- With `g j = deriv^[j] f`, `mellinCont` is `mellinUnitCont`. -/
theorem mellinUnitCont_eq_mellinCont (k : ℕ) (f : ℝ → ℂ) (s : ℂ) :
    mellinUnitCont k f s = mellinCont k (fun j => deriv^[j] f) s := by
  induction k generalizing f s with
  | zero => rfl
  | succ k ih =>
    simp only [mellinUnitCont, mellinCont, ih, Function.iterate_succ_apply,
      Function.iterate_zero_apply]

/-- A family `g j z` of `t`-derivatives up to order `k`, depending on a complex parameter `z ∈ U`:
`g (j + 1) z = ∂ₜ g j z` on `(0, 1)`, each `g j` jointly continuous on `U × [0, 1]` and
holomorphic in `z` on `U` for each `t ∈ [0, 1]`. -/
structure TDerivFamily (g : ℕ → ℂ → ℝ → ℂ) (k : ℕ) (U : Set ℂ) : Prop where
  hasDerivAt : ∀ j < k, ∀ z ∈ U, ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (g j z) (g (j + 1) z t) t
  continuousOn : ∀ j ≤ k, ContinuousOn (fun p : ℂ × ℝ => g j p.1 p.2) (U ×ˢ Icc 0 1)
  differentiableOn : ∀ j ≤ k, ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => g j z t) U

namespace TDerivFamily

variable {g : ℕ → ℂ → ℝ → ℂ} {k : ℕ} {U : Set ℂ}

/-- Dropping the first member of a family of derivatives. -/
theorem succ (h : TDerivFamily g (k + 1) U) : TDerivFamily (fun j => g (j + 1)) k U where
  hasDerivAt j hj := h.hasDerivAt (j + 1) (by omega)
  continuousOn j hj := h.continuousOn (j + 1) (by omega)
  differentiableOn j hj := h.differentiableOn (j + 1) (by omega)

theorem continuousOn_t (h : TDerivFamily g k U) {j : ℕ} (hj : j ≤ k) {z : ℂ} (hz : z ∈ U) :
    ContinuousOn (g j z) (Icc 0 1) :=
  (h.continuousOn j hj).comp (continuousOn_const.prodMk continuousOn_id) fun _ ht => ⟨hz, ht⟩

end TDerivFamily

/-- The continuation agrees with the integral on `re s > 0`. -/
theorem mellinCont_eq {g : ℕ → ℂ → ℝ → ℂ} {k : ℕ} {U : Set ℂ} (hg : TDerivFamily g k U)
    {z : ℂ} (hz : z ∈ U) {s : ℂ} (hs : 0 < s.re) :
    mellinCont k (fun j => g j z) s = mellinUnit (g 0 z) s := by
  induction k generalizing g s with
  | zero => rfl
  | succ k ih =>
    have hs1 : 0 < (s + 1).re := by simp; linarith
    have hs0 : s ≠ 0 := fun h => by simp [h] at hs
    have h1 := ih hg.succ hs1
    have h2 := mul_mellinUnit_of_hasDerivAt (hg.continuousOn_t (j := 0) (by omega) hz)
      (hg.continuousOn_t (j := 1) (by omega) hz) (hg.hasDerivAt 0 (by omega) z hz) hs
    change (g 0 z 1 - mellinCont k (fun j => g (j + 1) z) (s + 1)) / s = _
    rw [h1, ← h2, mul_div_cancel_left₀ _ hs0]

/-! ### The base case: analyticity of a parametric unit Mellin integral -/

/-- **Differentiability of a parametric unit Mellin integral.** Differentiation under the
integral sign, the `z`-derivative dominated by a Cauchy estimate on a small disc. -/
theorem differentiableAt_mellinUnit_param {h : ℂ → ℝ → ℂ} {s : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hc : ContinuousOn (fun p : ℂ × ℝ => h p.1 p.2) (U ×ˢ Icc 0 1))
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => h z t) U)
    (hs : DifferentiableOn ℂ s U) {z₁ : ℂ} (hz₁ : z₁ ∈ U) (hs₁ : 0 < (s z₁).re) :
    DifferentiableAt ℂ (fun z => mellinUnit (h z) (s z)) z₁ := by
  set σ := (s z₁).re / 2 with hσ
  have hσ0 : 0 < σ := half_pos hs₁
  have hV : IsOpen (U ∩ s ⁻¹' {w | σ < w.re}) :=
    hs.continuousOn.isOpen_inter_preimage hU (isOpen_lt continuous_const continuous_re)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV z₁
    ⟨hz₁, show σ < (s z₁).re by rw [hσ]; linarith⟩
  set r := ε / 3 with hrdef
  have hr : 0 < r := div_pos hε (by norm_num)
  have hcl : closedBall z₁ (2 * r) ⊆ U ∩ s ⁻¹' {w | σ < w.re} :=
    (closedBall_subset_ball (by rw [hrdef]; linarith)).trans hball
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall z₁ (2 * r)).prod isCompact_Icc).exists_bound_of_continuousOn
    (hc.mono (prod_mono (hcl.trans inter_subset_left) subset_rfl))
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμ
  set F : ℂ → ℝ → ℂ := fun w t => (t : ℂ) ^ (s w - 1) * h w t with hF
  have hFb : ∀ w ∈ closedBall z₁ (2 * r), ∀ t ∈ Ioc (0 : ℝ) 1, ‖F w t‖ ≤ t ^ (σ - 1) * C := by
    intro w hw t ht
    have hw' : σ < (s w).re := (hcl hw).2
    rw [hF, norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1]
    have e1 : t ^ ((s w - 1).re) ≤ t ^ (σ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 (by simp; linarith)
    exact mul_le_mul e1 (hC (w, t) ⟨hw, Ioc_subset_Icc_self ht⟩) (norm_nonneg _)
      (Real.rpow_nonneg ht.1.le _)
  have hFd : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ w ∈ U, DifferentiableAt ℂ (fun w => F w t) w := by
    intro t ht w hw
    have h1 : DifferentiableAt ℂ (fun w => (t : ℂ) ^ (s w - 1)) w :=
      ((hs.differentiableAt (hU.mem_nhds hw)).sub_const 1).const_cpow
        (Or.inl (ofReal_ne_zero.mpr ht.1.ne'))
    exact h1.mul ((hh t (Ioc_subset_Icc_self ht)).differentiableAt (hU.mem_nhds hw))
  have hF'b : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ w ∈ ball z₁ r,
      ‖deriv (fun w => F w t) w‖ ≤ t ^ (σ - 1) * C / r := by
    intro t ht w hw
    have hsub : closedBall w r ⊆ ball z₁ (2 * r) := by
      intro u hu
      rw [mem_ball] at hw ⊢
      rw [mem_closedBall] at hu
      calc dist u z₁ ≤ dist u w + dist w z₁ := dist_triangle _ _ _
        _ < 2 * r := by linarith
    have hdiff : DifferentiableOn ℂ (fun w => F w t) (ball z₁ (2 * r)) := fun u hu =>
      (hFd t ht u (hcl (ball_subset_closedBall hu)).1).differentiableWithinAt
    refine norm_deriv_le_of_forall_mem_sphere_norm_le hr (hdiff.diffContOnCl_ball hsub) ?_
    intro u hu
    exact hFb u (ball_subset_closedBall (hsub (sphere_subset_closedBall hu))) t ht
  have hFm : ∀ w ∈ U, AEStronglyMeasurable (F w) μ := by
    intro w hw
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    have hht : ContinuousOn (h w) (Icc 0 1) :=
      hc.comp (continuousOn_const.prodMk continuousOn_id) fun _ ht => ⟨hw, ht⟩
    refine ContinuousOn.mul ?_ (hht.mono Ioc_subset_Icc_self)
    intro t ht
    exact (continuous_ofReal.continuousAt.cpow continuousAt_const
      (ofReal_mem_slitPlane.mpr ht.1)).continuousWithinAt
  have hbint0 : Integrable (fun t : ℝ => t ^ (σ - 1) * C) μ :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by linarith : (-1 : ℝ) < σ - 1)).1.mul_const C
  have hFint : Integrable (F z₁) μ := by
    refine hbint0.mono' (hFm z₁ hz₁) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hFb z₁ (mem_closedBall_self (by positivity)) t ht
  have hF'm : AEStronglyMeasurable (fun t => deriv (fun w => F w t) z₁) μ := by
    set δ : ℕ → ℂ := fun n => ((r * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) with hδ
    have hδmem : ∀ n : ℕ, z₁ + δ n ∈ U := by
      intro n
      refine (hcl ?_).1
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hδ, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
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
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hd := (hFd t ht z₁ hz₁).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope_zero] at hd
      exact hd.comp hδt
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F)
    (F' := fun w t => deriv (fun w => F w t) w) (x₀ := z₁)
    (bound := fun t => t ^ (σ - 1) * C / r) (s := ball z₁ r) (ball_mem_nhds z₁ hr)
    (eventually_of_mem (hU.mem_nhds hz₁) hFm) hFint hF'm
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht x hx
        using hF'b t ht x hx)
    (hbint0.div_const r)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht x hx
      exact (hFd t ht x (hcl (ball_subset_closedBall
        (ball_subset_ball (by linarith) hx))).1).hasDerivAt)
  have he : (fun z => mellinUnit (h z) (s z)) = fun z => ∫ t, F z t ∂μ := funext fun z => by
    rw [mellinUnit, intervalIntegral.integral_of_le zero_le_one]
  rw [he]
  exact hmain.2.differentiableAt

/-- **Base case.** If `h` is jointly continuous on `U × [0, 1]` and holomorphic in `z ∈ U` for
each `t ∈ [0, 1]`, and `s` is holomorphic on the open set `U`, then `z ↦ M (h z) (s z)` is
analytic at every `z₀ ∈ U` with `re s z₀ > 0`. -/
theorem analyticAt_mellinUnit_param {h : ℂ → ℝ → ℂ} {s : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hc : ContinuousOn (fun p : ℂ × ℝ => h p.1 p.2) (U ×ˢ Icc 0 1))
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableOn ℂ (fun z => h z t) U)
    (hs : DifferentiableOn ℂ s U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hs₀ : 0 < (s z₀).re) :
    AnalyticAt ℂ (fun z => mellinUnit (h z) (s z)) z₀ := by
  have hV : IsOpen (U ∩ s ⁻¹' {w | 0 < w.re}) :=
    hs.continuousOn.isOpen_inter_preimage hU (isOpen_lt continuous_const continuous_re)
  exact DifferentiableOn.analyticAt (s := U ∩ s ⁻¹' {w | 0 < w.re})
    (fun z hz => (differentiableAt_mellinUnit_param hU hc hh hs hz.1 hz.2).differentiableWithinAt)
    (hV.mem_nhds ⟨hz₀, hs₀⟩)

/-! ### The induction step -/

/-- **Analyticity of the parametric continuation.** For a family of `t`-derivatives of order `k`
on the open set `U` and `s` holomorphic on `U`, `z ↦ mellinCont k (g · z) (s z)` is analytic at
`z₀ ∈ U` when `re s z₀ > -k` and `s z₀ ∉ {0, -1, …, -(k - 1)}`. -/
theorem analyticAt_mellinCont_param {g : ℕ → ℂ → ℝ → ℂ} {k : ℕ} {U : Set ℂ} (hU : IsOpen U)
    (hg : TDerivFamily g k U) {s : ℂ → ℂ} (hs : DifferentiableOn ℂ s U) {z₀ : ℂ}
    (hz₀ : z₀ ∈ U) (hre : -(k : ℝ) < (s z₀).re) (hpole : ∀ j : ℕ, j < k → s z₀ ≠ -(j : ℂ)) :
    AnalyticAt ℂ (fun z => mellinCont k (fun j => g j z) (s z)) z₀ := by
  induction k generalizing g s with
  | zero =>
    exact analyticAt_mellinUnit_param hU (hg.continuousOn 0 le_rfl) (hg.differentiableOn 0 le_rfl)
      hs hz₀ (by simpa using hre)
  | succ k ih =>
    have hs1 : DifferentiableOn ℂ (fun z => s z + 1) U := hs.add_const 1
    have hre1 : -(k : ℝ) < (s z₀ + 1).re := by simp; push_cast at hre; linarith
    have hpole1 : ∀ j : ℕ, j < k → s z₀ + 1 ≠ -(j : ℂ) := by
      intro j hj h
      exact hpole (j + 1) (by omega) (by push_cast; linear_combination h)
    have hs0 : s z₀ ≠ 0 := by simpa using hpole 0 (by omega)
    have h1 := ih hg.succ hs1 hre1 hpole1
    have h0 : AnalyticAt ℂ (fun z => g 0 z 1) z₀ :=
      (hg.differentiableOn 0 (by omega) 1 ⟨zero_le_one, le_rfl⟩).analyticAt (hU.mem_nhds hz₀)
    have hsa : AnalyticAt ℂ s z₀ := hs.analyticAt (hU.mem_nhds hz₀)
    exact (h0.sub h1).div hsa hs0

/-- **Meromorphy of the parametric continuation** on `re s z₀ > -k`. -/
theorem meromorphicAt_mellinCont_param {g : ℕ → ℂ → ℝ → ℂ} {k : ℕ} {U : Set ℂ}
    (hU : IsOpen U) (hg : TDerivFamily g k U) {s : ℂ → ℂ} (hs : DifferentiableOn ℂ s U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hre : -(k : ℝ) < (s z₀).re) :
    MeromorphicAt (fun z => mellinCont k (fun j => g j z) (s z)) z₀ := by
  induction k generalizing g s with
  | zero =>
    exact (analyticAt_mellinUnit_param hU (hg.continuousOn 0 le_rfl)
      (hg.differentiableOn 0 le_rfl) hs hz₀ (by simpa using hre)).meromorphicAt
  | succ k ih =>
    have hs1 : DifferentiableOn ℂ (fun z => s z + 1) U := hs.add_const 1
    have hre1 : -(k : ℝ) < (s z₀ + 1).re := by simp; push_cast at hre; linarith
    have h1 := ih hg.succ hs1 hre1
    have h0 : AnalyticAt ℂ (fun z => g 0 z 1) z₀ :=
      (hg.differentiableOn 0 (by omega) 1 ⟨zero_le_one, le_rfl⟩).analyticAt (hU.mem_nhds hz₀)
    have hsa : AnalyticAt ℂ s z₀ := hs.analyticAt (hU.mem_nhds hz₀)
    exact (h0.meromorphicAt.sub h1).div hsa.meromorphicAt

end QED.DimReg
