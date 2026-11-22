/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegDispCtLoBUndKern
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The kernels of the mass part at zero momentum transfer

Helper level for the mass part `QED.ChainProof.SetCRegDisp.CBLoBEq` of set (c), layer 5 of the
plan. The merged insertion at `cbBParams` on the doubled line is `b (1/D - 2m A/D²)`; its outer
vertex is the undoubled value `undVal` minus `2m` times the doubled value `dblVal`, i.e.
`i (π²/6) 4 κ_e q² (4m² + q²)² ∫ (undKern - 2m² dblKern)`. This file gives

* `tendsto_integral_undKern`, `tendsto_integral_dblKern`: the kernel integrals are continuous in
  `s = q²` at `s = 0` from above (dominated convergence, uniform bounds for `s ≥ 0`);
* **`integral_comb_zero`**: at `s = 0`, with `K = y² m²/(1-y)` and the photon function
  `g(K) = ∏_i (K + M_i²)⁻¹` (`phf`),
  `∫ (undKern - 2m² dblKern) = ∫₀¹ 6 y (g(K) - K g(K) Σ_i (K + M_i²)⁻¹) dy = ∫₀¹ 6 y (K g)'(K) dy`.

The last form is the shape of `QED.ChainProof.SetCRegDisp.vpInsertW`
(`∫₀¹ x (K R(K))' dx` at `K = x²/(1-x)`): the mass derivative of the Pauli value acts on the
photon function as `g ↦ (K g)'`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set intervalIntegral
open scoped Real

namespace QED.ChainProof.CtLoB

open QED.OneLoop QED.OneLoop.VertexLimit QED.Integration QED.TwoLoop.VPHalfAtLimit
open QED.TwoLoop.VPUnitNested

/-! ### Continuity in the momentum transfer -/

theorem continuousAt_kDen_s (m M : ℝ) (z : ℝ × ℝ) (s : ℝ) :
    ContinuousAt (fun s => kDen m M s z) s := by
  unfold kDen kC
  fun_prop

theorem tendsto_integral_dblKern {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) {k : ℕ}
    {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) (d : Fin 2) :
    Tendsto (fun s => ∫ z, dblKern m s Ms d z ∂feynmanMeasure) (𝓝[≥] 0)
      (𝓝 (∫ z, dblKern m 0 Ms d z ∂feynmanMeasure)) := by
  have hc₀ : (0 : ℝ) < 3 / 4 * min (M₀ ^ 2) (m ^ 2) := by positivity
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => 6 * (k + 2) / (3 / 4 * min (M₀ ^ 2) (m ^ 2)) ^ (k + 3))
    (Eventually.of_forall fun s => (measurable_dblKern m s Ms d).aestronglyMeasurable) ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 ≤ s)
    filter_upwards [ae_feynmanMeasure] with z hz
    rw [Real.norm_eq_abs]
    exact abs_dblKern_le hm hs hM₀ hMs d (Ioc_prod_subset hz)
  · filter_upwards [ae_feynmanMeasure] with z hz
    have hDz : ∀ i, kDen m (Ms i) 0 z ≠ 0 := fun i =>
      (hc₀.trans_le (kDen_ge_min le_rfl hM₀.le (hMs i) (Ioc_prod_subset hz))).ne'
    have hc : ContinuousAt (fun s => dblKern m s Ms d z) 0 := by
      unfold dblKern
      refine ContinuousAt.div (continuousAt_const.mul ?_) ?_
        (Finset.prod_ne_zero_iff.2 fun i _ => hDz i)
      · exact tendsto_finsetSum _ fun i _ =>
          ContinuousAt.inv₀ (continuousAt_kDen_s m (Ms i) z 0) (hDz i)
      · exact tendsto_finsetProd _ fun i _ => continuousAt_kDen_s m (Ms i) z 0
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_integral_undKern {m M₀ : ℝ} (hm : 0 < m) (hM₀ : 0 < M₀) {k : ℕ}
    {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, M₀ ≤ Ms i) :
    Tendsto (fun s => ∫ z, undKern m s Ms z ∂feynmanMeasure) (𝓝[≥] 0)
      (𝓝 (∫ z, undKern m 0 Ms z ∂feynmanMeasure)) := by
  have hc₀ : (0 : ℝ) < 3 / 4 * min (M₀ ^ 2) (m ^ 2) := by positivity
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => 6 / (3 / 4 * min (M₀ ^ 2) (m ^ 2)) ^ (k + 2))
    (Eventually.of_forall fun s => (measurable_undKern m s Ms).aestronglyMeasurable) ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 0 ≤ s)
    filter_upwards [ae_feynmanMeasure] with z hz
    rw [Real.norm_eq_abs]
    exact abs_undKern_le hm hs hM₀ hMs (Ioc_prod_subset hz)
  · filter_upwards [ae_feynmanMeasure] with z hz
    have hDz : ∀ i, kDen m (Ms i) 0 z ≠ 0 := fun i =>
      (hc₀.trans_le (kDen_ge_min le_rfl hM₀.le (hMs i) (Ioc_prod_subset hz))).ne'
    have hc : ContinuousAt (fun s => undKern m s Ms z) 0 := by
      unfold undKern
      exact ContinuousAt.div continuousAt_const
        (tendsto_finsetProd _ fun i _ => continuousAt_kDen_s m (Ms i) z 0)
        (Finset.prod_ne_zero_iff.2 fun i _ => hDz i)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-! ### The identity at zero momentum transfer -/

/-- The photon function `g(K) = ∏_i (K + M_i²)⁻¹`. -/
noncomputable def phf {n : ℕ} (Ms : Fin n → ℝ) (K : ℝ) : ℝ := ∏ i, (K + Ms i ^ 2)⁻¹

/-- The radial variable `K = y² m²/(1 - y)` of the Feynman parameter `y`. -/
noncomputable def radKY (m y : ℝ) : ℝ := y ^ 2 * m ^ 2 / (1 - y)

theorem kDen_zero_eq (m M : ℝ) {z : ℝ × ℝ} (hy : z.2 ≠ 1) :
    kDen m M 0 z = (1 - z.2) * (radKY m z.2 + M ^ 2) := by
  have h : 1 - z.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  unfold kDen kC radKY
  field_simp
  ring

theorem integral_dblLineWt (d : Fin 2) : ∫ x in Ioc (0 : ℝ) 1, dblLineWt d x = 1 / 2 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  unfold dblLineWt
  split_ifs
  · rw [intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    simp
    norm_num
  · simp

/-- The inner (`x`) integral of the combination at `s = 0`, for `0 < y < 1`. -/
theorem inner_comb_zero {m : ℝ} {k : ℕ} {Ms : Fin (k + 2) → ℝ} (hMs : ∀ i, 0 < Ms i)
    (d : Fin 2) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ∫ x in Ioc (0 : ℝ) 1, (undKern m 0 Ms (x, y) - 2 * m ^ 2 * dblKern m 0 Ms d (x, y)) =
      6 * y * (phf Ms (radKY m y) -
        radKY m y * phf Ms (radKY m y) * ∑ i, (radKY m y + Ms i ^ 2)⁻¹) := by
  obtain ⟨hy0, hy1⟩ := hy
  have h1 : (1 - y) ≠ 0 := by linarith
  have hK : 0 ≤ radKY m y := div_nonneg (by positivity) (by linarith)
  set K := radKY m y with hKdef
  have hP : ∀ i, K + Ms i ^ 2 ≠ 0 := fun i => (by have := hMs i; positivity : 0 < K + Ms i ^ 2).ne'
  set P := ∏ i, (K + Ms i ^ 2) with hPdef
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hP i
  set S := ∑ i, (K + Ms i ^ 2)⁻¹ with hSdef
  have hD : ∀ x : ℝ, ∏ i, kDen m (Ms i) 0 (x, y) = (1 - y) ^ (k + 2) * P := by
    intro x
    rw [Finset.prod_congr rfl fun i _ => kDen_zero_eq m (Ms i) (z := (x, y)) (by simpa using
      (show y ≠ 1 by linarith)), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hS : ∀ x : ℝ, ∑ i, (kDen m (Ms i) 0 (x, y))⁻¹ = (1 - y)⁻¹ * S := by
    intro x
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [kDen_zero_eq m (Ms i) (z := (x, y)) (by simpa using (show y ≠ 1 by linarith)), mul_inv]
  have hphf : phf Ms K = P⁻¹ := by
    rw [phf, hPdef, Finset.prod_inv_distrib]
  have hpt : ∀ x : ℝ, undKern m 0 Ms (x, y) - 2 * m ^ 2 * dblKern m 0 Ms d (x, y) =
      6 * y * P⁻¹ - dblLineWt d x * (2 * (6 * y * K * P⁻¹ * S)) := by
    intro x
    unfold undKern dblKern
    rw [hD x, hS x, hKdef, radKY]
    simp only
    field_simp
    ring
  simp_rw [hpt]
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub intervalIntegrable_const
      ((by unfold dblLineWt; split_ifs <;> fun_prop : Continuous (dblLineWt d)).intervalIntegrable
        _ _ |>.mul_const _),
    intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_of_le zero_le_one,
    integral_dblLineWt, hphf]
  simp
  ring

/-- **The combination at zero momentum transfer.** At `s = 0` the Feynman-parameter integral of
`undKern - 2m² dblKern` is `∫₀¹ 6 y (g - K g Σ_i (K + M_i²)⁻¹) dy`, `K = y² m²/(1 - y)`,
`g = phf Ms K`; i.e. `∫₀¹ 6 y (K g)'(K) dy`. -/
theorem integral_comb_zero {m : ℝ} (hm : 0 < m) {k : ℕ} {Ms : Fin (k + 2) → ℝ}
    (hMs : ∀ i, 0 < Ms i) (d : Fin 2) :
    ∫ z, (undKern m 0 Ms z - 2 * m ^ 2 * dblKern m 0 Ms d z) ∂feynmanMeasure =
      ∫ y in (0 : ℝ)..1,
        6 * y * (phf Ms (radKY m y) -
        radKY m y * phf Ms (radKY m y) * ∑ i, (radKY m y + Ms i ^ 2)⁻¹) := by
  obtain ⟨M₀, hM₀, hle⟩ : ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ i, M₀ ≤ Ms i :=
    ⟨Finset.univ.inf' Finset.univ_nonempty Ms,
      (Finset.lt_inf'_iff _).2 fun i _ => hMs i, fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
  have hint : Integrable (fun z => undKern m 0 Ms z - 2 * m ^ 2 * dblKern m 0 Ms d z)
      feynmanMeasure :=
    (integrable_undKern hm le_rfl hM₀ hle).sub
      ((integrable_dblKern hm le_rfl hM₀ hle d).const_mul _)
  rw [feynmanMeasure] at hint ⊢
  rw [integral_prod_symm _ hint, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun y hy => inner_comb_zero hMs d hy

end QED.ChainProof.CtLoB

end
