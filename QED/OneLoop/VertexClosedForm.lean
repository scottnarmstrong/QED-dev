/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.VertexEnergyFirst
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Toward the closed form of the one-loop vertex

The `ε → 0⁺` limit of the energy-first integral of the one-loop vertex integrand is
`∫ v, spatialG 0 v` (`QED.OneLoop.VertexLimit.tendsto_energyFirstIntegral_vertexIntegrand`).
This module swaps the spatial integral with the Feynman-parameter integral at `ε = 0`, so that
the spatial integral can be done at fixed Feynman parameters.

## Main statements

* `QED.OneLoop.VertexLimit.integral_spatialG_zero_eq`: `∫ v, spatialG 0 v` equals the
  Feynman-parameter integral of `κ · 2y · ∫ v, (T_γ - T_Λ)` at `ε = 0`.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexLimit

/-- Almost every point of a product with `feynmanMeasure` has Feynman parameters in the open-closed
unit square. -/
theorem ae_prod_feynmanMeasure {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ] :
    ∀ᵐ q ∂μ.prod feynmanMeasure, q.2 ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
  have h : μ.prod feynmanMeasure
      = (μ.prod (volume : Measure (ℝ × ℝ))).restrict (univ ×ˢ (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1)) := by
    rw [feynmanMeasure_eq, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [h]
  exact ae_restrict_of_forall_mem
    (MeasurableSet.univ.prod (measurableSet_Ioc.prod measurableSet_Ioc)) fun q hq => hq.2

theorem continuous_massW_prod (m M : ℝ) (p' p : Fin 4 → ℝ) :
    Continuous fun q : (Fin 3 → ℝ) × (ℝ × ℝ) => massW m M p' p q.2 q.1 := by
  have hK := (continuous_shiftK p' p).comp (continuous_snd (X := Fin 3 → ℝ) (Y := ℝ × ℝ))
  have hD := (continuous_feynmanMass m M p' p).comp (continuous_snd (X := Fin 3 → ℝ) (Y := ℝ × ℝ))
  unfold massW
  refine (continuous_finsetSum _ fun k _ => ?_).add hD
  exact (((continuous_apply k).comp continuous_fst).add ((continuous_apply k.succ).comp hK)).pow 2

theorem measurable_timeT (m M ε : ℝ) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) => timeT m M ε p' p μ i j q.2 q.1 := by
  have hX : Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) =>
      (-(massW m M p' p q.2 q.1 : ℂ) + ε * I) :=
    (Complex.measurable_ofReal.comp (continuous_massW_prod m M p' p).measurable).neg.add_const _
  have ha : Continuous fun q : (Fin 3 → ℝ) × (ℝ × ℝ) => -shiftK p' p q.2 0 :=
    ((continuous_apply 0).comp ((continuous_shiftK p' p).comp continuous_snd)).neg
  have hN : Continuous fun q : (Fin 3 → ℝ) × (ℝ × ℝ) =>
      vertexNumerator m p' p μ (Fin.cons (-shiftK p' p q.2 0) q.1 : Fin 4 → ℝ) i j :=
    (continuous_vertexNumerator m p' p μ i j).comp
      (Continuous.finCons (A := fun _ : Fin 4 => ℝ) ha continuous_fst)
  unfold timeT
  exact ((measurable_const.mul (hX.pow_const _)).neg).sub
    ((measurable_const.mul hN.measurable).mul (hX.pow_const _))

/-- At `ε = 0`, the spatial integral and the Feynman-parameter integral can be swapped. -/
theorem integral_spatialG_zero_eq {e m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ)
    {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -m ^ 2) (hp : Minkowski.dot p p = -m ^ 2)
    (hp0' : 0 < p' 0) (hp0 : 0 < p 0) (μ i j : Fin 4) :
    ∫ v, spatialG e m mγ Λ 0 p' p μ i j v =
      ∫ z, (kappa e * (2 * (z.2 : ℂ)) *
        ∫ v, (timeT m mγ 0 p' p μ i j z v - timeT m Λ 0 p' p μ i j z v)) ∂feynmanMeasure := by
  obtain ⟨Cb, hCb⟩ := norm_timeT_zero_sub_le hm hmγ hΛ hp' hp hp0' hp0 μ i j
  set f : (Fin 3 → ℝ) → ℝ × ℝ → ℂ := fun v z => kappa e * (2 * (z.2 : ℂ)) *
    (timeT m mγ 0 p' p μ i j z v - timeT m Λ 0 p' p μ i j z v) with hf
  have hint : Integrable (Function.uncurry f)
      ((volume : Measure (Fin 3 → ℝ)).prod feynmanMeasure) := by
    have hg := ((integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5)
      (by simp; norm_num)).const_mul (‖kappa e‖ * 2 * Cb)).mul_prod
        (integrable_const (μ := feynmanMeasure) (1 : ℝ))
    refine Integrable.mono' hg ?_ ((ae_prod_feynmanMeasure _).mono fun q hq => ?_)
    · have h2 : Measurable fun q : (Fin 3 → ℝ) × (ℝ × ℝ) => (2 * (q.2.2 : ℂ)) :=
        measurable_const.mul (Complex.measurable_ofReal.comp measurable_snd.snd)
      exact ((measurable_const.mul h2).mul ((measurable_timeT m mγ 0 p' p μ i j).sub
        (measurable_timeT m Λ 0 p' p μ i j))).aestronglyMeasurable
    · obtain ⟨v, z⟩ := q
      simp only [Function.uncurry_apply_pair, hf, mul_one] at hq ⊢
      have hb := hCb z (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self hq) v
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hq.2.1]
      calc ‖kappa e‖ * (2 * z.2) *
            ‖timeT m mγ 0 p' p μ i j z v - timeT m Λ 0 p' p μ i j z v‖
          ≤ ‖kappa e‖ * (2 * 1) * (Cb * (1 + ‖v‖) ^ (-(5 : ℝ))) := by
            gcongr
            exact hq.2.2
        _ = ‖kappa e‖ * 2 * Cb * (1 + ‖v‖) ^ (-(5 : ℝ)) := by ring
  have hG : ∀ v, spatialG e m mγ Λ 0 p' p μ i j v = ∫ z, f v z ∂feynmanMeasure := fun v => rfl
  simp_rw [hG]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hf]
  rw [integral_const_mul]

/-- The reflection `x ↦ 1 - x` of the first Feynman parameter preserves `feynmanMeasure`. -/
theorem measurePreserving_feynman_reflect :
    MeasurePreserving (fun z : ℝ × ℝ => (1 - z.1, z.2)) feynmanMeasure feynmanMeasure := by
  have h0 : MeasurePreserving (fun x : ℝ => 1 - x) (volume.restrict (Ioc (0 : ℝ) 1))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have h := ((volume : Measure ℝ).measurePreserving_sub_left (1 : ℝ)).restrict_preimage
      (measurableSet_Ico (a := (0 : ℝ)) (b := 1))
    have hpre : (fun x : ℝ => 1 - x) ⁻¹' Ico (0 : ℝ) 1 = Ioc (0 : ℝ) 1 := by
      ext x; simp only [mem_preimage, mem_Ico, mem_Ioc]; constructor <;> intro h <;>
        constructor <;> linarith [h.1, h.2]
    rw [hpre, Measure.restrict_congr_set Ico_ae_eq_Ioc] at h
    exact h
  unfold feynmanMeasure
  exact h0.prod (MeasurePreserving.id _)

/-- Integrals against `feynmanMeasure` are invariant under `x ↦ 1 - x`. -/
theorem integral_feynman_reflect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) :
    ∫ z, f (1 - z.1, z.2) ∂feynmanMeasure = ∫ z, f z ∂feynmanMeasure := by
  have he : MeasurableEmbedding (fun z : ℝ × ℝ => (1 - z.1, z.2)) :=
    ((MeasurableEquiv.subLeft (1 : ℝ)).prodCongr (MeasurableEquiv.refl ℝ)).measurableEmbedding
  exact measurePreserving_feynman_reflect.integral_comp he f

/-- An integrand that is odd under `x ↦ 1 - x` integrates to zero against `feynmanMeasure`. -/
theorem integral_feynman_eq_zero_of_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} (hf : ∀ z, f (1 - z.1, z.2) = -f z) :
    ∫ z, f z ∂feynmanMeasure = 0 := by
  have h := integral_feynman_reflect f
  simp_rw [hf, integral_neg] at h
  have h2 : (2 : ℝ) • ∫ z, f z ∂feynmanMeasure = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end QED.OneLoop.VertexLimit

end
