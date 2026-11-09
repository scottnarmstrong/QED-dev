/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.OneLoop.VertexEnergyFirst
import QED.OneLoop.VertexOffShell
import QED.OneLoop.VertexOffShellBound
import QED.Integration.LoopBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Integrability of the regulated one-loop vertex at all momenta

At a fixed regulator `ε > 0` both stages of the energy-first integral of each entry of the
regulated one-loop vertex integrand are integrable, for all external momenta `p', p` and all
masses: no on-shell premise and no positivity of the masses is needed. The inner (energy) stage is
`QED.OneLoop.VertexLimit.integrable_time_vertexIntegrand`. For the outer (spatial) stage, the
mass term `massW` grows like `‖v‖²`, so for large `‖v‖` the pointwise Pauli–Villars bound
`norm_timeT_sub_le_of_massW_ge` applies, while for bounded `v` the closed-form energy integral is
continuous (its base stays in the slit plane since `ε > 0`), hence bounded on a compact set.
Together these give a `(1 + ‖v‖)⁻⁵` bound (with an `ε`-dependent constant).

## Main statements

* `integrable_spatialG_of_pos`: the outer stage is integrable at every `ε > 0`.
* `integrable_energyFirst_of_pos`: both stages, in the form of the frozen theorem (E).

The declarations here are internal helpers, not source-facing definitions.
-/

@[expose] public section

open Matrix Complex Filter Topology MeasureTheory Set
open QED.OneLoop QED.Integration
open scoped Real

namespace QED.OneLoop.VertexOffShell

open QED.OneLoop.VertexLimit

/-- At `ε > 0` the closed-form energy integral is jointly continuous in the Feynman parameters
and the spatial loop momentum. -/
theorem continuous_timeT_prod {ε : ℝ} (hε : 0 < ε) (m M : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) :
    Continuous fun q : (ℝ × ℝ) × (Fin 3 → ℝ) => timeT m M ε p' p μ i j q.1 q.2 := by
  unfold timeT
  have hW : Continuous fun q : (ℝ × ℝ) × (Fin 3 → ℝ) => massW m M p' p q.1 q.2 :=
    continuous_massW_comp m M continuous_const continuous_const continuous_fst continuous_snd
  have hX : Continuous fun q : (ℝ × ℝ) × (Fin 3 → ℝ) =>
      (-(massW m M p' p q.1 q.2 : ℂ) + ε * I) := by fun_prop
  have h32 := hX.cpow (continuous_const (y := -(3 / 2 : ℂ)))
    (fun q => mem_slitPlane_neg_add_mul_I hε _)
  have h52 := hX.cpow (continuous_const (y := -(5 / 2 : ℂ)))
    (fun q => mem_slitPlane_neg_add_mul_I hε _)
  have ha : Continuous fun q : (ℝ × ℝ) × (Fin 3 → ℝ) => -shiftK p' p q.1 0 :=
    ((continuous_apply 0).comp ((continuous_shiftK p' p).comp continuous_fst)).neg
  have hN : Continuous fun q : (ℝ × ℝ) × (Fin 3 → ℝ) =>
      vertexNumerator m p' p μ (Fin.cons (-shiftK p' p q.1 0) q.2 : Fin 4 → ℝ) i j :=
    (continuous_vertexNumerator m p' p μ i j).comp
      (Continuous.finCons (A := fun _ : Fin 4 => ℝ) ha continuous_snd)
  fun_prop

/-- At `ε > 0`, the Pauli–Villars difference of the closed-form energy integrals decays like
`(1 + ‖v‖)⁻⁵` uniformly in the Feynman parameters, for all momenta and masses. -/
theorem exists_norm_timeT_sub_le_of_pos {ε : ℝ} (hε : 0 < ε) (m mγ Λ : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) :
    ∃ Cb : ℝ, ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ v : Fin 3 → ℝ,
      ‖timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v‖
        ≤ Cb * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  have hSc : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨Bγ, hBγ⟩ := hSc.exists_bound_of_continuousOn
    (continuous_feynmanMass m mγ p' p).continuousOn
  obtain ⟨BΛ, hBΛ⟩ := hSc.exists_bound_of_continuousOn
    (continuous_feynmanMass m Λ p' p).continuousOn
  set B : ℝ := |Bγ| + |BΛ| with hB_def
  have hB0 : 0 ≤ B := by positivity
  have hD : ∀ M : ℝ, (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      ‖feynmanMass m M z.1 z.2 p' p‖ ≤ |Bγ| + |BΛ|) →
      ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, -B ≤ feynmanMass m M z.1 z.2 p' p := by
    intro M hM z hz
    have h := hM z hz
    rw [Real.norm_eq_abs] at h
    linarith [neg_abs_le (feynmanMass m M z.1 z.2 p' p)]
  have hDγ := hD mγ fun z hz =>
    (hBγ z hz).trans (by linarith [le_abs_self Bγ, abs_nonneg BΛ])
  have hDΛ := hD Λ fun z hz =>
    (hBΛ z hz).trans (by linarith [le_abs_self BΛ, abs_nonneg Bγ])
  set A0 : ℝ := ‖p'‖ + ‖p‖ with hA0_def
  have hA0 : 0 ≤ A0 := by positivity
  obtain ⟨c1, hc1, hcoer⟩ := exists_mul_one_add_norm_sq_le (n := 3) A0 (D₀ := 1) one_pos
  obtain ⟨CN, hCN⟩ := exists_norm_vertexNumerator_le m p' p μ i j
  have hCN0 : 0 ≤ CN := nonneg_of_norm_le_mul_sq hCN
  set R0 : ℝ := 2 * (1 + B) / c1 with hR0_def
  have hR0 : 0 ≤ R0 := by positivity
  have hKc : IsCompact ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ Metric.closedBall (0 : Fin 3 → ℝ) R0) :=
    hSc.prod (isCompact_closedBall 0 R0)
  obtain ⟨M0, hM0⟩ := hKc.exists_bound_of_continuousOn
    ((continuous_timeT_prod hε m mγ p' p μ i j).sub
      (continuous_timeT_prod hε m Λ p' p μ i j)).continuousOn
  set W0 : ℝ := (1 + R0) ^ (-(5 : ℝ)) with hW0_def
  have hW0 : 0 < W0 := by positivity
  set K1 : ℝ := π / 8 * ‖alphaN m p' p μ i j‖
        * (3 / 2 * (mγ ^ 2 + Λ ^ 2) * (c1 / 2) ^ (-(3 / 2 + 1 : ℝ)))
      + 3 * π / 8 * (CN * (1 + A0) ^ 2) * (5 / 2 * (mγ ^ 2 + Λ ^ 2) * (c1 / 2) ^ (-(5 / 2 + 1 : ℝ)))
    with hK1_def
  have hK1 : 0 ≤ K1 := by positivity
  refine ⟨K1 + |M0| / W0, fun z hz v => ?_⟩
  have hu5 : 0 < (1 + ‖v‖) ^ (-(5 : ℝ)) := by positivity
  have hb : ‖(fun k : Fin 3 => shiftK p' p z k.succ)‖ ≤ A0 :=
    (pi_norm_le_iff_of_nonneg hA0).2 fun k =>
      (norm_le_pi_norm (shiftK p' p z) k.succ).trans (norm_shiftK_le p' p hz)
  have hsq : c1 * (1 + ‖v‖) ^ 2 ≤ ∑ k : Fin 3, (v k + shiftK p' p z k.succ) ^ 2 + 1 :=
    hcoer v _ 1 hb le_rfl
  by_cases hv : 2 * (1 + B) ≤ c1 * (1 + ‖v‖) ^ 2
  · -- Large `v`: both mass terms are at least `(c₁/2) (1 + ‖v‖)²`.
    have hW : ∀ M : ℝ, -B ≤ feynmanMass m M z.1 z.2 p' p →
        c1 / 2 * (1 + ‖v‖) ^ 2 ≤ massW m M p' p z v := by
      intro M hDM
      have hm : massW m M p' p z v
          = ∑ k : Fin 3, (v k + shiftK p' p z k.succ) ^ 2 + feynmanMass m M z.1 z.2 p' p := rfl
      rw [hm]
      linarith
    have hN : ‖vertexNumerator m p' p μ (Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ) i j‖
        ≤ CN * (1 + A0) ^ 2 * (1 + ‖v‖) ^ 2 := by
      refine (hCN _).trans ?_
      have ha : |-shiftK p' p z 0| ≤ A0 := by
        rw [abs_neg]
        exact (Real.norm_eq_abs _ ▸ norm_le_pi_norm (shiftK p' p z) 0).trans
          (norm_shiftK_le p' p hz)
      have h1 := norm_finCons_le (-shiftK p' p z 0) v
      have h2 : 1 + ‖(Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖ ≤ (1 + A0) * (1 + ‖v‖) := by
        nlinarith [norm_nonneg v]
      calc CN * (1 + ‖(Fin.cons (-shiftK p' p z 0) v : Fin 4 → ℝ)‖) ^ 2
          ≤ CN * ((1 + A0) * (1 + ‖v‖)) ^ 2 := by gcongr
        _ = CN * (1 + A0) ^ 2 * (1 + ‖v‖) ^ 2 := by ring
    have h := norm_timeT_sub_le_of_massW_ge hε μ i j hz.2 (by positivity : 0 < c1 / 2)
      (hW mγ (hDγ z hz)) (hW Λ (hDΛ z hz)) hN
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hu5.le)
    have : 0 ≤ |M0| / W0 := by positivity
    linarith
  · -- Bounded `v`: the compact bound.
    have hv' : c1 * (1 + ‖v‖) ^ 2 < 2 * (1 + B) := lt_of_not_ge hv
    have hu2 : (1 + ‖v‖) ^ 2 < R0 := by
      rw [hR0_def, lt_div_iff₀ hc1]
      linarith
    have hvR : ‖v‖ ≤ R0 := by nlinarith [norm_nonneg v]
    have hball : v ∈ Metric.closedBall (0 : Fin 3 → ℝ) R0 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hvR
    have h1 : ‖timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v‖ ≤ M0 :=
      hM0 (z, v) ⟨hz, hball⟩
    have h2 : W0 ≤ (1 + ‖v‖) ^ (-(5 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have h3 : |M0| = |M0| / W0 * W0 := by field_simp
    have h4 : |M0| / W0 * W0 ≤ |M0| / W0 * (1 + ‖v‖) ^ (-(5 : ℝ)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : 0 ≤ K1 * (1 + ‖v‖) ^ (-(5 : ℝ)) := by positivity
    calc ‖timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v‖
        ≤ |M0| := h1.trans (le_abs_self M0)
      _ = |M0| / W0 * W0 := h3
      _ ≤ |M0| / W0 * (1 + ‖v‖) ^ (-(5 : ℝ)) := h4
      _ ≤ (K1 + |M0| / W0) * (1 + ‖v‖) ^ (-(5 : ℝ)) := by nlinarith

/-- At `ε > 0`, the energy integral `spatialG` decays like `(1 + ‖v‖)⁻⁵`, for all momenta. -/
theorem exists_norm_spatialG_le_of_pos {ε : ℝ} (hε : 0 < ε) (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) :
    ∃ C : ℝ, ∀ v : Fin 3 → ℝ, ‖spatialG e m mγ Λ ε p' p μ i j v‖ ≤ C * (1 + ‖v‖) ^ (-(5 : ℝ)) := by
  obtain ⟨Cb, hCb⟩ := exists_norm_timeT_sub_le_of_pos hε m mγ Λ p' p μ i j
  refine ⟨‖kappa e‖ * 2 * Cb * feynmanMeasure.real univ, fun v => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := feynmanMeasure)
    (f := fun z => kappa e * (2 * (z.2 : ℂ)) *
      (timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v))
    (C := ‖kappa e‖ * 2 * (Cb * (1 + ‖v‖) ^ (-(5 : ℝ))))
    (ae_feynmanMeasure.mono fun z hz => by
      have hzI := Ioc_prod_subset hz
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hz.2.1]
      calc ‖kappa e‖ * (2 * z.2) *
            ‖timeT m mγ ε p' p μ i j z v - timeT m Λ ε p' p μ i j z v‖
          ≤ ‖kappa e‖ * (2 * 1) * (Cb * (1 + ‖v‖) ^ (-(5 : ℝ))) := by
            gcongr
            · exact hz.2.2
            · exact hCb z hzI v
        _ = ‖kappa e‖ * 2 * (Cb * (1 + ‖v‖) ^ (-(5 : ℝ))) := by ring)
  refine h.trans (le_of_eq ?_)
  ring

/-- At `ε > 0`, the outer (spatial) stage of the energy-first integral is integrable, for all
momenta and masses. -/
theorem integrable_spatialG_of_pos {ε : ℝ} (hε : 0 < ε) (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) : Integrable (spatialG e m mγ Λ ε p' p μ i j) := by
  obtain ⟨C, hC⟩ := exists_norm_spatialG_le_of_pos hε e m mγ Λ p' p μ i j
  have h := integrable_one_add_norm (E := Fin 3 → ℝ) (μ := volume) (r := 5) (by simp; norm_num)
  exact (h.const_mul C).mono' (aestronglyMeasurable_spatialG hε e m mγ Λ p' p μ i j)
    (Eventually.of_forall hC)

/-- At `ε > 0`, both stages of the energy-first integral of each entry of the regulated one-loop
vertex integrand are integrable, for all momenta and masses (the integrability clause of the
frozen theorem (E), without its on-shell premises). -/
theorem integrable_energyFirst_of_pos {ε : ℝ} (hε : 0 < ε) (e m mγ Λ : ℝ) (p' p : Fin 4 → ℝ)
    (μ i j : Fin 4) :
    (∀ v : Fin 3 → ℝ,
      Integrable fun t : ℝ => vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons t v : Fin 4 → ℝ) i j) ∧
    Integrable fun v : Fin 3 → ℝ =>
      ∫ t : ℝ, vertexIntegrand e m mγ Λ ε p' p μ (Fin.cons t v : Fin 4 → ℝ) i j :=
  ⟨fun v => integrable_time_vertexIntegrand hε e m mγ Λ p' p μ i j v,
    (integrable_spatialG_of_pos hε e m mγ Λ p' p μ i j).congr
      (Eventually.of_forall fun v => (integral_vertexIntegrand_time hε e m mγ Λ p' p μ i j v).symm)⟩

end QED.OneLoop.VertexOffShell

end
