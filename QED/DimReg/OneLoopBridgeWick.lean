/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import QED.Frozen.Algebra.Dot
public import QED.DimReg.Tadpole
public import QED.Integration.ShiftedEnergyIntegral
public import QED.Integration.SpatialIntegral
import QED.Algebra.Minkowski
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The one-loop Wick rotation as a theorem (pilot P1, part 1)

The dimensionally regularized side (`QED.DimReg`) defines its loop integrals as Euclidean
parametric integrals; the passage from Minkowski momentum space to these definitions is
stated there as a convention (`QED.DimReg.LR96Family`, `QED.DimReg.OneLoopSchwinger`). The
model side (`QED.OneLoop`) never Wick-rotates: it evaluates Minkowski loop integrals by the
energy-first prescription M1 (`QED.OneLoop.energyFirstIntegral`, `docs/REGULARIZATION.md`,
section 4), with the energy integral done on the slit plane
(`QED.Integration.integral_neg_sq_add_zpow_three`).

This module proves that the two agree for the scalar kernel that carries the one-loop Pauli
form factor. For `Δ > 0` and the mostly-plus metric,

  `lim_{ε → 0⁺} ∫ d³ℓ ∫ dℓ⁰ (ℓ·ℓ + Δ - iε)⁻³ = i π² · I_E(Δ; 3, 4)`,

where `I_E(Δ; ν, d) = ∫ dᵈℓ_E / π^{d/2} (ℓ_E² + Δ)^{-ν}` is the Euclidean tadpole of the
dimensionally regularized side at `d = 4` (`QED.DimReg.tadpole`, identified with the family
integral of `QED.DimReg.tadpoleFamily` by `QED.DimReg.integral_tadpoleFamily`). So the factor
`i π^{d/2}` and the sign of the Wick rotation are theorems at `d = 4`, not conventions.

Proof: at `ε > 0` the energy integral is `-(3π/8) (-w)^{-5/2}` with
`w = |ℓ⃗|² + Δ - iε` (`QED.Integration.integral_neg_sq_add_zpow_three`); the spatial integrand is
bounded by `(3π/8)(|ℓ⃗|² + Δ)^{-5/2}` uniformly in `ε`, and tends pointwise to
`-(3π/8) (-1)^{-5/2} (|ℓ⃗|² + Δ)^{-5/2} = (3πi/8)(|ℓ⃗|² + Δ)^{-5/2}` (the branch is approached
from the upper half plane, `QED.Integration.tendsto_cpow_neg_add_mul_I`); dominated convergence
and `∫ d³ℓ (|ℓ⃗|² + Δ)^{-5/2} = 4π/(3Δ)`
(`QED.Integration.integral_sum_sq_add_rpow_neg_five_halves`) give
`i π² / (2Δ) = i π² Γ(1)/Γ(3) Δ^{-1}`.

## Main statements

* `QED.DimReg.OneLoopBridge.integrable_wickKernel_time`,
  `QED.DimReg.OneLoopBridge.integrable_wickKernel_space`: both stages of M1 are integrable.
* `QED.DimReg.OneLoopBridge.tendsto_energyFirstIntegral_wickKernel`: the limit above.
* `QED.DimReg.OneLoopBridge.tendsto_energyFirstIntegral_wickKernel_family`: the same with the
  limit written as the family integral `(tadpoleFamily Δ).integral 3 4`.
-/

@[expose] public section

open MeasureTheory Set Complex Filter Topology
open QED.Integration
open scoped Real

namespace QED.DimReg.OneLoopBridge

/-- The scalar one-loop kernel of prescription M1 at `d = 4`: `(ℓ·ℓ + Δ - iε)⁻³`, with the
mostly-plus Minkowski product `QED.Minkowski.dot`. -/
noncomputable def wickKernel (Δ ε : ℝ) (ℓ : Fin 4 → ℝ) : ℂ :=
  (((Minkowski.dot ℓ ℓ + Δ : ℝ) : ℂ) - ε * I) ^ (-3 : ℤ)

theorem dot_cons_self (t : ℝ) (v : Fin 3 → ℝ) :
    Minkowski.dot (Fin.cons t v : Fin 4 → ℝ) (Fin.cons t v) = -t ^ 2 + ∑ k, v k ^ 2 := by
  rw [Minkowski.dot_eq]
  simp only [Fin.sum_univ_three]
  change -(t * t) + v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = _
  ring

/-- The spatial weight `W(ℓ⃗) = |ℓ⃗|² + Δ`. -/
noncomputable def spatialW (Δ : ℝ) (v : Fin 3 → ℝ) : ℝ := ∑ k, v k ^ 2 + Δ

theorem spatialW_pos {Δ : ℝ} (hΔ : 0 < Δ) (v : Fin 3 → ℝ) : 0 < spatialW Δ v := by
  unfold spatialW
  have : 0 ≤ ∑ k, v k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  linarith

theorem wickKernel_cons (Δ ε t : ℝ) (v : Fin 3 → ℝ) :
    wickKernel Δ ε (Fin.cons t v) = (-(t : ℂ) ^ 2 + ((spatialW Δ v : ℂ) - ε * I)) ^ (-3 : ℤ) := by
  simp only [wickKernel, dot_cons_self, spatialW]
  push_cast
  ring_nf

theorem neg_mem_slitPlane {Δ ε : ℝ} (hε : 0 < ε) (v : Fin 3 → ℝ) :
    -((spatialW Δ v : ℂ) - ε * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  simp [hε.ne']

theorem neg_spatialW_sub (Δ ε : ℝ) (v : Fin 3 → ℝ) :
    -((spatialW Δ v : ℂ) - ε * I) = -(spatialW Δ v : ℂ) + ε * I := by ring

/-- The energy stage of M1 is integrable at every `ε > 0`. -/
theorem integrable_wickKernel_time {Δ ε : ℝ} (hε : 0 < ε) (v : Fin 3 → ℝ) :
    Integrable fun t : ℝ => wickKernel Δ ε (Fin.cons t v) := by
  simp_rw [wickKernel_cons]
  simpa using integrable_pow_mul_neg_sq_add_zpow_three (neg_mem_slitPlane (Δ := Δ) hε v)
    (k := 0) (by norm_num)

/-- The energy integral at fixed spatial momentum: `-(3π/8) (-W + iε)^{-5/2}`. -/
theorem integral_wickKernel_time {Δ ε : ℝ} (hε : 0 < ε) (v : Fin 3 → ℝ) :
    ∫ t : ℝ, wickKernel Δ ε (Fin.cons t v)
      = -((3 * π / 8 : ℂ) * (-(spatialW Δ v : ℂ) + ε * I) ^ (-(5 / 2 : ℂ))) := by
  simp_rw [wickKernel_cons]
  rw [integral_neg_sq_add_zpow_three (neg_mem_slitPlane hε v), neg_spatialW_sub]

/-- The spatial integrand of M1 after the energy integral. -/
noncomputable def spatialG (Δ ε : ℝ) (v : Fin 3 → ℝ) : ℂ :=
  -((3 * π / 8 : ℂ) * (-(spatialW Δ v : ℂ) + ε * I) ^ (-(5 / 2 : ℂ)))

theorem neg_five_halves : (-(5 / 2 : ℂ)) = ((-(5 / 2) : ℝ) : ℂ) := by push_cast; ring

/-- The uniform bound `‖spatialG‖ ≤ (3π/8) W^{-5/2}`, for every real `ε`. -/
theorem norm_spatialG_le {Δ : ℝ} (hΔ : 0 < Δ) (ε : ℝ) (v : Fin 3 → ℝ) :
    ‖spatialG Δ ε v‖ ≤ 3 * π / 8 * spatialW Δ v ^ (-(5 / 2 : ℝ)) := by
  have hW := spatialW_pos hΔ v
  have hnorm : spatialW Δ v ≤ ‖-(spatialW Δ v : ℂ) + ε * I‖ := by
    have h := Complex.abs_re_le_norm (-(spatialW Δ v : ℂ) + ε * I)
    simp only [add_re, neg_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
      sub_zero] at h
    rw [show -spatialW Δ v + 0 = -spatialW Δ v by ring, abs_neg, abs_of_pos hW] at h
    exact h
  have hpi : ‖(3 * π / 8 : ℂ)‖ = 3 * π / 8 := by
    rw [show (3 * π / 8 : ℂ) = ((3 * π / 8 : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [spatialG, norm_neg, norm_mul, hpi, neg_five_halves, norm_cpow_real]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hW hnorm (by norm_num))
    (by positivity)

theorem measurable_spatialW (Δ : ℝ) : Measurable (spatialW Δ) := by
  unfold spatialW; fun_prop

theorem aestronglyMeasurable_spatialG (Δ ε : ℝ) :
    AEStronglyMeasurable (spatialG Δ ε) volume := by
  have h : Measurable (spatialG Δ ε) := by
    unfold spatialG
    have hW := measurable_spatialW Δ
    fun_prop
  exact h.aestronglyMeasurable

theorem integrable_spatialW_rpow {Δ : ℝ} (hΔ : 0 < Δ) :
    Integrable fun v : Fin 3 → ℝ => 3 * π / 8 * spatialW Δ v ^ (-(5 / 2 : ℝ)) :=
  (integrable_sum_sq_add_rpow hΔ (by norm_num)).const_mul _

/-- The spatial stage of M1 is integrable at every `ε > 0`. -/
theorem integrable_wickKernel_space {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε) :
    Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ, wickKernel Δ ε (Fin.cons t v) := by
  simp_rw [integral_wickKernel_time hε]
  exact (integrable_spatialW_rpow hΔ).mono' (aestronglyMeasurable_spatialG Δ ε)
    (Eventually.of_forall fun v => norm_spatialG_le hΔ ε v)

theorem energyFirstIntegral_wickKernel {Δ ε : ℝ} (hε : 0 < ε) :
    QED.OneLoop.energyFirstIntegral (wickKernel Δ ε) = ∫ v, spatialG Δ ε v := by
  unfold QED.OneLoop.energyFirstIntegral
  simp_rw [integral_wickKernel_time hε]
  rfl

/-- `(-X)^{-5/2} = -i X^{-5/2}` for `X > 0` (principal branch). -/
theorem neg_cpow_neg_five_halves {X : ℝ} (hX : 0 < X) :
    (-(X : ℂ)) ^ (-(5 / 2 : ℂ)) = -I * ((X ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ) := by
  have h := ofReal_cpow_of_nonpos (x := -X) (by linarith) (-(5 / 2 : ℂ))
  rw [ofReal_neg, neg_neg] at h
  rw [h, ofReal_cpow hX.le, neg_five_halves]
  have he : cexp (π * I * ((-(5 / 2) : ℝ) : ℂ)) = -I := by
    have e1 : (π : ℂ) * I * ((-(5 / 2) : ℝ) : ℂ) = -(π / 2 * I) - 2 * (π * I) := by
      push_cast; ring
    rw [e1, Complex.exp_sub, Complex.exp_neg, exp_pi_div_two_mul_I,
      show 2 * ((π : ℂ) * I) = 2 * π * I by ring, Complex.exp_two_pi_mul_I]
    simp
  rw [he]
  ring

theorem tendsto_spatialG {Δ : ℝ} (hΔ : 0 < Δ) (v : Fin 3 → ℝ) :
    Tendsto (fun ε => spatialG Δ ε v) (𝓝[>] 0)
      (𝓝 ((3 * π / 8 : ℂ) * I * ((spatialW Δ v ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))) := by
  have h := ((tendsto_cpow_neg_add_mul_I (spatialW_pos hΔ v) (-(5 / 2 : ℂ))).const_mul
    (3 * π / 8 : ℂ)).neg
  rw [neg_cpow_neg_five_halves (spatialW_pos hΔ v)] at h
  rw [show (3 * π / 8 : ℂ) * I * ((spatialW Δ v ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)
    = -((3 * π / 8 : ℂ) * (-I * ((spatialW Δ v ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))) by ring]
  exact h

/-- `I_E(Δ; 3, 4) = Γ(1)/Γ(3) · Δ⁻¹ = 1/(2Δ)`. -/
theorem tadpole_three_four {Δ : ℝ} (hΔ : 0 < Δ) : tadpole Δ 3 4 = 1 / (2 * Δ) := by
  have hΔ' : (Δ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hΔ.ne'
  have g3 : Gamma (3 : ℂ) = 2 := by
    rw [show (3 : ℂ) = (2 : ℕ) + 1 by norm_num, Gamma_nat_eq_factorial]; norm_num
  rw [tadpole, show (3 : ℂ) - 4 / 2 = 1 by norm_num, show (4 : ℂ) / 2 - 3 = -1 by norm_num,
    Gamma_one, g3, cpow_neg_one]
  field_simp

/-- **The one-loop Wick rotation at `d = 4`, as a theorem.** For `Δ > 0` the energy-first
integral (prescription M1) of `(ℓ·ℓ + Δ - iε)⁻³` tends, as `ε → 0⁺`, to `i π²` times the
Euclidean tadpole `I_E(Δ; 3, 4)` of the dimensionally regularized side. -/
theorem tendsto_energyFirstIntegral_wickKernel {Δ : ℝ} (hΔ : 0 < Δ) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (wickKernel Δ ε)) (𝓝[>] 0)
      (𝓝 (I * (π : ℂ) ^ 2 * tadpole Δ 3 4)) := by
  have hlim : Tendsto (fun ε => ∫ v, spatialG Δ ε v) (𝓝[>] 0)
      (𝓝 (∫ v, (3 * π / 8 : ℂ) * I * ((spatialW Δ v ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun v => 3 * π / 8 * spatialW Δ v ^ (-(5 / 2 : ℝ))) ?_ ?_ (integrable_spatialW_rpow hΔ)
      (Eventually.of_forall fun v => tendsto_spatialG hΔ v)
    · exact Eventually.of_forall fun ε => aestronglyMeasurable_spatialG Δ ε
    · exact Eventually.of_forall fun ε => Eventually.of_forall fun v => norm_spatialG_le hΔ ε v
  have hval : ∫ v, (3 * π / 8 : ℂ) * I * ((spatialW Δ v ^ (-(5 / 2 : ℝ)) : ℝ) : ℂ)
      = I * (π : ℂ) ^ 2 * tadpole Δ 3 4 := by
    rw [integral_const_mul, integral_complex_ofReal]
    have h := integral_sum_sq_add_rpow_neg_five_halves hΔ
    simp only [spatialW]
    rw [h, tadpole_three_four hΔ]
    have hΔ' : (Δ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hΔ.ne'
    push_cast
    field_simp
    ring
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (energyFirstIntegral_wickKernel hε).symm

/-- The same limit, written as the dimensionally regularized family integral of
`QED.DimReg.tadpoleFamily` at `ν = 3`, `d = 4` (inside its strip of convergence). -/
theorem tendsto_energyFirstIntegral_wickKernel_family {Δ : ℝ} (hΔ : 0 < Δ) :
    Tendsto (fun ε => QED.OneLoop.energyFirstIntegral (wickKernel Δ ε)) (𝓝[>] 0)
      (𝓝 (I * (π : ℂ) ^ 2 * (tadpoleFamily Δ).integral (fun _ => (3 : ℂ)) 4)) := by
  rw [integral_tadpoleFamily hΔ (by norm_num) (by norm_num)]
  exact tendsto_energyFirstIntegral_wickKernel hΔ

end QED.DimReg.OneLoopBridge

end
