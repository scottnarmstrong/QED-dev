/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKVOne

/-!
# Set (a), stage D4: the mass-class constant at unit mass, and `KsCoreOne` normalized

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient). The constant of the
mass class at unit mass is elementary:
`c_m(1) = ∫₀¹ (1 + x) log((1 - x)/x²) dx = -7/4 + 5/2 = 3/4`, by the fundamental theorem of
calculus with an antiderivative built from `x log x` and `(1 - x) log(1 - x)` (both continuous
on `[0, 1]`). With `ksUKe 1 = 1/(256π⁴)`, `KsCoreOne` is then the identity
`2ΔF(t) + ΔF_B(t) = 16 Π̂⁽⁴⁾(t) + 6 D(t)` for `t > -4`, with no `π` left.

Main results:

* **`ksW_ksUcm_one`**: `ksUcm 1 = 3/4`;
* **`ksW_ksCoreOne_iff`**: `KsCoreOne` is equivalent to the normalized identity.
-/

@[expose] public section

open Real MeasureTheory Set

namespace QED.ChainProof.SetAKS

open QED.Chain QED.GradedProof.RPi4

/-- An antiderivative of `(1 + x)(log(1 - x) - 2 log x)` on `(0, 1)`, continuous on `[0, 1]`. -/
noncomputable def ksWCmG (x : ℝ) : ℝ :=
  -(2 - (1 - x) / 2) * ((1 - x) * log (1 - x)) + 2 * (1 - x) - (1 - x) ^ 2 / 4 -
    2 * ((1 + x / 2) * (x * log x) - x - x ^ 2 / 4)

theorem ksW_continuous_ksWCmG : Continuous ksWCmG := by
  have h1 : Continuous fun x : ℝ => (1 - x) * log (1 - x) :=
    continuous_mul_log.comp (by fun_prop)
  have h2 : Continuous fun x : ℝ => x * log x := continuous_mul_log
  unfold ksWCmG
  fun_prop

theorem ksW_hasDerivAt_ksWCmG {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt ksWCmG ((1 + x) * log (ksUam 1 x)) x := by
  obtain ⟨h0, h1⟩ := hx
  have hu : (1 - x) ≠ 0 := by linarith
  have hA : HasDerivAt (fun x : ℝ => (1 - x) * log (1 - x)) (-log (1 - x) - 1) x := by
    have := (((hasDerivAt_id x).const_sub 1).log hu)
    have h2 := ((hasDerivAt_id x).const_sub 1).mul this
    refine h2.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hB : HasDerivAt (fun x : ℝ => x * log x) (log x + 1) x := hasDerivAt_mul_log h0.ne'
  have hI := hasDerivAt_id x
  have hP : HasDerivAt (fun x : ℝ => -(3 / 2) - x / 2) (-(1 / 2)) x := by
    simpa using (hI.div_const 2).const_sub (-(3 / 2))
  have hQ : HasDerivAt (fun x : ℝ => 2 * (1 - x) - (1 - x) ^ 2 / 4) (-2 + (1 - x) / 2) x := by
    have := ((hI.const_sub 1).const_mul 2).sub (((hI.const_sub 1).pow 2).div_const 4)
    refine this.congr_deriv ?_
    simp only [id]
    ring
  have hR : HasDerivAt (fun x : ℝ => 1 + x / 2) (1 / 2) x := by
    simpa using (hI.div_const 2).const_add 1
  have hS : HasDerivAt (fun x : ℝ => x + x ^ 2 / 4) (1 + x / 2) x := by
    have := hI.add ((hI.pow 2).div_const 4)
    refine this.congr_deriv ?_
    simp only [id]
    ring
  have h : HasDerivAt ksWCmG
      (-(1 / 2) * ((1 - x) * log (1 - x)) + (-(3 / 2) - x / 2) * (-log (1 - x) - 1) +
        (-2 + (1 - x) / 2) - 2 * ((1 / 2 * (x * log x) + (1 + x / 2) * (log x + 1)) -
          (1 + x / 2))) x := by
    have := ((hP.mul hA).add hQ).sub (((hR.mul hB).sub hS).const_mul 2)
    convert this using 1
    · funext y
      simp only [ksWCmG, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring
  refine h.congr_deriv ?_
  have ha : ksUam 1 x = (1 - x) / x ^ 2 := by simp [ksUam]
  rw [ha, log_div hu (by positivity), log_pow]
  push_cast
  ring

/-- **The mass-class constant at unit mass**: `c_m(1) = 3/4`. -/
theorem ksW_ksUcm_one : ksUcm 1 = 3 / 4 := by
  have hint : IntervalIntegrable (fun x => (1 + x) * log (ksUam 1 x)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact ksV_integrableOn_ksUcm_one
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    ksW_continuous_ksWCmG.continuousOn (fun x hx => ksW_hasDerivAt_ksWCmG hx) hint
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hF
  rw [ksUcm, hF]
  simp [ksWCmG]
  norm_num

/-- **`KsCoreOne`, normalized**: `2ΔF(t) + ΔF_B(t) = 16 Π̂⁽⁴⁾(t) + 6 D(t)` for `t > -4`. -/
theorem ksW_ksCoreOne_iff : KsCoreOne ↔ ∀ t : ℝ, -4 < t →
    2 * (ksUF 1 t - ksUF 1 0) + (ksUFB 1 t - ksUFB 1 0) = 16 * piHat4 t + 6 * ksDm t := by
  have hπ : π ^ 4 ≠ 0 := pow_ne_zero 4 Real.pi_ne_zero
  refine forall₂_congr fun t _ => ?_
  rw [ksW_ksUKe_one, ksW_ksUcm_one]
  constructor <;> intro h
  · field_simp at h
    linear_combination h / 2048
  · field_simp
    linear_combination 2048 * h

end QED.ChainProof.SetAKS

end
