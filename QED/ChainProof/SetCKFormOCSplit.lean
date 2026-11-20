/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOCFub
public import QED.ChainProof.SetCKFormOCYInt

/-!
# Set (c), Stage K, closed forms: the outer-massive corner kernel split into `K + κ + P`

Helper level (no frozen statement). Step 2 of the `ρ_oC` route (Stage K notes, Session 28+).
For `Y > 0`, `a < 1` and `x < X` the kernel `formOCKer X (Y, (a, x))` is
`Y (K + κ + P)` at `y₃ = a Y`, `v = Q(X) - Q(x)` (**`formOC_ker_eq`**), with
`K = scOutCK`, `κ = scOutCkap` and `P = -c₀ ρ log m`. The `P` part integrates in `Y` in closed
form (**`formOC_integral_P`**): with `m = Y² D₀`,

`∫₀¹ Y (-(x²/2) log (Y² D₀)) dY = (x²/4)(1 - log D₀)`.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

section

variable {X Y a x : ℝ}

/-- **The kernel split** `Y T = Y K + Y κ + Y P` at `y₃ = a Y`. -/
theorem formOC_ker_eq (hY : 0 < Y) (ha : a < 1) (hxX : x < X) :
    formOCKer X (Y, a, x) =
      Y * scOutCK (cornerC0 x) (cornerC1 x (a * Y) (Y - a * Y)) (cornerC2 x (a * Y) (Y - a * Y))
          (cornerC3 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x) (a * Y * (Y - a * Y))
          (scOutRho x) (scOutCs Y (a * Y) x) (scOutVX x X) +
        Y * scOutCkap (cornerA0 x (a * Y) (Y - a * Y)) (cornerA1 x (a * Y) (Y - a * Y))
          (cornerA2 x (a * Y) (Y - a * Y)) (scOutCm Y (a * Y) x) (a * Y * (Y - a * Y))
          (scOutRho x) (scOutCs Y (a * Y) x) (scOutVX x X) +
        Y * -(cornerC0 x * scOutRho x * log (scOutCm Y (a * Y) x)) := by
  have h : a * Y < Y ∧ x < X := ⟨by nlinarith, hxX⟩
  simp only [formOCKer, scOutCKer, h, and_self, ↓reduceIte, scOutCT, scOutCTg]
  ring

/-- **The `P` part in closed form**: `∫₀¹ Y P dY = (x²/4)(1 - log D₀)`. -/
theorem formOC_integral_P (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (fun Y => Y * -(cornerC0 x * scOutRho x * log (scOutCm Y (a * Y) x)))
        (Ioo 0 1) ∧
      ∫ Y in Ioo (0 : ℝ) 1, Y * -(cornerC0 x * scOutRho x * log (scOutCm Y (a * Y) x)) =
        x ^ 2 / 4 * (1 - log (formOCD0 a x)) := by
  have hD0 := formOCD0_pos ha hx
  have h1x : 1 - x ≠ 0 := by linarith [hx.2]
  have hc : cornerC0 x * scOutRho x = x ^ 2 / 2 := by
    unfold cornerC0 scOutRho
    field_simp
  set f' : ℝ → ℝ := fun Y => -(x ^ 2 / 2) * (2 * (Y * log Y) + Y * log (formOCD0 a x))
    with hf'
  have he : EqOn (fun Y => Y * -(cornerC0 x * scOutRho x * log (scOutCm Y (a * Y) x))) f'
      (Ioo 0 1) := fun Y hY => by
    simp only [hf', formOC_m_eq, hc]
    rw [log_mul (pow_ne_zero 2 hY.1.ne') hD0.ne', log_pow]
    push_cast
    ring
  have hcf : Continuous f' :=
    continuous_const.mul ((continuous_const.mul continuous_mul_log).add
      (continuous_id.mul continuous_const))
  set F : ℝ → ℝ := fun Y => -(x ^ 2 / 2) *
    (Y * (Y * log Y) - Y ^ 2 / 2 + Y ^ 2 * log (formOCD0 a x) / 2) with hF
  have hcF : Continuous F := continuous_const.mul
    (((continuous_id.mul continuous_mul_log).sub ((continuous_id.pow 2).div_const 2)).add
      (((continuous_id.pow 2).mul continuous_const).div_const 2))
  have hd : ∀ Y ∈ Ioo (0 : ℝ) 1, HasDerivAt F (f' Y) Y := fun Y hY => by
    have hl := hasDerivAt_log hY.1.ne'
    have h1 : HasDerivAt (fun Y : ℝ => Y * (Y * log Y)) (1 * (Y * log Y) +
        Y * (1 * log Y + Y * Y⁻¹)) Y :=
      (hasDerivAt_id Y).mul ((hasDerivAt_id Y).mul hl)
    have h2 := (hasDerivAt_pow 2 Y).div_const 2
    have h3 := ((hasDerivAt_pow 2 Y).mul_const (log (formOCD0 a x))).div_const 2
    refine (((h1.sub h2).add h3).const_mul (-(x ^ 2 / 2))).congr_deriv ?_
    simp only [hf']
    field_simp [hY.1.ne']
    ring
  have hint : IntervalIntegrable f' volume 0 1 := hcf.intervalIntegrable 0 1
  refine ⟨(hcf.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun he.symm
    measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo he, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcF.continuousOn hd hint]
  simp only [hF, log_one, log_zero]
  ring

end

end QED.ChainProof.SetCK

end
