/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXXiPhi
public import QED.TwoLoop.UnitXXiRat
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The `ξ`-antiderivative of the crossed-ladder integrand

Step 4.5.2 of `docs/TWO-LOOP-UNITS.md`: for `Y, ξ ∈ (0, 1)` with `Y ≠ 1/2`, `ξ ≠ 1/2`,

`∂_ξ xiF(Y, ξ) = Y Φ_X(Y ξ, Y (1 - ξ))` (`hasDerivAt_xiF`).

The derivatives of the dilogarithm terms are logarithms of the letters divided by `ξ`, `1 - ξ` or
`1 - 2ξ` (`hasDerivAt_xi_Li₂_mul`, …); for instance
`∂_ξ Li((2Y - 1) ξ/Y) = -(log (ξ + Y - 2 Y ξ) - log Y)/ξ`. Grouping the derivative by the letters
`1, log Y, log ξ, log (1 - Y ξ), log (ξ + Y - 2 Y ξ)` gives five rational identities
(`xiF_deriv_one`, …), each checked by `field_simp` and `ring` after writing the coefficients as
single fractions (`QED.TwoLoop.UnitXXiRat`); the `log (1 - Y)` and `log 2` terms cancel. Eq. (4.5)
(`crossedPhi_yxi`) identifies the result with the integrand.

At `ξ = 1/2` the formula for `Φ_X` divides by `z₃ - z₂ = 0`; there `xiF` is still continuous
(`QED.TwoLoop.UnitXXi.continuousAt_xiF`, in `QED.TwoLoop.UnitXXiLimits`).
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.TwoLoop.UnitXXi

open QED.TwoLoop.UnitXClose

/-! ### The derivatives of the dilogarithm terms -/

theorem hasDerivAt_Li₂_comp {f : ℝ → ℝ} {f' ξ : ℝ} (hf : HasDerivAt f f' ξ) (h1 : |f ξ| < 1)
    (h0 : f ξ ≠ 0) : HasDerivAt (fun y => Li₂ (f y)) (-log (1 - f ξ) / f ξ * f') ξ :=
  (hasDerivAt_Li₂ h1 h0).comp ξ hf

theorem hasDerivAt_dilogI_comp {f : ℝ → ℝ} {f' ξ : ℝ} (hf : HasDerivAt f f' ξ) (h1 : f ξ < 1)
    (h0 : f ξ ≠ 0) : HasDerivAt (fun y => dilogI (f y)) (-log (1 - f ξ) / f ξ * f') ξ :=
  (hasDerivAt_dilogI_of_ne h1 h0).comp ξ hf

section Atoms

variable {Y ξ : ℝ}

theorem hasDerivAt_xi_log_A (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ξ => log (1 - Y * ξ)) (-Y / (1 - Y * ξ)) ξ := by
  have hA : 0 < 1 - Y * ξ := by nlinarith [hY.1, hY.2, hξ.1, hξ.2]
  have h := (((hasDerivAt_id' ξ).const_mul Y).const_sub 1).log hA.ne'
  convert h using 1
  ring

theorem hasDerivAt_xi_log_B (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ξ => log (ξ + Y - 2 * Y * ξ)) ((1 - 2 * Y) / (ξ + Y - 2 * Y * ξ)) ξ := by
  have hB : 0 < ξ + Y - 2 * Y * ξ := by nlinarith [hY.1, hY.2, hξ.1, hξ.2]
  have h := ((((hasDerivAt_id' ξ).add_const Y).sub ((hasDerivAt_id' ξ).const_mul (2 * Y))).log
    hB.ne')
  convert h using 1
  simp only [Pi.sub_apply]
  ring

theorem hasDerivAt_xi_Li₂_mul (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ξ => Li₂ (Y * ξ)) (-log (1 - Y * ξ) / ξ) ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have h := hasDerivAt_Li₂_comp ((hasDerivAt_id' ξ).const_mul Y)
    (abs_lt.mpr ⟨by nlinarith, by nlinarith⟩) (by positivity)
  convert h using 1
  field_simp

theorem hasDerivAt_xi_Li₂_one_sub (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ξ => Li₂ (1 - ξ)) (log ξ / (1 - ξ)) ξ := by
  obtain ⟨hξ0, hξ1⟩ := hξ
  have h := hasDerivAt_Li₂_comp ((hasDerivAt_id' ξ).const_sub 1)
    (abs_lt.mpr ⟨by linarith, by linarith⟩) (by linarith)
  have hξ1' : 1 - ξ ≠ 0 := by linarith
  convert h using 1
  rw [sub_sub_cancel]
  field_simp

theorem hasDerivAt_xi_dilogI_A (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun ξ => dilogI (-(Y * (1 - ξ) / (1 - Y))))
      ((log (1 - Y * ξ) - log (1 - Y)) / (1 - ξ)) ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY1' : 0 < 1 - Y := by linarith
  have hξ1' : 0 < 1 - ξ := by linarith
  have hA : 0 < 1 - Y * ξ := by nlinarith
  have hf : HasDerivAt (fun ξ => -(Y * (1 - ξ) / (1 - Y))) (Y / (1 - Y)) ξ := by
    have := ((((hasDerivAt_id' ξ).const_sub 1).const_mul Y).div_const (1 - Y)).neg
    convert this using 1
    field_simp
  have hpos : 0 < Y * (1 - ξ) / (1 - Y) := by positivity
  have h := hasDerivAt_dilogI_comp hf (by linarith) (by linarith)
  have e : 1 - -(Y * (1 - ξ) / (1 - Y)) = (1 - Y * ξ) / (1 - Y) := by field_simp; ring
  convert h using 1
  rw [e, log_div hA.ne' hY1'.ne']
  field_simp

theorem hasDerivAt_xi_dilogI_B (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hY2 : Y ≠ 1 / 2) :
    HasDerivAt (fun ξ => dilogI ((1 - 2 * Y) * (1 - ξ) / (1 - Y)))
      ((log (ξ + Y - 2 * Y * ξ) - log (1 - Y)) / (1 - ξ)) ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY1' : 0 < 1 - Y := by linarith
  have hξ1' : 0 < 1 - ξ := by linarith
  have hY2' : 1 - 2 * Y ≠ 0 := fun h => hY2 (by linarith)
  have hY2'' : 1 - Y * 2 ≠ 0 := fun h => hY2 (by linarith)
  have hB : 0 < ξ + Y - 2 * Y * ξ := by nlinarith
  have hf : HasDerivAt (fun ξ => (1 - 2 * Y) * (1 - ξ) / (1 - Y)) (-((1 - 2 * Y) / (1 - Y))) ξ := by
    have := (((hasDerivAt_id' ξ).const_sub 1).const_mul (1 - 2 * Y)).div_const (1 - Y)
    convert this using 1
    field_simp
  have e : 1 - (1 - 2 * Y) * (1 - ξ) / (1 - Y) = (ξ + Y - 2 * Y * ξ) / (1 - Y) := by
    field_simp; ring
  have hlt : (1 - 2 * Y) * (1 - ξ) / (1 - Y) < 1 := by
    rw [← sub_pos, e]; positivity
  have h := hasDerivAt_dilogI_comp hf hlt (by positivity)
  convert h using 1
  rw [e, log_div hB.ne' hY1'.ne']
  field_simp

theorem hasDerivAt_xi_dilogI_D (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hY2 : Y ≠ 1 / 2) :
    HasDerivAt (fun ξ => dilogI ((2 * Y - 1) * ξ / Y))
      (-(log (ξ + Y - 2 * Y * ξ) - log Y) / ξ) ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY2' : 2 * Y - 1 ≠ 0 := fun h => hY2 (by linarith)
  have hY2'' : Y * 2 - 1 ≠ 0 := fun h => hY2 (by linarith)
  have hB : 0 < ξ + Y - 2 * Y * ξ := by nlinarith
  have hf : HasDerivAt (fun ξ => (2 * Y - 1) * ξ / Y) ((2 * Y - 1) / Y) ξ := by
    have := ((hasDerivAt_id' ξ).const_mul (2 * Y - 1)).div_const Y
    convert this using 1
    ring
  have e : 1 - (2 * Y - 1) * ξ / Y = (ξ + Y - 2 * Y * ξ) / Y := by field_simp; ring
  have hlt : (2 * Y - 1) * ξ / Y < 1 := by
    rw [← sub_pos, e]; positivity
  have h := hasDerivAt_dilogI_comp hf hlt (by positivity)
  convert h using 1
  rw [e, log_div hB.ne' hY0.ne']
  field_simp

theorem hasDerivAt_xi_Li₂_one_sub_two (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hh : ξ ≠ 1 / 2) :
    HasDerivAt (fun ξ => Li₂ (1 - 2 * ξ)) (2 * (log 2 + log ξ) / (1 - 2 * ξ)) ξ := by
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hξ2 : 1 - 2 * ξ ≠ 0 := fun h => hh (by linarith)
  have h := hasDerivAt_Li₂_comp (((hasDerivAt_id' ξ).const_mul 2).const_sub 1)
    (abs_lt.mpr ⟨by linarith, by linarith⟩) hξ2
  convert h using 1
  rw [show 1 - (1 - 2 * ξ) = 2 * ξ by ring, log_mul two_ne_zero hξ0.ne']
  field_simp

theorem hasDerivAt_xi_Li₂_kappa (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hY2 : Y ≠ 1 / 2) (hh : ξ ≠ 1 / 2) :
    HasDerivAt (fun ξ => Li₂ ((1 - 2 * Y) * (1 - 2 * ξ)))
      (2 * (log 2 + log (ξ + Y - 2 * Y * ξ)) / (1 - 2 * ξ)) ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hξ2 : 1 - 2 * ξ ≠ 0 := fun h => hh (by linarith)
  have hY2' : 1 - 2 * Y ≠ 0 := fun h => hY2 (by linarith)
  have hB : 0 < ξ + Y - 2 * Y * ξ := by nlinarith
  have habs : |(1 - 2 * Y) * (1 - 2 * ξ)| < 1 := by
    rw [abs_mul]
    have h1 : |1 - 2 * Y| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have h2 : |1 - 2 * ξ| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    calc |1 - 2 * Y| * |1 - 2 * ξ| ≤ |1 - 2 * Y| * 1 :=
          mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)
      _ < 1 := by linarith
  have h := hasDerivAt_Li₂_comp ((((hasDerivAt_id' ξ).const_mul 2).const_sub 1).const_mul
    (1 - 2 * Y)) habs (mul_ne_zero hY2' hξ2)
  convert h using 1
  rw [show 1 - (1 - 2 * Y) * (1 - 2 * ξ) = 2 * (ξ + Y - 2 * Y * ξ) by ring,
    log_mul two_ne_zero hB.ne']
  field_simp

end Atoms

/-! ### The derivative, grouped by letters -/

section Identities

variable {Y ξ : ℝ}

theorem xiF_deriv_one (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    xiR0D Y ξ + xiPx Y ξ / ξ + xiPA Y ξ * (-Y / (1 - Y * ξ)) +
      xiPB Y ξ * ((1 - 2 * Y) / (ξ + Y - 2 * Y * ξ)) = xiΦ1 Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hA : 1 - Y * ξ ≠ 0 := by nlinarith
  have hB : ξ + Y - 2 * Y * ξ ≠ 0 := by nlinarith
  have hY1' : Y - 1 ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hY2' : 2 * Y - 1 ≠ 0 := fun h => hY2 (by linarith)
  have hY2'' : Y * 2 - 1 ≠ 0 := fun h => hY2 (by linarith)
  rw [xiR0D_eq hY0.ne' hY1' hξ0.ne' hξ1', xiPx_eq hY0.ne' hξ1',
    xiPA_eq hY0.ne' hY1' hξ0.ne' hξ1', xiPB_eq hY0.ne' hY1' hY2' hξ0.ne' hξ1']
  unfold xiΦ1
  field_simp
  ring

theorem xiF_deriv_x (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hh : ξ ≠ 1 / 2) :
    xiPxD Y ξ + xiCq Y / (1 - ξ) + 1 / (1 - 2 * ξ) / Y ^ 2 = xiΦx Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hξ1'' : 1 - ξ ≠ 0 := by linarith
  have hξ2 : 2 * ξ - 1 ≠ 0 := fun h => hh (by linarith)
  have hξ2' : 1 - 2 * ξ ≠ 0 := fun h => hh (by linarith)
  have hξ2'' : ξ * 2 - 1 ≠ 0 := fun h => hh (by linarith)
  have hξ2''' : 1 - ξ * 2 ≠ 0 := fun h => hh (by linarith)
  rw [xiPxD_eq hY0.ne' hξ1']
  unfold xiCq xiΦx
  field_simp
  ring

theorem xiF_deriv_A (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    xiPAD Y ξ - xiCL Y / ξ + xiCq Y / (1 - ξ) = xiΦA Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY1' : Y - 1 ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hξ1'' : 1 - ξ ≠ 0 := by linarith
  rw [xiPAD_eq hY0.ne' hY1' hξ0.ne' hξ1']
  unfold xiCL xiCq xiΦA
  field_simp
  ring

theorem xiF_deriv_B (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hh : ξ ≠ 1 / 2) :
    xiPBD Y ξ - xiCq Y / (1 - ξ) - 1 / (1 - 2 * ξ) / Y ^ 2 - xiCD Y / ξ = xiΦB Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY1' : Y - 1 ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hξ1'' : 1 - ξ ≠ 0 := by linarith
  have hξ2 : 2 * ξ - 1 ≠ 0 := fun h => hh (by linarith)
  have hξ2' : 1 - 2 * ξ ≠ 0 := fun h => hh (by linarith)
  have hξ2'' : ξ * 2 - 1 ≠ 0 := fun h => hh (by linarith)
  have hξ2''' : 1 - ξ * 2 ≠ 0 := fun h => hh (by linarith)
  rw [xiPBD_eq hY0.ne' hY1' hξ0.ne' hξ1']
  unfold xiCq xiCD xiΦB
  field_simp
  ring

theorem xiF_deriv_Y (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    xiPYD Y ξ + xiCD Y / ξ = xiΦY Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY1' : Y - 1 ≠ 0 := by linarith
  rw [xiPYD_eq hY1' hξ0.ne']
  unfold xiCD xiΦY
  field_simp
  ring

end Identities

/-- **The `ξ`-antiderivative**: `∂_ξ xiF(Y, ξ) = Y Φ_X(Y ξ, Y (1 - ξ))` for `Y, ξ ∈ (0, 1)`,
`Y ≠ 1/2`, `ξ ≠ 1/2`. -/
theorem hasDerivAt_xiF {Y ξ : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2)
    (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hh : ξ ≠ 1 / 2) :
    HasDerivAt (xiF Y) (Y * crossedPhi (Y * ξ) (Y * (1 - ξ))) ξ := by
  have h0 : ξ ≠ 0 := hξ.1.ne'
  have h1 : ξ - 1 ≠ 0 := by linarith [hξ.2]
  have hlx := hasDerivAt_log h0
  have h := ((((((((hasDerivAt_xiR0 Y h0 h1).add ((hasDerivAt_xiPx Y h0 h1).mul hlx)).add
    ((hasDerivAt_xiPA Y h0 h1).mul (hasDerivAt_xi_log_A hY hξ))).add
    ((hasDerivAt_xiPB Y h0 h1).mul (hasDerivAt_xi_log_B hY hξ))).add
    ((hasDerivAt_xiPY Y h0 h1).mul_const (log Y))).add
    ((hasDerivAt_xi_Li₂_mul hY hξ).const_mul (xiCL Y))).add
    ((((hasDerivAt_xi_Li₂_one_sub hξ).add (hasDerivAt_xi_dilogI_A hY hξ)).sub
      (hasDerivAt_xi_dilogI_B hY hξ hY2)).const_mul (xiCq Y))).add
    (((hasDerivAt_xi_Li₂_one_sub_two hξ hh).sub (hasDerivAt_xi_Li₂_kappa hY hξ hY2 hh)).div_const
      (2 * Y ^ 2))).add ((hasDerivAt_xi_dilogI_D hY hξ hY2).const_mul (xiCD Y))
  rw [crossedPhi_yxi hY hξ hh]
  refine h.congr_deriv ?_
  have i1 := xiF_deriv_one hY hY2 hξ
  have ix := xiF_deriv_x hY hξ hh
  have iA := xiF_deriv_A hY hξ
  have iB := xiF_deriv_B hY hξ hh
  have iY := xiF_deriv_Y hY hξ
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hξ1 : 1 - ξ ≠ 0 := by linarith [hξ.2]
  have hξ2 : 1 - 2 * ξ ≠ 0 := fun h => hh (by linarith)
  have e1 : xiPx Y ξ * ξ⁻¹ = xiPx Y ξ / ξ := (div_eq_mul_inv _ _).symm
  rw [e1]
  linear_combination i1 + log ξ * ix + log (1 - Y * ξ) * iA + log (ξ + Y - 2 * Y * ξ) * iB +
    log Y * iY

end QED.TwoLoop.UnitXXi

end
