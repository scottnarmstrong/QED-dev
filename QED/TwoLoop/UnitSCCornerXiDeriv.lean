/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerXiRat
public import QED.TwoLoop.UnitXXiDeriv
public import QED.TwoLoop.UnitSCCornerXInt
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The `ξ`-antiderivative of the corner integrand

Step 6.6.2 of `docs/TWO-LOOP-UNITS.md`: for `Y, ξ ∈ (0, 1)` with `Y ≠ 1/2`, `ξ ≠ 1/2`,
`∂_ξ cxiF(Y, ξ) = Y Φ_C(Y, ξ)` (`hasDerivAt_cxiF`), with `Φ_C = QED.TwoLoop.UnitSCCorner.cornerPhi`
in the letters (`mul_cornerPhi`). The derivatives of the dilogarithm terms are those of
`QED.TwoLoop.UnitXXi` (`hasDerivAt_xi_Li₂_mul`, …); grouping by the letters gives five rational
identities (`cxiF_deriv_one`, …), each checked by `field_simp` and `ring`.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.TwoLoop.UnitSCCornerXi

open QED.TwoLoop.UnitXClose QED.TwoLoop.UnitXXi QED.TwoLoop.UnitSCCorner

/-! ### The integrand in the letters -/

theorem mul_cornerPhi {Y ξ : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hh : ξ ≠ 1 / 2) :
    Y * cornerPhi Y ξ = cxiΦ1 Y ξ + cxiΦY Y ξ * log Y + cxiΦx Y ξ * log ξ +
      cxiΦA Y ξ * log (1 - Y * ξ) + cxiΦB Y ξ * log (ξ + Y - 2 * Y * ξ) := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY0' : Y ≠ 0 := hY0.ne'
  have hξ0' : ξ ≠ 0 := hξ0.ne'
  have hY1' : Y - 1 ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hξ2 : 2 * ξ - 1 ≠ 0 := fun h => hh (by linarith)
  have hξ2' : ξ * 2 - 1 ≠ 0 := fun h => hh (by linarith)
  have := hY0.ne'
  have := hξ0.ne'
  have e1 : Y * cφ1 Y ξ = cxiΦ1 Y ξ := by unfold cφ1 cxiΦ1; field_simp
  have e2 : Y * cφY Y ξ = cxiΦY Y ξ := by unfold cφY cxiΦY; field_simp
  have e3 : Y * cφx Y ξ = cxiΦx Y ξ := by unfold cφx cxiΦx; field_simp
  have e4 : Y * cφA Y ξ = cxiΦA Y ξ := by unfold cφA cxiΦA; field_simp
  have e5 : Y * cφB Y ξ = cxiΦB Y ξ := by unfold cφB cxiΦB; field_simp
  unfold cornerPhi
  linear_combination e1 + log Y * e2 + log ξ * e3 + log (1 - Y * ξ) * e4 +
    log (ξ + Y - 2 * Y * ξ) * e5

/-! ### The derivative, grouped by letters -/

section Identities

variable {Y ξ : ℝ}

theorem cxiF_deriv_one (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    cxiR0D Y ξ + cxiPx Y ξ / ξ + cxiPA Y ξ * (-Y / (1 - Y * ξ)) +
      cxiPB Y ξ * ((1 - 2 * Y) / (ξ + Y - 2 * Y * ξ)) = cxiΦ1 Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY0' : Y ≠ 0 := hY0.ne'
  have hξ0' : ξ ≠ 0 := hξ0.ne'
  have hA : 1 - Y * ξ ≠ 0 := by nlinarith
  have hB : ξ + Y - 2 * Y * ξ ≠ 0 := by nlinarith
  have hB' : ξ + Y - Y * ξ * 2 ≠ 0 := fun h => hB (by linarith)
  have hY1' : Y - 1 ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hY2' : 2 * Y - 1 ≠ 0 := fun h => hY2 (by linarith)
  have hY2'' : Y * 2 - 1 ≠ 0 := fun h => hY2 (by linarith)
  rw [cxiR0D_eq, cxiPx_eq,
    cxiPA_eq, cxiPB_eq]
  unfold cxiΦ1
  field_simp
  ring

theorem cxiF_deriv_x (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hh : ξ ≠ 1 / 2) :
    cxiPxD Y ξ + cxiCq Y / (1 - ξ) - 1 / (1 - 2 * ξ) / Y ^ 2 = cxiΦx Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY0' : Y ≠ 0 := hY0.ne'
  have hξ0' : ξ ≠ 0 := hξ0.ne'
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hξ1'' : 1 - ξ ≠ 0 := by linarith
  have hξ2 : 2 * ξ - 1 ≠ 0 := fun h => hh (by linarith)
  have hξ2' : 1 - 2 * ξ ≠ 0 := fun h => hh (by linarith)
  have hξ2'' : ξ * 2 - 1 ≠ 0 := fun h => hh (by linarith)
  have hξ2''' : 1 - ξ * 2 ≠ 0 := fun h => hh (by linarith)
  rw [cxiPxD_eq]
  unfold cxiCq cxiΦx
  field_simp
  ring

theorem cxiF_deriv_A (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    cxiPAD Y ξ - cxiCL Y / ξ + cxiCq Y / (1 - ξ) = cxiΦA Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY0' : Y ≠ 0 := hY0.ne'
  have hξ0' : ξ ≠ 0 := hξ0.ne'
  have hY1' : Y - 1 ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hξ1'' : 1 - ξ ≠ 0 := by linarith
  rw [cxiPAD_eq]
  unfold cxiCL cxiCq cxiΦA
  field_simp
  ring

theorem cxiF_deriv_B (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hh : ξ ≠ 1 / 2) :
    cxiPBD Y ξ - cxiCq Y / (1 - ξ) + 1 / (1 - 2 * ξ) / Y ^ 2 - cxiCD Y / ξ = cxiΦB Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY0' : Y ≠ 0 := hY0.ne'
  have hξ0' : ξ ≠ 0 := hξ0.ne'
  have hY1' : Y - 1 ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hξ1'' : 1 - ξ ≠ 0 := by linarith
  have hξ2 : 2 * ξ - 1 ≠ 0 := fun h => hh (by linarith)
  have hξ2' : 1 - 2 * ξ ≠ 0 := fun h => hh (by linarith)
  have hξ2'' : ξ * 2 - 1 ≠ 0 := fun h => hh (by linarith)
  have hξ2''' : 1 - ξ * 2 ≠ 0 := fun h => hh (by linarith)
  rw [cxiPBD_eq]
  unfold cxiCq cxiCD cxiΦB
  field_simp
  ring

theorem cxiF_deriv_Y (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    cxiPYD Y ξ + cxiCD Y / ξ = cxiΦY Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY0' : Y ≠ 0 := hY0.ne'
  have hξ0' : ξ ≠ 0 := hξ0.ne'
  have hY1' : Y - 1 ≠ 0 := by linarith
  rw [cxiPYD_eq]
  unfold cxiCD cxiΦY
  field_simp
  ring

end Identities

/-- **The `ξ`-antiderivative**: `∂_ξ cxiF(Y, ξ) = Y Φ_C(Y, ξ)` for `Y, ξ ∈ (0, 1)`,
`Y ≠ 1/2`, `ξ ≠ 1/2`. -/
theorem hasDerivAt_cxiF {Y ξ : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2)
    (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hh : ξ ≠ 1 / 2) :
    HasDerivAt (cxiF Y) (Y * cornerPhi Y ξ) ξ := by
  have h0 : ξ ≠ 0 := hξ.1.ne'
  have h1 : ξ - 1 ≠ 0 := by linarith [hξ.2]
  have hlx := hasDerivAt_log h0
  have h := ((((((((hasDerivAt_cxiR0 Y h0 h1).add ((hasDerivAt_cxiPx Y h0 h1).mul hlx)).add
    ((hasDerivAt_cxiPA Y h0 h1).mul (hasDerivAt_xi_log_A hY hξ))).add
    ((hasDerivAt_cxiPB Y h0 h1).mul (hasDerivAt_xi_log_B hY hξ))).add
    ((hasDerivAt_cxiPY Y h0 h1).mul_const (log Y))).add
    ((hasDerivAt_xi_Li₂_mul hY hξ).const_mul (cxiCL Y))).add
    ((((hasDerivAt_xi_Li₂_one_sub hξ).add (hasDerivAt_xi_dilogI_A hY hξ)).sub
      (hasDerivAt_xi_dilogI_B hY hξ hY2)).const_mul (cxiCq Y))).add
    (((hasDerivAt_xi_Li₂_kappa hY hξ hY2 hh).sub (hasDerivAt_xi_Li₂_one_sub_two hξ hh)).div_const
      (2 * Y ^ 2))).add ((hasDerivAt_xi_dilogI_D hY hξ hY2).const_mul (cxiCD Y))
  rw [mul_cornerPhi hY hξ hh]
  refine h.congr_deriv ?_
  have i1 := cxiF_deriv_one hY hY2 hξ
  have ix := cxiF_deriv_x hY hξ hh
  have iA := cxiF_deriv_A hY hξ
  have iB := cxiF_deriv_B hY hξ hh
  have iY := cxiF_deriv_Y hY hξ
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hξ1 : 1 - ξ ≠ 0 := by linarith [hξ.2]
  have hξ2 : 1 - 2 * ξ ≠ 0 := fun h => hh (by linarith)
  have e1 : cxiPx Y ξ * ξ⁻¹ = cxiPx Y ξ / ξ := (div_eq_mul_inv _ _).symm
  rw [e1]
  linear_combination i1 + log ξ * ix + log (1 - Y * ξ) * iA + log (ξ + Y - 2 * Y * ξ) * iB +
    log Y * iY

end QED.TwoLoop.UnitSCCornerXi

end
