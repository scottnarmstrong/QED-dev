/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXXiDefs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The crossed-ladder integrand in the letters of `(Y, ξ)`

Eq. (4.5) of `docs/TWO-LOOP-UNITS.md`: for `Y, ξ ∈ (0, 1)`, `ξ ≠ 1/2`,

`Y Φ_X(Y ξ, Y (1 - ξ)) = R₁ + R_Y log Y + R_ξ log ξ + R_A log (1 - Y ξ) + R_B log (ξ + Y - 2 Y ξ)`

(`crossedPhi_yxi`), with `R₁ = xiΦ1`, `R_Y = xiΦY`, `R_ξ = xiΦx`, `R_A = xiΦA`, `R_B = xiΦB`.

With `z₂ = Y ξ`, `z₃ = Y (1 - ξ)` and `g = z₂ (1 - Y)`, the arguments of the logarithms in
`Φ_X = -K(g)` (`QED.TwoLoop.UnitXClose.crossedPhi`) are `g + e = Y ξ (1 - Y ξ)`, `g + p = Y ξ` and
`g + q = Y (ξ + Y - 2 Y ξ)`, and `L(g) = log Y + log (1 - Y ξ) - log (ξ + Y - 2 Y ξ)`. The five
coefficients are then `-Y Q`, `-Y (S + κ_e + κ_p + κ_q)`, `-Y (κ_e + κ_p)`, `-Y (S + κ_e)` and
`Y (S - κ_q)` at `g` (`xiΦ1_eq`, …, `xiΦB_eq`), each checked by `field_simp` and `ring`.
-/

@[expose] public section

open Real Set

namespace QED.TwoLoop.UnitXXi

open QED.TwoLoop.UnitXClose

section Coefficients

variable {Y ξ : ℝ}

theorem xiΦ1_eq (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    -(Y * xQ (Y * ξ) (Y * (1 - ξ)) (Y * ξ * (1 - Y))) = xiΦ1 Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hA : 0 < 1 - Y * ξ := by nlinarith
  have hY1' : Y - 1 ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  simp only [xQ, xc₂₀, xc₂₀N, xc₃₀, xc₃₀N, xc₂ₑ, xc₂ₑN, xc₃ₑ, xc₃ₑN, xiΦ1]
  rw [show Y * ξ * (1 - Y) + Y * ξ * (Y * (1 - ξ)) = Y * ξ * (1 - Y * ξ) by ring]
  field_simp
  ring

theorem xiΦY_eq (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    -(Y * xS (Y * ξ) (Y * (1 - ξ)) (Y * ξ * (1 - Y))) = xiΦY Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY1' : Y - 1 ≠ 0 := by linarith
  have hY1'' : 1 - Y ≠ 0 := by linarith
  simp only [xS, xr₂, xr₂N, xr₃, xr₃N, xr₄, xr₄N, xr₅, xr₅N, xr₅N_0, xr₅N_1, xiΦY]
  field_simp
  ring

theorem xiΦx_eq (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hh : ξ ≠ 1 / 2) :
    -(Y * (xκe (Y * ξ) (Y * (1 - ξ)) + xκp (Y * ξ) (Y * (1 - ξ)))) = xiΦx Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hξ1'' : 1 - ξ ≠ 0 := by linarith
  have hξ2 : 2 * ξ - 1 ≠ 0 := fun h => hh (by linarith)
  have hξ2' : -ξ + (1 - ξ) ≠ 0 := fun h => hh (by linarith)
  have hξ2'' : ξ * 2 - 1 ≠ 0 := fun h => hh (by linarith)
  have e1 : -(Y * ξ) + Y * (1 - ξ) ≠ 0 := by
    rw [show -(Y * ξ) + Y * (1 - ξ) = Y * (1 - 2 * ξ) by ring]
    exact mul_ne_zero hY0.ne' (fun h => hh (by linarith))
  have e2 : Y * ξ + Y * (1 - ξ) ≠ 0 := by rw [show Y * ξ + Y * (1 - ξ) = Y by ring]; positivity
  simp only [xκe, xκeN, xκp, xκpN, xiΦx]
  field_simp
  ring

theorem xiΦA_eq (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    -(Y * (xS (Y * ξ) (Y * (1 - ξ)) (Y * ξ * (1 - Y)) + xκe (Y * ξ) (Y * (1 - ξ)))) =
      xiΦA Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY1' : Y - 1 ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hY1'' : 1 - Y ≠ 0 := by linarith
  have hξ1'' : 1 - ξ ≠ 0 := by linarith
  simp only [xS, xr₂, xr₂N, xr₃, xr₃N, xr₄, xr₄N, xr₅, xr₅N, xr₅N_0, xr₅N_1, xκe, xκeN, xiΦA]
  field_simp
  ring

theorem xiΦB_eq (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hh : ξ ≠ 1 / 2) :
    Y * (xS (Y * ξ) (Y * (1 - ξ)) (Y * ξ * (1 - Y)) - xκq (Y * ξ) (Y * (1 - ξ))) =
      xiΦB Y ξ := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hY1' : Y - 1 ≠ 0 := by linarith
  have hξ1' : ξ - 1 ≠ 0 := by linarith
  have hY1'' : 1 - Y ≠ 0 := by linarith
  have hξ1'' : 1 - ξ ≠ 0 := by linarith
  have hξ2 : 2 * ξ - 1 ≠ 0 := fun h => hh (by linarith)
  have hξ2' : -ξ + (1 - ξ) ≠ 0 := fun h => hh (by linarith)
  have hξ2'' : ξ * 2 - 1 ≠ 0 := fun h => hh (by linarith)
  have e1 : -(Y * ξ) + Y * (1 - ξ) ≠ 0 := by
    rw [show -(Y * ξ) + Y * (1 - ξ) = Y * (1 - 2 * ξ) by ring]
    exact mul_ne_zero hY0.ne' (fun h => hh (by linarith))
  have e2 : Y * ξ + Y * (1 - ξ) ≠ 0 := by rw [show Y * ξ + Y * (1 - ξ) = Y by ring]; positivity
  simp only [xS, xr₂, xr₂N, xr₃, xr₃N, xr₄, xr₄N, xr₅, xr₅N, xr₅N_0, xr₅N_1, xκq, xκqN, xiΦB]
  field_simp
  ring

end Coefficients

/-- **The integrand in the letters of `(Y, ξ)`** (eq. (4.5)). -/
theorem crossedPhi_yxi {Y ξ : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1)
    (hh : ξ ≠ 1 / 2) :
    Y * crossedPhi (Y * ξ) (Y * (1 - ξ)) =
      xiΦ1 Y ξ + xiΦY Y ξ * log Y + xiΦx Y ξ * log ξ + xiΦA Y ξ * log (1 - Y * ξ) +
        xiΦB Y ξ * log (ξ + Y - 2 * Y * ξ) := by
  have i1 := xiΦ1_eq hY hξ
  have iY := xiΦY_eq hY hξ
  have ix := xiΦx_eq hY hξ hh
  have iA := xiΦA_eq hY hξ
  have iB := xiΦB_eq hY hξ hh
  have hs := xκ_sum (mul_pos hY.1 hξ.1) (mul_pos hY.1 (sub_pos.mpr hξ.2))
    (fun h => hh (by nlinarith [hY.1]))
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hξ0, hξ1⟩ := hξ
  have hA : 0 < 1 - Y * ξ := by nlinarith
  have hB : 0 < ξ + Y - 2 * Y * ξ := by nlinarith
  have l0 : log (Y * ξ + Y * (1 - ξ)) = log Y := by congr 1; ring
  have l1 : log (Y * ξ * (1 - Y) + Y * ξ * (Y * (1 - ξ))) = log Y + log ξ + log (1 - Y * ξ) := by
    rw [show Y * ξ * (1 - Y) + Y * ξ * (Y * (1 - ξ)) = Y * ξ * (1 - Y * ξ) by ring,
      log_mul (by positivity) hA.ne', log_mul hY0.ne' hξ0.ne']
  have l2 : log (Y * ξ * (1 - Y) + (Y * ξ + Y * (1 - ξ)) * (Y * ξ)) = log Y + log ξ := by
    rw [show Y * ξ * (1 - Y) + (Y * ξ + Y * (1 - ξ)) * (Y * ξ) = Y * ξ by ring,
      log_mul hY0.ne' hξ0.ne']
  have l3 : log (Y * ξ * (1 - Y) + (Y * ξ + Y * (1 - ξ)) * (Y * (1 - ξ))) =
      log Y + log (ξ + Y - 2 * Y * ξ) := by
    rw [show Y * ξ * (1 - Y) + (Y * ξ + Y * (1 - ξ)) * (Y * (1 - ξ)) =
      Y * (ξ + Y - 2 * Y * ξ) by ring, log_mul hY0.ne' hB.ne']
  have eB : Y * ξ * (1 - Y * ξ - Y * (1 - ξ)) = Y * ξ * (1 - Y) := by ring
  simp only [crossedPhi, xK, xL]
  rw [eB, l0, l1, l2, l3]
  linear_combination i1 + log Y * iY + log ξ * ix + log (1 - Y * ξ) * iA +
    log (ξ + Y - 2 * Y * ξ) * iB - (Y * log Y) * hs

end QED.TwoLoop.UnitXXi

end
