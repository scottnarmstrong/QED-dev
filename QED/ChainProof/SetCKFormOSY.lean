/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOSYInt
public import QED.ChainProof.SetCKScOutSDom
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the `Y`-integral of the outer self-energy weight

Helper level (no frozen statement). For `x ∈ (0, 1)` and `v > 0` the weight
`W(Y, x, v) = scOutSW Y x v` of `SetCKScOutSDom` switches branch at the threshold
`Y_c = v/(ρ + v)` (`ρ = x/(1 - x)`, `v ≤ V ⟺ Y ≥ Y_c` for `V = Y ρ/(1 - Y)`). Above it `W` is
a Laurent polynomial in `Y` plus a multiple of `log Y` (`scOutSW_eq_hi`), below it a linear
polynomial plus multiples of `log Y` and `log(1 - Y)` (`scOutSW_eq_lo`). With the integrals of
`SetCKFormOSYInt` (**`integral_scOutSW_Y`**):

`∫₀¹ W(Y, x, v) dY = c_v log(v/(ρ + v)) + c_ρ log(ρ/(ρ + v)) + c₀` (`formOSF`),

with the polynomials `c_v(x, v)` (`formOSCv`), `c_ρ(x) = x²(5 - 2x)/2` (`formOSCr`) and
`c₀(x, v)` (`formOSC0`). No dilogarithm appears.
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- The coefficient of `log(v/(ρ + v))`. -/
noncomputable def formOSCv (x v : ℝ) : ℝ :=
  -(-3 * v ^ 2 - 2 * x ^ 4 + 6 * x ^ 3 - 18 * v * x ^ 3 - 15 * v ^ 2 * x ^ 2 - 8 * v * x +
    3 * v * x ^ 4 + 6 * v ^ 2 * x ^ 3 + 12 * x * v ^ 2 + 23 * v * x ^ 2) / 2

/-- The coefficient of `log(ρ/(ρ + v))`. -/
noncomputable def formOSCr (x : ℝ) : ℝ := -x ^ 2 * (-5 + 2 * x) / 2

/-- The rational part. -/
noncomputable def formOSC0 (x v : ℝ) : ℝ :=
  x * (-7 * x - 3 * x ^ 2 + 3 * v + 3 * x ^ 3 - 9 * v * x + 6 * v * x ^ 2) / 2

/-- **The `Y`-integral of the outer self-energy weight** in closed form. -/
noncomputable def formOSF (x v : ℝ) : ℝ :=
  formOSCv x v * (log v - log (scOutRho x + v)) +
    formOSCr x * (log (scOutRho x) - log (scOutRho x + v)) + formOSC0 x v

section

variable {x v Y : ℝ}

theorem formOS_V_eq (hY : Y ∈ Ioo (0 : ℝ) 1) :
    Y ^ 2 * scOutRho x / (Y * (1 - Y)) = Y * scOutRho x / (1 - Y) := by
  have := hY.1.ne'
  have : 1 - Y ≠ 0 := by linarith [hY.2]
  field_simp

/-- Above the threshold `W` is a Laurent polynomial plus a multiple of `log Y`. -/
theorem scOutSW_eq_hi (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hc : v / (scOutRho x + v) < Y) :
    scOutSW Y x v = formOSHi
      (-v * (-1 + x) * (x ^ 3 - 3 * x ^ 2 + 2 * v - 4 * v * x + 2 * v * x ^ 2) / 2)
      ((-3 * v ^ 2 - 2 * x ^ 4 + 6 * x ^ 3 - 18 * v * x ^ 3 - 15 * v ^ 2 * x ^ 2 - 8 * v * x +
        3 * v * x ^ 4 + 6 * v ^ 2 * x ^ 3 + 12 * x * v ^ 2 + 23 * v * x ^ 2) / 2)
      (-x * (-4 * v - 4 * x ^ 3 - 2 * x ^ 2 + 6 * v ^ 2 + 16 * x - 24 * v * x ^ 2 -
        12 * x * v ^ 2 + 3 * v * x ^ 3 + 6 * v ^ 2 * x ^ 2 + 25 * v * x) / 2)
      ((-1 + x) * (-v ^ 2 - 2 * x ^ 3 + v * x ^ 3 - x * v ^ 2 - 9 * v * x ^ 2 - 4 * v * x +
        2 * v ^ 2 * x ^ 2) / 2)
      (4 * x ^ 2 * (-1 + x)) (-2 * x ^ 2 * (1 + 2 * x)) Y := by
  have hr := scOutRho_pos hx
  have hY0 := hY.1
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hle : v ≤ Y ^ 2 * scOutRho x / (Y * (1 - Y)) := by
    rw [formOS_V_eq hY, le_div_iff₀ hY1]
    rw [div_lt_iff₀ (by positivity)] at hc
    nlinarith
  unfold scOutSW
  rw [scOutTg_of_le hle, log_pow]
  unfold selfK1 selfK2 scOutRho scOutSA formOSHi
  have : 1 - x ≠ 0 := by linarith [hx.2]
  have := hx.1.ne'
  have := hY0.ne'
  have := hY1.ne'
  field_simp
  ring

/-- Below the threshold `W` is linear plus multiples of `log Y` and `log(1 - Y)`. -/
theorem scOutSW_eq_lo (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hc : Y < v / (scOutRho x + v)) :
    scOutSW Y x v = formOSLo
      (2 * x ^ 2 * (-1 + x) * log v - 2 * x ^ 2 * (-1 + x) * log (scOutRho x) +
        x ^ 2 * (x ^ 3 - 3 * x ^ 2 + 22 * v - 38 * v * x + 16 * v * x ^ 2) / (2 * v * (-1 + x)))
      (-x ^ 2 * (1 + 2 * x) * log v + x ^ 2 * (1 + 2 * x) * log (scOutRho x) -
        x ^ 2 * (x ^ 2 + 3 * v + 6 * v * x) / (2 * v))
      (2 * x ^ 2 * (-1 + x)) (-x ^ 2 * (1 + 2 * x))
      (2 * x ^ 2 * (-1 + x)) (-x ^ 2 * (1 + 2 * x)) Y := by
  have hr := scOutRho_pos hx
  have hY0 := hY.1
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hlt : Y ^ 2 * scOutRho x / (Y * (1 - Y)) < v := by
    rw [formOS_V_eq hY, div_lt_iff₀ hY1]
    rw [lt_div_iff₀ (by positivity)] at hc
    nlinarith
  unfold scOutSW
  rw [scOutTg_of_lt hlt, formOS_V_eq hY, log_div hv.ne' (by positivity),
    log_div (by positivity) hY1.ne', log_mul hY0.ne' hr.ne', log_pow]
  generalize log (scOutRho x) = LR
  unfold selfK1 selfK2 scOutRho scOutSA formOSLo
  have : 1 - x ≠ 0 := by linarith [hx.2]
  have : -1 + x ≠ 0 := by linarith [hx.2]
  have := hY0.ne'
  have := hv.ne'
  field_simp
  ring

end

/-- **The `Y`-integral of the outer self-energy weight**: for `x ∈ (0, 1)` and `v > 0`,
`Y ↦ W(Y, x, v)` is integrable on `(0, 1)` with integral `formOSF x v`. -/
theorem integral_scOutSW_Y {x v : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    IntegrableOn (fun Y => scOutSW Y x v) (Ioo 0 1) ∧
      ∫ Y in Ioo (0 : ℝ) 1, scOutSW Y x v = formOSF x v := by
  have hr := scOutRho_pos hx
  set a := v / (scOutRho x + v) with ha_def
  have ha : 0 < a := by positivity
  have ha1 : a < 1 := by rw [div_lt_one (by positivity)]; linarith
  obtain ⟨iH, vH⟩ := formOS_integral_hi
      (-v * (-1 + x) * (x ^ 3 - 3 * x ^ 2 + 2 * v - 4 * v * x + 2 * v * x ^ 2) / 2)
      ((-3 * v ^ 2 - 2 * x ^ 4 + 6 * x ^ 3 - 18 * v * x ^ 3 - 15 * v ^ 2 * x ^ 2 - 8 * v * x +
        3 * v * x ^ 4 + 6 * v ^ 2 * x ^ 3 + 12 * x * v ^ 2 + 23 * v * x ^ 2) / 2)
      (-x * (-4 * v - 4 * x ^ 3 - 2 * x ^ 2 + 6 * v ^ 2 + 16 * x - 24 * v * x ^ 2 -
        12 * x * v ^ 2 + 3 * v * x ^ 3 + 6 * v ^ 2 * x ^ 2 + 25 * v * x) / 2)
      ((-1 + x) * (-v ^ 2 - 2 * x ^ 3 + v * x ^ 3 - x * v ^ 2 - 9 * v * x ^ 2 - 4 * v * x +
        2 * v ^ 2 * x ^ 2) / 2)
      (4 * x ^ 2 * (-1 + x)) (-2 * x ^ 2 * (1 + 2 * x)) ha ha1.le
  obtain ⟨iL, vL⟩ := formOS_integral_lo
      (2 * x ^ 2 * (-1 + x) * log v - 2 * x ^ 2 * (-1 + x) * log (scOutRho x) +
        x ^ 2 * (x ^ 3 - 3 * x ^ 2 + 22 * v - 38 * v * x + 16 * v * x ^ 2) / (2 * v * (-1 + x)))
      (-x ^ 2 * (1 + 2 * x) * log v + x ^ 2 * (1 + 2 * x) * log (scOutRho x) -
        x ^ 2 * (x ^ 2 + 3 * v + 6 * v * x) / (2 * v))
      (2 * x ^ 2 * (-1 + x)) (-x ^ 2 * (1 + 2 * x))
      (2 * x ^ 2 * (-1 + x)) (-x ^ 2 * (1 + 2 * x)) ha ha1
  have eH : EqOn (fun Y => scOutSW Y x v) (formOSHi _ _ _ _ _ _) (Ioo a 1) := fun Y hY =>
    scOutSW_eq_hi hx hv ⟨ha.trans hY.1, hY.2⟩ hY.1
  have eL : EqOn (fun Y => scOutSW Y x v) (formOSLo _ _ _ _ _ _) (Ioo 0 a) := fun Y hY =>
    scOutSW_eq_lo hx hv ⟨hY.1, hY.2.trans ha1⟩ hY.2
  have jH : IntegrableOn (fun Y => scOutSW Y x v) (Ioo a 1) :=
    iH.congr_fun eH.symm measurableSet_Ioo
  have jL : IntegrableOn (fun Y => scOutSW Y x v) (Ioc 0 a) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (iL.mono_set Ioo_subset_Ioc_self).congr_fun eL.symm measurableSet_Ioo
  have hU : Ioc 0 a ∪ Ioo a 1 = Ioo (0 : ℝ) 1 := Ioc_union_Ioo_eq_Ioo ha.le ha1
  have hD : Disjoint (Ioc 0 a) (Ioo a (1 : ℝ)) :=
    Set.disjoint_left.2 fun Y h1 h2 => absurd h1.2 (not_le.2 h2.1)
  refine ⟨by rw [← hU]; exact jL.union jH, ?_⟩
  rw [← hU, setIntegral_union hD measurableSet_Ioo jL jH, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo eL, ← integral_Ioc_eq_integral_Ioo, vL,
    setIntegral_congr_fun measurableSet_Ioo eH, vH]
  have e1 : 1 - a = scOutRho x / (scOutRho x + v) := by
    rw [ha_def]
    have : scOutRho x + v ≠ 0 := by positivity
    field_simp
    ring
  have hla : log a = log v - log (scOutRho x + v) := log_div hv.ne' (by positivity)
  have hl1 : log (1 - a) = log (scOutRho x) - log (scOutRho x + v) := by
    rw [e1, log_div hr.ne' (by positivity)]
  unfold formOSLoP formOSHiP formOSF formOSCv formOSCr formOSC0
  rw [hla, hl1, log_one]
  generalize log v = LV
  generalize log (scOutRho x) = LR
  generalize log (scOutRho x + v) = LS
  have hxv : 0 < x + v * (1 - x) := by nlinarith [hx.1, hx.2]
  have : 1 - x ≠ 0 := by linarith [hx.2]
  have ea : a = v * (1 - x) / (x + v * (1 - x)) := by
    rw [ha_def]
    unfold scOutRho
    field_simp
  rw [ea]
  have : -1 + x ≠ 0 := by linarith [hx.2]
  have := hxv.ne'
  have := hv.ne'
  field_simp
  ring

end QED.ChainProof.SetCK

end
