/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9MThreeInner
public import QED.ThreeLoopD.SetDMastersI9MThreeOuter
public import QED.ThreeLoopD.SetDMastersI9KValB
import QED.ThreeLoopD.SetDMastersI9MTwo
import QED.ThreeLoopD.SetDMastersI9MThreeX
import QED.ThreeLoopD.SetDMastersI9MThreePA
import QED.ThreeLoopD.SetDMastersI9MThreePB
import QED.Polylog.HPLLowWeight
import QED.Polylog.DilogPM

/-!
# Set (d), master `I₉`: `M₃` and the Laurent expansion of `K`

The Taylor coefficient `M₃ = QED.ThreeLoopD.i9MCoeff 3` is an absolutely convergent integral over
the unit square (Cauchy estimates). By Fubini we integrate first in `x`. At fixed `w ∈ (0, 1)`
the integrand is `(1 - w²)/w · (s₃(x) + s₃(1 - x))` (`QED.ThreeLoopD.i9M3S`), whose integral is
`QED.ThreeLoopD.i9M3S_integral` with the nine pure integrals of
`QED.ThreeLoopD.SetDMastersI9MThreeX` and `QED.ThreeLoopD.SetDMastersI9MThreeP`. Written with
harmonic polylogarithms, the `x`-integral is `QED.ThreeLoopD.i9M3O w`, whose integral over
`(0, 1)` is computed in `QED.ThreeLoopD.SetDMastersI9MThreeOuter`.

## Main results

* `QED.ThreeLoopD.integrable_i9MCoeffFun_three`: the integrand of `M₃` is integrable.
* `QED.ThreeLoopD.i9MCoeff_three`: `M₃ = -621/2 + 235π²/4 + 147ζ(3) - π⁴/12 - 72π² log 2`.
* `QED.ThreeLoopD.i9KCoeff_three`: the coefficient `K₃`.
* `QED.ThreeLoopD.hasTruncLaurent_i9K`: the truncated Laurent expansion of `K` to order `4`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### The integrand of `M₃` -/

/-- **The integrand of `M₃` is integrable** on the unit square. -/
theorem integrable_i9MCoeffFun_three :
    Integrable (fun z : ℝ × ℝ => i9MCoeffFun 3 z.1 z.2)
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  refine (integrable_i9M_bound.const_mul (256000 / 3)).mono' ?_ ?_
  · have : Measurable (fun z : ℝ × ℝ => i9MCoeffFun 3 z.1 z.2) := by
      unfold i9MCoeffFun i9KB1 i9KB3 i9Poly
      fun_prop
    exact this.aestronglyMeasurable
  refine ae_restrict_of_forall_mem hS fun z hz => ?_
  obtain ⟨x, w⟩ := z
  have hc := norm_le_of_hasDerivAt_chain (D := fun k e => i9MD k e (x, w)) (R := 1 / 20)
    (ρ := 1 / 80) (by norm_num) (fun k ε => hasDerivAt_i9MD k ε (x, w))
    (fun ε hε => norm_i9MD_le hε hz.1 hz.2) 3 0 (by norm_num)
  have he := i9MD_at_zero (x := x) hz.2 3
  have h : ‖(i9MCoeffFun 3 x w : ℂ)‖ ≤
      256000 / 3 * (w ^ (-(3 / 5) : ℝ) * (x * (1 - x)) ^ (-(7 / 10) : ℝ)) := by
    rw [← he, norm_div]
    norm_num [Nat.factorial] at hc ⊢
    linarith
  simpa only [Complex.norm_real] using h

/-- At fixed `x, w ∈ (0, 1)`, the integrand of `M₃` is `(1 - w²)/w · (s₃(x) + s₃(1 - x))`. -/
theorem i9MCoeffFun_three_eq {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    i9MCoeffFun 3 x w = (1 - w ^ 2) / w * (i9M3S w x + i9M3S w (1 - x)) := by
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hw0 := hw.1
  have hA := i9M2_A_pos hw hx0.le
  have hB := i9M2_B_pos hw hx.2.le
  unfold i9MCoeffFun i9KB1 i9KB3 i9Poly i9M3S
  rw [show x * (1 - x) * (1 - w) ^ 2 + w * 1 = (w + (1 - w) * x) * (1 - (1 - w) * x) by ring,
    show w + (1 - w) * (1 - x) = 1 - (1 - w) * x by ring,
    show 1 - (1 - w) * (1 - x) = w + (1 - w) * x by ring,
    show 1 - (1 - x) = x by ring,
    Real.log_mul hA.ne' hB.ne', Real.log_mul hx0.ne' hx1.ne']
  simp only [Nat.factorial]
  field_simp
  ring

/-! ### The `x`-integral in harmonic polylogarithms -/

theorem i9M3_Li_two_one_sub {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    Li₂ (1 - w) = π ^ 2 / 6 + Real.log w * hpl [one] w - hpl [zero, one] w := by
  have h := Li_two_one_sub' hw
  rw [Li_two] at h
  rw [hpl_one hw, hpl_zero_one hw, Li_two, h]
  ring

theorem i9M3_JAB {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    i9M2JAB w = (2 - 2 * w - (1 - w) * Real.log w + (1 + w) * (Real.log w -
      2 * Real.log w * hpl [negOne] w + 2 * hpl [zero, negOne] w - π ^ 2 / 6)) / (1 - w) := by
  have h2 := Li_two_div_one_add hw
  have h3 := Li_two_inv_one_add hw
  rw [Li_two] at h2 h3
  unfold i9M2JAB
  rw [h2, h3, hpl_negOne hw, hpl_zero_negOne hw, Li_two]
  ring

/-- **The `x`-integral in terms of `O`**: `(1 - w²)/w · 2 ∫₀¹ s₃ = O(w)`. -/
theorem i9M3Sig_eq_O {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {P1 P3 P5 P6 P7 P8 P9 R1 R3 : ℝ}
    (h1 : P1 = 2 * zeta3 - 2 * (π ^ 2 / 6) * hpl [negOne] w - 2 * hpl [zero, zero, negOne] w +
      4 * hpl [zero, negOne, negOne] w + 4 * hpl [negOne, zero, negOne] w +
      2 * Real.log w * hpl [zero, negOne] w - 4 * Real.log w * hpl [negOne, negOne] w -
      Real.log w ^ 2 * hpl [negOne] w)
    (h3 : P3 = 2 * zeta3 - 2 * hpl [zero, zero, one] w + 2 * Real.log w * hpl [zero, one] w -
      Real.log w ^ 2 * hpl [one] w)
    (h5 : P5 = zeta3 + hpl [zero, one, one] w + hpl [one, zero, one] w -
      Real.log w * hpl [one, one] w - π ^ 2 / 6 * hpl [one] w)
    (h6 : P6 = zeta3 - 2 * hpl [zero, zero, one] w - hpl [zero, one, one] w -
      hpl [one, zero, one] w + Real.log w * hpl [zero, one] w + Real.log w * hpl [one, one] w +
      π ^ 2 / 6 * hpl [one] w)
    (h7 : P7 = 2 * zeta3 - hpl [zero, zero, one] w + hpl [zero, one, one] w +
      hpl [one, zero, one] w + Real.log w * hpl [zero, one] w - Real.log w * hpl [one, one] w -
      Real.log w ^ 2 * hpl [one] w / 2 - π ^ 2 / 6 * hpl [one] w)
    (h8 : P8 = 2 * zeta3 - π ^ 2 / 6 * hpl [one] w - 2 * (π ^ 2 / 6) * hpl [negOne] w -
      hpl [zero, zero, negOne] w + 2 * hpl [zero, one, negOne] w +
      2 * hpl [zero, negOne, one] w + 2 * hpl [one, zero, negOne] w +
      2 * hpl [negOne, zero, one] w + Real.log w * hpl [zero, negOne] w -
      2 * (Real.log w * hpl [one, negOne] w) - 2 * (Real.log w * hpl [negOne, one] w) -
      Real.log w ^ 2 * hpl [negOne] w / 2)
    (h9 : P9 = zeta3 + 2 * hpl [zero, zero, one] w - 4 * hpl [zero, zero, negOne] w -
      Real.log w * hpl [zero, one] w + 2 * (Real.log w * hpl [zero, negOne] w))
    (hr1 : R1 = -zeta3 + hpl [zero, zero, one] w - Real.log w ^ 2 * hpl [one] w / 2 -
      Real.log w ^ 3 / 3 - π ^ 2 / 6 * Real.log w)
    (hr3 : R3 = 2 * hpl [zero, zero, one] w + 2 * hpl [zero, one, one] w +
      2 * hpl [one, zero, one] w - 2 * Real.log w * hpl [one, one] w -
      Real.log w ^ 2 * hpl [one] w - Real.log w ^ 3 / 3 - 2 * (π ^ 2 / 6) * hpl [one] w -
      2 * (π ^ 2 / 6) * Real.log w) :
    (1 - w ^ 2) / w * (2 * i9M3Sig w P1 P3 P5 P6 P7 P8 P9 R1 R3) = i9M3O w := by
  have hw0 := hw.1.ne'
  have hu : (1 - w) ≠ 0 := by linarith [hw.2]
  unfold i9M3Sig i9M3VAA i9M3VAP i9M3VAQ i9M3O
  rw [i9M3_Li_two_one_sub hw, i9M3_JAB hw, h1, h3, h5, h6, h7, h8, h9, hr1, hr3]
  field_simp
  ring

/-- **The `x`-integral of the integrand of `M₃`** is `O(w)`. -/
theorem integral_i9MCoeffFun_three_x {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∫ x in Ioo (0 : ℝ) 1, i9MCoeffFun 3 x w = i9M3O w := by
  rw [setIntegral_congr_fun measurableSet_Ioo fun x hx => i9MCoeffFun_three_eq hx hw,
    integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  obtain ⟨hs, hv⟩ := i9M3S_integral hw (i9M3X_P1 hw) (i9M3X_P3 hw) (i9M3X_P5 hw) (i9M3P_P6 hw)
    (i9M3P_P7 hw) (i9M3P_P8 hw) (i9M3P_P9 hw) (i9M3X_R1 hw) (i9M3X_R3 hw)
  have hs' : IntervalIntegrable (fun x => i9M3S w (1 - x)) volume 0 1 := by
    simpa using (hs.comp_sub_left 1).symm
  rw [intervalIntegral.integral_add hs hs', intervalIntegral.integral_comp_sub_left
    (fun x => i9M3S w x) 1]
  simp only [sub_self, sub_zero]
  rw [hv, ← i9M3Sig_eq_O hw rfl rfl rfl rfl rfl rfl rfl rfl rfl]
  ring

/-! ### `M₃` and `K₃` -/

/-- **`M₃ = -621/2 + 235π²/4 + 147ζ(3) - π⁴/12 - 72π² log 2`**. -/
theorem i9MCoeff_three : i9MCoeff 3 =
    -621 / 2 + 235 * π ^ 2 / 4 + 147 * zeta3 - π ^ 4 / 12 - 72 * π ^ 2 * Real.log 2 := by
  have hint := integrable_i9MCoeffFun_three
  rw [volume_restrict_prod2] at hint
  have hO : IntervalIntegrable i9M3O volume 0 1 := by
    refine (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 ?_
    refine hint.integral_prod_right.congr ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioo fun w hw =>
      integral_i9MCoeffFun_three_x hw
  rw [i9MCoeff, volume_restrict_prod2,
    integral_prod_symm (fun z : ℝ × ℝ => i9MCoeffFun 3 z.1 z.2) hint,
    setIntegral_congr_fun measurableSet_Ioo fun w hw => integral_i9MCoeffFun_three_x hw,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_i9M3O hO]

/-- **`K₃ = -197 + 265π²/6 + 144ζ(3) - π⁴/12 - 72π² log 2`**. -/
theorem i9KCoeff_three : i9KCoeff 3 =
    -197 + 265 * π ^ 2 / 6 + 144 * zeta3 - π ^ 4 / 12 - 72 * π ^ 2 * Real.log 2 :=
  i9KCoeff_three_of_M i9MCoeff_two i9MCoeff_three

/-- **The truncated Laurent expansion of `K` to order `4`**, unconditionally. -/
theorem hasTruncLaurent_i9K : HasTruncLaurent i9K i9KTarget 4 :=
  hasTruncLaurent_i9K_of_M i9MCoeff_two i9MCoeff_three

end QED.ThreeLoopD
