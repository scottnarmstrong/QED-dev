/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4W

/-!
# Set (d), master `I₈`: more basis functions near `ξ = 0`

The Lyndon words of weight at most five used by the limit of `F₄ - A₄` that are not already in
`QED.ThreeLoopD.SetDMastersI13R3S` or `QED.ThreeLoopD.SetDMastersI13R4S`, each written as
`c₁ x + c₂ x² + x³ ρ_w(x)` with the first two coefficients of its power series and the normalized
remainder `ρ_w` (`QED.ThreeLoopD.i13Rho`, `|ρ_w| ≤ 2` on `(0, 1/2)` by
`QED.ThreeLoopD.abs_i13Rho_le`).

## Main results

* `QED.ThreeLoopD.i8hpl_rho_m11` and its companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

theorem i8hpl_rho_00101 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, one, zero, one] x = x ^ 2 / 8 +
      i13Rho [zero, zero, one, zero, one] x * x ^ 3 := by
  have h1 : coef [zero, zero, one, zero, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, zero, one, zero, one] 2 = 1 / 8 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0011m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, one, one, negOne] x = i13Rho [zero, zero, one, one, negOne] x * x ^ 3 := by
  have h1 : coef [zero, zero, one, one, negOne] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, zero, one, one, negOne] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_001m1 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, one, negOne, one] x = i13Rho [zero, zero, one, negOne, one] x * x ^ 3 := by
  have h1 : coef [zero, zero, one, negOne, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, zero, one, negOne, one] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_001mm {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, one, negOne, negOne] x = i13Rho [zero, zero, one, negOne, negOne] x * x ^ 3 :=
      by
  have h1 : coef [zero, zero, one, negOne, negOne] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, zero, one, negOne, negOne] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_00m11 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, negOne, one, one] x = i13Rho [zero, zero, negOne, one, one] x * x ^ 3 := by
  have h1 : coef [zero, zero, negOne, one, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, zero, negOne, one, one] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_00m1m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, negOne, one, negOne] x = i13Rho [zero, zero, negOne, one, negOne] x * x ^ 3 :=
      by
  have h1 : coef [zero, zero, negOne, one, negOne] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, zero, negOne, one, negOne] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_00mm1 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, negOne, negOne, one] x = i13Rho [zero, zero, negOne, negOne, one] x * x ^ 3 :=
      by
  have h1 : coef [zero, zero, negOne, negOne, one] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, zero, negOne, negOne, one] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0101m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one, zero, one, negOne] x = i13Rho [zero, one, zero, one, negOne] x * x ^ 3 := by
  have h1 : coef [zero, one, zero, one, negOne] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, one, zero, one, negOne] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_01111 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one, one, one, one] x = i13Rho [zero, one, one, one, one] x * x ^ 3 := by
  have h1 : coef [zero, one, one, one, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, one, one, one, one] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0111m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one, one, one, negOne] x = i13Rho [zero, one, one, one, negOne] x * x ^ 3 := by
  have h1 : coef [zero, one, one, one, negOne] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, one, one, one, negOne] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_011m1 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one, one, negOne, one] x = i13Rho [zero, one, one, negOne, one] x * x ^ 3 := by
  have h1 : coef [zero, one, one, negOne, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, one, one, negOne, one] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_011mm {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one, one, negOne, negOne] x = i13Rho [zero, one, one, negOne, negOne] x * x ^ 3 := by
  have h1 : coef [zero, one, one, negOne, negOne] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, one, one, negOne, negOne] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_01m11 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one, negOne, one, one] x = i13Rho [zero, one, negOne, one, one] x * x ^ 3 := by
  have h1 : coef [zero, one, negOne, one, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, one, negOne, one, one] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_01m1m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one, negOne, one, negOne] x = i13Rho [zero, one, negOne, one, negOne] x * x ^ 3 := by
  have h1 : coef [zero, one, negOne, one, negOne] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, one, negOne, one, negOne] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_01mm1 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one, negOne, negOne, one] x = i13Rho [zero, one, negOne, negOne, one] x * x ^ 3 := by
  have h1 : coef [zero, one, negOne, negOne, one] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, one, negOne, negOne, one] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_01mmm {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one, negOne, negOne, negOne] x = i13Rho [zero, one, negOne, negOne, negOne] x * x ^ 3
      := by
  have h1 : coef [zero, one, negOne, negOne, negOne] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, one, negOne, negOne, negOne] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0m01m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, zero, one, negOne] x = i13Rho [zero, negOne, zero, one, negOne] x * x ^ 3 :=
      by
  have h1 : coef [zero, negOne, zero, one, negOne] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, negOne, zero, one, negOne] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0m0m1 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, zero, negOne, one] x = i13Rho [zero, negOne, zero, negOne, one] x * x ^ 3 :=
      by
  have h1 : coef [zero, negOne, zero, negOne, one] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, negOne, zero, negOne, one] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0m101 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, one, zero, one] x = i13Rho [zero, negOne, one, zero, one] x * x ^ 3 := by
  have h1 : coef [zero, negOne, one, zero, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, negOne, one, zero, one] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0m111 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, one, one, one] x = i13Rho [zero, negOne, one, one, one] x * x ^ 3 := by
  have h1 : coef [zero, negOne, one, one, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, negOne, one, one, one] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0m11m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, one, one, negOne] x = i13Rho [zero, negOne, one, one, negOne] x * x ^ 3 := by
  have h1 : coef [zero, negOne, one, one, negOne] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, negOne, one, one, negOne] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0m1m1 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, one, negOne, one] x = i13Rho [zero, negOne, one, negOne, one] x * x ^ 3 := by
  have h1 : coef [zero, negOne, one, negOne, one] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, negOne, one, negOne, one] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0m1mm {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, one, negOne, negOne] x = i13Rho [zero, negOne, one, negOne, negOne] x * x ^ 3
      := by
  have h1 : coef [zero, negOne, one, negOne, negOne] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, negOne, one, negOne, negOne] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0mm11 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, negOne, one, one] x = i13Rho [zero, negOne, negOne, one, one] x * x ^ 3 := by
  have h1 : coef [zero, negOne, negOne, one, one] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, negOne, negOne, one, one] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0mm1m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, negOne, one, negOne] x = i13Rho [zero, negOne, negOne, one, negOne] x * x ^ 3
      := by
  have h1 : coef [zero, negOne, negOne, one, negOne] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, negOne, negOne, one, negOne] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0mmm1 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, negOne, negOne, one] x = i13Rho [zero, negOne, negOne, negOne, one] x * x ^ 3
      := by
  have h1 : coef [zero, negOne, negOne, negOne, one] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, negOne, negOne, negOne, one] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_0mmmm {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, negOne, negOne, negOne] x = i13Rho [zero, negOne, negOne, negOne, negOne] x *
      x ^ 3 := by
  have h1 : coef [zero, negOne, negOne, negOne, negOne] 1 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  have h2 : coef [zero, negOne, negOne, negOne, negOne] 2 = 0 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_m11 {x : ℝ} (hx : x ≠ 0) :
    hpl [negOne, one, one] x = i13Rho [negOne, one, one] x * x ^ 3 := by
  have h1 : coef [negOne, one, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [negOne, one, one] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_mm1 {x : ℝ} (hx : x ≠ 0) :
    hpl [negOne, negOne, one] x = i13Rho [negOne, negOne, one] x * x ^ 3 := by
  have h1 : coef [negOne, negOne, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [negOne, negOne, one] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i8hpl_rho_mm11 {x : ℝ} (hx : x ≠ 0) :
    hpl [negOne, negOne, one, one] x = i13Rho [negOne, negOne, one, one] x * x ^ 3 := by
  have h1 : coef [negOne, negOne, one, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [negOne, negOne, one, one] 2 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

end QED.ThreeLoopD
