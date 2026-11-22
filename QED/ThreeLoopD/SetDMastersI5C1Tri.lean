/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Bas

/-!
# Set (d), master `I₅`: the trilogarithms of the primitive of `I(x)`

For `0 < ξ < 1`, `y = 1 - ξ` and `0 < x < y`, each of the thirty-two trilogarithm arguments `h`
of the primitive of `I(x)` lies in `(-1, 1) \ {0}`, so `Li₃ (h x)` has derivative
`Li₂ (h x) · h'/h` with `h'/h` a combination of the letter derivatives
(`QED.ThreeLoopD.i5C1T_d0`, ...). For the arguments with `h(0) = 1` the reflection formula
moves `Li₂ (h)` to `Li₂ (1 - h)` (`QED.ThreeLoopD.i5C1F_0`, ...).

## Main results

* `QED.ThreeLoopD.i5C1T_d0`, ..., `QED.ThreeLoopD.i5C1T_d31`.
* `QED.ThreeLoopD.i5C1F_0`, `QED.ThreeLoopD.i5C1F_3`, `QED.ThreeLoopD.i5C1F_4`,
  `QED.ThreeLoopD.i5C1F_5`, `QED.ThreeLoopD.i5C1F_8`, `QED.ThreeLoopD.i5C1F_13`,
  `QED.ThreeLoopD.i5C1F_19`.
-/

@[expose] public section

open Set Real QED.Polylog

namespace QED.ThreeLoopD

theorem i5C1T_d0 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((1 - x))) (Li₂ ((1 - x)) * ((-1 / (1 - x)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(1 - x)| < 1 := by
    rw [abs_of_pos (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x)
  have hne : (1 - x) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x d3).congr_deriv ?_
  field_simp

theorem i5C1T_d1 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (x / (1 - ξ))) (Li₂ (x / (1 - ξ)) * ((1 / x))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |x / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  have hne : x / (1 - ξ) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (hid.div (hasDerivAt_const x ((1 - ξ)))
      hy.ne')).congr_deriv ?_
  field_simp; ring

theorem i5C1T_d2 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (ξ / (1 - x))) (Li₂ (ξ / (1 - x)) * (-(-1 / (1 - x)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |ξ / (1 - x)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  have hne : ξ / (1 - x) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x ((hasDerivAt_const x (ξ)).div d3 l3.ne')).congr_deriv ?_
  field_simp; ring

theorem i5C1T_d3 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (ξ * (1 - x))) (Li₂ (ξ * (1 - x)) * ((-1 / (1 - x)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |ξ * (1 - x)| < 1 := by
    rw [abs_of_pos (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : ξ * (1 - x) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x ((hasDerivAt_const x (ξ)).mul d3)).congr_deriv ?_
  field_simp; ring

theorem i5C1T_d4 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (-(ξ * x / (1 - ξ)))) (Li₂ (-(ξ * x / (1 - ξ))) * ((1 / x))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |-(ξ * x / (1 - ξ))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : -(ξ * x / (1 - ξ)) ≠ 0 := neg_ne_zero.mpr (by positivity)
  refine ((hasDerivAt_Li₃ hlt hne).comp x ((((hasDerivAt_const x (ξ)).mul hid).div
      (hasDerivAt_const x ((1 - ξ))) hy.ne').neg)).congr_deriv ?_
  field_simp; ring

theorem i5C1T_d5 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((ξ * x + (1 - ξ)))) (Li₂ ((ξ * x + (1 - ξ))) *
        ((ξ / (ξ * x + (1 - ξ))))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ ^ 2) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x))
  have hne : (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x d2).congr_deriv ?_
  field_simp

theorem i5C1T_d6 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((1 - ξ - x) / (1 - x))) (Li₂ ((1 - ξ - x) / (1 - x)) *
        ((-1 / (1 - ξ - x)) - (-1 / (1 - x)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(1 - ξ - x) / (1 - x)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ)
  have hne : (1 - ξ - x) / (1 - x) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (d1.div d3 l3.ne')).congr_deriv ?_
  field_simp

theorem i5C1T_d7 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (-(ξ * x ^ 2 / (1 - ξ) ^ 2))) (Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) *
        (2 * (1 / x))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |-(ξ * x ^ 2 / (1 - ξ) ^ 2)| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < ξ * (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) + 3 *
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  have hne : -(ξ * x ^ 2 / (1 - ξ) ^ 2) ≠ 0 := neg_ne_zero.mpr (by positivity)
  refine ((hasDerivAt_Li₃ hlt hne).comp x ((((hasDerivAt_const x (ξ)).mul (hid.pow 2)).div
      (hasDerivAt_const x ((1 - ξ) ^ 2)) (pow_pos hy 2).ne').neg)).congr_deriv ?_
  field_simp; ring

theorem i5C1T_d8 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((1 - ξ - x) / (1 - ξ))) (Li₂ ((1 - ξ - x) / (1 - ξ)) *
        ((-1 / (1 - ξ - x)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(1 - ξ - x) / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x)
  have hne : (1 - ξ - x) / (1 - ξ) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (d1.div (hasDerivAt_const x ((1 - ξ)))
      hy.ne')).congr_deriv ?_
  field_simp; ring

theorem i5C1T_d9 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (ξ * (1 - ξ - x) / (1 - ξ))) (Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) *
        ((-1 / (1 - ξ - x)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |ξ * (1 - ξ - x) / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : ξ * (1 - ξ - x) / (1 - ξ) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x (ξ)).mul d1).div
      (hasDerivAt_const x ((1 - ξ))) hy.ne')).congr_deriv ?_
  field_simp; ring

theorem i5C1T_d10 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) (Li₂ ((1 + ξ) *
        x / (ξ * x + (1 - ξ))) * ((1 / x) - (ξ / (ξ * x + (1 - ξ))))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(1 + ξ) * x / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  have hne : (1 + ξ) * x / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x ((1 + ξ))).mul hid).div d2
      l2.ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d11 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) (Li₂ (ξ *
        (1 - ξ) / (ξ * x + (1 - ξ))) * (-(ξ / (ξ * x + (1 - ξ))))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |ξ * (1 - ξ) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : ξ * (1 - ξ) / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x (ξ)).mul (hasDerivAt_const x ((1 -
      ξ)))).div d2 l2.ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d12 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((1 - ξ - x) / (ξ * x + (1 - ξ)))) (Li₂ ((1 - ξ - x) / (ξ * x +
        (1 - ξ))) * ((-1 / (1 - ξ - x)) - (ξ / (ξ * x + (1 - ξ))))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(1 - ξ - x) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) +
        (by positivity : (0 : ℝ) < x * (1 - ξ - x))
  have hne : (1 - ξ - x) / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (d1.div d2 l2.ne')).congr_deriv ?_
  field_simp

theorem i5C1T_d13 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))))) (Li₂ (-(ξ *
        (1 - ξ - x) / (ξ * x + (1 - ξ)))) * ((-1 / (1 - ξ - x)) - (ξ / (ξ * x + (1 - ξ))))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < x ^ 2) +
        2 * (by positivity : (0 : ℝ) < x * (1 - ξ - x)) + (by positivity : (0 : ℝ) <
        (1 - ξ - x) ^ 2)
  have hne : -(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ))) ≠ 0 := neg_ne_zero.mpr (by positivity)
  refine ((hasDerivAt_Li₃ hlt hne).comp x ((((hasDerivAt_const x (ξ)).mul d1).div d2
      l2.ne').neg)).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d14 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((1 - ξ) * (1 - x) / (ξ * x + (1 - ξ)))) (Li₂ ((1 - ξ) *
        (1 - x) / (ξ * x + (1 - ξ))) * (-(ξ / (ξ * x + (1 - ξ))) + (-1 / (1 - x)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(1 - ξ) * (1 - x) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x)
  have hne : (1 - ξ) * (1 - x) / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x ((1 - ξ))).mul d3).div d2
      l2.ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d15 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ))) (Li₂ ((ξ * x + (1 - ξ) ^ 2) / (1 -
        ξ)) * ((ξ / (ξ * x + (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(ξ * x + (1 - ξ) ^ 2) / (1 - ξ)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * (1 - ξ - x))
  have hne : (ξ * x + (1 - ξ) ^ 2) / (1 - ξ) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (d4.div (hasDerivAt_const x ((1 - ξ)))
      hy.ne')).congr_deriv ?_
  field_simp; ring

theorem i5C1T_d16 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)))) (Li₂ ((ξ * x +
        (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) * (-(ξ / (ξ * x + (1 - ξ))) +
        (ξ / (ξ * x + (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x))
  have hne : (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (d4.div d2 l2.ne')).congr_deriv ?_
  field_simp; ring

theorem i5C1T_d17 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2))) (Li₂ ((ξ *
        x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)) * (-(ξ / (ξ * x + (1 - ξ) ^ 2)) +
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ ^ 2 * x) + (by positivity : (0 : ℝ) < ξ * x *
        (1 - ξ - x))
  have hne : (ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (d5.div d4 l4.ne')).congr_deriv ?_
  field_simp; ring

theorem i5C1T_d18 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (ξ * x / (ξ * x + (1 - ξ)))) (Li₂ (ξ * x / (ξ * x + (1 - ξ))) *
        ((1 / x) - (ξ / (ξ * x + (1 - ξ))))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |ξ * x / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x) + (by positivity : (0 : ℝ) < (1 - ξ - x))
  have hne : ξ * x / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x (ξ)).mul hid).div d2
      l2.ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d19 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ)))) (Li₂ (ξ *
        (1 - ξ - x) / ((1 - ξ) * (1 + ξ))) * ((-1 / (1 - ξ - x)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x (ξ)).mul d1).div
      ((hasDerivAt_const x ((1 - ξ))).mul (hasDerivAt_const x ((1 + ξ))))
      (mul_pos hy h1p).ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d20 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (ξ ^ 2 * (1 - ξ - x) / (ξ * x + (1 - ξ)))) (Li₂ (ξ ^ 2 *
        (1 - ξ - x) / (ξ * x + (1 - ξ))) * ((-1 / (1 - ξ - x)) - (ξ / (ξ * x + (1 - ξ))))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |ξ ^ 2 * (1 - ξ - x) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ ^ 2 * x) + 3 *
        (by positivity : (0 : ℝ) < ξ * x ^ 2) + 5 * (by positivity : (0 : ℝ) < ξ * x *
        (1 - ξ - x)) + 2 * (by positivity : (0 : ℝ) < ξ * (1 - ξ - x) ^ 2) +
        (by positivity : (0 : ℝ) < x ^ 3) + 3 * (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) +
        3 * (by positivity : (0 : ℝ) < x * (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) <
        (1 - ξ - x) ^ 3)
  have hne : ξ ^ 2 * (1 - ξ - x) / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x (ξ ^ 2)).mul d1).div d2
      l2.ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d21 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (Li₂ (ξ *
        x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2)) * (2 * (1 / x) - (ξ * (2 * x) / (ξ * x ^ 2 +
        (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x ^ 2) + 2 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x)) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x (ξ)).mul (hid.pow 2)).div d5
      l5.ne')).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply]; generalize Li₂ (ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2)) =
      L; field_simp; ring

theorem i5C1T_d22 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2))) (Li₂ ((1 - ξ) ^ 2 / (ξ * x +
        (1 - ξ) ^ 2)) * (-(ξ / (ξ * x + (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x)
  have hne : (1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x ((hasDerivAt_const x ((1 - ξ) ^ 2)).div d4
      l4.ne')).congr_deriv ?_
  field_simp; ring

theorem i5C1T_d23 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((1 - ξ - x) / ((1 - ξ) * (1 + ξ) * (1 - x)))) (Li₂ ((1 - ξ -
        x) / ((1 - ξ) * (1 + ξ) * (1 - x))) * ((-1 / (1 - ξ - x)) - (-1 / (1 - x)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(1 - ξ - x) / ((1 - ξ) * (1 + ξ) * (1 - x))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ ^ 2 * x) +
        (by positivity : (0 : ℝ) < ξ ^ 2 * (1 - ξ - x)) + (by positivity : (0 : ℝ) < ξ * x ^ 2) +
        2 * (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x) ^ 2)
  have hne : (1 - ξ - x) / ((1 - ξ) * (1 + ξ) * (1 - x)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (d1.div (((hasDerivAt_const x ((1 - ξ))).mul
      (hasDerivAt_const x ((1 + ξ)))).mul d3) (mul_pos (mul_pos hy h1p) l3).ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d24 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ))))) (Li₂ (ξ * x *
        (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))) * ((1 / x) + (-1 / (1 - ξ - x)) -
        (ξ / (ξ * x + (1 - ξ))))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ)))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x ^ 2) + 2 *
        (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) + 3 *
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  have hne : ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ))) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x ((((hasDerivAt_const x (ξ)).mul hid).mul d1).div
      ((hasDerivAt_const x ((1 - ξ))).mul d2) (mul_pos hy l2).ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d25 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x)))) (Li₂ (ξ *
        (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))) * ((ξ / (ξ * x + (1 - ξ))) -
        (-1 / (1 - x)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < (1 - ξ - x))
  have hne : ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x (ξ)).mul d2).div
      (((hasDerivAt_const x ((1 - ξ))).mul (hasDerivAt_const x ((1 + ξ)))).mul d3)
      (mul_pos (mul_pos hy h1p) l3).ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d26 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (Li₂ (x *
        (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) * ((1 / x) + (ξ / (ξ * x + (1 - ξ))) -
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 2)
  have hne : x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x ((hid.mul d2).div d5 l5.ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; generalize Li₂ (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) =
      L; field_simp

theorem i5C1T_d27 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) (Li₂ (-(ξ * x *
        (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) * ((1 / x) + (-1 / (1 - ξ - x)) -
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) < ξ * x ^ 2) +
        (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) + (by positivity : (0 : ℝ) < ξ *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) + 3 *
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 3 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  have hne : -(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) ≠ 0 :=
      neg_ne_zero.mpr (by positivity)
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((((hasDerivAt_const x (ξ)).mul hid).mul d1).div d5
      l5.ne').neg)).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d28 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) (Li₂ ((1 -
        ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) * ((-1 / (1 - x)) -
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x ^ 2) + (by positivity : (0 : ℝ) < x ^ 3) +
        2 * (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2)
  have hne : (1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x ((1 - ξ) ^ 2)).mul d3).div d5
      l5.ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d29 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)))) (Li₂ ((1 + ξ) *
        (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))) * (-(ξ / (ξ * x + (1 - ξ))) +
        (ξ / (ξ * x + (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ ^ 2 * (1 - ξ - x))
  have hne : (1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)) ≠ 0 := by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x ((1 + ξ))).mul d4).div d2
      l2.ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d30 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ (ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ)) *
        (1 - x)))) (Li₂ (ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ)) * (1 - x))) *
        (-(ξ / (ξ * x + (1 - ξ))) - (-1 / (1 - x)) + (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) x
        := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ)) * (1 - x))| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ * x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < x ^ 2 * (1 - ξ - x)) + 2 * (by positivity : (0 : ℝ) < x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < (1 - ξ - x) ^ 3)
  have hne : ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ)) * (1 - x)) ≠ 0 :=
      by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x (((hasDerivAt_const x (ξ)).mul d5).div
      (((hasDerivAt_const x ((1 - ξ))).mul d2).mul d3) (mul_pos (mul_pos hy l2)
      l3).ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; field_simp; ring

theorem i5C1T_d31 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (fun x => Li₃ ((ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 +
        (1 - ξ) ^ 2))) (Li₂ ((ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 +
        (1 - ξ) ^ 2)) * ((ξ / (ξ * x + (1 - ξ))) + (ξ / (ξ * x + (1 - ξ) ^ 2)) -
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))) x := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have hid : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id' x
  have d1 : HasDerivAt (fun x : ℝ => 1 - ξ - x) (-1) x := by
    simpa using hid.const_sub (1 - ξ)
  have d2 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ)) ξ x := by
    simpa using (hid.const_mul ξ).add_const (1 - ξ)
  have d3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using hid.const_sub 1
  have d4 : HasDerivAt (fun x : ℝ => ξ * x + (1 - ξ) ^ 2) ξ x := by
    simpa using (hid.const_mul ξ).add_const ((1 - ξ) ^ 2)
  have d5 : HasDerivAt (fun x : ℝ => ξ * x ^ 2 + (1 - ξ) ^ 2) (ξ * (2 * x)) x := by
    simpa using ((hid.pow 2).const_mul ξ).add_const ((1 - ξ) ^ 2)
  have hlt : |(ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2)| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) < ξ ^ 2 * x * (1 - ξ - x)) +
        (by positivity : (0 : ℝ) < ξ ^ 2 * (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < ξ * x *
        (1 - ξ - x) ^ 2) + (by positivity : (0 : ℝ) < ξ * (1 - ξ - x) ^ 3)
  have hne : (ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2) ≠ 0 :=
      by positivity
  refine ((hasDerivAt_Li₃ hlt hne).comp x ((d2.mul d4).div d5 l5.ne')).congr_deriv ?_
  simp only [Pi.mul_apply]; generalize Li₂ ((ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ *
      x ^ 2 + (1 - ξ) ^ 2)) = L; field_simp

theorem i5C1F_0 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ ((1 - x)) = π ^ 2 / 6 - Li₂ (x) - (log (1 - x)) * (log x) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have e1 : 1 - ((1 - x)) = x := by field_simp; ring
  have ev : log ((1 - x)) = log (1 - x) := by
    rfl
  have ew : log (x) = log x := by
    rfl
  have hle : (1 - x) ≤ 1 := by
    linear_combination (by positivity : (0 : ℝ) ≤ x)
  have h := Li₂_add_Li₂_one_sub (x := (1 - x)) (by positivity) hle
  rw [e1, ev, ew] at h
  linarith

theorem i5C1F_3 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ ((1 - ξ - x) / (1 - ξ)) = π ^ 2 / 6 - Li₂ (x / (1 - ξ)) -
        (-log (1 - ξ) + log (1 - ξ - x)) * (-log (1 - ξ) + log x) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have e1 : 1 - ((1 - ξ - x) / (1 - ξ)) = x / (1 - ξ) := by field_simp; ring
  have ev : log ((1 - ξ - x) / (1 - ξ)) = -log (1 - ξ) + log (1 - ξ - x) := by
    rw [log_div (by positivity) (by positivity)]; ring
  have ew : log (x / (1 - ξ)) = -log (1 - ξ) + log x := by
    rw [log_div (by positivity) (by positivity)]; ring
  have hle : (1 - ξ - x) / (1 - ξ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) ≤ x)
  have h := Li₂_add_Li₂_one_sub (x := (1 - ξ - x) / (1 - ξ)) (by positivity) hle
  rw [e1, ev, ew] at h
  linarith

theorem i5C1F_4 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ ((1 - ξ - x) / (ξ * x + (1 - ξ))) = π ^ 2 / 6 - Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) -
        (log (1 - ξ - x) - log (ξ * x + (1 - ξ))) * (log (1 + ξ) + log x -
        log (ξ * x + (1 - ξ))) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have e1 : 1 - ((1 - ξ - x) / (ξ * x + (1 - ξ))) = (1 + ξ) * x / (ξ * x + (1 - ξ)) :=
      by field_simp; ring
  have ev : log ((1 - ξ - x) / (ξ * x + (1 - ξ))) = log (1 - ξ - x) - log (ξ * x + (1 - ξ)) := by
    rw [log_div (by positivity) (by positivity)]
  have ew : log ((1 + ξ) * x / (ξ * x + (1 - ξ))) = log (1 + ξ) + log x -
      log (ξ * x + (1 - ξ)) := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  have hle : (1 - ξ - x) / (ξ * x + (1 - ξ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linear_combination 2 * (by positivity : (0 : ℝ) ≤ ξ * x) + (by positivity : (0 : ℝ) ≤ x ^ 2) +
        (by positivity : (0 : ℝ) ≤ x * (1 - ξ - x))
  have h := Li₂_add_Li₂_one_sub (x := (1 - ξ - x) / (ξ * x + (1 - ξ))) (by positivity) hle
  rw [e1, ev, ew] at h
  linarith

theorem i5C1F_5 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ ((1 - ξ) * (1 - x) / (ξ * x + (1 - ξ))) = π ^ 2 / 6 - Li₂ (x / (ξ * x + (1 - ξ))) -
        (log (1 - ξ) - log (ξ * x + (1 - ξ)) + log (1 - x)) * (log x - log (ξ * x + (1 - ξ))) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have e1 : 1 - ((1 - ξ) * (1 - x) / (ξ * x + (1 - ξ))) = x / (ξ * x + (1 - ξ)) :=
      by field_simp; ring
  have ev : log ((1 - ξ) * (1 - x) / (ξ * x + (1 - ξ))) = log (1 - ξ) - log (ξ * x + (1 - ξ)) +
      log (1 - x) := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]; ring
  have ew : log (x / (ξ * x + (1 - ξ))) = log x - log (ξ * x + (1 - ξ)) := by
    rw [log_div (by positivity) (by positivity)]
  have hle : (1 - ξ) * (1 - x) / (ξ * x + (1 - ξ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) ≤ x)
  have h := Li₂_add_Li₂_one_sub (x := (1 - ξ) * (1 - x) / (ξ * x + (1 - ξ))) (by positivity) hle
  rw [e1, ev, ew] at h
  linarith

theorem i5C1F_8 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ ((ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)) = π ^ 2 / 6 -
        Li₂ (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) - (-log (ξ * x + (1 - ξ) ^ 2) +
        log (ξ * x ^ 2 + (1 - ξ) ^ 2)) * (log ξ + log x + log (1 - x) -
        log (ξ * x + (1 - ξ) ^ 2)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have e1 : 1 - ((ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)) = ξ * x *
      (1 - x) / (ξ * x + (1 - ξ) ^ 2) := by field_simp; ring
  have ev : log ((ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)) = -log (ξ * x + (1 - ξ) ^ 2) +
      log (ξ * x ^ 2 + (1 - ξ) ^ 2) := by
    rw [log_div (by positivity) (by positivity)]; ring
  have ew : log (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) = log ξ + log x + log (1 - x) -
      log (ξ * x + (1 - ξ) ^ 2) := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_mul (by positivity) (by positivity)]
  have hle : (ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) ≤ ξ ^ 2 * x) + (by positivity : (0 : ℝ) ≤ ξ * x *
        (1 - ξ - x))
  have h := Li₂_add_Li₂_one_sub (x := (ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x +
      (1 - ξ) ^ 2)) (by positivity) hle
  rw [e1, ev, ew] at h
  linarith

theorem i5C1F_13 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ ((1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2)) = π ^ 2 / 6 - Li₂ (ξ * x / (ξ * x + (1 - ξ) ^ 2)) -
        (2 * log (1 - ξ) - log (ξ * x + (1 - ξ) ^ 2)) * (log ξ + log x -
        log (ξ * x + (1 - ξ) ^ 2)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have e1 : 1 - ((1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2)) = ξ * x / (ξ * x + (1 - ξ) ^ 2) :=
      by field_simp; ring
  have ev : log ((1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2)) = 2 * log (1 - ξ) -
      log (ξ * x + (1 - ξ) ^ 2) := by
    rw [log_div (by positivity) (by positivity), log_pow]; ring
  have ew : log (ξ * x / (ξ * x + (1 - ξ) ^ 2)) = log ξ + log x - log (ξ * x + (1 - ξ) ^ 2) := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  have hle : (1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) ≤ ξ * x)
  have h := Li₂_add_Li₂_one_sub (x := (1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2)) (by positivity) hle
  rw [e1, ev, ew] at h
  linarith

theorem i5C1F_19 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    Li₂ ((1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) = π ^ 2 / 6 -
        Li₂ (x * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) -
        (2 * log (1 - ξ) + log (1 - x) - log (ξ * x ^ 2 + (1 - ξ) ^ 2)) *
        (log x + log (ξ * x + (1 - ξ) ^ 2) - log (ξ * x ^ 2 + (1 - ξ) ^ 2)) := by
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  have e1 : 1 - ((1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) = x *
      (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2) := by field_simp; ring
  have ev : log ((1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) = 2 * log (1 - ξ) +
      log (1 - x) - log (ξ * x ^ 2 + (1 - ξ) ^ 2) := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
        log_pow]; ring
  have ew : log (x * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) = log x +
      log (ξ * x + (1 - ξ) ^ 2) - log (ξ * x ^ 2 + (1 - ξ) ^ 2) := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  have hle : (1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linear_combination (by positivity : (0 : ℝ) ≤ ξ * x ^ 2) + (by positivity : (0 : ℝ) ≤ x ^ 3) +
        2 * (by positivity : (0 : ℝ) ≤ x ^ 2 * (1 - ξ - x)) + (by positivity : (0 : ℝ) ≤ x *
        (1 - ξ - x) ^ 2)
  have h := Li₂_add_Li₂_one_sub (x := (1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 +
      (1 - ξ) ^ 2)) (by positivity) hle
  rw [e1, ev, ew] at h
  linarith

end QED.ThreeLoopD
