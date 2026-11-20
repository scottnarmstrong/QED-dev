/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKFormOSXInt
public import QED.ChainProof.SetCKAsmRho
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, closed forms: the density of the outer self-energy group

Helper level (no frozen statement). The Stieltjes density of the outer self-energy group
(`scOutS`, weight `H_oS = scOutSH`) is the weight-one function (`rhoScOutS`)

`ρ_oS = a + b log X + c log(1 - X) + d log(2 - X)`,
`a = (29X³ - 81X² + 74X - 20)/(12(X - 1)²)`, `b = -X(3X⁴ - 6X³ - 5X² + 10X - 6)/(6(X - 1)⁴)`,
`c = -(X - 1)(4X² + 3X + 2)/(6X)`, `d = X²(4X⁴ - 17X³ + 27X² - 20X + 10)/(6(X - 1)⁴)`.

This file proves **`setCKRhoH_rhoScOutS`**: `H_ρ(X) = ∫₀^X ρ_oS Q = K(X)` on `(0, 1)`, with
`K = E + X³(1 - X)/2` (`formOSK`, `formOSK_eq`) and `E` the closed form `formOSE` of the kernel
part. Proof: `K` has derivative `ρ_oS Q` on `(0, 1)` (`hasDerivAt_formOSK`), is continuous on
`[0, X]` and vanishes at `0` (the `log X` term carries `X⁴`); `ρ_oS Q` agrees on `[0, 1)` with
a function continuous there (`rhoScOutSQ`).
-/

@[expose] public section

open Real Set MeasureTheory

namespace QED.ChainProof.SetCK

/-- **The Stieltjes density of the outer self-energy group** `ρ_oS`. -/
noncomputable def rhoScOutS (X : ℝ) : ℝ :=
  (29 * X ^ 3 - 81 * X ^ 2 + 74 * X - 20) / (12 * (X - 1) ^ 2) -
    X * (3 * X ^ 4 - 6 * X ^ 3 - 5 * X ^ 2 + 10 * X - 6) / (6 * (X - 1) ^ 4) * log X -
    (X - 1) * (4 * X ^ 2 + 3 * X + 2) / (6 * X) * log (1 - X) +
    X ^ 2 * (4 * X ^ 4 - 17 * X ^ 3 + 27 * X ^ 2 - 20 * X + 10) / (6 * (X - 1) ^ 4) * log (2 - X)

/-- `ρ_oS Q` in a form continuous on `[0, 1)`. -/
noncomputable def rhoScOutSQ (X : ℝ) : ℝ :=
  (29 * X ^ 3 - 81 * X ^ 2 + 74 * X - 20) / (12 * (X - 1) ^ 2) * (X ^ 2 / (1 - X)) -
    X ^ 2 * (3 * X ^ 4 - 6 * X ^ 3 - 5 * X ^ 2 + 10 * X - 6) / (6 * (X - 1) ^ 4 * (1 - X)) *
      (X * log X) +
    X * (4 * X ^ 2 + 3 * X + 2) / 6 * log (1 - X) +
    X ^ 2 * (4 * X ^ 4 - 17 * X ^ 3 + 27 * X ^ 2 - 20 * X + 10) / (6 * (X - 1) ^ 4) *
      (X ^ 2 / (1 - X)) * log (2 - X)

/-- **The closed form of `H_oS`**: `K = E + X³(1 - X)/2`, expanded. -/
noncomputable def formOSK (X : ℝ) : ℝ :=
  (3 * X ^ 4 + (-4) * X ^ 5 + 1 * X ^ 6 + 2 * X ^ 7) / (12 * (-1 + X) ^ 4) * log X +
    (1 + 2 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4) / 12 * log (1 - X) +
    (2 * X ^ 5 + (-3) * X ^ 6 + 3 * X ^ 7 + (-1) * X ^ 8) / (6 * (-1 + X) ^ 4) * log (2 - X) +
    ((-6) * X + 3 * X ^ 2 + 73 * X ^ 3 + (-130) * X ^ 4 + 36 * X ^ 5) / (72 * (-1 + X)) +
    ((1 / 2) * X ^ 3 + (-1 / 2) * X ^ 4)

theorem formOSK_eq (X : ℝ) : formOSK X = formOSE X + X ^ 3 * (1 - X) / 2 := by
  unfold formOSK formOSE
  ring

theorem rhoScOutS_mul_setCKQ {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    rhoScOutS X * setCKQ X = rhoScOutSQ X := by
  have := hX.1.ne'
  have : 1 - X ≠ 0 := by linarith [hX.2]
  have : X - 1 ≠ 0 := by linarith [hX.2]
  unfold rhoScOutS rhoScOutSQ setCKQ
  field_simp
  ring

theorem rhoScOutS_mul_setCKQ_zero : rhoScOutS 0 * setCKQ 0 = rhoScOutSQ 0 := by
  simp [rhoScOutSQ, setCKQ]

/-- **`K' = ρ_oS Q`** on `(0, 1)`. -/
theorem hasDerivAt_formOSK {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt formOSK (rhoScOutSQ X) X := by
  have hX0 : X ≠ 0 := hX.1.ne'
  have hm : -1 + X ≠ 0 := by linarith [hX.2]
  have h1 : 1 - X ≠ 0 := by linarith [hX.2]
  have h2 : 2 - X ≠ 0 := by linarith [hX.2]
  have h := (((((((((((hasDerivAt_pow 4 X).const_mul 3).add ((hasDerivAt_pow 5 X).const_mul
      (-4))).add ((hasDerivAt_pow 6 X).const_mul 1)).add ((hasDerivAt_pow 7 X).const_mul 2)).div
      ((((hasDerivAt_id' X).const_add (-1)).pow 4).const_mul 12) (mul_ne_zero (by norm_num)
      (pow_ne_zero _ hm))).mul ((hasDerivAt_id' X).log hX0)).add ((((((hasDerivAt_const X (1 :
      ℝ)).add ((hasDerivAt_pow 2 X).const_mul 2)).add ((hasDerivAt_pow 3 X).const_mul 2)).add
      ((hasDerivAt_pow 4 X).const_mul 2)).div (hasDerivAt_const X (12 : ℝ)) (by norm_num)).mul
      (((hasDerivAt_id' X).const_sub 1).log h1))).add (((((((hasDerivAt_pow 5 X).const_mul 2).add
      ((hasDerivAt_pow 6 X).const_mul (-3))).add ((hasDerivAt_pow 7 X).const_mul 3)).add
      ((hasDerivAt_pow 8 X).const_mul (-1))).div ((((hasDerivAt_id' X).const_add (-1)).pow
      4).const_mul 6) (mul_ne_zero (by norm_num) (pow_ne_zero _ hm))).mul (((hasDerivAt_id'
      X).const_sub 2).log h2))).add (((((((hasDerivAt_id' X).const_mul (-6)).add ((hasDerivAt_pow 2
      X).const_mul 3)).add ((hasDerivAt_pow 3 X).const_mul 73)).add ((hasDerivAt_pow 4 X).const_mul
      (-130))).add ((hasDerivAt_pow 5 X).const_mul 36)).div (((hasDerivAt_id' X).const_add
      (-1)).const_mul 72) (mul_ne_zero (by norm_num) hm))).add (((hasDerivAt_pow 3 X).const_mul (1 /
      2)).add ((hasDerivAt_pow 4 X).const_mul (-1 / 2))))
  refine h.congr_deriv ?_
  have : X - 1 ≠ 0 := by linarith [hX.2]
  unfold rhoScOutSQ
  simp only [Pi.add_apply, Pi.div_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

theorem continuousOn_formOSK {X : ℝ} (hX : X < 1) : ContinuousOn formOSK (Icc 0 X) := by
  have e : formOSK = fun X => (3 * X ^ 3 + (-4) * X ^ 4 + 1 * X ^ 5 + 2 * X ^ 6) /
      (12 * (-1 + X) ^ 4) * (X * log X) +
      (1 + 2 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4) / 12 * log (1 - X) +
      (2 * X ^ 5 + (-3) * X ^ 6 + 3 * X ^ 7 + (-1) * X ^ 8) / (6 * (-1 + X) ^ 4) * log (2 - X) +
      ((-6) * X + 3 * X ^ 2 + 73 * X ^ 3 + (-130) * X ^ 4 + 36 * X ^ 5) / (72 * (-1 + X)) +
      ((1 / 2) * X ^ 3 + (-1 / 2) * X ^ 4) := by
    funext X
    unfold formOSK
    ring
  have hm : ∀ y ∈ Icc (0 : ℝ) X, -1 + y ≠ 0 := fun y hy => by linarith [hy.2]
  have c1 : ContinuousOn (fun y : ℝ => log (1 - y)) (Icc 0 X) :=
    ContinuousOn.log (by fun_prop) fun y hy => by linarith [hy.2]
  have c2 : ContinuousOn (fun y : ℝ => log (2 - y)) (Icc 0 X) :=
    ContinuousOn.log (by fun_prop) fun y hy => by linarith [hy.2]
  have cl : ContinuousOn (fun y : ℝ => y * log y) (Icc 0 X) := continuous_mul_log.continuousOn
  have d4 : ContinuousOn (fun y : ℝ => 12 * (-1 + y) ^ 4) (Icc 0 X) := by fun_prop
  have d4' : ContinuousOn (fun y : ℝ => 6 * (-1 + y) ^ 4) (Icc 0 X) := by fun_prop
  have d1 : ContinuousOn (fun y : ℝ => 72 * (-1 + y)) (Icc 0 X) := by fun_prop
  rw [e]
  refine ((((ContinuousOn.mul (ContinuousOn.div (by fun_prop) d4 fun y hy => ?_) cl).add
    (ContinuousOn.mul (by fun_prop) c1)).add
    (ContinuousOn.mul (ContinuousOn.div (by fun_prop) d4' fun y hy => ?_) c2)).add
    (ContinuousOn.div (by fun_prop) d1 fun y hy => ?_)).add (by fun_prop)
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (hm y hy))
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (hm y hy))
  · exact mul_ne_zero (by norm_num) (hm y hy)

theorem formOSK_zero : formOSK 0 = 0 := by
  simp [formOSK]

theorem continuousOn_rhoScOutSQ {X : ℝ} (hX : X < 1) : ContinuousOn rhoScOutSQ (Icc 0 X) := by
  have hm : ∀ y ∈ Icc (0 : ℝ) X, y - 1 ≠ 0 := fun y hy => by linarith [hy.2]
  have hm' : ∀ y ∈ Icc (0 : ℝ) X, 1 - y ≠ 0 := fun y hy => by linarith [hy.2]
  have c1 : ContinuousOn (fun y : ℝ => log (1 - y)) (Icc 0 X) :=
    ContinuousOn.log (by fun_prop) hm'
  have c2 : ContinuousOn (fun y : ℝ => log (2 - y)) (Icc 0 X) :=
    ContinuousOn.log (by fun_prop) fun y hy => by linarith [hy.2]
  have cl : ContinuousOn (fun y : ℝ => y * log y) (Icc 0 X) := continuous_mul_log.continuousOn
  have q : ContinuousOn (fun y : ℝ => y ^ 2 / (1 - y)) (Icc 0 X) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) hm'
  unfold rhoScOutSQ
  refine (((ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => ?_) q).sub
    (ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy => ?_) cl)).add
    (ContinuousOn.mul (by fun_prop) c1)).add
    (ContinuousOn.mul (ContinuousOn.mul (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun y hy => ?_) q) c2)
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (hm y hy))
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (hm y hy))) (hm' y hy)
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (hm y hy))

/-- **`H_ρ(X) = ∫₀^X ρ_oS Q = K(X)`** for `X ∈ (0, 1)`. -/
theorem setCKRhoH_rhoScOutS {X : ℝ} (hX : X ∈ Ioo (0 : ℝ) 1) :
    setCKRhoH rhoScOutS X = formOSK X := by
  unfold setCKRhoH
  have he : EqOn (fun x => rhoScOutS x * setCKQ x) rhoScOutSQ (uIcc 0 X) := fun x hx => by
    rw [uIcc_of_le hX.1.le] at hx
    rcases hx.1.eq_or_lt with h | h
    · rw [← h]
      exact rhoScOutS_mul_setCKQ_zero
    · exact rhoScOutS_mul_setCKQ ⟨h, hx.2.trans_lt hX.2⟩
  rw [intervalIntegral.integral_congr he,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX.1.le (continuousOn_formOSK hX.2)
      (fun x hx => hasDerivAt_formOSK ⟨hx.1, hx.2.trans hX.2⟩)
      (ContinuousOn.intervalIntegrable_of_Icc hX.1.le (continuousOn_rhoScOutSQ hX.2)),
    formOSK_zero, sub_zero]

end QED.ChainProof.SetCK

end
