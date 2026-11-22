/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondAsm
public import QED.ThreeLoopD.SetDMastersI12RSecondEVal
public import QED.ThreeLoopD.SetDMastersI12RSecondT2

/-!
# Set (d), master `I₁₂`: the second Taylor coefficient of the remainder

`QED.ThreeLoopD.iteratedDeriv_two_i12Rest_of` reduces `r2` to the closed form of `E`
(`QED.ThreeLoopD.integral_i12REx_eq_i12REcl`) and the value of `T_A''(0) + T_B''(0)`
(`QED.ThreeLoopD.deriv_deriv_i12TA_add_deriv_deriv_i12TB`).

## Main results

* `QED.ThreeLoopD.iteratedDeriv_two_i12Rest`.
-/

@[expose] public section

namespace QED.ThreeLoopD

/-- **The second Taylor coefficient of the remainder**: `i12Rest''(0) / 2! = r2`. -/
theorem iteratedDeriv_two_i12Rest :
    iteratedDeriv 2 i12Rest 0 / (2 : ℕ).factorial = i12RestR2 :=
  iteratedDeriv_two_i12Rest_of integral_i12REx_eq_i12REcl
    deriv_deriv_i12TA_add_deriv_deriv_i12TB

end QED.ThreeLoopD
