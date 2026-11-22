/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RSecondD
public import QED.ThreeLoopD.SetDMastersI12RSecondEPrim

/-!
# Set (d), master `I₁₂`: the value of `R₁'(0) + B₃ᵇ`

The closed form `∫₀¹ i12REx (y (1 - y)) x dx = QED.ThreeLoopD.i12REcl y` on `(0, 1/2]`
(`QED.ThreeLoopD.integral_i12REx_eq`) is the hypothesis of
`QED.ThreeLoopD.deriv_i12R1_add_i12B3bad_eq_of_E`, which therefore holds unconditionally:

  `R₁'(0) + B₃ᵇ = 1475/36 - 3π²/4 + 6ℓ - 6ℓ² + π²ℓ + 2ℓ³ - 21 ζ(3)`,   `ℓ = log 2`.

## Main results

* `QED.ThreeLoopD.integral_i12REx_eq_i12REcl`.
* `QED.ThreeLoopD.deriv_i12R1_add_i12B3bad_eq`.
-/

@[expose] public section

open Real Set MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- **`E` in closed form** on `(0, 1/2]`. -/
theorem integral_i12REx_eq_i12REcl :
    ∀ y ∈ Ioc (0 : ℝ) (1 / 2), ∫ x in Ioo (0 : ℝ) 1, i12REx (y * (1 - y)) x = i12REcl y :=
  fun y hy => by
    rw [integral_i12REx_eq ⟨hy.1, by linarith [hy.2]⟩, i12REcl]

/-- **`R₁'(0) + B₃ᵇ` in closed form.** -/
theorem deriv_i12R1_add_i12B3bad_eq :
    deriv i12R1 0 + ((∫ x in Ioo (0 : ℝ) 1, i12B3bad x : ℝ) : ℂ) =
      ((1475 / 36 - 3 * π ^ 2 / 4 + 6 * log 2 - 6 * log 2 ^ 2 + π ^ 2 * log 2 +
        2 * log 2 ^ 3 - 21 * zeta3 : ℝ) : ℂ) :=
  deriv_i12R1_add_i12B3bad_eq_of_E integral_i12REx_eq_i12REcl

end QED.ThreeLoopD
