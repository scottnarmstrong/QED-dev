/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1PBa
public import QED.ThreeLoopD.SetDMastersI5C1IdA
public import QED.ThreeLoopD.SetDMastersI5C1IdB
public import QED.ThreeLoopD.SetDMastersI5C1IdC
public import QED.ThreeLoopD.SetDMastersI5C1IdD

/-!
# Set (d), master `I₅`: the primitive of `I(x)` in parts (second half)

The primitive `P(x)` of the integrand `I(x)` of `t K₁(t) = ∫₀^{1-ξ} I(x) dx` is a combination of
products of three logarithms of the letters, dilogarithms of the basis times logarithms, and
thirty-two trilogarithms. This file continues `QED.ThreeLoopD.SetDMastersI5C1PBa` with the parts
`QED.ThreeLoopD.i5C1Q17`, ..., `QED.ThreeLoopD.i5C1Q41` and the derivatives of the parts up to
`QED.ThreeLoopD.i5C1Q39` in letter form; for the trilogarithmic parts the dilogarithms
`Li₂ (h)` of the arguments are reduced to the basis by the identities of
`QED.ThreeLoopD.SetDMastersI5C1IdA`, ... The last two parts (single trilogarithms with long
reductions) are differentiated directly where the primitive is assembled.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i5C1Q17`, ..., `QED.ThreeLoopD.hasDerivAt_i5C1Q39`.
-/

@[expose] public section

open Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- Part 17 of the primitive of `I(x)`. -/
noncomputable def i5C1Q17 (ξ x : ℝ) : ℝ :=
  2 * (Li₂ (-(ξ * x / (1 - ξ))) * log (ξ * x + (1 - ξ) ^ 2)) + 8 *
      (Li₂ (-(ξ * x / (1 - ξ))) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-3) *
      (Li₂ (-(ξ * x / (1 - ξ))) * log ξ) + (-9) * (Li₂ (-(ξ * x / (1 - ξ))) * log (1 - ξ)) + 3 *
      (Li₂ (-(ξ * x / (1 - ξ))) * log (1 + ξ)) + (-2) * (Li₂ (x / (ξ * x + (1 - ξ))) *
      log (1 - ξ - x))

theorem hasDerivAt_i5C1Q17 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q17 ξ) (2 * Li₂ (-(ξ * x / (1 - ξ))) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 8 *
        Li₂ (-(ξ * x / (1 - ξ))) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 2 *
        Li₂ (x / (ξ * x + (1 - ξ))) * (-1 / (1 - ξ - x)) - 2 * log (1 - ξ - x) *
        log (ξ * x + (1 - ξ)) * (1 / x) + 2 * log (1 - ξ - x) * log (ξ * x + (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) + 2 * log (1 - ξ - x) * log (1 - x) * (1 / x) - 2 *
        log (1 - ξ - x) * log (1 - x) * (ξ / (ξ * x + (1 - ξ))) + 2 * log (1 - ξ - x) *
        log (1 - ξ) * (1 / x) - 2 * log (1 - ξ - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - 2 *
        log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) * (1 / x) - 8 * log (ξ * x + (1 - ξ)) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) + 3 * log (ξ * x + (1 - ξ)) * log ξ * (1 / x) + 9 *
        log (ξ * x + (1 - ξ)) * log (1 - ξ) * (1 / x) - 3 * log (ξ * x + (1 - ξ)) * log (1 + ξ) *
        (1 / x) + 2 * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (1 / x) + 8 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) * (1 / x) - 3 * log ξ * log (1 - ξ) * (1 / x) -
        9 * log (1 - ξ) ^ 2 * (1 / x) + 3 * log (1 - ξ) * log (1 + ξ) * (1 / x)) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q17 ξ) ((((((((i5C1B_d4 hξ hx hxy).mul
      (i5C1L_d4 hξ hx)).const_mul 2).add (((i5C1B_d4 hξ hx hxy).mul (i5C1L_d5 hξ)).const_mul
      8)).add (((i5C1B_d4 hξ hx hxy).mul (hasDerivAt_const x (log ξ))).const_mul (-3))).add
      (((i5C1B_d4 hξ hx hxy).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul (-9))).add
      (((i5C1B_d4 hξ hx hxy).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul 3)).add
      (((i5C1B_d5 hξ hx hxy).mul (i5C1L_d1 hxy)).const_mul (-2))) ?_
  ring

/-- Part 18 of the primitive of `I(x)`. -/
noncomputable def i5C1Q18 (ξ x : ℝ) : ℝ :=
  (-2) * (Li₂ (x / (ξ * x + (1 - ξ))) * log (ξ * x + (1 - ξ))) + 2 *
      (Li₂ (x / (ξ * x + (1 - ξ))) * log (1 - x)) + 2 * (Li₂ (x / (ξ * x + (1 - ξ))) *
      log (ξ * x + (1 - ξ) ^ 2)) + 2 * (Li₂ (x / (ξ * x + (1 - ξ))) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 3 * (Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * log x) + (-1) *
      (Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * log (1 - x))

theorem hasDerivAt_i5C1Q18 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q18 ξ) (-2 * Li₂ (x / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) + 2 *
        Li₂ (x / (ξ * x + (1 - ξ))) * (-1 / (1 - x)) + 2 * Li₂ (x / (ξ * x + (1 - ξ))) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * Li₂ (x / (ξ * x + (1 - ξ))) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 3 * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) *
        (1 / x) - Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (-1 / (1 - x)) - 6 * log x *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) + 12 * log x * log (1 - ξ) * (1 / x) - 2 *
        log (ξ * x + (1 - ξ)) ^ 2 * (1 / x) + 2 * log (ξ * x + (1 - ξ)) ^ 2 *
        (ξ / (ξ * x + (1 - ξ))) + 4 * log (ξ * x + (1 - ξ)) * log (1 - x) * (1 / x) - 4 *
        log (ξ * x + (1 - ξ)) * log (1 - x) * (ξ / (ξ * x + (1 - ξ))) + 2 * log (ξ * x + (1 - ξ)) *
        log (ξ * x + (1 - ξ) ^ 2) * (1 / x) - 2 * log (ξ * x + (1 - ξ)) *
        log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) + 2 * log (ξ * x + (1 - ξ)) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) - 2 * log (ξ * x + (1 - ξ)) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) + 2 * log (ξ * x + (1 - ξ)) *
        log (1 - ξ) * (1 / x) - 2 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) -
        2 * log (1 - x) ^ 2 * (1 / x) + 2 * log (1 - x) ^ 2 * (ξ / (ξ * x + (1 - ξ))) - 2 *
        log (1 - x) * log (ξ * x + (1 - ξ) ^ 2) * (1 / x) + 2 * log (1 - x) *
        log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) + 2 * log (1 - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) - 6 * log (1 - x) * log (1 - ξ) *
        (1 / x) + 2 * log (1 - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (1 / x) + 2 * log (ξ * x + (1 - ξ) ^ 2) *
        log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - 2 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) *
        (1 / x) + 2 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ)))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q18 ξ) ((((((((i5C1B_d5 hξ hx hxy).mul
      (i5C1L_d2 hξ hx)).const_mul (-2)).add (((i5C1B_d5 hξ hx hxy).mul (i5C1L_d3 hξ hxy)).const_mul
      2)).add (((i5C1B_d5 hξ hx hxy).mul (i5C1L_d4 hξ hx)).const_mul 2)).add
      (((i5C1B_d5 hξ hx hxy).mul (i5C1L_d5 hξ)).const_mul 2)).add
      (((i5C1B_d6 hξ hx hxy).mul (i5C1L_d0 hx)).const_mul 3)).add
      (((i5C1B_d6 hξ hx hxy).mul (i5C1L_d3 hξ hxy)).const_mul (-1))) ?_
  ring

/-- Part 19 of the primitive of `I(x)`. -/
noncomputable def i5C1Q19 (ξ x : ℝ) : ℝ :=
  1 * (Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * log (ξ * x + (1 - ξ) ^ 2)) + 1 *
      (Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * log ξ) + (-4) * (Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) *
      log (1 - ξ)) + 1 * (Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) * log (ξ * x + (1 - ξ))) + (-1) *
      (Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) * log (1 - ξ)) + 1 * (Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) *
      log (1 + ξ))

theorem hasDerivAt_i5C1Q19 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q19 ξ) (Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (ξ / (ξ * x + (1 - ξ) ^ 2)) +
        Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) - log (ξ * x + (1 - ξ)) *
        log (ξ * x + (1 - ξ) ^ 2) * (-1 / (1 - ξ - x)) + log (ξ * x + (1 - ξ)) * log (1 - ξ) *
        (-1 / (1 - ξ - x)) - 2 * log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (1 / x) + 4 * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (1 / x) +
        log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (-1 / (1 - ξ - x)) - log (ξ * x + (1 - ξ) ^ 2) *
        log (1 + ξ) * (-1 / (1 - ξ - x)) - 2 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log ξ * (1 / x) +
        8 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) * (1 / x) + 4 * log ξ * log (1 - ξ) *
        (1 / x) - 16 * log (1 - ξ) ^ 2 * (1 / x) - log (1 - ξ) ^ 2 * (-1 / (1 - ξ - x)) +
        log (1 - ξ) * log (1 + ξ) * (-1 / (1 - ξ - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q19 ξ) ((((((((i5C1B_d6 hξ hx hxy).mul
      (i5C1L_d4 hξ hx)).const_mul 1).add (((i5C1B_d6 hξ hx hxy).mul
      (hasDerivAt_const x (log ξ))).const_mul 1)).add (((i5C1B_d6 hξ hx hxy).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul (-4))).add (((i5C1B_d7 hξ hx hxy).mul
      (i5C1L_d2 hξ hx)).const_mul 1)).add (((i5C1B_d7 hξ hx hxy).mul (hasDerivAt_const x (log (1 -
      ξ)))).const_mul (-1))).add (((i5C1B_d7 hξ hx hxy).mul (hasDerivAt_const x (log (1 +
      ξ)))).const_mul 1)) ?_
  ring

/-- Part 20 of the primitive of `I(x)`. -/
noncomputable def i5C1Q20 (ξ x : ℝ) : ℝ :=
  (-6) * (Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * log x) + 3 * (Li₂ ((1 + ξ) *
      x / (ξ * x + (1 - ξ))) * log (1 - x)) + (-3) * (Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) *
      log ξ) + 12 * (Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * log (1 - ξ)) + (-2) *
      (Li₂ (x / (ξ * x + (1 - ξ) ^ 2)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 4 *
      (Li₂ (x / (ξ * x + (1 - ξ) ^ 2)) * log (1 - ξ))

theorem hasDerivAt_i5C1Q20 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q20 ξ) (-6 * Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (1 / x) + 3 *
        Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (-1 / (1 - x)) - 2 *
        Li₂ (x / (ξ * x + (1 - ξ) ^ 2)) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 6 * log x *
        log (1 - ξ - x) * (1 / x) - 6 * log x * log (1 - ξ - x) * (ξ / (ξ * x + (1 - ξ))) - 6 *
        log x * log (ξ * x + (1 - ξ)) * (1 / x) + 6 * log x * log (ξ * x + (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) - 3 * log (1 - ξ - x) * log (1 - x) * (1 / x) + 3 *
        log (1 - ξ - x) * log (1 - x) * (ξ / (ξ * x + (1 - ξ))) + 2 * log (1 - ξ - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) - 2 * log (1 - ξ - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 3 * log (1 - ξ - x) * log ξ *
        (1 / x) - 3 * log (1 - ξ - x) * log ξ * (ξ / (ξ * x + (1 - ξ))) - 16 * log (1 - ξ - x) *
        log (1 - ξ) * (1 / x) + 12 * log (1 - ξ - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + 4 *
        log (1 - ξ - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 3 * log (ξ * x + (1 - ξ)) *
        log (1 - x) * (1 / x) - 3 * log (ξ * x + (1 - ξ)) * log (1 - x) * (ξ / (ξ * x + (1 - ξ))) -
        3 * log (ξ * x + (1 - ξ)) * log ξ * (1 / x) + 3 * log (ξ * x + (1 - ξ)) * log ξ *
        (ξ / (ξ * x + (1 - ξ))) + 12 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (1 / x) - 12 *
        log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) + 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ) ^ 2)) +
        4 * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (1 / x) - 4 * log (ξ * x + (1 - ξ) ^ 2) *
        log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        log (1 - ξ) * (1 / x) - 2 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 4 * log (1 - ξ) ^ 2 * (1 / x) + 4 * log (1 - ξ) ^ 2 *
        (ξ / (ξ * x + (1 - ξ) ^ 2))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q20 ξ) ((((((((i5C1B_d8 hξ hx hxy).mul
      (i5C1L_d0 hx)).const_mul (-6)).add (((i5C1B_d8 hξ hx hxy).mul (i5C1L_d3 hξ hxy)).const_mul
      3)).add (((i5C1B_d8 hξ hx hxy).mul (hasDerivAt_const x (log ξ))).const_mul (-3))).add
      (((i5C1B_d8 hξ hx hxy).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul 12)).add
      (((i5C1B_d9 hξ hx hxy).mul (i5C1L_d5 hξ)).const_mul (-2))).add
      (((i5C1B_d9 hξ hx hxy).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul 4)) ?_
  ring

/-- Part 21 of the primitive of `I(x)`. -/
noncomputable def i5C1Q21 (ξ x : ℝ) : ℝ :=
  1 * (Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * log (1 - ξ - x)) + 2 *
      (Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * log (ξ * x + (1 - ξ))) + (-2) *
      (Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * log (1 - x)) + (-2) *
      (Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * log (ξ * x + (1 - ξ) ^ 2)) + 2 *
      (Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-3) *
      (Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * log (1 - ξ))

theorem hasDerivAt_i5C1Q21 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q21 ξ) (Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * (-1 / (1 - ξ - x)) + 2 *
        Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) - 2 *
        Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * (-1 / (1 - x)) - 2 *
        Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 *
        Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) -
        log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) + log (1 - ξ - x) *
        log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) - 2 * log (ξ * x + (1 - ξ)) ^ 2 *
        (ξ / (ξ * x + (1 - ξ))) + 2 * log (ξ * x + (1 - ξ)) * log (1 - x) *
        (ξ / (ξ * x + (1 - ξ))) + 4 * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ))) - 2 * log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ))) + 3 * log (ξ * x + (1 - ξ)) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ))) - 2 * log (1 - x) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ))) - 2 * log (ξ * x + (1 - ξ) ^ 2) ^ 2 * (ξ / (ξ * x + (1 - ξ))) + 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) - 3 *
        log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ)))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q21 ξ) ((((((((i5C1B_d10 hξ hx hxy).mul
      (i5C1L_d1 hxy)).const_mul 1).add (((i5C1B_d10 hξ hx hxy).mul (i5C1L_d2 hξ hx)).const_mul
      2)).add (((i5C1B_d10 hξ hx hxy).mul (i5C1L_d3 hξ hxy)).const_mul (-2))).add
      (((i5C1B_d10 hξ hx hxy).mul (i5C1L_d4 hξ hx)).const_mul (-2))).add
      (((i5C1B_d10 hξ hx hxy).mul (i5C1L_d5 hξ)).const_mul 2)).add
      (((i5C1B_d10 hξ hx hxy).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul (-3))) ?_
  ring

/-- Part 22 of the primitive of `I(x)`. -/
noncomputable def i5C1Q22 (ξ x : ℝ) : ℝ :=
  1 * (Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * log (1 + ξ)) + 3 *
      (Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * log x) + 3 *
      (Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * log (ξ * x + (1 - ξ) ^ 2)) + (-3) *
      (Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * log x) + 1 *
      (Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * log (1 - x)) + (-1) *
      (Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * log (ξ * x + (1 - ξ) ^ 2))

theorem hasDerivAt_i5C1Q22 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q22 ξ) (3 * Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (1 / x) + 3 *
        Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 3 *
        Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * (1 / x) +
        Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * (-1 / (1 - x)) -
        Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 9 *
        log x * log (ξ * x + (1 - ξ)) * (-1 / (1 - ξ - x)) + 9 * log x * log (ξ * x + (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) + 6 * log x * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - ξ - x)) -
        6 * log x * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) - 3 * log x *
        log (1 - ξ) * (-1 / (1 - ξ - x)) + 3 * log x * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + 3 *
        log x * log (1 + ξ) * (-1 / (1 - ξ - x)) - 3 * log x * log (1 + ξ) *
        (ξ / (ξ * x + (1 - ξ))) + 4 * log (ξ * x + (1 - ξ)) * log (1 - x) * (-1 / (1 - ξ - x)) -
        4 * log (ξ * x + (1 - ξ)) * log (1 - x) * (ξ / (ξ * x + (1 - ξ))) - log (ξ * x + (1 - ξ)) *
        log (ξ * x + (1 - ξ) ^ 2) * (-1 / (1 - ξ - x)) + log (ξ * x + (1 - ξ)) *
        log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) - log (ξ * x + (1 - ξ)) * log (1 + ξ) *
        (ξ / (ξ * x + (1 - ξ))) - 2 * log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (-1 / (1 - ξ - x)) + 2 * log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ))) - 2 * log (1 - x) * log (1 + ξ) * (-1 / (1 - ξ - x)) + 2 *
        log (1 - x) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) + 2 * log (ξ * x + (1 - ξ) ^ 2) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - ξ - x)) - 2 * log (ξ * x + (1 - ξ) ^ 2) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) - 3 * log (ξ * x + (1 - ξ) ^ 2) *
        log (1 - ξ) * (-1 / (1 - ξ - x)) + 3 * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ))) - log (ξ * x + (1 - ξ) ^ 2) * log (1 + ξ) * (-1 / (1 - ξ - x)) +
        2 * log (ξ * x + (1 - ξ) ^ 2) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ)))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q22 ξ) ((((((((i5C1B_d10 hξ hx hxy).mul
      (hasDerivAt_const x (log (1 + ξ)))).const_mul 1).add (((i5C1B_d11 hξ hx hxy).mul
      (i5C1L_d0 hx)).const_mul 3)).add (((i5C1B_d11 hξ hx hxy).mul (i5C1L_d4 hξ hx)).const_mul
      3)).add (((i5C1B_d12 hξ hx hxy).mul (i5C1L_d0 hx)).const_mul (-3))).add
      (((i5C1B_d12 hξ hx hxy).mul (i5C1L_d3 hξ hxy)).const_mul 1)).add
      (((i5C1B_d12 hξ hx hxy).mul (i5C1L_d4 hξ hx)).const_mul (-1))) ?_
  ring

/-- Part 23 of the primitive of `I(x)`. -/
noncomputable def i5C1Q23 (ξ x : ℝ) : ℝ :=
  (-1) * (Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * log ξ) + 4 *
      (Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * log (1 - ξ)) + (-3) *
      (log x * log (ξ * x + (1 - ξ))) + 3 * (log x * log (1 - ξ)) + (-1 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ))) + 1 * (log (ξ * x + (1 - ξ)) * log (1 - x))

theorem hasDerivAt_i5C1Q23 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q23 ξ) (-3 * log x * (ξ / (ξ * x + (1 - ξ))) - 4 * log (ξ * x + (1 - ξ)) *
        log ξ * (-1 / (1 - ξ - x)) + 4 * log (ξ * x + (1 - ξ)) * log ξ * (ξ / (ξ * x + (1 - ξ))) +
        16 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (-1 / (1 - ξ - x)) - 16 *
        log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - 3 * log (ξ * x + (1 - ξ)) *
        (1 / x) - log (ξ * x + (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) + log (ξ * x + (1 - ξ)) *
        (-1 / (1 - x)) + log (1 - x) * (ξ / (ξ * x + (1 - ξ))) + 2 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log ξ * (-1 / (1 - ξ - x)) - 2 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log ξ * (ξ / (ξ * x + (1 - ξ))) - 8 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) * (-1 / (1 - ξ - x)) + 8 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + 2 * log ξ *
        log (1 + ξ) * (-1 / (1 - ξ - x)) - 2 * log ξ * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) - 8 *
        log (1 - ξ) * log (1 + ξ) * (-1 / (1 - ξ - x)) + 8 * log (1 - ξ) * log (1 + ξ) *
        (ξ / (ξ * x + (1 - ξ))) + 3 * log (1 - ξ) * (1 / x)) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q23 ξ) ((((((((i5C1B_d12 hξ hx hxy).mul
      (hasDerivAt_const x (log ξ))).const_mul (-1)).add (((i5C1B_d12 hξ hx hxy).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul 4)).add (((i5C1L_d0 hx).mul
      (i5C1L_d2 hξ hx)).const_mul (-3))).add (((i5C1L_d0 hx).mul (hasDerivAt_const x (log (1 -
      ξ)))).const_mul 3)).add (((i5C1L_d2 hξ hx).mul (i5C1L_d2 hξ hx)).const_mul (-1 / 2))).add
      (((i5C1L_d2 hξ hx).mul (i5C1L_d3 hξ hxy)).const_mul 1)) ?_
  ring

/-- Part 24 of the primitive of `I(x)`. -/
noncomputable def i5C1Q24 (ξ x : ℝ) : ℝ :=
  (-1) * (log (ξ * x + (1 - ξ)) * log ξ) + 4 * (log (ξ * x + (1 - ξ)) * log (1 - ξ)) + 1 *
      (Li₂ (ξ * (1 - x))) + (-3) * (Li₂ (-(ξ * x / (1 - ξ)))) + (-1) *
      (Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ)))) + (-(π ^ 2 / 6)) * (2 * log (ξ * x + (1 - ξ)) - 3 *
      log (ξ * x + (1 - ξ) ^ 2) - 6 * log (ξ * x ^ 2 + (1 - ξ) ^ 2))

theorem hasDerivAt_i5C1Q24 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q24 ξ) (-(1 / 3) * π ^ 2 * (ξ / (ξ * x + (1 - ξ))) + (1 / 2) * π ^ 2 *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + π ^ 2 * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 3 *
        log (ξ * x + (1 - ξ)) * (1 / x) + log (ξ * x + (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) -
        log (ξ * x + (1 - ξ)) * (-1 / (1 - x)) - log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ))) - log ξ * (ξ / (ξ * x + (1 - ξ))) - 3 * log (1 - ξ) * (1 / x) + 4 *
        log (1 - ξ) * (ξ / (ξ * x + (1 - ξ)))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q24 ξ) ((((((((i5C1L_d2 hξ hx).mul
      (hasDerivAt_const x (log ξ))).const_mul (-1)).add (((i5C1L_d2 hξ hx).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul 4)).add ((i5C1B_d3 hξ hx hxy).const_mul 1)).add
      ((i5C1B_d4 hξ hx hxy).const_mul (-3))).add ((i5C1B_d10 hξ hx hxy).const_mul (-1))).add
      (((((i5C1L_d2 hξ hx).const_mul 2).sub ((i5C1L_d4 hξ hx).const_mul 3)).sub
      ((i5C1L_d5 hξ).const_mul 6)).const_mul (-(π ^ 2 / 6)))) ?_
  ring

/-- Part 25 of the primitive of `I(x)`. -/
noncomputable def i5C1Q25 (ξ x : ℝ) : ℝ :=
  (-8) * (Li₃ ((1 - x))) + (-9) * (Li₃ (x / (1 - ξ)))

theorem hasDerivAt_i5C1Q25 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q25 ξ) (8 * Li₂ (x) * (-1 / (1 - x)) - 9 * Li₂ (x / (1 - ξ)) * (1 / x) -
        (4 / 3) * π ^ 2 * (-1 / (1 - x)) + 8 * log x * log (1 - x) * (-1 / (1 - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q25 ξ) (((i5C1T_d0 hξ hx hxy).const_mul (-8)).add
      ((i5C1T_d1 hξ hx hxy).const_mul (-9))) ?_
  simp only [i5C1F_0 hξ hx hxy]
  ring

/-- Part 26 of the primitive of `I(x)`. -/
noncomputable def i5C1Q26 (ξ x : ℝ) : ℝ :=
  4 * (Li₃ (ξ / (1 - x))) + 3 * (Li₃ (ξ * (1 - x)))

theorem hasDerivAt_i5C1Q26 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q26 ξ) (-4 * Li₂ (ξ / (1 - x)) * (-1 / (1 - x)) + 3 * Li₂ (ξ * (1 - x)) *
        (-1 / (1 - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q26 ξ) (((i5C1T_d2 hξ hx hxy).const_mul 4).add
      ((i5C1T_d3 hξ hx hxy).const_mul 3)) ?_
  ring

/-- Part 27 of the primitive of `I(x)`. -/
noncomputable def i5C1Q27 (ξ x : ℝ) : ℝ :=
  (-18) * (Li₃ (-(ξ * x / (1 - ξ)))) + (-1) * (Li₃ ((ξ * x + (1 - ξ))))

theorem hasDerivAt_i5C1Q27 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q27 ξ) (Li₂ (ξ * (1 - x)) * (ξ / (ξ * x + (1 - ξ))) - 18 *
        Li₂ (-(ξ * x / (1 - ξ))) * (1 / x) - (1 / 6) * π ^ 2 * (ξ / (ξ * x + (1 - ξ))) +
        log (ξ * x + (1 - ξ)) * log (1 - x) * (ξ / (ξ * x + (1 - ξ))) + log (ξ * x + (1 - ξ)) *
        log ξ * (ξ / (ξ * x + (1 - ξ)))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q27 ξ) (((i5C1T_d4 hξ hx hxy).const_mul (-18)).add
      ((i5C1T_d5 hξ hx hxy).const_mul (-1))) ?_
  simp only [i5C1_id1 hξ hx hxy]
  simp only [i5C1R1]
  ring

/-- Part 28 of the primitive of `I(x)`. -/
noncomputable def i5C1Q28 (ξ x : ℝ) : ℝ :=
  1 * (Li₃ ((1 - ξ - x) / (1 - x))) + (-6) * (Li₃ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)))

theorem hasDerivAt_i5C1Q28 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q28 ξ) (-Li₂ (ξ / (1 - x)) * (-1 / (1 - ξ - x)) + Li₂ (ξ / (1 - x)) *
        (-1 / (1 - x)) - 12 * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (1 / x) + (1 / 6) * π ^ 2 *
        (-1 / (1 - ξ - x)) - (1 / 6) * π ^ 2 * (-1 / (1 - x)) + log (1 - ξ - x) * log (1 - x) *
        (-1 / (1 - ξ - x)) - log (1 - ξ - x) * log (1 - x) * (-1 / (1 - x)) - log (1 - ξ - x) *
        log ξ * (-1 / (1 - ξ - x)) + log (1 - ξ - x) * log ξ * (-1 / (1 - x)) - log (1 - x) ^ 2 *
        (-1 / (1 - ξ - x)) + log (1 - x) ^ 2 * (-1 / (1 - x)) + log (1 - x) * log ξ *
        (-1 / (1 - ξ - x)) - log (1 - x) * log ξ * (-1 / (1 - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q28 ξ) (((i5C1T_d6 hξ hx hxy).const_mul 1).add
      ((i5C1T_d7 hξ hx hxy).const_mul (-6))) ?_
  simp only [i5C1_id2 hξ hx hxy]
  simp only [i5C1R2]
  ring

/-- Part 29 of the primitive of `I(x)`. -/
noncomputable def i5C1Q29 (ξ x : ℝ) : ℝ :=
  3 * (Li₃ ((1 - ξ - x) / (1 - ξ))) + 1 * (Li₃ (ξ * (1 - ξ - x) / (1 - ξ)))

theorem hasDerivAt_i5C1Q29 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q29 ξ) (-3 * Li₂ (x / (1 - ξ)) * (-1 / (1 - ξ - x)) +
        Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) * (-1 / (1 - ξ - x)) + (1 / 2) * π ^ 2 *
        (-1 / (1 - ξ - x)) - 3 * log x * log (1 - ξ - x) * (-1 / (1 - ξ - x)) + 3 * log x *
        log (1 - ξ) * (-1 / (1 - ξ - x)) + 3 * log (1 - ξ - x) * log (1 - ξ) * (-1 / (1 - ξ - x)) -
        3 * log (1 - ξ) ^ 2 * (-1 / (1 - ξ - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q29 ξ) (((i5C1T_d8 hξ hx hxy).const_mul 3).add
      ((i5C1T_d9 hξ hx hxy).const_mul 1)) ?_
  simp only [i5C1F_3 hξ hx hxy]
  ring

/-- Part 30 of the primitive of `I(x)`. -/
noncomputable def i5C1Q30 (ξ x : ℝ) : ℝ :=
  3 * (Li₃ ((1 + ξ) * x / (ξ * x + (1 - ξ)))) + 4 * (Li₃ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))))

theorem hasDerivAt_i5C1Q30 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q30 ξ) (-4 * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) +
        3 * Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (1 / x) - 3 *
        Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ)))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q30 ξ) (((i5C1T_d10 hξ hx hxy).const_mul 3).add
      ((i5C1T_d11 hξ hx hxy).const_mul 4)) ?_
  ring

/-- Part 31 of the primitive of `I(x)`. -/
noncomputable def i5C1Q31 (ξ x : ℝ) : ℝ :=
  (-3) * (Li₃ ((1 - ξ - x) / (ξ * x + (1 - ξ)))) + 6 * (Li₃ (-(ξ *
      (1 - ξ - x) / (ξ * x + (1 - ξ)))))

theorem hasDerivAt_i5C1Q31 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q31 ξ) (6 * Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (-1 / (1 - ξ - x)) -
        6 * Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (ξ / (ξ * x + (1 - ξ))) + 3 *
        Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (-1 / (1 - ξ - x)) - 3 *
        Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) - (1 / 2) * π ^ 2 *
        (-1 / (1 - ξ - x)) + (1 / 2) * π ^ 2 * (ξ / (ξ * x + (1 - ξ))) + 3 * log x *
        log (1 - ξ - x) * (-1 / (1 - ξ - x)) - 3 * log x * log (1 - ξ - x) *
        (ξ / (ξ * x + (1 - ξ))) - 3 * log x * log (ξ * x + (1 - ξ)) * (-1 / (1 - ξ - x)) + 3 *
        log x * log (ξ * x + (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) - 3 * log (1 - ξ - x) *
        log (ξ * x + (1 - ξ)) * (-1 / (1 - ξ - x)) + 3 * log (1 - ξ - x) * log (ξ * x + (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) + 3 * log (1 - ξ - x) * log (1 + ξ) * (-1 / (1 - ξ - x)) - 3 *
        log (1 - ξ - x) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) + 3 * log (ξ * x + (1 - ξ)) ^ 2 *
        (-1 / (1 - ξ - x)) - 3 * log (ξ * x + (1 - ξ)) ^ 2 * (ξ / (ξ * x + (1 - ξ))) - 3 *
        log (ξ * x + (1 - ξ)) * log (1 + ξ) * (-1 / (1 - ξ - x)) + 3 * log (ξ * x + (1 - ξ)) *
        log (1 + ξ) * (ξ / (ξ * x + (1 - ξ)))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q31 ξ) (((i5C1T_d12 hξ hx hxy).const_mul (-3)).add
      ((i5C1T_d13 hξ hx hxy).const_mul 6)) ?_
  simp only [i5C1F_4 hξ hx hxy]
  ring

/-- Part 32 of the primitive of `I(x)`. -/
noncomputable def i5C1Q32 (ξ x : ℝ) : ℝ :=
  6 * (Li₃ ((1 - ξ) * (1 - x) / (ξ * x + (1 - ξ)))) + (-3) * (Li₃ ((ξ * x + (1 - ξ) ^ 2) / (1 - ξ)))

theorem hasDerivAt_i5C1Q32 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q32 ξ) (6 * Li₂ (x / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) - 6 *
        Li₂ (x / (ξ * x + (1 - ξ))) * (-1 / (1 - x)) + 3 * Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - π ^ 2 * (ξ / (ξ * x + (1 - ξ))) + π ^ 2 * (-1 / (1 - x)) -
        (1 / 2) * π ^ 2 * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 6 * log x * log (ξ * x + (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) + 6 * log x * log (ξ * x + (1 - ξ)) * (-1 / (1 - x)) + 6 * log x *
        log (1 - x) * (ξ / (ξ * x + (1 - ξ))) - 6 * log x * log (1 - x) * (-1 / (1 - x)) + 6 *
        log x * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - 6 * log x * log (1 - ξ) * (-1 / (1 - x)) +
        3 * log (1 - ξ - x) * log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 3 *
        log (1 - ξ - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 6 *
        log (ξ * x + (1 - ξ)) ^ 2 * (ξ / (ξ * x + (1 - ξ))) - 6 * log (ξ * x + (1 - ξ)) ^ 2 *
        (-1 / (1 - x)) - 6 * log (ξ * x + (1 - ξ)) * log (1 - x) * (ξ / (ξ * x + (1 - ξ))) + 6 *
        log (ξ * x + (1 - ξ)) * log (1 - x) * (-1 / (1 - x)) - 6 * log (ξ * x + (1 - ξ)) *
        log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + 6 * log (ξ * x + (1 - ξ)) * log (1 - ξ) *
        (-1 / (1 - x)) + 3 * log (ξ * x + (1 - ξ) ^ 2) * log ξ * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 3 *
        log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 3 * log ξ *
        log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 3 * log (1 - ξ) ^ 2 *
        (ξ / (ξ * x + (1 - ξ) ^ 2))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q32 ξ) (((i5C1T_d14 hξ hx hxy).const_mul 6).add
      ((i5C1T_d15 hξ hx hxy).const_mul (-3))) ?_
  simp only [i5C1F_5 hξ hx hxy]
  simp only [i5C1_id6 hξ hx hxy]
  simp only [i5C1R6]
  ring

/-- Part 33 of the primitive of `I(x)`. -/
noncomputable def i5C1Q33 (ξ x : ℝ) : ℝ :=
  (-3) * (Li₃ ((ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ)))) + (-2) *
      (Li₃ ((ξ * x ^ 2 + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ) ^ 2)))

theorem hasDerivAt_i5C1Q33 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q33 ξ) (-3 * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) +
        3 * Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 *
        Li₂ (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 *
        Li₂ (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
        (1 / 2) * π ^ 2 * (ξ / (ξ * x + (1 - ξ))) - (1 / 6) * π ^ 2 * (ξ / (ξ * x + (1 - ξ) ^ 2)) -
        (1 / 3) * π ^ 2 * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 * log x *
        log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log x *
        log (ξ * x + (1 - ξ) ^ 2) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 2 * log x *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * log x *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 3 *
        log (ξ * x + (1 - ξ)) ^ 2 * (ξ / (ξ * x + (1 - ξ))) + 3 * log (ξ * x + (1 - ξ)) ^ 2 *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 3 * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ))) - 3 * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 3 * log (ξ * x + (1 - ξ)) * log ξ * (ξ / (ξ * x + (1 - ξ))) -
        3 * log (ξ * x + (1 - ξ)) * log ξ * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 3 *
        log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - 3 * log (ξ * x + (1 - ξ)) *
        log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * log (1 - x) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (1 - x) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 2 * log (1 - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * log (1 - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 2 *
        log (ξ * x + (1 - ξ) ^ 2) ^ 2 * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 *
        log (ξ * x + (1 - ξ) ^ 2) ^ 2 * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ) ^ 2)) -
        2 * log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 3 * log (ξ * x + (1 - ξ) ^ 2) * log ξ *
        (ξ / (ξ * x + (1 - ξ))) + 5 * log (ξ * x + (1 - ξ) ^ 2) * log ξ *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (ξ * x + (1 - ξ) ^ 2) * log ξ *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 3 * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ))) + 3 * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log ξ *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log ξ *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q33 ξ) (((i5C1T_d16 hξ hx hxy).const_mul (-3)).add
      ((i5C1T_d17 hξ hx hxy).const_mul (-2))) ?_
  simp only [i5C1F_8 hξ hx hxy]
  simp only [i5C1_id7 hξ hx hxy]
  simp only [i5C1R7]
  ring

/-- Part 34 of the primitive of `I(x)`. -/
noncomputable def i5C1Q34 (ξ x : ℝ) : ℝ :=
  (-15) * (Li₃ (ξ * x / (ξ * x + (1 - ξ)))) + 3 * (Li₃ (ξ * (1 - ξ - x) / ((1 - ξ) * (1 + ξ))))

theorem hasDerivAt_i5C1Q34 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q34 ξ) (-3 * Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) *
        (-1 / (1 - ξ - x)) + 15 * Li₂ (-(ξ * x / (1 - ξ))) * (1 / x) - 15 *
        Li₂ (-(ξ * x / (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) + (15 / 2) * log (ξ * x + (1 - ξ)) ^ 2 *
        (1 / x) - (3 / 2) * log (ξ * x + (1 - ξ)) ^ 2 * (-1 / (1 - ξ - x)) - (15 / 2) *
        log (ξ * x + (1 - ξ)) ^ 2 * (ξ / (ξ * x + (1 - ξ))) - 15 * log (ξ * x + (1 - ξ)) *
        log (1 - ξ) * (1 / x) + 3 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (-1 / (1 - ξ - x)) + 15 *
        log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + 3 * log (ξ * x + (1 - ξ)) *
        log (1 + ξ) * (-1 / (1 - ξ - x)) + (15 / 2) * log (1 - ξ) ^ 2 * (1 / x) - (3 / 2) *
        log (1 - ξ) ^ 2 * (-1 / (1 - ξ - x)) - (15 / 2) * log (1 - ξ) ^ 2 *
        (ξ / (ξ * x + (1 - ξ))) - 3 * log (1 - ξ) * log (1 + ξ) * (-1 / (1 - ξ - x)) - (3 / 2) *
        log (1 + ξ) ^ 2 * (-1 / (1 - ξ - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q34 ξ) (((i5C1T_d18 hξ hx hxy).const_mul (-15)).add
      ((i5C1T_d19 hξ hx hxy).const_mul 3)) ?_
  simp only [i5C1_id9 hξ hx hxy, i5C1_id10 hξ hx hxy]
  simp only [i5C1R9, i5C1R10]
  ring

/-- Part 35 of the primitive of `I(x)`. -/
noncomputable def i5C1Q35 (ξ x : ℝ) : ℝ :=
  (-1) * (Li₃ (ξ ^ 2 * (1 - ξ - x) / (ξ * x + (1 - ξ)))) + (-6) *
      (Li₃ (ξ * x ^ 2 / (ξ * x ^ 2 + (1 - ξ) ^ 2)))

theorem hasDerivAt_i5C1Q35 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q35 ξ) (Li₂ (x / (1 - ξ)) * (-1 / (1 - ξ - x)) - Li₂ (x / (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) - Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * (-1 / (1 - ξ - x)) +
        Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) - 2 *
        Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (-1 / (1 - ξ - x)) + 2 *
        Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (ξ / (ξ * x + (1 - ξ))) -
        Li₂ (-(ξ * x / (1 - ξ))) * (-1 / (1 - ξ - x)) + Li₂ (-(ξ * x / (1 - ξ))) *
        (ξ / (ξ * x + (1 - ξ))) + 12 * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (1 / x) - 6 *
        Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) -
        Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) * (-1 / (1 - ξ - x)) + Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) - Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (-1 / (1 - ξ - x)) +
        Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) + log (1 - ξ - x) *
        log (ξ * x + (1 - ξ)) * (-1 / (1 - ξ - x)) - log (1 - ξ - x) * log (ξ * x + (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) - log (1 - ξ - x) * log (1 - ξ) * (-1 / (1 - ξ - x)) +
        log (1 - ξ - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - log (1 - ξ - x) * log (1 + ξ) *
        (-1 / (1 - ξ - x)) + log (1 - ξ - x) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) - (3 / 2) *
        log (ξ * x + (1 - ξ)) ^ 2 * (-1 / (1 - ξ - x)) + (3 / 2) * log (ξ * x + (1 - ξ)) ^ 2 *
        (ξ / (ξ * x + (1 - ξ))) + 2 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (-1 / (1 - ξ - x)) -
        2 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + log (ξ * x + (1 - ξ)) *
        log (1 + ξ) * (-1 / (1 - ξ - x)) - log (ξ * x + (1 - ξ)) * log (1 + ξ) *
        (ξ / (ξ * x + (1 - ξ))) + 6 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 * (1 / x) - 3 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 24 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) * (1 / x) + 12 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
        24 * log (1 - ξ) ^ 2 * (1 / x) - (1 / 2) * log (1 - ξ) ^ 2 * (-1 / (1 - ξ - x)) + (1 / 2) *
        log (1 - ξ) ^ 2 * (ξ / (ξ * x + (1 - ξ))) - 12 * log (1 - ξ) ^ 2 *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q35 ξ) (((i5C1T_d20 hξ hx hxy).const_mul (-1)).add
      ((i5C1T_d21 hξ hx hxy).const_mul (-6))) ?_
  simp only [i5C1_id11 hξ hx hxy, i5C1_id12 hξ hx hxy]
  simp only [i5C1R11, i5C1R12]
  ring

/-- Part 36 of the primitive of `I(x)`. -/
noncomputable def i5C1Q36 (ξ x : ℝ) : ℝ :=
  2 * (Li₃ ((1 - ξ) ^ 2 / (ξ * x + (1 - ξ) ^ 2))) + (-1) * (Li₃ ((1 - ξ - x) / ((1 - ξ) * (1 + ξ) *
      (1 - x))))

theorem hasDerivAt_i5C1Q36 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q36 ξ) (-2 * Li₂ (x) * (-1 / (1 - ξ - x)) + 2 * Li₂ (x) * (-1 / (1 - x)) + 2 *
        Li₂ (x) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * Li₂ (x / (1 - ξ)) * (-1 / (1 - ξ - x)) - 2 *
        Li₂ (x / (1 - ξ)) * (-1 / (1 - x)) - 2 * Li₂ (x / (1 - ξ)) * (ξ / (ξ * x + (1 - ξ) ^ 2)) -
        Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (-1 / (1 - ξ - x)) +
        Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (-1 / (1 - x)) + Li₂ (ξ / (1 - x)) *
        (-1 / (1 - ξ - x)) - Li₂ (ξ / (1 - x)) * (-1 / (1 - x)) - Li₂ (ξ * (1 - x)) *
        (-1 / (1 - ξ - x)) + Li₂ (ξ * (1 - x)) * (-1 / (1 - x)) + 2 * Li₂ (ξ * (1 - x)) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * Li₂ (-(ξ * x / (1 - ξ))) * (ξ / (ξ * x + (1 - ξ) ^ 2)) +
        2 * Li₂ (x / (ξ * x + (1 - ξ))) * (-1 / (1 - ξ - x)) - 2 * Li₂ (x / (ξ * x + (1 - ξ))) *
        (-1 / (1 - x)) - 2 * Li₂ (x / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 *
        Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 *
        Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (-1 / (1 - ξ - x)) + 2 *
        Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (-1 / (1 - x)) + 2 *
        Li₂ (x / (ξ * x + (1 - ξ) ^ 2)) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - (1 / 6) * π ^ 2 *
        (-1 / (1 - ξ - x)) + (1 / 6) * π ^ 2 * (-1 / (1 - x)) - (1 / 3) * π ^ 2 *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log x * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 4 * log x * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 *
        log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * (-1 / (1 - ξ - x)) - 2 * log (1 - ξ - x) *
        log (ξ * x + (1 - ξ)) * (-1 / (1 - x)) - log (1 - ξ - x) * log (1 - x) *
        (-1 / (1 - ξ - x)) + log (1 - ξ - x) * log (1 - x) * (-1 / (1 - x)) - 2 * log (1 - ξ - x) *
        log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + log (1 - ξ - x) * log ξ *
        (-1 / (1 - ξ - x)) - log (1 - ξ - x) * log ξ * (-1 / (1 - x)) - 2 * log (1 - ξ - x) *
        log (1 - ξ) * (-1 / (1 - ξ - x)) + 2 * log (1 - ξ - x) * log (1 - ξ) * (-1 / (1 - x)) + 2 *
        log (1 - ξ - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (1 - ξ - x) *
        log (1 + ξ) * (-1 / (1 - ξ - x)) + 2 * log (1 - ξ - x) * log (1 + ξ) * (-1 / (1 - x)) -
        (1 / 2) * log (ξ * x + (1 - ξ)) ^ 2 * (-1 / (1 - ξ - x)) + (1 / 2) *
        log (ξ * x + (1 - ξ)) ^ 2 * (-1 / (1 - x)) - log (ξ * x + (1 - ξ)) ^ 2 *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (ξ * x + (1 - ξ)) * log (1 - x) *
        (-1 / (1 - ξ - x)) + 2 * log (ξ * x + (1 - ξ)) * log (1 - x) * (-1 / (1 - x)) + 2 *
        log (ξ * x + (1 - ξ)) * log (1 - x) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - log (ξ * x + (1 - ξ)) *
        log (1 - ξ) * (-1 / (1 - ξ - x)) + log (ξ * x + (1 - ξ)) * log (1 - ξ) * (-1 / (1 - x)) +
        2 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) +
        log (ξ * x + (1 - ξ)) * log (1 + ξ) * (-1 / (1 - ξ - x)) - log (ξ * x + (1 - ξ)) *
        log (1 + ξ) * (-1 / (1 - x)) + log (1 - x) ^ 2 * (-1 / (1 - ξ - x)) - log (1 - x) ^ 2 *
        (-1 / (1 - x)) - log (1 - x) * log ξ * (-1 / (1 - ξ - x)) + log (1 - x) * log ξ *
        (-1 / (1 - x)) + log (1 - x) * log (1 - ξ) * (-1 / (1 - ξ - x)) - log (1 - x) *
        log (1 - ξ) * (-1 / (1 - x)) + log (1 - x) * log (1 + ξ) * (-1 / (1 - ξ - x)) -
        log (1 - x) * log (1 + ξ) * (-1 / (1 - x)) + 2 * log (ξ * x + (1 - ξ) ^ 2) ^ 2 *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (ξ * x + (1 - ξ) ^ 2) * log ξ *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - log ξ * log (1 - ξ) * (-1 / (1 - ξ - x)) + log ξ *
        log (1 - ξ) * (-1 / (1 - x)) + 4 * log ξ * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) -
        log ξ * log (1 + ξ) * (-1 / (1 - ξ - x)) + log ξ * log (1 + ξ) * (-1 / (1 - x)) + (3 / 2) *
        log (1 - ξ) ^ 2 * (-1 / (1 - ξ - x)) - (3 / 2) * log (1 - ξ) ^ 2 * (-1 / (1 - x)) - 3 *
        log (1 - ξ) ^ 2 * (ξ / (ξ * x + (1 - ξ) ^ 2)) + log (1 - ξ) * log (1 + ξ) *
        (-1 / (1 - ξ - x)) - log (1 - ξ) * log (1 + ξ) * (-1 / (1 - x)) + (1 / 2) *
        log (1 + ξ) ^ 2 * (-1 / (1 - ξ - x)) - (1 / 2) * log (1 + ξ) ^ 2 * (-1 / (1 - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q36 ξ) (((i5C1T_d22 hξ hx hxy).const_mul 2).add
      ((i5C1T_d23 hξ hx hxy).const_mul (-1))) ?_
  simp only [i5C1F_13 hξ hx hxy]
  simp only [i5C1_id13 hξ hx hxy, i5C1_id14 hξ hx hxy]
  simp only [i5C1R13, i5C1R14]
  ring

/-- Part 37 of the primitive of `I(x)`. -/
noncomputable def i5C1Q37 (ξ x : ℝ) : ℝ :=
  6 * (Li₃ (ξ * x * (1 - ξ - x) / ((1 - ξ) * (ξ * x + (1 - ξ))))) + (-2) *
      (Li₃ (ξ * (ξ * x + (1 - ξ)) / ((1 - ξ) * (1 + ξ) * (1 - x))))

theorem hasDerivAt_i5C1Q37 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q37 ξ) (4 * Li₂ (x) * (ξ / (ξ * x + (1 - ξ))) - 4 * Li₂ (x) * (-1 / (1 - x)) -
        3 * Li₂ (x / (1 - ξ)) * (1 / x) - 3 * Li₂ (x / (1 - ξ)) * (-1 / (1 - ξ - x)) -
        Li₂ (x / (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) + 4 * Li₂ (x / (1 - ξ)) * (-1 / (1 - x)) - 3 *
        Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (1 / x) - 3 *
        Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (-1 / (1 - ξ - x)) + 5 *
        Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (ξ / (ξ * x + (1 - ξ))) - 2 *
        Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (-1 / (1 - x)) + 3 *
        Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * (1 / x) + 3 *
        Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * (-1 / (1 - ξ - x)) - 3 *
        Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * (ξ / (ξ * x + (1 - ξ))) - 2 *
        Li₂ (ξ / (1 - x)) * (ξ / (ξ * x + (1 - ξ))) + 2 * Li₂ (ξ / (1 - x)) * (-1 / (1 - x)) + 2 *
        Li₂ (ξ * (1 - x)) * (ξ / (ξ * x + (1 - ξ))) - 2 * Li₂ (ξ * (1 - x)) * (-1 / (1 - x)) - 3 *
        Li₂ (-(ξ * x / (1 - ξ))) * (1 / x) - 3 * Li₂ (-(ξ * x / (1 - ξ))) * (-1 / (1 - ξ - x)) +
        3 * Li₂ (-(ξ * x / (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) - 4 * Li₂ (x / (ξ * x + (1 - ξ))) *
        (ξ / (ξ * x + (1 - ξ))) + 4 * Li₂ (x / (ξ * x + (1 - ξ))) * (-1 / (1 - x)) + 3 *
        Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (1 / x) + 3 * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) *
        (-1 / (1 - ξ - x)) - 3 * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (ξ / (ξ * x + (1 - ξ))) + 3 *
        Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (1 / x) + 3 * Li₂ ((1 + ξ) *
        x / (ξ * x + (1 - ξ))) * (-1 / (1 - ξ - x)) + Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) *
        (ξ / (ξ * x + (1 - ξ))) - 4 * Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (-1 / (1 - x)) - 3 *
        log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * (1 / x) - 3 * log (1 - ξ - x) *
        log (ξ * x + (1 - ξ)) * (-1 / (1 - ξ - x)) + log (1 - ξ - x) * log (ξ * x + (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) + 2 * log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * (-1 / (1 - x)) +
        3 * log (1 - ξ - x) * log (1 - ξ) * (1 / x) + 3 * log (1 - ξ - x) * log (1 - ξ) *
        (-1 / (1 - ξ - x)) - log (1 - ξ - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - 2 *
        log (1 - ξ - x) * log (1 - ξ) * (-1 / (1 - x)) + 3 * log (1 - ξ - x) * log (1 + ξ) *
        (1 / x) + 3 * log (1 - ξ - x) * log (1 + ξ) * (-1 / (1 - ξ - x)) - log (1 - ξ - x) *
        log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) - 2 * log (1 - ξ - x) * log (1 + ξ) *
        (-1 / (1 - x)) + 3 * log (ξ * x + (1 - ξ)) ^ 2 * (1 / x) + 3 * log (ξ * x + (1 - ξ)) ^ 2 *
        (-1 / (1 - ξ - x)) - 2 * log (ξ * x + (1 - ξ)) ^ 2 * (ξ / (ξ * x + (1 - ξ))) -
        log (ξ * x + (1 - ξ)) ^ 2 * (-1 / (1 - x)) + 2 * log (ξ * x + (1 - ξ)) * log (1 - x) *
        (ξ / (ξ * x + (1 - ξ))) - 2 * log (ξ * x + (1 - ξ)) * log (1 - x) * (-1 / (1 - x)) - 3 *
        log (ξ * x + (1 - ξ)) * log (1 - ξ) * (1 / x) - 3 * log (ξ * x + (1 - ξ)) * log (1 - ξ) *
        (-1 / (1 - ξ - x)) + 3 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) -
        3 * log (ξ * x + (1 - ξ)) * log (1 + ξ) * (1 / x) - 3 * log (ξ * x + (1 - ξ)) *
        log (1 + ξ) * (-1 / (1 - ξ - x)) - log (ξ * x + (1 - ξ)) * log (1 + ξ) *
        (ξ / (ξ * x + (1 - ξ))) + 4 * log (ξ * x + (1 - ξ)) * log (1 + ξ) * (-1 / (1 - x)) + 2 *
        log (1 - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - 2 * log (1 - x) * log (1 - ξ) *
        (-1 / (1 - x)) + 2 * log (1 - x) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) - 2 *
        log (1 - x) * log (1 + ξ) * (-1 / (1 - x)) - log (1 - ξ) ^ 2 * (ξ / (ξ * x + (1 - ξ))) +
        log (1 - ξ) ^ 2 * (-1 / (1 - x)) + 2 * log (1 - ξ) * log (1 + ξ) *
        (ξ / (ξ * x + (1 - ξ))) - 2 * log (1 - ξ) * log (1 + ξ) * (-1 / (1 - x)) +
        log (1 + ξ) ^ 2 * (ξ / (ξ * x + (1 - ξ))) - log (1 + ξ) ^ 2 * (-1 / (1 - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q37 ξ) (((i5C1T_d24 hξ hx hxy).const_mul 6).add
      ((i5C1T_d25 hξ hx hxy).const_mul (-2))) ?_
  simp only [i5C1_id15 hξ hx hxy, i5C1_id16 hξ hx hxy]
  simp only [i5C1R15, i5C1R16]
  ring

/-- Part 38 of the primitive of `I(x)`. -/
noncomputable def i5C1Q38 (ξ x : ℝ) : ℝ :=
  6 * (Li₃ (x * (ξ * x + (1 - ξ)) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) + 6 *
      (Li₃ (-(ξ * x * (1 - ξ - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))))

theorem hasDerivAt_i5C1Q38 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q38 ξ) (6 * Li₂ (x / (1 - ξ)) * (1 / x) + 3 * Li₂ (x / (1 - ξ)) *
        (-1 / (1 - ξ - x)) + 3 * Li₂ (x / (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) - 6 *
        Li₂ (x / (1 - ξ)) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 3 *
        Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (-1 / (1 - ξ - x)) - 3 *
        Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) * (ξ / (ξ * x + (1 - ξ))) - 3 *
        Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * (-1 / (1 - ξ - x)) + 3 *
        Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) * (ξ / (ξ * x + (1 - ξ))) + 6 *
        Li₂ (-(ξ * x / (1 - ξ))) * (1 / x) + 3 * Li₂ (-(ξ * x / (1 - ξ))) * (-1 / (1 - ξ - x)) +
        3 * Li₂ (-(ξ * x / (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) - 6 * Li₂ (-(ξ * x / (1 - ξ))) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 6 * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) *
        (1 / x) - 3 * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (-1 / (1 - ξ - x)) - 3 *
        Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (ξ / (ξ * x + (1 - ξ))) + 6 *
        Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 3 *
        Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (-1 / (1 - ξ - x)) + 3 *
        Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) - 6 * log (1 - ξ - x) *
        log (ξ * x + (1 - ξ)) * (1 / x) + 3 * log (1 - ξ - x) * log (ξ * x + (1 - ξ)) *
        (-1 / (1 - ξ - x)) - 9 * log (1 - ξ - x) * log (ξ * x + (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) + 6 * log (1 - ξ - x) * log (ξ * x + (1 - ξ)) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 6 * log (1 - ξ - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) + 6 * log (1 - ξ - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) - 6 * log (1 - ξ - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 6 *
        log (1 - ξ - x) * log (1 - ξ) * (1 / x) - 3 * log (1 - ξ - x) * log (1 - ξ) *
        (-1 / (1 - ξ - x)) - 3 * log (1 - ξ - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + 6 *
        log (1 - ξ - x) * log (1 - ξ) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 3 *
        log (1 - ξ - x) * log (1 + ξ) * (-1 / (1 - ξ - x)) + 3 * log (1 - ξ - x) * log (1 + ξ) *
        (ξ / (ξ * x + (1 - ξ))) - 6 * log (ξ * x + (1 - ξ)) ^ 2 * (-1 / (1 - ξ - x)) + 6 *
        log (ξ * x + (1 - ξ)) ^ 2 * (ξ / (ξ * x + (1 - ξ))) + 6 * log (ξ * x + (1 - ξ)) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) + 6 * log (ξ * x + (1 - ξ)) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - ξ - x)) - 6 * log (ξ * x + (1 - ξ)) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 6 *
        log (ξ * x + (1 - ξ)) * log (1 - ξ) * (1 / x) - 3 * log (ξ * x + (1 - ξ)) * log (1 - ξ) *
        (-1 / (1 - ξ - x)) - 3 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) +
        6 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 3 *
        log (ξ * x + (1 - ξ)) * log (1 + ξ) * (-1 / (1 - ξ - x)) - 3 * log (ξ * x + (1 - ξ)) *
        log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) - 6 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 * (1 / x) -
        3 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 * (-1 / (1 - ξ - x)) - 3 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 * (ξ / (ξ * x + (1 - ξ))) + 6 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 12 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) * (1 / x) + 6 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        log (1 - ξ) * (-1 / (1 - ξ - x)) + 6 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ))) - 12 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 6 * log (1 - ξ) ^ 2 * (1 / x) - 3 *
        log (1 - ξ) ^ 2 * (-1 / (1 - ξ - x)) - 3 * log (1 - ξ) ^ 2 * (ξ / (ξ * x + (1 - ξ))) + 6 *
        log (1 - ξ) ^ 2 * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q38 ξ) (((i5C1T_d26 hξ hx hxy).const_mul 6).add
      ((i5C1T_d27 hξ hx hxy).const_mul 6)) ?_
  simp only [i5C1_id17 hξ hx hxy, i5C1_id18 hξ hx hxy]
  simp only [i5C1R17, i5C1R18]
  ring

/-- Part 39 of the primitive of `I(x)`. -/
noncomputable def i5C1Q39 (ξ x : ℝ) : ℝ :=
  2 * (Li₃ ((1 - ξ) ^ 2 * (1 - x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) + 1 *
      (Li₃ ((1 + ξ) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x + (1 - ξ))))

theorem hasDerivAt_i5C1Q39 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q39 ξ) (-Li₂ (x / (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) - 2 * Li₂ (x / (1 - ξ)) *
        (-1 / (1 - x)) + Li₂ (x / (1 - ξ)) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * Li₂ (x / (1 - ξ)) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) *
        (ξ / (ξ * x + (1 - ξ))) - Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) *
        (ξ / (ξ * x + (1 - ξ))) - 2 * Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * Li₂ (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) *
        (-1 / (1 - x)) + 2 * Li₂ (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 * Li₂ (ξ * (1 - x)) * (-1 / (1 - x)) - 2 *
        Li₂ (ξ * (1 - x)) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + Li₂ (-(ξ * x / (1 - ξ))) *
        (ξ / (ξ * x + (1 - ξ))) - 2 * Li₂ (-(ξ * x / (1 - ξ))) * (-1 / (1 - x)) -
        Li₂ (-(ξ * x / (1 - ξ))) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * Li₂ (-(ξ * x / (1 - ξ))) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 2 * Li₂ (x / (ξ * x + (1 - ξ))) *
        (-1 / (1 - x)) + 2 * Li₂ (x / (ξ * x + (1 - ξ))) * (ξ * (2 * x) / (ξ * x ^ 2 +
        (1 - ξ) ^ 2)) + 2 * Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (-1 / (1 - x)) - 2 *
        Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
        Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) - 2 *
        Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) * (-1 / (1 - x)) - Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) *
        (ξ / (ξ * x + (1 - ξ))) - Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * Li₂ (x / (ξ * x + (1 - ξ) ^ 2)) * (-1 / (1 - x)) - 2 *
        Li₂ (x / (ξ * x + (1 - ξ) ^ 2)) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - (1 / 6) *
        π ^ 2 * (ξ / (ξ * x + (1 - ξ))) + (1 / 3) * π ^ 2 * (-1 / (1 - x)) + (1 / 6) * π ^ 2 *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - (1 / 3) * π ^ 2 * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) -
        2 * log x * log (1 - x) * (-1 / (1 - x)) + 2 * log x * log (1 - x) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 * log x * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (-1 / (1 - x)) - 2 * log x * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 4 * log x * log (1 - ξ) * (-1 / (1 - x)) + 4 *
        log x * log (1 - ξ) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 2 * log (1 - ξ - x) *
        log (ξ * x + (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) + 2 * log (1 - ξ - x) *
        log (ξ * x + (1 - ξ)) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + log (1 - ξ - x) *
        log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) - 2 * log (1 - ξ - x) *
        log (ξ * x + (1 - ξ) ^ 2) * (-1 / (1 - x)) - log (1 - ξ - x) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * log (1 - ξ - x) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + log (1 - ξ - x) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ))) + 2 * log (1 - ξ - x) * log (1 - ξ) * (-1 / (1 - x)) -
        log (1 - ξ - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (1 - ξ - x) *
        log (1 - ξ) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 * log (1 - ξ - x) *
        log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) - 2 * log (1 - ξ - x) * log (1 + ξ) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + (5 / 2) * log (ξ * x + (1 - ξ)) ^ 2 *
        (ξ / (ξ * x + (1 - ξ))) - log (ξ * x + (1 - ξ)) ^ 2 * (-1 / (1 - x)) - (5 / 2) *
        log (ξ * x + (1 - ξ)) ^ 2 * (ξ / (ξ * x + (1 - ξ) ^ 2)) + log (ξ * x + (1 - ξ)) ^ 2 *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 * log (ξ * x + (1 - ξ)) * log (1 - x) *
        (-1 / (1 - x)) - 2 * log (ξ * x + (1 - ξ)) * log (1 - x) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - log (ξ * x + (1 - ξ)) *
        log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) + log (ξ * x + (1 - ξ)) *
        log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (ξ * x + (1 - ξ)) *
        log ξ * (ξ / (ξ * x + (1 - ξ))) + 2 * log (ξ * x + (1 - ξ)) * log ξ *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (ξ * x + (1 - ξ)) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ))) + 2 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (-1 / (1 - x)) + 2 *
        log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 *
        log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 2 *
        log (ξ * x + (1 - ξ)) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) + 2 * log (ξ * x + (1 - ξ)) *
        log (1 + ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * log (ξ * x + (1 - ξ) ^ 2) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - x)) - 2 * log (ξ * x + (1 - ξ) ^ 2) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log ξ * (ξ / (ξ * x + (1 - ξ))) - 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log ξ * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (-1 / (1 - x)) + 2 * log (ξ * x + (1 - ξ) ^ 2) *
        log (1 - ξ) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) -
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 * (-1 / (1 - x)) + log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 * log ξ * log (1 + ξ) *
        (ξ / (ξ * x + (1 - ξ))) - 2 * log ξ * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) + (1 / 2) *
        log (1 - ξ) ^ 2 * (ξ / (ξ * x + (1 - ξ))) + log (1 - ξ) ^ 2 * (-1 / (1 - x)) - (1 / 2) *
        log (1 - ξ) ^ 2 * (ξ / (ξ * x + (1 - ξ) ^ 2)) - log (1 - ξ) ^ 2 *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q39 ξ) (((i5C1T_d28 hξ hx hxy).const_mul 2).add
      ((i5C1T_d29 hξ hx hxy).const_mul 1)) ?_
  simp only [i5C1F_19 hξ hx hxy]
  simp only [i5C1_id19 hξ hx hxy, i5C1_id20 hξ hx hxy]
  simp only [i5C1R19, i5C1R20]
  ring

/-- Part 40 of the primitive of `I(x)`. -/
noncomputable def i5C1Q40 (ξ x : ℝ) : ℝ :=
  (-2) * (Li₃ (ξ * (ξ * x ^ 2 + (1 - ξ) ^ 2) / ((1 - ξ) * (ξ * x + (1 - ξ)) * (1 - x))))

/-- Part 41 of the primitive of `I(x)`. -/
noncomputable def i5C1Q41 (ξ x : ℝ) : ℝ :=
  2 * (Li₃ ((ξ * x + (1 - ξ)) * (ξ * x + (1 - ξ) ^ 2) / (ξ * x ^ 2 + (1 - ξ) ^ 2)))

end QED.ThreeLoopD
