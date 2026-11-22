/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Tri
public import QED.ThreeLoopD.SetDMastersI5C1IdA
public import QED.ThreeLoopD.SetDMastersI5C1IdB
public import QED.ThreeLoopD.SetDMastersI5C1IdC
public import QED.ThreeLoopD.SetDMastersI5C1IdD

/-!
# Set (d), master `I₅`: the primitive of `I(x)` in parts (first half)

The primitive `P(x)` of the integrand `I(x)` of `t K₁(t) = ∫₀^{1-ξ} I(x) dx` is a combination of
products of three logarithms of the letters, dilogarithms of the basis times logarithms, and
thirty-two trilogarithms. It is split into parts `QED.ThreeLoopD.i5C1Q0`, ..., each with its
derivative in letter form (`QED.ThreeLoopD.hasDerivAt_i5C1Q0`, ...); for the trilogarithmic parts
the dilogarithms `Li₂ (h)` of the arguments are reduced to the basis by the identities of
`QED.ThreeLoopD.SetDMastersI5C1IdA`, ...

## Main results

* `QED.ThreeLoopD.hasDerivAt_i5C1Q0`, ..., `QED.ThreeLoopD.hasDerivAt_i5C1Q16`.
-/

@[expose] public section

open Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- Part 0 of the primitive of `I(x)`. -/
noncomputable def i5C1Q0 (ξ x : ℝ) : ℝ :=
  3 * (log x * log x * log (ξ * x + (1 - ξ))) + (-3) * (log x * log x * log (1 - ξ)) + 9 *
      (log x * log (1 - ξ - x) * log (ξ * x + (1 - ξ))) + (-9) * (log x * log (1 - ξ - x) *
      log (1 - ξ)) + (-6) * (log x * log (1 - ξ - x) * log (1 + ξ)) + (-9 / 2) *
      (log x * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)))

theorem hasDerivAt_i5C1Q0 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q0 ξ) (3 * log x ^ 2 * (ξ / (ξ * x + (1 - ξ))) + 9 * log x * log (1 - ξ - x) *
        (ξ / (ξ * x + (1 - ξ))) + 6 * log x * log (ξ * x + (1 - ξ)) * (1 / x) + 9 * log x *
        log (ξ * x + (1 - ξ)) * (-1 / (1 - ξ - x)) - 9 * log x * log (ξ * x + (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) - 6 * log x * log (1 - ξ) * (1 / x) - 9 * log x * log (1 - ξ) *
        (-1 / (1 - ξ - x)) - 6 * log x * log (1 + ξ) * (-1 / (1 - ξ - x)) + 9 * log (1 - ξ - x) *
        log (ξ * x + (1 - ξ)) * (1 / x) - 9 * log (1 - ξ - x) * log (1 - ξ) * (1 / x) - 6 *
        log (1 - ξ - x) * log (1 + ξ) * (1 / x) - (9 / 2) * log (ξ * x + (1 - ξ)) ^ 2 *
        (1 / x)) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q0 ξ) (((((((((i5C1L_d0 hx).mul (i5C1L_d0 hx)).mul
      (i5C1L_d2 hξ hx)).const_mul 3).add ((((i5C1L_d0 hx).mul (i5C1L_d0 hx)).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul (-3))).add ((((i5C1L_d0 hx).mul
      (i5C1L_d1 hxy)).mul (i5C1L_d2 hξ hx)).const_mul 9)).add ((((i5C1L_d0 hx).mul
      (i5C1L_d1 hxy)).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul (-9))).add
      ((((i5C1L_d0 hx).mul (i5C1L_d1 hxy)).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul
      (-6))).add ((((i5C1L_d0 hx).mul (i5C1L_d2 hξ hx)).mul (i5C1L_d2 hξ hx)).const_mul
      (-9 / 2))) ?_
  simp only [Pi.mul_apply]; ring

/-- Part 1 of the primitive of `I(x)`. -/
noncomputable def i5C1Q1 (ξ x : ℝ) : ℝ :=
  (-6) * (log x * log (ξ * x + (1 - ξ)) * log (1 - x)) + 6 * (log x * log (ξ * x + (1 - ξ)) *
      log (1 + ξ)) + (-2) * (log x * log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 10 *
      (log x * log (1 - x) * log (1 - ξ)) + 2 * (log x * log (ξ * x + (1 - ξ) ^ 2) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-4) * (log x * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ))

theorem hasDerivAt_i5C1Q1 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q1 ξ) (-6 * log x * log (ξ * x + (1 - ξ)) * (-1 / (1 - x)) - 6 * log x *
        log (1 - x) * (ξ / (ξ * x + (1 - ξ))) - 2 * log x * log (1 - x) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 * log x * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 2 * log x * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (-1 / (1 - x)) + 2 * log x * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ) ^ 2)) +
        10 * log x * log (1 - ξ) * (-1 / (1 - x)) - 4 * log x * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 6 * log x * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) - 6 *
        log (ξ * x + (1 - ξ)) * log (1 - x) * (1 / x) + 6 * log (ξ * x + (1 - ξ)) * log (1 + ξ) *
        (1 / x) - 2 * log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) + 10 * log (1 - x) *
        log (1 - ξ) * (1 / x) + 2 * log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (1 / x) - 4 * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (1 / x)) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q1 ξ) (((((((((i5C1L_d0 hx).mul (i5C1L_d2 hξ hx)).mul
      (i5C1L_d3 hξ hxy)).const_mul (-6)).add ((((i5C1L_d0 hx).mul (i5C1L_d2 hξ hx)).mul
      (hasDerivAt_const x (log (1 + ξ)))).const_mul 6)).add ((((i5C1L_d0 hx).mul
      (i5C1L_d3 hξ hxy)).mul (i5C1L_d5 hξ)).const_mul (-2))).add ((((i5C1L_d0 hx).mul
      (i5C1L_d3 hξ hxy)).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul 10)).add
      ((((i5C1L_d0 hx).mul (i5C1L_d4 hξ hx)).mul (i5C1L_d5 hξ)).const_mul 2)).add
      ((((i5C1L_d0 hx).mul (i5C1L_d4 hξ hx)).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul
      (-4))) ?_
  simp only [Pi.mul_apply]; ring

/-- Part 2 of the primitive of `I(x)`. -/
noncomputable def i5C1Q2 (ξ x : ℝ) : ℝ :=
  (-4) * (log x * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ)) + (25 / 2) *
      (log x * log (1 - ξ) * log (1 - ξ)) + (7 / 2) * (log (1 - ξ - x) * log (ξ * x + (1 - ξ)) *
      log (ξ * x + (1 - ξ))) + (-1) * (log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * log (1 - x)) + 1 *
      (log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2)) + (-6) *
      (log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2))

theorem hasDerivAt_i5C1Q2 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q2 ξ) (-4 * log x * log (1 - ξ) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
        7 * log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) - log (1 - ξ - x) *
        log (ξ * x + (1 - ξ)) * (-1 / (1 - x)) + log (1 - ξ - x) * log (ξ * x + (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 6 * log (1 - ξ - x) * log (ξ * x + (1 - ξ)) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - log (1 - ξ - x) * log (1 - x) *
        (ξ / (ξ * x + (1 - ξ))) + log (1 - ξ - x) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ))) - 6 * log (1 - ξ - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ))) + (7 / 2) * log (ξ * x + (1 - ξ)) ^ 2 * (-1 / (1 - ξ - x)) -
        log (ξ * x + (1 - ξ)) * log (1 - x) * (-1 / (1 - ξ - x)) + log (ξ * x + (1 - ξ)) *
        log (ξ * x + (1 - ξ) ^ 2) * (-1 / (1 - ξ - x)) - 6 * log (ξ * x + (1 - ξ)) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - ξ - x)) - 4 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        log (1 - ξ) * (1 / x) + (25 / 2) * log (1 - ξ) ^ 2 * (1 / x)) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q2 ξ) (((((((((i5C1L_d0 hx).mul (i5C1L_d5 hξ)).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul (-4)).add ((((i5C1L_d0 hx).mul
      (hasDerivAt_const x (log (1 - ξ)))).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul
      (25 / 2))).add ((((i5C1L_d1 hxy).mul (i5C1L_d2 hξ hx)).mul (i5C1L_d2 hξ hx)).const_mul
      (7 / 2))).add ((((i5C1L_d1 hxy).mul (i5C1L_d2 hξ hx)).mul (i5C1L_d3 hξ hxy)).const_mul
      (-1))).add ((((i5C1L_d1 hxy).mul (i5C1L_d2 hξ hx)).mul (i5C1L_d4 hξ hx)).const_mul 1)).add
      ((((i5C1L_d1 hxy).mul (i5C1L_d2 hξ hx)).mul (i5C1L_d5 hξ)).const_mul (-6))) ?_
  simp only [Pi.mul_apply]; ring

/-- Part 3 of the primitive of `I(x)`. -/
noncomputable def i5C1Q3 (ξ x : ℝ) : ℝ :=
  3 * (log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * log ξ) + (-11) *
      (log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * log (1 - ξ)) + (-2) *
      (log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * log (1 + ξ)) + 2 *
      (log (1 - ξ - x) * log (1 - x) * log (1 - ξ)) + 2 * (log (1 - ξ - x) * log (1 - x) *
      log (1 + ξ)) + (-1) * (log (1 - ξ - x) * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ))

theorem hasDerivAt_i5C1Q3 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q3 ξ) (3 * log (1 - ξ - x) * log ξ * (ξ / (ξ * x + (1 - ξ))) - 11 *
        log (1 - ξ - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + 2 * log (1 - ξ - x) *
        log (1 - ξ) * (-1 / (1 - x)) - log (1 - ξ - x) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (1 - ξ - x) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) +
        2 * log (1 - ξ - x) * log (1 + ξ) * (-1 / (1 - x)) + 3 * log (ξ * x + (1 - ξ)) * log ξ *
        (-1 / (1 - ξ - x)) - 11 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (-1 / (1 - ξ - x)) - 2 *
        log (ξ * x + (1 - ξ)) * log (1 + ξ) * (-1 / (1 - ξ - x)) + 2 * log (1 - x) * log (1 - ξ) *
        (-1 / (1 - ξ - x)) + 2 * log (1 - x) * log (1 + ξ) * (-1 / (1 - ξ - x)) -
        log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (-1 / (1 - ξ - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q3 ξ) (((((((((i5C1L_d1 hxy).mul (i5C1L_d2 hξ hx)).mul
      (hasDerivAt_const x (log ξ))).const_mul 3).add ((((i5C1L_d1 hxy).mul (i5C1L_d2 hξ hx)).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul (-11))).add ((((i5C1L_d1 hxy).mul
      (i5C1L_d2 hξ hx)).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul (-2))).add
      ((((i5C1L_d1 hxy).mul (i5C1L_d3 hξ hxy)).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul
      2)).add ((((i5C1L_d1 hxy).mul (i5C1L_d3 hξ hxy)).mul (hasDerivAt_const x (log (1 +
      ξ)))).const_mul 2)).add ((((i5C1L_d1 hxy).mul (i5C1L_d4 hξ hx)).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul (-1))) ?_
  ring

/-- Part 4 of the primitive of `I(x)`. -/
noncomputable def i5C1Q4 (ξ x : ℝ) : ℝ :=
  1 * (log (1 - ξ - x) * log (ξ * x + (1 - ξ) ^ 2) * log (1 + ξ)) + 3 *
      (log (1 - ξ - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-6) *
      (log (1 - ξ - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ)) + (-2) *
      (log (1 - ξ - x) * log ξ * log (1 - ξ)) + (-2) * (log (1 - ξ - x) * log ξ * log (1 + ξ)) +
      (39 / 2) * (log (1 - ξ - x) * log (1 - ξ) * log (1 - ξ))

theorem hasDerivAt_i5C1Q4 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q4 ξ) (6 * log (1 - ξ - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 6 * log (1 - ξ - x) * log (1 - ξ) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + log (1 - ξ - x) * log (1 + ξ) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + log (ξ * x + (1 - ξ) ^ 2) * log (1 + ξ) *
        (-1 / (1 - ξ - x)) + 3 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 * (-1 / (1 - ξ - x)) - 6 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) * (-1 / (1 - ξ - x)) - 2 * log ξ *
        log (1 - ξ) * (-1 / (1 - ξ - x)) - 2 * log ξ * log (1 + ξ) * (-1 / (1 - ξ - x)) +
        (39 / 2) * log (1 - ξ) ^ 2 * (-1 / (1 - ξ - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q4 ξ) (((((((((i5C1L_d1 hxy).mul (i5C1L_d4 hξ hx)).mul
      (hasDerivAt_const x (log (1 + ξ)))).const_mul 1).add ((((i5C1L_d1 hxy).mul (i5C1L_d5 hξ)).mul
      (i5C1L_d5 hξ)).const_mul 3)).add ((((i5C1L_d1 hxy).mul (i5C1L_d5 hξ)).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul (-6))).add ((((i5C1L_d1 hxy).mul
      (hasDerivAt_const x (log ξ))).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul (-2))).add
      ((((i5C1L_d1 hxy).mul (hasDerivAt_const x (log ξ))).mul (hasDerivAt_const x (log (1 +
      ξ)))).const_mul (-2))).add ((((i5C1L_d1 hxy).mul (hasDerivAt_const x (log (1 - ξ)))).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul (39 / 2))) ?_
  simp only [Pi.mul_apply]; ring

/-- Part 5 of the primitive of `I(x)`. -/
noncomputable def i5C1Q5 (ξ x : ℝ) : ℝ :=
  13 * (log (1 - ξ - x) * log (1 - ξ) * log (1 + ξ)) + 1 * (log (1 - ξ - x) * log (1 + ξ) *
      log (1 + ξ)) + (-1 / 3) * (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) *
      log (ξ * x + (1 - ξ))) + (15 / 2) * (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) *
      log (1 - x)) + (-3 / 2) * (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) *
      log (ξ * x + (1 - ξ) ^ 2)) + 1 * (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2))

theorem hasDerivAt_i5C1Q5 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q5 ξ) (-log (ξ * x + (1 - ξ)) ^ 2 * (ξ / (ξ * x + (1 - ξ))) + (15 / 2) *
        log (ξ * x + (1 - ξ)) ^ 2 * (-1 / (1 - x)) - (3 / 2) * log (ξ * x + (1 - ξ)) ^ 2 *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + log (ξ * x + (1 - ξ)) ^ 2 *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 15 * log (ξ * x + (1 - ξ)) * log (1 - x) *
        (ξ / (ξ * x + (1 - ξ))) - 3 * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ))) + 2 * log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ))) + 13 * log (1 - ξ) * log (1 + ξ) * (-1 / (1 - ξ - x)) +
        log (1 + ξ) ^ 2 * (-1 / (1 - ξ - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q5 ξ) (((((((((i5C1L_d1 hxy).mul
      (hasDerivAt_const x (log (1 - ξ)))).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul 13).add
      ((((i5C1L_d1 hxy).mul (hasDerivAt_const x (log (1 + ξ)))).mul (hasDerivAt_const x (log (1 +
      ξ)))).const_mul 1)).add ((((i5C1L_d2 hξ hx).mul (i5C1L_d2 hξ hx)).mul
      (i5C1L_d2 hξ hx)).const_mul (-1 / 3))).add ((((i5C1L_d2 hξ hx).mul (i5C1L_d2 hξ hx)).mul
      (i5C1L_d3 hξ hxy)).const_mul (15 / 2))).add ((((i5C1L_d2 hξ hx).mul (i5C1L_d2 hξ hx)).mul
      (i5C1L_d4 hξ hx)).const_mul (-3 / 2))).add ((((i5C1L_d2 hξ hx).mul (i5C1L_d2 hξ hx)).mul
      (i5C1L_d5 hξ)).const_mul 1)) ?_
  simp only [Pi.mul_apply]; ring

/-- Part 6 of the primitive of `I(x)`. -/
noncomputable def i5C1Q6 (ξ x : ℝ) : ℝ :=
  (-3) * (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log ξ) + (19 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (1 - ξ)) + (5 / 2) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ)) * log (1 + ξ)) + (-3 / 2) *
      (log (ξ * x + (1 - ξ)) * log (1 - x) * log (1 - x)) + (-6) *
      (log (ξ * x + (1 - ξ)) * log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 1 *
      (log (ξ * x + (1 - ξ)) * log (1 - x) * log (1 - ξ))

theorem hasDerivAt_i5C1Q6 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q6 ξ) (-3 * log (ξ * x + (1 - ξ)) * log (1 - x) * (-1 / (1 - x)) - 6 *
        log (ξ * x + (1 - ξ)) * log (1 - x) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 6 *
        log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - x)) - 6 *
        log (ξ * x + (1 - ξ)) * log ξ * (ξ / (ξ * x + (1 - ξ))) + 19 * log (ξ * x + (1 - ξ)) *
        log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + log (ξ * x + (1 - ξ)) * log (1 - ξ) *
        (-1 / (1 - x)) + 5 * log (ξ * x + (1 - ξ)) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) -
        (3 / 2) * log (1 - x) ^ 2 * (ξ / (ξ * x + (1 - ξ))) - 6 * log (1 - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) + log (1 - x) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ)))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q6 ξ) (((((((((i5C1L_d2 hξ hx).mul (i5C1L_d2 hξ hx)).mul
      (hasDerivAt_const x (log ξ))).const_mul (-3)).add ((((i5C1L_d2 hξ hx).mul
      (i5C1L_d2 hξ hx)).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul (19 / 2))).add
      ((((i5C1L_d2 hξ hx).mul (i5C1L_d2 hξ hx)).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul
      (5 / 2))).add ((((i5C1L_d2 hξ hx).mul (i5C1L_d3 hξ hxy)).mul (i5C1L_d3 hξ hxy)).const_mul
      (-3 / 2))).add ((((i5C1L_d2 hξ hx).mul (i5C1L_d3 hξ hxy)).mul (i5C1L_d5 hξ)).const_mul
      (-6))).add ((((i5C1L_d2 hξ hx).mul (i5C1L_d3 hξ hxy)).mul (hasDerivAt_const x (log (1 -
      ξ)))).const_mul 1)) ?_
  simp only [Pi.mul_apply]; ring

/-- Part 7 of the primitive of `I(x)`. -/
noncomputable def i5C1Q7 (ξ x : ℝ) : ℝ :=
  (-5) * (log (ξ * x + (1 - ξ)) * log (1 - x) * log (1 + ξ)) + 1 *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2)) + 3 *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) * log ξ) + (-1) *
      (log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) * log (1 + ξ)) + 4 *
      (log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
      (-2) * (log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log ξ)

theorem hasDerivAt_i5C1Q7 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q7 ξ) (2 * log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 8 * log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 3 * log (ξ * x + (1 - ξ)) * log ξ *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 * log (ξ * x + (1 - ξ)) * log ξ *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 5 * log (ξ * x + (1 - ξ)) * log (1 + ξ) *
        (-1 / (1 - x)) - log (ξ * x + (1 - ξ)) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 5 *
        log (1 - x) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) + log (ξ * x + (1 - ξ) ^ 2) ^ 2 *
        (ξ / (ξ * x + (1 - ξ))) + 3 * log (ξ * x + (1 - ξ) ^ 2) * log ξ * (ξ / (ξ * x + (1 - ξ))) -
        log (ξ * x + (1 - ξ) ^ 2) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) + 4 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 * (ξ / (ξ * x + (1 - ξ))) - 2 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log ξ * (ξ / (ξ * x + (1 - ξ)))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q7 ξ) (((((((((i5C1L_d2 hξ hx).mul (i5C1L_d3 hξ hxy)).mul
      (hasDerivAt_const x (log (1 + ξ)))).const_mul (-5)).add ((((i5C1L_d2 hξ hx).mul
      (i5C1L_d4 hξ hx)).mul (i5C1L_d4 hξ hx)).const_mul 1)).add ((((i5C1L_d2 hξ hx).mul
      (i5C1L_d4 hξ hx)).mul (hasDerivAt_const x (log ξ))).const_mul 3)).add
      ((((i5C1L_d2 hξ hx).mul (i5C1L_d4 hξ hx)).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul
      (-1))).add ((((i5C1L_d2 hξ hx).mul (i5C1L_d5 hξ)).mul (i5C1L_d5 hξ)).const_mul 4)).add
      ((((i5C1L_d2 hξ hx).mul (i5C1L_d5 hξ)).mul (hasDerivAt_const x (log ξ))).const_mul (-2))) ?_
  simp only [Pi.mul_apply]; ring

/-- Part 8 of the primitive of `I(x)`. -/
noncomputable def i5C1Q8 (ξ x : ℝ) : ℝ :=
  (-12) * (log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ)) + (-1 / 2) *
      (log (ξ * x + (1 - ξ)) * log ξ * log ξ) + 5 * (log (ξ * x + (1 - ξ)) * log ξ * log (1 - ξ)) +
      1 * (log (ξ * x + (1 - ξ)) * log ξ * log (1 + ξ)) + (-14) *
      (log (ξ * x + (1 - ξ)) * log (1 - ξ) * log (1 + ξ)) + (-1) *
      (log (ξ * x + (1 - ξ)) * log (1 + ξ) * log (1 + ξ))

theorem hasDerivAt_i5C1Q8 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (_hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q8 ξ) (-12 * log (ξ * x + (1 - ξ)) * log (1 - ξ) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 12 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - (1 / 2) * log ξ ^ 2 * (ξ / (ξ * x + (1 - ξ))) + 5 *
        log ξ * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + log ξ * log (1 + ξ) *
        (ξ / (ξ * x + (1 - ξ))) - 14 * log (1 - ξ) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) -
        log (1 + ξ) ^ 2 * (ξ / (ξ * x + (1 - ξ)))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q8 ξ) (((((((((i5C1L_d2 hξ hx).mul (i5C1L_d5 hξ)).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul (-12)).add ((((i5C1L_d2 hξ hx).mul
      (hasDerivAt_const x (log ξ))).mul (hasDerivAt_const x (log ξ))).const_mul (-1 / 2))).add
      ((((i5C1L_d2 hξ hx).mul (hasDerivAt_const x (log ξ))).mul (hasDerivAt_const x (log (1 -
      ξ)))).const_mul 5)).add ((((i5C1L_d2 hξ hx).mul (hasDerivAt_const x (log ξ))).mul
      (hasDerivAt_const x (log (1 + ξ)))).const_mul 1)).add ((((i5C1L_d2 hξ hx).mul
      (hasDerivAt_const x (log (1 - ξ)))).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul
      (-14))).add ((((i5C1L_d2 hξ hx).mul (hasDerivAt_const x (log (1 + ξ)))).mul
      (hasDerivAt_const x (log (1 + ξ)))).const_mul (-1))) ?_
  ring

/-- Part 9 of the primitive of `I(x)`. -/
noncomputable def i5C1Q9 (ξ x : ℝ) : ℝ :=
  1 * (log (1 - x) * log (1 - x) * log (1 - ξ)) + 1 * (log (1 - x) * log (1 - x) * log (1 + ξ)) +
      1 * (log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-2) *
      (log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ)) + (-1) *
      (log (1 - x) * log ξ * log (1 - ξ)) + (-1) * (log (1 - x) * log ξ * log (1 + ξ))

theorem hasDerivAt_i5C1Q9 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (_hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q9 ξ) (2 * log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 * log (1 - x) * log (1 - ξ) *
        (-1 / (1 - x)) - 2 * log (1 - x) * log (1 - ξ) * (ξ * (2 * x) / (ξ * x ^ 2 +
        (1 - ξ) ^ 2)) + 2 * log (1 - x) * log (1 + ξ) * (-1 / (1 - x)) +
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 * (-1 / (1 - x)) - 2 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        log (1 - ξ) * (-1 / (1 - x)) - log ξ * log (1 - ξ) * (-1 / (1 - x)) - log ξ * log (1 + ξ) *
        (-1 / (1 - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q9 ξ) (((((((((i5C1L_d3 hξ hxy).mul
      (i5C1L_d3 hξ hxy)).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul 1).add
      ((((i5C1L_d3 hξ hxy).mul (i5C1L_d3 hξ hxy)).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul
      1)).add ((((i5C1L_d3 hξ hxy).mul (i5C1L_d5 hξ)).mul (i5C1L_d5 hξ)).const_mul 1)).add
      ((((i5C1L_d3 hξ hxy).mul (i5C1L_d5 hξ)).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul
      (-2))).add ((((i5C1L_d3 hξ hxy).mul (hasDerivAt_const x (log ξ))).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul (-1))).add ((((i5C1L_d3 hξ hxy).mul
      (hasDerivAt_const x (log ξ))).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul (-1))) ?_
  simp only [Pi.mul_apply]; ring

/-- Part 10 of the primitive of `I(x)`. -/
noncomputable def i5C1Q10 (ξ x : ℝ) : ℝ :=
  (-3 / 2) * (log (1 - x) * log (1 - ξ) * log (1 - ξ)) + 3 * (log (1 - x) * log (1 - ξ) *
      log (1 + ξ)) + (3 / 2) * (log (1 - x) * log (1 + ξ) * log (1 + ξ)) + (-2) *
      (log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
      (-1) * (log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2) * log ξ) + 3 *
      (log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ))

theorem hasDerivAt_i5C1Q10 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q10 ξ) (-2 * log (ξ * x + (1 - ξ) ^ 2) ^ 2 * (ξ *
        (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 4 * log (ξ * x + (1 - ξ) ^ 2) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log ξ * (ξ / (ξ * x + (1 - ξ) ^ 2)) + 6 *
        log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) - (3 / 2) *
        log (1 - ξ) ^ 2 * (-1 / (1 - x)) + 3 * log (1 - ξ) * log (1 + ξ) * (-1 / (1 - x)) +
        (3 / 2) * log (1 + ξ) ^ 2 * (-1 / (1 - x))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q10 ξ) (((((((((i5C1L_d3 hξ hxy).mul
      (hasDerivAt_const x (log (1 - ξ)))).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul
      (-3 / 2)).add ((((i5C1L_d3 hξ hxy).mul (hasDerivAt_const x (log (1 - ξ)))).mul
      (hasDerivAt_const x (log (1 + ξ)))).const_mul 3)).add ((((i5C1L_d3 hξ hxy).mul
      (hasDerivAt_const x (log (1 + ξ)))).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul
      (3 / 2))).add ((((i5C1L_d4 hξ hx).mul (i5C1L_d4 hξ hx)).mul (i5C1L_d5 hξ)).const_mul
      (-2))).add ((((i5C1L_d4 hξ hx).mul (i5C1L_d4 hξ hx)).mul (hasDerivAt_const x
      (log ξ))).const_mul (-1))).add ((((i5C1L_d4 hξ hx).mul (i5C1L_d4 hξ hx)).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul 3)) ?_
  simp only [Pi.mul_apply]; ring

/-- Part 11 of the primitive of `I(x)`. -/
noncomputable def i5C1Q11 (ξ x : ℝ) : ℝ :=
  1 * (log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
      (-1) * (log (ξ * x + (1 - ξ) ^ 2) * log ξ * log (1 - ξ)) + 2 *
      (log (ξ * x + (1 - ξ) ^ 2) * log ξ * log (1 + ξ)) + (-5 / 2) *
      (log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * log (1 - ξ)) + (-5 / 3) *
      (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 2 * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
      log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ))

theorem hasDerivAt_i5C1Q11 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (_hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q11 ξ) (2 * log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 5 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) ^ 2 *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 4 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        log (1 - ξ) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - log ξ * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) + 2 * log ξ * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ) ^ 2)) -
        (5 / 2) * log (1 - ξ) ^ 2 * (ξ / (ξ * x + (1 - ξ) ^ 2))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q11 ξ) (((((((((i5C1L_d4 hξ hx).mul (i5C1L_d5 hξ)).mul
      (i5C1L_d5 hξ)).const_mul 1).add ((((i5C1L_d4 hξ hx).mul (hasDerivAt_const x (log ξ))).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul (-1))).add ((((i5C1L_d4 hξ hx).mul
      (hasDerivAt_const x (log ξ))).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul 2)).add
      ((((i5C1L_d4 hξ hx).mul (hasDerivAt_const x (log (1 - ξ)))).mul (hasDerivAt_const x (log (1 -
      ξ)))).const_mul (-5 / 2))).add ((((i5C1L_d5 hξ).mul (i5C1L_d5 hξ)).mul
      (i5C1L_d5 hξ)).const_mul (-5 / 3))).add ((((i5C1L_d5 hξ).mul (i5C1L_d5 hξ)).mul
      (hasDerivAt_const x (log (1 - ξ)))).const_mul 2)) ?_
  simp only [Pi.mul_apply]; ring

/-- Part 12 of the primitive of `I(x)`. -/
noncomputable def i5C1Q12 (ξ x : ℝ) : ℝ :=
  7 * (log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) * log (1 - ξ))

theorem hasDerivAt_i5C1Q12 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (_hx : 0 < x) (_hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q12 ξ) (7 * log (1 - ξ) ^ 2 * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2))) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q12 ξ) ((((i5C1L_d5 hξ).mul (hasDerivAt_const x (log (1 -
      ξ)))).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul 7) ?_
  ring

/-- Part 13 of the primitive of `I(x)`. -/
noncomputable def i5C1Q13 (ξ x : ℝ) : ℝ :=
  2 * (Li₂ (x) * log (1 - ξ - x)) + 2 * (Li₂ (x) * log (ξ * x + (1 - ξ))) + (-2) *
      (Li₂ (x) * log (1 - x)) + (-2) * (Li₂ (x) * log (ξ * x + (1 - ξ) ^ 2)) + (-4) *
      (Li₂ (x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 4 * (Li₂ (x) * log (1 - ξ))

theorem hasDerivAt_i5C1Q13 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q13 ξ) (2 * Li₂ (x) * (-1 / (1 - ξ - x)) + 2 * Li₂ (x) *
        (ξ / (ξ * x + (1 - ξ))) - 2 * Li₂ (x) * (-1 / (1 - x)) - 2 * Li₂ (x) *
        (ξ / (ξ * x + (1 - ξ) ^ 2)) - 4 * Li₂ (x) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 2 *
        log (1 - ξ - x) * log (1 - x) * (1 / x) - 2 * log (ξ * x + (1 - ξ)) * log (1 - x) *
        (1 / x) + 2 * log (1 - x) ^ 2 * (1 / x) + 2 * log (1 - x) * log (ξ * x + (1 - ξ) ^ 2) *
        (1 / x) + 4 * log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) - 4 * log (1 - x) *
        log (1 - ξ) * (1 / x)) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q13 ξ) ((((((((i5C1B_d0 hξ hx hxy).mul
      (i5C1L_d1 hxy)).const_mul 2).add (((i5C1B_d0 hξ hx hxy).mul (i5C1L_d2 hξ hx)).const_mul
      2)).add (((i5C1B_d0 hξ hx hxy).mul (i5C1L_d3 hξ hxy)).const_mul (-2))).add
      (((i5C1B_d0 hξ hx hxy).mul (i5C1L_d4 hξ hx)).const_mul (-2))).add
      (((i5C1B_d0 hξ hx hxy).mul (i5C1L_d5 hξ)).const_mul (-4))).add
      (((i5C1B_d0 hξ hx hxy).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul 4)) ?_
  ring

/-- Part 14 of the primitive of `I(x)`. -/
noncomputable def i5C1Q14 (ξ x : ℝ) : ℝ :=
  6 * (Li₂ (x / (1 - ξ)) * log x) + (-3) * (Li₂ (x / (1 - ξ)) * log (ξ * x + (1 - ξ))) + (-3) *
      (Li₂ (x / (1 - ξ)) * log (1 - x)) + 8 * (Li₂ (x / (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
      3 * (Li₂ (x / (1 - ξ)) * log ξ) + (-25) * (Li₂ (x / (1 - ξ)) * log (1 - ξ))

theorem hasDerivAt_i5C1Q14 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q14 ξ) (6 * Li₂ (x / (1 - ξ)) * (1 / x) - 3 * Li₂ (x / (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) - 3 * Li₂ (x / (1 - ξ)) * (-1 / (1 - x)) + 8 * Li₂ (x / (1 - ξ)) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) - 6 * log x * log (1 - ξ - x) * (1 / x) + 6 *
        log x * log (1 - ξ) * (1 / x) + 3 * log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * (1 / x) + 3 *
        log (1 - ξ - x) * log (1 - x) * (1 / x) - 8 * log (1 - ξ - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) - 3 * log (1 - ξ - x) * log ξ * (1 / x) + 25 *
        log (1 - ξ - x) * log (1 - ξ) * (1 / x) - 3 * log (ξ * x + (1 - ξ)) * log (1 - ξ) *
        (1 / x) - 3 * log (1 - x) * log (1 - ξ) * (1 / x) + 8 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        log (1 - ξ) * (1 / x) + 3 * log ξ * log (1 - ξ) * (1 / x) - 25 * log (1 - ξ) ^ 2 *
        (1 / x)) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q14 ξ) ((((((((i5C1B_d1 hξ hx hxy).mul
      (i5C1L_d0 hx)).const_mul 6).add (((i5C1B_d1 hξ hx hxy).mul (i5C1L_d2 hξ hx)).const_mul
      (-3))).add (((i5C1B_d1 hξ hx hxy).mul (i5C1L_d3 hξ hxy)).const_mul (-3))).add
      (((i5C1B_d1 hξ hx hxy).mul (i5C1L_d5 hξ)).const_mul 8)).add
      (((i5C1B_d1 hξ hx hxy).mul (hasDerivAt_const x (log ξ))).const_mul 3)).add
      (((i5C1B_d1 hξ hx hxy).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul (-25))) ?_
  ring

/-- Part 15 of the primitive of `I(x)`. -/
noncomputable def i5C1Q15 (ξ x : ℝ) : ℝ :=
  (-3) * (Li₂ (x / (1 - ξ)) * log (1 + ξ)) + (-1) * (Li₂ (ξ / (1 - x)) * log (ξ * x + (1 - ξ))) +
      2 * (Li₂ (ξ / (1 - x)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + (-3) *
      (Li₂ (ξ / (1 - x)) * log (1 - ξ)) + (-1) * (Li₂ (ξ / (1 - x)) * log (1 + ξ)) + 1 *
      (Li₂ (ξ * (1 - x)) * log (1 - ξ - x))

theorem hasDerivAt_i5C1Q15 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q15 ξ) (-Li₂ (ξ / (1 - x)) * (ξ / (ξ * x + (1 - ξ))) + 2 * Li₂ (ξ / (1 - x)) *
        (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) + Li₂ (ξ * (1 - x)) * (-1 / (1 - ξ - x)) - 2 *
        log (1 - ξ - x) * log (ξ * x + (1 - ξ)) * (-1 / (1 - x)) + 2 * log (1 - ξ - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - x)) - 3 * log (1 - ξ - x) * log (1 - ξ) *
        (-1 / (1 - x)) + 3 * log (1 - ξ - x) * log (1 + ξ) * (1 / x) - log (1 - ξ - x) *
        log (1 + ξ) * (-1 / (1 - x)) + log (ξ * x + (1 - ξ)) * log (1 - x) * (-1 / (1 - x)) - 2 *
        log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - x)) + 3 * log (1 - x) *
        log (1 - ξ) * (-1 / (1 - x)) + log (1 - x) * log (1 + ξ) * (-1 / (1 - x)) - 3 *
        log (1 - ξ) * log (1 + ξ) * (1 / x)) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q15 ξ) ((((((((i5C1B_d1 hξ hx hxy).mul
      (hasDerivAt_const x (log (1 + ξ)))).const_mul (-3)).add (((i5C1B_d2 hξ hx hxy).mul
      (i5C1L_d2 hξ hx)).const_mul (-1))).add (((i5C1B_d2 hξ hx hxy).mul (i5C1L_d5 hξ)).const_mul
      2)).add (((i5C1B_d2 hξ hx hxy).mul (hasDerivAt_const x (log (1 - ξ)))).const_mul (-3))).add
      (((i5C1B_d2 hξ hx hxy).mul (hasDerivAt_const x (log (1 + ξ)))).const_mul (-1))).add
      (((i5C1B_d3 hξ hx hxy).mul (i5C1L_d1 hxy)).const_mul 1)) ?_
  ring

/-- Part 16 of the primitive of `I(x)`. -/
noncomputable def i5C1Q16 (ξ x : ℝ) : ℝ :=
  (-4) * (Li₂ (ξ * (1 - x)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2)) + 3 *
      (Li₂ (ξ * (1 - x)) * log (1 - ξ)) + (-1) * (Li₂ (ξ * (1 - x)) * log (1 + ξ)) + 1 *
      (Li₂ (-(ξ * x / (1 - ξ))) * log (1 - ξ - x)) + 4 * (Li₂ (-(ξ * x / (1 - ξ))) *
      log (ξ * x + (1 - ξ))) + (-1) * (Li₂ (-(ξ * x / (1 - ξ))) * log (1 - x))

theorem hasDerivAt_i5C1Q16 {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1Q16 ξ) (-4 * Li₂ (ξ * (1 - x)) * (ξ * (2 * x) / (ξ * x ^ 2 + (1 - ξ) ^ 2)) +
        Li₂ (-(ξ * x / (1 - ξ))) * (-1 / (1 - ξ - x)) + 4 * Li₂ (-(ξ * x / (1 - ξ))) *
        (ξ / (ξ * x + (1 - ξ))) - Li₂ (-(ξ * x / (1 - ξ))) * (-1 / (1 - x)) - log (1 - ξ - x) *
        log (ξ * x + (1 - ξ)) * (1 / x) + log (1 - ξ - x) * log (1 - ξ) * (1 / x) - 4 *
        log (ξ * x + (1 - ξ)) ^ 2 * (1 / x) + log (ξ * x + (1 - ξ)) * log (1 - x) * (1 / x) + 4 *
        log (ξ * x + (1 - ξ)) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - x)) + 4 *
        log (ξ * x + (1 - ξ)) * log (1 - ξ) * (1 / x) - 3 * log (ξ * x + (1 - ξ)) * log (1 - ξ) *
        (-1 / (1 - x)) + log (ξ * x + (1 - ξ)) * log (1 + ξ) * (-1 / (1 - x)) - log (1 - x) *
        log (1 - ξ) * (1 / x)) x := by
  refine HasDerivAt.congr_deriv (f := i5C1Q16 ξ) ((((((((i5C1B_d3 hξ hx hxy).mul
      (i5C1L_d5 hξ)).const_mul (-4)).add (((i5C1B_d3 hξ hx hxy).mul (hasDerivAt_const x (log (1 -
      ξ)))).const_mul 3)).add (((i5C1B_d3 hξ hx hxy).mul (hasDerivAt_const x (log (1 +
      ξ)))).const_mul (-1))).add (((i5C1B_d4 hξ hx hxy).mul (i5C1L_d1 hxy)).const_mul 1)).add
      (((i5C1B_d4 hξ hx hxy).mul (i5C1L_d2 hξ hx)).const_mul 4)).add
      (((i5C1B_d4 hξ hx hxy).mul (i5C1L_d3 hξ hxy)).const_mul (-1))) ?_
  ring

end QED.ThreeLoopD
