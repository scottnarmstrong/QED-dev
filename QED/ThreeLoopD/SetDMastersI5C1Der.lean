/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1PBb
public import QED.ThreeLoopD.SetDMastersI5C1Inn

/-!
# Set (d), master `I₅`: the primitive of the integrand `I(x)` of `t K₁(t)`

With the dilogarithm identities for `Li₂(ρ₀/ρ₁)`, `Li₂(D₁)`, `Li₂(D₂)` the integrand
`QED.ThreeLoopD.i5K1I` becomes a combination of the letter derivatives with coefficients in the
logarithms of the letters and the dilogarithm basis (`QED.ThreeLoopD.i5K1I_eq_letters`); this
is the derivative of the primitive `QED.ThreeLoopD.i5C1PB` (`QED.ThreeLoopD.hasDerivAt_i5C1PB`).

## Main results

* `QED.ThreeLoopD.i5K1I_eq_letters`, `QED.ThreeLoopD.hasDerivAt_i5C1PB`.
-/

@[expose] public section

open Set Real QED.Polylog

namespace QED.ThreeLoopD

/-- **The integrand in letter form**: `I(x)` as a combination of the letter derivatives with
logarithmic and dilogarithmic coefficients in the basis. -/
theorem i5K1I_eq_letters {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    i5K1I ξ x = 2 * Li₂ (x) * (ξ / (ξ * x + (1 - ξ))) + Li₂ (x / (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) - Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) +
        4 * Li₂ (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) * (ξ / (ξ * x + (1 - ξ))) -
        Li₂ (ξ / (1 - x)) * (ξ / (ξ * x + (1 - ξ))) - 3 * Li₂ (ξ * (1 - x)) *
        (ξ / (ξ * x + (1 - ξ))) + Li₂ (-(ξ * x / (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) + 4 *
        Li₂ (x / (ξ * x + (1 - ξ))) * (ξ / (ξ * x + (1 - ξ))) - 8 *
        Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) * (ξ / (ξ * x + (1 - ξ))) + 5 *
        Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) * (ξ / (ξ * x + (1 - ξ))) - 4 *
        Li₂ (x / (ξ * x + (1 - ξ) ^ 2)) * (ξ / (ξ * x + (1 - ξ))) - (1 / 3) * π ^ 2 *
        (ξ / (ξ * x + (1 - ξ))) + 3 * log x ^ 2 * (ξ / (ξ * x + (1 - ξ))) - 3 * log x *
        log (ξ * x + (1 - ξ)) * (-1 / (1 - ξ - x)) + 3 * log x * log (ξ * x + (1 - ξ)) *
        (ξ / (ξ * x + (1 - ξ))) - 6 * log x * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) + 6 * log x *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - ξ - x)) - 6 * log x *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) + 12 * log x * log (1 - ξ) *
        (1 / x) - 9 * log x * log (1 - ξ) * (-1 / (1 - ξ - x)) + 9 * log x * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ))) - 3 * log x * log (1 + ξ) * (-1 / (1 - ξ - x)) + 3 * log x *
        log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) - 3 * log x * (ξ / (ξ * x + (1 - ξ))) + 5 *
        log (1 - ξ - x) * log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) - 5 *
        log (1 - ξ - x) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + (3 / 2) *
        log (ξ * x + (1 - ξ)) ^ 2 * (ξ / (ξ * x + (1 - ξ))) + log (ξ * x + (1 - ξ)) * log (1 - x) *
        (-1 / (1 - ξ - x)) - 5 * log (ξ * x + (1 - ξ)) * log (1 - x) * (ξ / (ξ * x + (1 - ξ))) -
        log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) * (-1 / (1 - ξ - x)) + 2 *
        log (ξ * x + (1 - ξ)) * log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) -
        log (ξ * x + (1 - ξ)) * log ξ * (-1 / (1 - ξ - x)) + log (ξ * x + (1 - ξ)) * log ξ *
        (ξ / (ξ * x + (1 - ξ))) + 4 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (-1 / (1 - ξ - x)) -
        8 * log (ξ * x + (1 - ξ)) * log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + (1 / 2) *
        log (1 - x) ^ 2 * (ξ / (ξ * x + (1 - ξ))) - 2 * log (1 - x) * log (ξ * x + (1 - ξ) ^ 2) *
        (ξ / (ξ * x + (1 - ξ))) + 2 * log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) - 2 *
        log (1 - x) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - ξ - x)) + 2 * log (1 - x) *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) - 4 * log (1 - x) * log (1 - ξ) *
        (1 / x) + 3 * log (1 - x) * log (1 - ξ) * (-1 / (1 - ξ - x)) + 3 * log (1 - x) *
        log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) + log (1 - x) * log (1 + ξ) * (-1 / (1 - ξ - x)) -
        log (1 - x) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) + log (1 - x) *
        (ξ / (ξ * x + (1 - ξ))) - log (ξ * x + (1 - ξ) ^ 2) ^ 2 * (ξ / (ξ * x + (1 - ξ))) - 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (1 / x) + 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (-1 / (1 - ξ - x)) - 2 *
        log (ξ * x + (1 - ξ) ^ 2) * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) + 4 *
        log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) * (1 / x) - 3 * log (ξ * x + (1 - ξ) ^ 2) *
        log (1 - ξ) * (-1 / (1 - ξ - x)) + log (ξ * x + (1 - ξ) ^ 2) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ))) - log (ξ * x + (1 - ξ) ^ 2) * log (1 + ξ) * (-1 / (1 - ξ - x)) +
        log (ξ * x + (1 - ξ) ^ 2) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) -
        log (ξ * x + (1 - ξ) ^ 2) * (ξ / (ξ * x + (1 - ξ))) - 2 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        log ξ * (1 / x) + 2 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log ξ * (-1 / (1 - ξ - x)) - 2 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log ξ * (ξ / (ξ * x + (1 - ξ))) + 8 *
        log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) * (1 / x) - 8 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) *
        log (1 - ξ) * (-1 / (1 - ξ - x)) + 8 * log (ξ * x ^ 2 + (1 - ξ) ^ 2) * log (1 - ξ) *
        (ξ / (ξ * x + (1 - ξ))) - (1 / 2) * log ξ ^ 2 * (ξ / (ξ * x + (1 - ξ))) + 4 * log ξ *
        log (1 - ξ) * (1 / x) - 3 * log ξ * log (1 - ξ) * (-1 / (1 - ξ - x)) + 5 * log ξ *
        log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) - log ξ * log (1 + ξ) * (-1 / (1 - ξ - x)) + log ξ *
        log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) - log ξ * (ξ / (ξ * x + (1 - ξ))) - 16 *
        log (1 - ξ) ^ 2 * (1 / x) + 12 * log (1 - ξ) ^ 2 * (-1 / (1 - ξ - x)) - (21 / 2) *
        log (1 - ξ) ^ 2 * (ξ / (ξ * x + (1 - ξ))) + 4 * log (1 - ξ) * log (1 + ξ) *
        (-1 / (1 - ξ - x)) - 4 * log (1 - ξ) * log (1 + ξ) * (ξ / (ξ * x + (1 - ξ))) + 4 *
        log (1 - ξ) * (ξ / (ξ * x + (1 - ξ))) := by
  have hid25 := i5C1_id25 hξ hx hxy
  have hid12 := i5C1_id12 hξ hx hxy
  have hid19 := i5C1_id19 hξ hx hxy
  have hf19 := i5C1F_19 hξ hx hxy
  obtain ⟨h0, h1⟩ := hξ
  have hy : 0 < 1 - ξ := by linarith
  have h1p : 0 < 1 + ξ := by linarith
  have l1 : 0 < 1 - ξ - x := by linarith
  have l2 : 0 < ξ * x + (1 - ξ) := by positivity
  have l3 : 0 < 1 - x := by linarith
  have l4 : 0 < ξ * x + (1 - ξ) ^ 2 := by positivity
  have l5 : 0 < ξ * x ^ 2 + (1 - ξ) ^ 2 := by positivity
  unfold i5K1I i5C1Hx i5C1br i5C1r0 i5C1r1
  simp only [hid25, hid12, hf19, hid19]
  simp only [i5C1R25, i5C1R12, i5C1R19]
  generalize Li₂ (x) = B0
  generalize Li₂ (x / (1 - ξ)) = B1
  generalize Li₂ (ξ / (1 - x)) = B2
  generalize Li₂ (ξ * (1 - x)) = B3
  generalize Li₂ (-(ξ * x / (1 - ξ))) = B4
  generalize Li₂ (x / (ξ * x + (1 - ξ))) = B5
  generalize Li₂ (-(ξ * x ^ 2 / (1 - ξ) ^ 2)) = B6
  generalize Li₂ (ξ * (1 - ξ - x) / (1 - ξ)) = B7
  generalize Li₂ ((1 + ξ) * x / (ξ * x + (1 - ξ))) = B8
  generalize Li₂ (x / (ξ * x + (1 - ξ) ^ 2)) = B9
  generalize Li₂ (ξ * (1 - ξ) / (ξ * x + (1 - ξ))) = B10
  generalize Li₂ (-(ξ * (1 - ξ - x) / (ξ * x + (1 - ξ)))) = B11
  generalize Li₂ (-(ξ * (1 - ξ - x) ^ 2 / (ξ * x + (1 - ξ)) ^ 2)) = B12
  generalize Li₂ (ξ * x * (1 - x) / (ξ * x + (1 - ξ) ^ 2)) = B13
  generalize log x = a0
  generalize log (1 - ξ - x) = a1
  generalize log (ξ * x + (1 - ξ)) = a2
  generalize log (1 - x) = a3
  generalize log (ξ * x + (1 - ξ) ^ 2) = a4
  generalize log (ξ * x ^ 2 + (1 - ξ) ^ 2) = a5
  generalize log ξ = a6
  generalize log (1 - ξ) = a7
  generalize log (1 + ξ) = a8
  field_simp; ring

/-- **The primitive of `I(x)`.** -/
noncomputable def i5C1PB (ξ x : ℝ) : ℝ :=
  i5C1Q0 ξ x + i5C1Q1 ξ x + i5C1Q2 ξ x + i5C1Q3 ξ x + i5C1Q4 ξ x + i5C1Q5 ξ x + i5C1Q6 ξ x +
      i5C1Q7 ξ x + i5C1Q8 ξ x + i5C1Q9 ξ x + i5C1Q10 ξ x + i5C1Q11 ξ x + i5C1Q12 ξ x +
      i5C1Q13 ξ x + i5C1Q14 ξ x + i5C1Q15 ξ x + i5C1Q16 ξ x + i5C1Q17 ξ x + i5C1Q18 ξ x +
      i5C1Q19 ξ x + i5C1Q20 ξ x + i5C1Q21 ξ x + i5C1Q22 ξ x + i5C1Q23 ξ x + i5C1Q24 ξ x +
      i5C1Q25 ξ x + i5C1Q26 ξ x + i5C1Q27 ξ x + i5C1Q28 ξ x + i5C1Q29 ξ x + i5C1Q30 ξ x +
      i5C1Q31 ξ x + i5C1Q32 ξ x + i5C1Q33 ξ x + i5C1Q34 ξ x + i5C1Q35 ξ x + i5C1Q36 ξ x +
      i5C1Q37 ξ x + i5C1Q38 ξ x + i5C1Q39 ξ x + i5C1Q40 ξ x + i5C1Q41 ξ x

/-- **`P' = I`** on `0 < x < 1 - ξ`. -/
theorem hasDerivAt_i5C1PB {ξ x : ℝ} (hξ : ξ ∈ Ioo (0 : ℝ) 1) (hx : 0 < x) (hxy : x < 1 - ξ) :
    HasDerivAt (i5C1PB ξ) (i5K1I ξ x) x := by
  rw [i5K1I_eq_letters hξ hx hxy]
  refine HasDerivAt.congr_deriv (f :=
      i5C1PB ξ) ((((((((((((((((((((((((((((((((((((((((((hasDerivAt_i5C1Q0 hξ hx hxy).add
      (hasDerivAt_i5C1Q1 hξ hx hxy)).add (hasDerivAt_i5C1Q2 hξ hx hxy)).add
      (hasDerivAt_i5C1Q3 hξ hx hxy)).add (hasDerivAt_i5C1Q4 hξ hx hxy)).add
      (hasDerivAt_i5C1Q5 hξ hx hxy)).add (hasDerivAt_i5C1Q6 hξ hx hxy)).add
      (hasDerivAt_i5C1Q7 hξ hx hxy)).add (hasDerivAt_i5C1Q8 hξ hx hxy)).add
      (hasDerivAt_i5C1Q9 hξ hx hxy)).add (hasDerivAt_i5C1Q10 hξ hx hxy)).add
      (hasDerivAt_i5C1Q11 hξ hx hxy)).add (hasDerivAt_i5C1Q12 hξ hx hxy)).add
      (hasDerivAt_i5C1Q13 hξ hx hxy)).add (hasDerivAt_i5C1Q14 hξ hx hxy)).add
      (hasDerivAt_i5C1Q15 hξ hx hxy)).add (hasDerivAt_i5C1Q16 hξ hx hxy)).add
      (hasDerivAt_i5C1Q17 hξ hx hxy)).add (hasDerivAt_i5C1Q18 hξ hx hxy)).add
      (hasDerivAt_i5C1Q19 hξ hx hxy)).add (hasDerivAt_i5C1Q20 hξ hx hxy)).add
      (hasDerivAt_i5C1Q21 hξ hx hxy)).add (hasDerivAt_i5C1Q22 hξ hx hxy)).add
      (hasDerivAt_i5C1Q23 hξ hx hxy)).add (hasDerivAt_i5C1Q24 hξ hx hxy)).add
      (hasDerivAt_i5C1Q25 hξ hx hxy)).add (hasDerivAt_i5C1Q26 hξ hx hxy)).add
      (hasDerivAt_i5C1Q27 hξ hx hxy)).add (hasDerivAt_i5C1Q28 hξ hx hxy)).add
      (hasDerivAt_i5C1Q29 hξ hx hxy)).add (hasDerivAt_i5C1Q30 hξ hx hxy)).add
      (hasDerivAt_i5C1Q31 hξ hx hxy)).add (hasDerivAt_i5C1Q32 hξ hx hxy)).add
      (hasDerivAt_i5C1Q33 hξ hx hxy)).add (hasDerivAt_i5C1Q34 hξ hx hxy)).add
      (hasDerivAt_i5C1Q35 hξ hx hxy)).add (hasDerivAt_i5C1Q36 hξ hx hxy)).add
      (hasDerivAt_i5C1Q37 hξ hx hxy)).add (hasDerivAt_i5C1Q38 hξ hx hxy)).add
      (hasDerivAt_i5C1Q39 hξ hx hxy)).add ((i5C1T_d30 hξ hx hxy).const_mul (-2))).add
      ((i5C1T_d31 hξ hx hxy).const_mul 2)) ?_
  simp only [i5C1_id21 hξ hx hxy, i5C1_id22 hξ hx hxy]
  simp only [i5C1R21, i5C1R22]
  ring

end QED.ThreeLoopD
