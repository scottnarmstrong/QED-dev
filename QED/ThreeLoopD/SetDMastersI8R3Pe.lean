/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3Pd

/-!
# Set (d), master `I₈`: a primitive of `p₃`, piece `e`

`p₃` splits as `p₃⁽ᵃ⁾ + p₃⁽ᵇ⁾ + p₃⁽ᶜ⁾` by the power of `λ = log t` (`QED.ThreeLoopD.i8P3xe`).
The piece `Ψ₃⁽e⁾` (`QED.ThreeLoopD.i8Psi3e`), a combination of harmonic polylogarithms of weight
at most four with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the shuffle-algebra engine of
the campaign, is a primitive of `p₃⁽e⁾ dt/dξ` (`QED.ThreeLoopD.i8Psi3eD_mul`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi3e`, `QED.ThreeLoopD.i8Psi3eD_mul`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₃⁽e⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi3eN0 (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [negOne] x +
    (1 / 2) * hpl [negOne, negOne] x +
    (-3 / 4) * hpl [negOne, zero] x +
    (-3 / 2) * hpl [negOne, one] x +
    (-1) * hpl [zero, negOne] x +
    (-3 / 2) * hpl [one, negOne] x +
    (1) * hpl [negOne, negOne, zero] x +
    (2) * hpl [negOne, negOne, one] x +
    (1) * hpl [negOne, zero, negOne] x +
    (2) * hpl [negOne, one, negOne] x +
    (1) * hpl [zero, negOne, negOne] x +
    (-1 / 2) * hpl [zero, negOne, zero] x +
    (-1) * hpl [zero, negOne, one] x +
    (-1) * hpl [zero, zero, negOne] x +
    (-1) * hpl [zero, one, negOne] x +
    (2) * hpl [one, negOne, negOne] x +
    (-1) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi3eN0`. -/
noncomputable def i8Psi3edN0 (x : ℝ) : ℝ :=
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [negOne] x) +
    (-3 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-3 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (-3 / 2) * (one.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [negOne, one] x) +
    (1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [one, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, one] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [one, negOne] x) +
    (2) * (one.kernel x * hpl [negOne, negOne] x) +
    (-1) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi3eN0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3eN0 (i8Psi3edN0 x) x := by
  unfold i8Psi3eN0 i8Psi3edN0
  exact ((((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₃⁽e⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi3eN1 (x : ℝ) : ℝ :=
    (3 / 4) +
    (-1) * hpl [negOne] x +
    (5 / 4) * hpl [zero] x +
    (5 / 2) * hpl [one] x +
    (2) * hpl [negOne, negOne] x +
    (1) * hpl [negOne, zero] x +
    (2) * hpl [negOne, one] x +
    (2) * hpl [one, negOne] x

/-- The derivative of `i8Psi3eN1`. -/
noncomputable def i8Psi3edN1 (x : ℝ) : ℝ :=
    0 +
    (-1) * (negOne.kernel x * hpl [] x) +
    (5 / 4) * (zero.kernel x * hpl [] x) +
    (5 / 2) * (one.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (2) * (negOne.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi3eN1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3eN1 (i8Psi3edN1 x) x := by
  unfold i8Psi3eN1 i8Psi3edN1
  exact ((((((((hasDerivAt_const x (3 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (5 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₃⁽e⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi3eN2 (x : ℝ) : ℝ :=
    (-2) * hpl [zero] x +
    (-29 / 4) * hpl [one] x +
    (-2) * hpl [zero, negOne] x +
    (-2) * hpl [zero, negOne, negOne] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi3eN2`. -/
noncomputable def i8Psi3edN2 (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [] x) +
    (-29 / 4) * (one.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi3eN2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3eN2 (i8Psi3edN2 x) x := by
  unfold i8Psi3eN2 i8Psi3edN2
  exact ((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-29 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₃⁽e⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi3eN3 (x : ℝ) : ℝ :=
    (1 / 2) +
    (1) * hpl [negOne] x +
    (15 / 4) * hpl [zero] x +
    (15 / 2) * hpl [one] x +
    (-2) * hpl [negOne, negOne] x +
    (-1) * hpl [negOne, zero] x +
    (-2) * hpl [negOne, one] x +
    (-2) * hpl [one, negOne] x

/-- The derivative of `i8Psi3eN3`. -/
noncomputable def i8Psi3edN3 (x : ℝ) : ℝ :=
    0 +
    (1) * (negOne.kernel x * hpl [] x) +
    (15 / 4) * (zero.kernel x * hpl [] x) +
    (15 / 2) * (one.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi3eN3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3eN3 (i8Psi3edN3 x) x := by
  unfold i8Psi3eN3 i8Psi3edN3
  exact ((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (15 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (15 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₃⁽e⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi3eN4 (x : ℝ) : ℝ :=
    (-15 / 16) +
    (1 / 2) * hpl [negOne] x +
    (-11 / 8) * hpl [zero] x +
    (-11 / 4) * hpl [one] x +
    (-1 / 2) * hpl [negOne, negOne] x +
    (3 / 4) * hpl [negOne, zero] x +
    (3 / 2) * hpl [negOne, one] x +
    (1) * hpl [zero, negOne] x +
    (3 / 2) * hpl [one, negOne] x +
    (-1) * hpl [negOne, negOne, zero] x +
    (-2) * hpl [negOne, negOne, one] x +
    (-1) * hpl [negOne, zero, negOne] x +
    (-2) * hpl [negOne, one, negOne] x +
    (-1) * hpl [zero, negOne, negOne] x +
    (1 / 2) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, zero, negOne] x +
    (1) * hpl [zero, one, negOne] x +
    (-2) * hpl [one, negOne, negOne] x +
    (1) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi3eN4`. -/
noncomputable def i8Psi3edN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (negOne.kernel x * hpl [] x) +
    (-11 / 8) * (zero.kernel x * hpl [] x) +
    (-11 / 4) * (one.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [negOne] x) +
    (3 / 4) * (negOne.kernel x * hpl [zero] x) +
    (3 / 2) * (negOne.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [negOne] x) +
    (3 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-2) * (negOne.kernel x * hpl [negOne, one] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-2) * (negOne.kernel x * hpl [one, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, negOne] x) +
    (1) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi3eN4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3eN4 (i8Psi3edN4 x) x := by
  unfold i8Psi3eN4 i8Psi3edN4
  exact ((((((((((((((((((((hasDerivAt_const x (-15 / 16)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-11 / 8))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-11 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (3 / 4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (1)))

/-- The part of `Ψ₃⁽e⁾` with constant coefficients. -/
noncomputable def i8Psi3eW (x : ℝ) : ℝ :=
    (1 / 4) * hpl [zero, zero] x +
    (1 / 2) * hpl [zero, one] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (8) * hpl [zero, negOne, negOne, one] x +
    (4) * hpl [zero, negOne, zero, negOne] x +
    (8) * hpl [zero, negOne, one, negOne] x +
    (4) * hpl [zero, zero, negOne, negOne] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne, one] x +
    (-4) * hpl [zero, zero, zero, negOne] x +
    (-4) * hpl [zero, zero, one, negOne] x +
    (8) * hpl [zero, one, negOne, negOne] x +
    (-4) * hpl [zero, one, zero, negOne] x

/-- The derivative of `i8Psi3eW`. -/
noncomputable def i8Psi3edW (x : ℝ) : ℝ :=
    (1 / 4) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [one] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, one, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, negOne] x) +
    (-4) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (8) * (zero.kernel x * hpl [one, negOne, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi3eW {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3eW (i8Psi3edW x) x := by
  unfold i8Psi3eW i8Psi3edW
  exact ((((((((((((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 4)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-4)))

/-- The piece `Ψ₃⁽e⁾` of the primitive of `p₃ dt/dξ`. -/
noncomputable def i8Psi3e (x : ℝ) : ℝ :=
  (i8Psi3eN0 x + x * i8Psi3eN1 x + x ^ 2 * i8Psi3eN2 x + x ^ 3 * i8Psi3eN3 x +
    x ^ 4 * i8Psi3eN4 x) / x ^ 2 + i8Psi3eW x

/-- The derivative of `Ψ₃⁽e⁾`. -/
noncomputable def i8Psi3eD (x : ℝ) : ℝ :=
  ((i8Psi3edN0 x + (i8Psi3eN1 x + x * i8Psi3edN1 x) +
      (2 * x * i8Psi3eN2 x + x ^ 2 * i8Psi3edN2 x) +
      (3 * x ^ 2 * i8Psi3eN3 x + x ^ 3 * i8Psi3edN3 x) +
      (4 * x ^ 3 * i8Psi3eN4 x + x ^ 4 * i8Psi3edN4 x)) * x ^ 2 -
    (i8Psi3eN0 x + x * i8Psi3eN1 x + x ^ 2 * i8Psi3eN2 x + x ^ 3 * i8Psi3eN3 x +
      x ^ 4 * i8Psi3eN4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi3edW x

theorem hasDerivAt_i8Psi3e {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3e (i8Psi3eD x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := (((((hasDerivAt_i8Psi3eN0 hx).add (X.mul (hasDerivAt_i8Psi3eN1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi3eN2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi3eN3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi3eN4 hx))).div (X.pow 2) (pow_ne_zero 2 h0) |>.add
    (hasDerivAt_i8Psi3eW hx)
  unfold i8Psi3e
  refine e.congr_deriv ?_
  unfold i8Psi3eD
  simp only [Pi.pow_apply]
  norm_num

/-- The part `-t λ A₂` of `p₃` in `ξ`. -/
noncomputable def i8P3xe (x : ℝ) : ℝ :=
  -((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) * i8A2x x)

/-- **`(Ψ₃⁽e⁾)'(ξ) ξ' = p₃⁽e⁾`**, in terms of `ξ`. -/
theorem i8Psi3eD_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3eD x * (-x ^ 2 / (1 - x ^ 2)) = i8P3xe x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi3eD i8Psi3eN0 i8Psi3eN1 i8Psi3eN2 i8Psi3eN3 i8Psi3eN4 i8Psi3edN0 i8Psi3edN1
    i8Psi3edN2 i8Psi3edN3 i8Psi3edN4 i8Psi3edW i8P3xe i8A2x
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_mm hx,
    i13hw_1m hx, i13hw_0m0 hx, i13hw_m0m hx, i13hw_mm0 hx, i13hw_10m hx, i8hw_m1m hx, i8hw_1mm hx,
    i13_log_one_sub_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
