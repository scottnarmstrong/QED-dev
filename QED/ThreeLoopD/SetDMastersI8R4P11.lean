/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P10

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 62 to 66

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s62`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s62D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s62`, `QED.ThreeLoopD.i8Psi4s62D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽62⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s62N0 (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [negOne, one] x +
    (-1 / 2) * hpl [one, negOne] x +
    (-1) * hpl [zero, negOne, one] x +
    (-1) * hpl [zero, one, negOne] x +
    (-1) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s62N0`. -/
noncomputable def i8Psi4s62dN0 (x : ℝ) : ℝ :=
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, one] x) +
    (-1) * (zero.kernel x * hpl [one, negOne] x) +
    (-1) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s62N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s62N0 (i8Psi4s62dN0 x) x := by
  unfold i8Psi4s62N0 i8Psi4s62dN0
  exact ((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽62⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s62N1 (x : ℝ) : ℝ :=
    (-3 / 2) * hpl [negOne] x +
    (-1 / 2) * hpl [one] x +
    (-1) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s62N1`. -/
noncomputable def i8Psi4s62dN1 (x : ℝ) : ℝ :=
    (-3 / 2) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s62N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s62N1 (i8Psi4s62dN1 x) x := by
  unfold i8Psi4s62N1 i8Psi4s62dN1
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽62⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s62N2 (x : ℝ) : ℝ :=
    (-5 / 2) * hpl [negOne] x +
    (3 / 4) * hpl [one] x +
    (1) * hpl [negOne, one] x +
    (1 / 2) * hpl [zero, negOne] x +
    (1) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s62N2`. -/
noncomputable def i8Psi4s62dN2 (x : ℝ) : ℝ :=
    (-5 / 2) * (negOne.kernel x * hpl [] x) +
    (3 / 4) * (one.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (1) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s62N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s62N2 (i8Psi4s62dN2 x) x := by
  unfold i8Psi4s62N2 i8Psi4s62dN2
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-5 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (3 / 4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽62⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s62N3 (x : ℝ) : ℝ :=
    (3 / 4) +
    (-3 / 2) * hpl [negOne] x +
    (-1 / 2) * hpl [one] x +
    (1) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s62N3`. -/
noncomputable def i8Psi4s62dN3 (x : ℝ) : ℝ :=
    0 +
    (-3 / 2) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (one.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s62N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s62N3 (i8Psi4s62dN3 x) x := by
  unfold i8Psi4s62N3 i8Psi4s62dN3
  exact ((((hasDerivAt_const x (3 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽62⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s62N4 (x : ℝ) : ℝ :=
    (3 / 8) +
    (-1 / 2) * hpl [negOne] x +
    (1 / 4) * hpl [one] x +
    (-1 / 2) * hpl [negOne, one] x +
    (1 / 2) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [one, negOne] x +
    (1) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, negOne] x +
    (1) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s62N4`. -/
noncomputable def i8Psi4s62dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (1 / 4) * (one.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (1) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s62N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s62N4 (i8Psi4s62dN4 x) x := by
  unfold i8Psi4s62N4 i8Psi4s62dN4
  exact (((((((((hasDerivAt_const x (3 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (1)))

/-- The part of `Ψ₄⁽62⁾` with constant coefficients. -/
noncomputable def i8Psi4s62W (x : ℝ) : ℝ :=
    (2) * hpl [zero] x +
    (-1 / 2) * hpl [zero, one] x +
    (1) * hpl [zero, zero, negOne] x +
    (-4) * hpl [zero, zero, negOne, one] x +
    (-4) * hpl [zero, zero, one, negOne] x +
    (-4) * hpl [zero, one, zero, negOne] x

/-- The derivative of `i8Psi4s62W`. -/
noncomputable def i8Psi4s62dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (-4) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s62W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s62W (i8Psi4s62dW x) x := by
  unfold i8Psi4s62W i8Psi4s62dW
  exact (((((((hasDerivAt_hpl_cons zero [] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-4)))

/-- The piece `Ψ₄⁽62⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s62 (x : ℝ) : ℝ :=
  (i8Psi4s62N0 x + x * i8Psi4s62N1 x + x ^ 2 * i8Psi4s62N2 x + x ^ 3 * i8Psi4s62N3 x +
    x ^ 4 * i8Psi4s62N4 x) / x ^ 2 + i8Psi4s62W x

/-- The derivative of `Ψ₄⁽62⁾`. -/
noncomputable def i8Psi4s62D (x : ℝ) : ℝ :=
  ((i8Psi4s62dN0 x + (i8Psi4s62N1 x + x * i8Psi4s62dN1 x) + (2 * x * i8Psi4s62N2 x +
    x ^ 2 * i8Psi4s62dN2 x) + (3 * x ^ 2 * i8Psi4s62N3 x + x ^ 3 * i8Psi4s62dN3 x) +
    (4 * x ^ 3 * i8Psi4s62N4 x + x ^ 4 * i8Psi4s62dN4 x)) * x ^ 2 - (i8Psi4s62N0 x +
    x * i8Psi4s62N1 x + x ^ 2 * i8Psi4s62N2 x + x ^ 3 * i8Psi4s62N3 x +
    x ^ 4 * i8Psi4s62N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s62dW x

theorem hasDerivAt_i8Psi4s62 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s62 (i8Psi4s62D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s62N0 hx).add (X.mul (hasDerivAt_i8Psi4s62N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s62N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s62N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s62N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s62W hx)
  unfold i8Psi4s62
  refine e.congr_deriv ?_
  unfold i8Psi4s62D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 62 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s62 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 - x) * (-hpl [zero, negOne] x)))

/-- **`(Ψ₄⁽62⁾)'(ξ) ξ' = p₄⁽62⁾`**, in terms of `ξ`. -/
theorem i8Psi4s62D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s62D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s62 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s62D i8Psi4s62N0 i8Psi4s62N1 i8Psi4s62N2 i8Psi4s62N3 i8Psi4s62N4 i8Psi4s62dN0
    i8Psi4s62dN1 i8Psi4s62dN2 i8Psi4s62dN3 i8Psi4s62dN4 i8Psi4s62dW i8P4s62
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, i13hw_1m hx, i13hw_10m hx,
    i13_log_one_sub_eq hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽63⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s63N0 (x : ℝ) : ℝ :=
    (-4) * hpl [negOne, negOne, negOne, one] x +
    (-4) * hpl [negOne, negOne, one, negOne] x +
    (-4) * hpl [negOne, one, negOne, negOne] x +
    (-4) * hpl [one, negOne, negOne, negOne] x

/-- The derivative of `i8Psi4s63N0`. -/
noncomputable def i8Psi4s63dN0 (x : ℝ) : ℝ :=
    (-4) * (negOne.kernel x * hpl [negOne, negOne, one] x) +
    (-4) * (negOne.kernel x * hpl [negOne, one, negOne] x) +
    (-4) * (negOne.kernel x * hpl [one, negOne, negOne] x) +
    (-4) * (one.kernel x * hpl [negOne, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s63N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s63N0 (i8Psi4s63dN0 x) x := by
  unfold i8Psi4s63N0 i8Psi4s63dN0
  exact (((((hasDerivAt_hpl_cons negOne [negOne, negOne, one] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽63⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s63N1 (x : ℝ) : ℝ :=
    (-4) * hpl [negOne, negOne, negOne] x +
    (-4) * hpl [negOne, negOne, one] x +
    (-4) * hpl [negOne, one, negOne] x +
    (-4) * hpl [one, negOne, negOne] x

/-- The derivative of `i8Psi4s63N1`. -/
noncomputable def i8Psi4s63dN1 (x : ℝ) : ℝ :=
    (-4) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (-4) * (negOne.kernel x * hpl [negOne, one] x) +
    (-4) * (negOne.kernel x * hpl [one, negOne] x) +
    (-4) * (one.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s63N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s63N1 (i8Psi4s63dN1 x) x := by
  unfold i8Psi4s63N1 i8Psi4s63dN1
  exact (((((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽63⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s63N2 (x : ℝ) : ℝ :=
    (-17 / 2) * hpl [negOne] x +
    (-13 / 2) * hpl [one] x +
    (2) * hpl [negOne, negOne] x +
    (-7) * hpl [negOne, one] x +
    (5) * hpl [one, negOne] x +
    (-2) * hpl [negOne, negOne, negOne] x +
    (2) * hpl [negOne, negOne, one] x +
    (2) * hpl [negOne, one, negOne] x +
    (2) * hpl [one, negOne, negOne] x

/-- The derivative of `i8Psi4s63N2`. -/
noncomputable def i8Psi4s63dN2 (x : ℝ) : ℝ :=
    (-17 / 2) * (negOne.kernel x * hpl [] x) +
    (-13 / 2) * (one.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [negOne] x) +
    (-7) * (negOne.kernel x * hpl [one] x) +
    (5) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, one] x) +
    (2) * (negOne.kernel x * hpl [one, negOne] x) +
    (2) * (one.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s63N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s63N2 (i8Psi4s63dN2 x) x := by
  unfold i8Psi4s63N2 i8Psi4s63dN2
  exact ((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-17 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-13 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽63⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s63N3 (x : ℝ) : ℝ :=
    (15) +
    (-7) * hpl [negOne] x +
    (7) * hpl [one] x +
    (-6) * hpl [negOne, one] x +
    (-6) * hpl [one, negOne] x +
    (4) * hpl [negOne, negOne, negOne] x +
    (4) * hpl [negOne, negOne, one] x +
    (4) * hpl [negOne, one, negOne] x +
    (4) * hpl [one, negOne, negOne] x

/-- The derivative of `i8Psi4s63N3`. -/
noncomputable def i8Psi4s63dN3 (x : ℝ) : ℝ :=
    0 +
    (-7) * (negOne.kernel x * hpl [] x) +
    (7) * (one.kernel x * hpl [] x) +
    (-6) * (negOne.kernel x * hpl [one] x) +
    (-6) * (one.kernel x * hpl [negOne] x) +
    (4) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (4) * (negOne.kernel x * hpl [negOne, one] x) +
    (4) * (negOne.kernel x * hpl [one, negOne] x) +
    (4) * (one.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s63N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s63N3 (i8Psi4s63dN3 x) x := by
  unfold i8Psi4s63N3 i8Psi4s63dN3
  exact (((((((((hasDerivAt_const x (15)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽63⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s63N4 (x : ℝ) : ℝ :=
    (-1) +
    (3 / 2) * hpl [negOne] x +
    (-1 / 2) * hpl [one] x +
    (-2) * hpl [negOne, negOne] x +
    (1) * hpl [negOne, one] x +
    (1) * hpl [one, negOne] x +
    (2) * hpl [negOne, negOne, negOne] x +
    (-2) * hpl [negOne, negOne, one] x +
    (-2) * hpl [negOne, one, negOne] x +
    (-2) * hpl [one, negOne, negOne] x +
    (4) * hpl [negOne, negOne, negOne, one] x +
    (4) * hpl [negOne, negOne, one, negOne] x +
    (4) * hpl [negOne, one, negOne, negOne] x +
    (4) * hpl [one, negOne, negOne, negOne] x

/-- The derivative of `i8Psi4s63N4`. -/
noncomputable def i8Psi4s63dN4 (x : ℝ) : ℝ :=
    0 +
    (3 / 2) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (one.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, one] x) +
    (-2) * (negOne.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, negOne] x) +
    (4) * (negOne.kernel x * hpl [negOne, negOne, one] x) +
    (4) * (negOne.kernel x * hpl [negOne, one, negOne] x) +
    (4) * (negOne.kernel x * hpl [one, negOne, negOne] x) +
    (4) * (one.kernel x * hpl [negOne, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s63N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s63N4 (i8Psi4s63dN4 x) x := by
  unfold i8Psi4s63N4 i8Psi4s63dN4
  exact ((((((((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, negOne] hx).const_mul (4)))

/-- The part of `Ψ₄⁽63⁾` with constant coefficients. -/
noncomputable def i8Psi4s63W (x : ℝ) : ℝ :=
    (8) * hpl [zero, negOne, negOne] x +
    (4) * hpl [zero, negOne, one] x +
    (4) * hpl [zero, one, negOne] x +
    (4) * hpl [zero, negOne, negOne, negOne] x +
    (-4) * hpl [zero, negOne, negOne, one] x +
    (-4) * hpl [zero, negOne, one, negOne] x +
    (-4) * hpl [zero, one, negOne, negOne] x +
    (-16) * hpl [zero, negOne, negOne, negOne, one] x +
    (-16) * hpl [zero, negOne, negOne, one, negOne] x +
    (-16) * hpl [zero, negOne, one, negOne, negOne] x +
    (-16) * hpl [zero, one, negOne, negOne, negOne] x

/-- The derivative of `i8Psi4s63W`. -/
noncomputable def i8Psi4s63dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [negOne, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, one] x) +
    (4) * (zero.kernel x * hpl [one, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, negOne] x) +
    (-4) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (-4) * (zero.kernel x * hpl [negOne, one, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, negOne, negOne] x) +
    (-16) * (zero.kernel x * hpl [negOne, negOne, negOne, one] x) +
    (-16) * (zero.kernel x * hpl [negOne, negOne, one, negOne] x) +
    (-16) * (zero.kernel x * hpl [negOne, one, negOne, negOne] x) +
    (-16) * (zero.kernel x * hpl [one, negOne, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s63W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s63W (i8Psi4s63dW x) x := by
  unfold i8Psi4s63W i8Psi4s63dW
  exact ((((((((((((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne, negOne] hx).const_mul (-16)))

/-- The piece `Ψ₄⁽63⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s63 (x : ℝ) : ℝ :=
  (i8Psi4s63N0 x + x * i8Psi4s63N1 x + x ^ 2 * i8Psi4s63N2 x + x ^ 3 * i8Psi4s63N3 x +
    x ^ 4 * i8Psi4s63N4 x) / x ^ 2 + i8Psi4s63W x

/-- The derivative of `Ψ₄⁽63⁾`. -/
noncomputable def i8Psi4s63D (x : ℝ) : ℝ :=
  ((i8Psi4s63dN0 x + (i8Psi4s63N1 x + x * i8Psi4s63dN1 x) + (2 * x * i8Psi4s63N2 x +
    x ^ 2 * i8Psi4s63dN2 x) + (3 * x ^ 2 * i8Psi4s63N3 x + x ^ 3 * i8Psi4s63dN3 x) +
    (4 * x ^ 3 * i8Psi4s63N4 x + x ^ 4 * i8Psi4s63dN4 x)) * x ^ 2 - (i8Psi4s63N0 x +
    x * i8Psi4s63N1 x + x ^ 2 * i8Psi4s63N2 x + x ^ 3 * i8Psi4s63N3 x +
    x ^ 4 * i8Psi4s63N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s63dW x

theorem hasDerivAt_i8Psi4s63 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s63 (i8Psi4s63D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s63N0 hx).add (X.mul (hasDerivAt_i8Psi4s63N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s63N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s63N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s63N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s63W hx)
  unfold i8Psi4s63
  refine e.congr_deriv ?_
  unfold i8Psi4s63D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 63 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s63 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 -
    x) * (-4 * hpl [negOne, negOne, negOne] x)))

/-- **`(Ψ₄⁽63⁾)'(ξ) ξ' = p₄⁽63⁾`**, in terms of `ξ`. -/
theorem i8Psi4s63D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s63D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s63 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s63D i8Psi4s63N0 i8Psi4s63N1 i8Psi4s63N2 i8Psi4s63N3 i8Psi4s63N4 i8Psi4s63dN0
    i8Psi4s63dN1 i8Psi4s63dN2 i8Psi4s63dN3 i8Psi4s63dN4 i8Psi4s63dW i8P4s63
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, i13hw_1m hx, i13hw_mm hx, i8hw_m1m hx,
    i13hw_1mm hx, i13hw_mmm hx, i8hw_1mmm hx, i8hw_m1mm hx, i8hw_mm1m hx, i13_log_one_sub_eq hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽64⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s64N0 (x : ℝ) : ℝ :=
    (2) * hpl [negOne, zero, negOne, one] x +
    (2) * hpl [negOne, zero, one, negOne] x +
    (2) * hpl [negOne, one, zero, negOne] x +
    (2) * hpl [one, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s64N0`. -/
noncomputable def i8Psi4s64dN0 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [zero, negOne, one] x) +
    (2) * (negOne.kernel x * hpl [zero, one, negOne] x) +
    (2) * (negOne.kernel x * hpl [one, zero, negOne] x) +
    (2) * (one.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s64N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s64N0 (i8Psi4s64dN0 x) x := by
  unfold i8Psi4s64N0 i8Psi4s64dN0
  exact (((((hasDerivAt_hpl_cons negOne [zero, negOne, one] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons negOne [zero, one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽64⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s64N1 (x : ℝ) : ℝ :=
    (2) * hpl [negOne, one] x +
    (2) * hpl [one, negOne] x +
    (2) * hpl [negOne, zero, negOne] x +
    (2) * hpl [zero, negOne, one] x +
    (2) * hpl [zero, one, negOne] x +
    (2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s64N1`. -/
noncomputable def i8Psi4s64dN1 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, one] x) +
    (2) * (zero.kernel x * hpl [one, negOne] x) +
    (2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s64N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s64N1 (i8Psi4s64dN1 x) x := by
  unfold i8Psi4s64N1 i8Psi4s64dN1
  exact (((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽64⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s64N2 (x : ℝ) : ℝ :=
    (9 / 4) * hpl [negOne] x +
    (9 / 4) * hpl [one] x +
    (9 / 2) * hpl [negOne, one] x +
    (-2) * hpl [zero, negOne] x +
    (-7 / 2) * hpl [one, negOne] x +
    (1) * hpl [negOne, zero, negOne] x +
    (-1) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s64N2`. -/
noncomputable def i8Psi4s64dN2 (x : ℝ) : ℝ :=
    (9 / 4) * (negOne.kernel x * hpl [] x) +
    (9 / 4) * (one.kernel x * hpl [] x) +
    (9 / 2) * (negOne.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [negOne] x) +
    (-7 / 2) * (one.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-1) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s64N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s64N2 (i8Psi4s64dN2 x) x := by
  unfold i8Psi4s64N2 i8Psi4s64dN2
  exact ((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (9 / 4)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (9 / 4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (9 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽64⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s64N3 (x : ℝ) : ℝ :=
    (-9 / 2) +
    (3 / 2) * hpl [negOne] x +
    (-5 / 2) * hpl [one] x +
    (2) * hpl [negOne, one] x +
    (2) * hpl [one, negOne] x +
    (-2) * hpl [negOne, zero, negOne] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, one, negOne] x +
    (-2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s64N3`. -/
noncomputable def i8Psi4s64dN3 (x : ℝ) : ℝ :=
    0 +
    (3 / 2) * (negOne.kernel x * hpl [] x) +
    (-5 / 2) * (one.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s64N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s64N3 (i8Psi4s64dN3 x) x := by
  unfold i8Psi4s64N3 i8Psi4s64dN3
  exact (((((((((hasDerivAt_const x (-9 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽64⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s64N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-3 / 4) * hpl [negOne] x +
    (1 / 4) * hpl [one] x +
    (-1 / 2) * hpl [negOne, one] x +
    (1) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [one, negOne] x +
    (-1) * hpl [negOne, zero, negOne] x +
    (1) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, negOne] x +
    (1) * hpl [one, zero, negOne] x +
    (-2) * hpl [negOne, zero, negOne, one] x +
    (-2) * hpl [negOne, zero, one, negOne] x +
    (-2) * hpl [negOne, one, zero, negOne] x +
    (-2) * hpl [one, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s64N4`. -/
noncomputable def i8Psi4s64dN4 (x : ℝ) : ℝ :=
    0 +
    (-3 / 4) * (negOne.kernel x * hpl [] x) +
    (1 / 4) * (one.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (1) * (one.kernel x * hpl [zero, negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, negOne, one] x) +
    (-2) * (negOne.kernel x * hpl [zero, one, negOne] x) +
    (-2) * (negOne.kernel x * hpl [one, zero, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s64N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s64N4 (i8Psi4s64dN4 x) x := by
  unfold i8Psi4s64N4 i8Psi4s64dN4
  exact ((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽64⁾` with constant coefficients. -/
noncomputable def i8Psi4s64W (x : ℝ) : ℝ :=
    (-2) * hpl [zero, one] x +
    (-4) * hpl [zero, zero, negOne] x +
    (-2) * hpl [zero, negOne, zero, negOne] x +
    (2) * hpl [zero, zero, negOne, one] x +
    (2) * hpl [zero, zero, one, negOne] x +
    (2) * hpl [zero, one, zero, negOne] x +
    (8) * hpl [zero, negOne, zero, negOne, one] x +
    (8) * hpl [zero, negOne, zero, one, negOne] x +
    (8) * hpl [zero, negOne, one, zero, negOne] x +
    (8) * hpl [zero, one, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s64W`. -/
noncomputable def i8Psi4s64dW (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [one] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (2) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (2) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, negOne, one] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, one, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, one, zero, negOne] x) +
    (8) * (zero.kernel x * hpl [one, negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s64W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s64W (i8Psi4s64dW x) x := by
  unfold i8Psi4s64W i8Psi4s64dW
  exact (((((((((((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero, negOne] hx).const_mul (8)))

/-- The piece `Ψ₄⁽64⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s64 (x : ℝ) : ℝ :=
  (i8Psi4s64N0 x + x * i8Psi4s64N1 x + x ^ 2 * i8Psi4s64N2 x + x ^ 3 * i8Psi4s64N3 x +
    x ^ 4 * i8Psi4s64N4 x) / x ^ 2 + i8Psi4s64W x

/-- The derivative of `Ψ₄⁽64⁾`. -/
noncomputable def i8Psi4s64D (x : ℝ) : ℝ :=
  ((i8Psi4s64dN0 x + (i8Psi4s64N1 x + x * i8Psi4s64dN1 x) + (2 * x * i8Psi4s64N2 x +
    x ^ 2 * i8Psi4s64dN2 x) + (3 * x ^ 2 * i8Psi4s64N3 x + x ^ 3 * i8Psi4s64dN3 x) +
    (4 * x ^ 3 * i8Psi4s64N4 x + x ^ 4 * i8Psi4s64dN4 x)) * x ^ 2 - (i8Psi4s64N0 x +
    x * i8Psi4s64N1 x + x ^ 2 * i8Psi4s64N2 x + x ^ 3 * i8Psi4s64N3 x +
    x ^ 4 * i8Psi4s64N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s64dW x

theorem hasDerivAt_i8Psi4s64 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s64 (i8Psi4s64D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s64N0 hx).add (X.mul (hasDerivAt_i8Psi4s64N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s64N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s64N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s64N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s64W hx)
  unfold i8Psi4s64
  refine e.congr_deriv ?_
  unfold i8Psi4s64D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 64 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s64 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 -
    x) * (2 * hpl [negOne, zero, negOne] x)))

/-- **`(Ψ₄⁽64⁾)'(ξ) ξ' = p₄⁽64⁾`**, in terms of `ξ`. -/
theorem i8Psi4s64D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s64D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s64 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s64D i8Psi4s64N0 i8Psi4s64N1 i8Psi4s64N2 i8Psi4s64N3 i8Psi4s64N4 i8Psi4s64dN0
    i8Psi4s64dN1 i8Psi4s64dN2 i8Psi4s64dN3 i8Psi4s64dN4 i8Psi4s64dW i8P4s64
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, i13hw_1m hx, i13hw_10m hx, i13hw_m0m
    hx, i8hw_m0m1 hx, i8hw_m10m hx, i13hw_1m0m hx, i13hw_m01m hx, i13_log_one_sub_eq hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽65⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s65N0 (x : ℝ) : ℝ :=
    (1) * hpl [negOne, negOne, one] x +
    (1) * hpl [negOne, one, negOne] x +
    (1) * hpl [one, negOne, negOne] x +
    (2) * hpl [zero, negOne, negOne, one] x +
    (2) * hpl [zero, negOne, one, negOne] x +
    (2) * hpl [zero, one, negOne, negOne] x +
    (2) * hpl [one, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s65N0`. -/
noncomputable def i8Psi4s65dN0 (x : ℝ) : ℝ :=
    (1) * (negOne.kernel x * hpl [negOne, one] x) +
    (1) * (negOne.kernel x * hpl [one, negOne] x) +
    (1) * (one.kernel x * hpl [negOne, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (2) * (zero.kernel x * hpl [negOne, one, negOne] x) +
    (2) * (zero.kernel x * hpl [one, negOne, negOne] x) +
    (2) * (one.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s65N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s65N0 (i8Psi4s65dN0 x) x := by
  unfold i8Psi4s65N0 i8Psi4s65dN0
  exact ((((((((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽65⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s65N1 (x : ℝ) : ℝ :=
    (3) * hpl [negOne, negOne] x +
    (1) * hpl [negOne, one] x +
    (1) * hpl [one, negOne] x +
    (2) * hpl [zero, negOne, negOne] x

/-- The derivative of `i8Psi4s65N1`. -/
noncomputable def i8Psi4s65dN1 (x : ℝ) : ℝ :=
    (3) * (negOne.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s65N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s65N1 (i8Psi4s65dN1 x) x := by
  unfold i8Psi4s65N1 i8Psi4s65dN1
  exact (((((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (3)).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽65⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s65N2 (x : ℝ) : ℝ :=
    (-3 / 4) * hpl [negOne] x +
    (5 / 4) * hpl [one] x +
    (5) * hpl [negOne, negOne] x +
    (5 / 2) * hpl [negOne, one] x +
    (-3 / 2) * hpl [one, negOne] x +
    (-2) * hpl [negOne, negOne, one] x +
    (-2) * hpl [negOne, one, negOne] x +
    (-1) * hpl [zero, negOne, negOne] x +
    (-2) * hpl [one, negOne, negOne] x

/-- The derivative of `i8Psi4s65N2`. -/
noncomputable def i8Psi4s65dN2 (x : ℝ) : ℝ :=
    (-3 / 4) * (negOne.kernel x * hpl [] x) +
    (5 / 4) * (one.kernel x * hpl [] x) +
    (5) * (negOne.kernel x * hpl [negOne] x) +
    (5 / 2) * (negOne.kernel x * hpl [one] x) +
    (-3 / 2) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, one] x) +
    (-2) * (negOne.kernel x * hpl [one, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s65N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s65N2 (i8Psi4s65dN2 x) x := by
  unfold i8Psi4s65N2 i8Psi4s65dN2
  exact ((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 4)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (5 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽65⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s65N3 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (-3 / 2) * hpl [negOne] x +
    (-3 / 2) * hpl [one] x +
    (3) * hpl [negOne, negOne] x +
    (1) * hpl [negOne, one] x +
    (1) * hpl [one, negOne] x +
    (-2) * hpl [zero, negOne, negOne] x

/-- The derivative of `i8Psi4s65N3`. -/
noncomputable def i8Psi4s65dN3 (x : ℝ) : ℝ :=
    0 +
    (-3 / 2) * (negOne.kernel x * hpl [] x) +
    (-3 / 2) * (one.kernel x * hpl [] x) +
    (3) * (negOne.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s65N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s65N3 (i8Psi4s65dN3 x) x := by
  unfold i8Psi4s65N3 i8Psi4s65dN3
  exact (((((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽65⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s65N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-3 / 4) * hpl [negOne] x +
    (1 / 4) * hpl [one] x +
    (1) * hpl [negOne, negOne] x +
    (-1 / 2) * hpl [negOne, one] x +
    (-1 / 2) * hpl [one, negOne] x +
    (1) * hpl [negOne, negOne, one] x +
    (1) * hpl [negOne, one, negOne] x +
    (-1) * hpl [zero, negOne, negOne] x +
    (1) * hpl [one, negOne, negOne] x +
    (-2) * hpl [zero, negOne, negOne, one] x +
    (-2) * hpl [zero, negOne, one, negOne] x +
    (-2) * hpl [zero, one, negOne, negOne] x +
    (-2) * hpl [one, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s65N4`. -/
noncomputable def i8Psi4s65dN4 (x : ℝ) : ℝ :=
    0 +
    (-3 / 4) * (negOne.kernel x * hpl [] x) +
    (1 / 4) * (one.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [negOne] x) +
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [negOne, one] x) +
    (1) * (negOne.kernel x * hpl [one, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, negOne] x) +
    (1) * (one.kernel x * hpl [negOne, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (-2) * (zero.kernel x * hpl [negOne, one, negOne] x) +
    (-2) * (zero.kernel x * hpl [one, negOne, negOne] x) +
    (-2) * (one.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s65N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s65N4 (i8Psi4s65dN4 x) x := by
  unfold i8Psi4s65N4 i8Psi4s65dN4
  exact ((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽65⁾` with constant coefficients. -/
noncomputable def i8Psi4s65W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, negOne] x +
    (-1) * hpl [zero, one] x +
    (1) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, negOne] x +
    (-2) * hpl [zero, zero, negOne, negOne] x +
    (8) * hpl [zero, zero, negOne, negOne, one] x +
    (8) * hpl [zero, zero, negOne, one, negOne] x +
    (8) * hpl [zero, zero, one, negOne, negOne] x +
    (8) * hpl [zero, one, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s65W`. -/
noncomputable def i8Psi4s65dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (zero.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, negOne, one] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, one, negOne] x) +
    (8) * (zero.kernel x * hpl [zero, one, negOne, negOne] x) +
    (8) * (zero.kernel x * hpl [one, zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s65W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s65W (i8Psi4s65dW x) x := by
  unfold i8Psi4s65W i8Psi4s65dW
  exact ((((((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne, negOne] hx).const_mul (8)))

/-- The piece `Ψ₄⁽65⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s65 (x : ℝ) : ℝ :=
  (i8Psi4s65N0 x + x * i8Psi4s65N1 x + x ^ 2 * i8Psi4s65N2 x + x ^ 3 * i8Psi4s65N3 x +
    x ^ 4 * i8Psi4s65N4 x) / x ^ 2 + i8Psi4s65W x

/-- The derivative of `Ψ₄⁽65⁾`. -/
noncomputable def i8Psi4s65D (x : ℝ) : ℝ :=
  ((i8Psi4s65dN0 x + (i8Psi4s65N1 x + x * i8Psi4s65dN1 x) + (2 * x * i8Psi4s65N2 x +
    x ^ 2 * i8Psi4s65dN2 x) + (3 * x ^ 2 * i8Psi4s65N3 x + x ^ 3 * i8Psi4s65dN3 x) +
    (4 * x ^ 3 * i8Psi4s65N4 x + x ^ 4 * i8Psi4s65dN4 x)) * x ^ 2 - (i8Psi4s65N0 x +
    x * i8Psi4s65N1 x + x ^ 2 * i8Psi4s65N2 x + x ^ 3 * i8Psi4s65N3 x +
    x ^ 4 * i8Psi4s65N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s65dW x

theorem hasDerivAt_i8Psi4s65 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s65 (i8Psi4s65D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s65N0 hx).add (X.mul (hasDerivAt_i8Psi4s65N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s65N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s65N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s65N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s65W hx)
  unfold i8Psi4s65
  refine e.congr_deriv ?_
  unfold i8Psi4s65D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 65 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s65 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 -
    x) * (2 * hpl [zero, negOne, negOne] x)))

/-- **`(Ψ₄⁽65⁾)'(ξ) ξ' = p₄⁽65⁾`**, in terms of `ξ`. -/
theorem i8Psi4s65D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s65D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s65 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s65D i8Psi4s65N0 i8Psi4s65N1 i8Psi4s65N2 i8Psi4s65N3 i8Psi4s65N4 i8Psi4s65dN0
    i8Psi4s65dN1 i8Psi4s65dN2 i8Psi4s65dN3 i8Psi4s65dN4 i8Psi4s65dW i8P4s65
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, i13hw_1m hx, i13hw_mm hx, i8hw_m1m hx,
    i13hw_1mm hx, i13hw_10mm hx, i13_log_one_sub_eq hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽66⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s66N0 (x : ℝ) : ℝ :=
    (-1 / 4) * hpl [negOne, one] x +
    (-1 / 4) * hpl [one, negOne] x +
    (-1 / 2) * hpl [zero, negOne, one] x +
    (-1 / 2) * hpl [zero, one, negOne] x +
    (-1 / 2) * hpl [one, zero, negOne] x +
    (-1) * hpl [zero, zero, negOne, one] x +
    (-1) * hpl [zero, zero, one, negOne] x +
    (-1) * hpl [zero, one, zero, negOne] x +
    (-1) * hpl [one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s66N0`. -/
noncomputable def i8Psi4s66dN0 (x : ℝ) : ℝ :=
    (-1 / 4) * (negOne.kernel x * hpl [one] x) +
    (-1 / 4) * (one.kernel x * hpl [negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne, one] x) +
    (-1 / 2) * (zero.kernel x * hpl [one, negOne] x) +
    (-1 / 2) * (one.kernel x * hpl [zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (-1) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (-1) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (-1) * (one.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s66N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s66N0 (i8Psi4s66dN0 x) x := by
  unfold i8Psi4s66N0 i8Psi4s66dN0
  exact ((((((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 4)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽66⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s66N1 (x : ℝ) : ℝ :=
    (-7 / 4) * hpl [negOne] x +
    (-1 / 4) * hpl [one] x +
    (-3 / 2) * hpl [zero, negOne] x +
    (-1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s66N1`. -/
noncomputable def i8Psi4s66dN1 (x : ℝ) : ℝ :=
    (-7 / 4) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (one.kernel x * hpl [] x) +
    (-3 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s66N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s66N1 (i8Psi4s66dN1 x) x := by
  unfold i8Psi4s66N1 i8Psi4s66dN1
  exact (((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-7 / 4)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽66⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s66N2 (x : ℝ) : ℝ :=
    (-3 / 8) * hpl [negOne] x +
    (1 / 8) * hpl [one] x +
    (1 / 4) * hpl [zero, negOne] x +
    (1 / 2) * hpl [zero, zero, negOne] x +
    (1) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s66N2`. -/
noncomputable def i8Psi4s66dN2 (x : ℝ) : ℝ :=
    (-3 / 8) * (negOne.kernel x * hpl [] x) +
    (1 / 8) * (one.kernel x * hpl [] x) +
    (1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (1) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s66N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s66N2 (i8Psi4s66dN2 x) x := by
  unfold i8Psi4s66N2 i8Psi4s66dN2
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 8)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽66⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s66N3 (x : ℝ) : ℝ :=
    (-5 / 4) +
    (7 / 4) * hpl [negOne] x +
    (1 / 4) * hpl [one] x +
    (-3 / 2) * hpl [zero, negOne] x +
    (1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s66N3`. -/
noncomputable def i8Psi4s66dN3 (x : ℝ) : ℝ :=
    0 +
    (7 / 4) * (negOne.kernel x * hpl [] x) +
    (1 / 4) * (one.kernel x * hpl [] x) +
    (-3 / 2) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s66N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s66N3 (i8Psi4s66dN3 x) x := by
  unfold i8Psi4s66N3 i8Psi4s66dN3
  exact (((((hasDerivAt_const x (-5 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (7 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽66⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s66N4 (x : ℝ) : ℝ :=
    (-1 / 4) +
    (3 / 8) * hpl [negOne] x +
    (-1 / 8) * hpl [one] x +
    (1 / 4) * hpl [negOne, one] x +
    (-1 / 2) * hpl [zero, negOne] x +
    (1 / 4) * hpl [one, negOne] x +
    (-1 / 2) * hpl [zero, negOne, one] x +
    (1 / 2) * hpl [zero, zero, negOne] x +
    (-1 / 2) * hpl [zero, one, negOne] x +
    (-1 / 2) * hpl [one, zero, negOne] x +
    (1) * hpl [zero, zero, negOne, one] x +
    (1) * hpl [zero, zero, one, negOne] x +
    (1) * hpl [zero, one, zero, negOne] x +
    (1) * hpl [one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s66N4`. -/
noncomputable def i8Psi4s66dN4 (x : ℝ) : ℝ :=
    0 +
    (3 / 8) * (negOne.kernel x * hpl [] x) +
    (-1 / 8) * (one.kernel x * hpl [] x) +
    (1 / 4) * (negOne.kernel x * hpl [one] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (1 / 4) * (one.kernel x * hpl [negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne, one] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [one, negOne] x) +
    (-1 / 2) * (one.kernel x * hpl [zero, negOne] x) +
    (1) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (1) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (1) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (1) * (one.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s66N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s66N4 (i8Psi4s66dN4 x) x := by
  unfold i8Psi4s66N4 i8Psi4s66dN4
  exact ((((((((((((((hasDerivAt_const x (-1 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 8))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 8))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, zero, negOne] hx).const_mul (1)))

/-- The part of `Ψ₄⁽66⁾` with constant coefficients. -/
noncomputable def i8Psi4s66W (x : ℝ) : ℝ :=
    (2) * hpl [zero] x +
    (-1 / 4) * hpl [zero, one] x +
    (1) * hpl [zero, zero, zero, negOne] x +
    (-4) * hpl [zero, zero, zero, negOne, one] x +
    (-4) * hpl [zero, zero, zero, one, negOne] x +
    (-4) * hpl [zero, zero, one, zero, negOne] x +
    (-4) * hpl [zero, one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s66W`. -/
noncomputable def i8Psi4s66dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [zero, zero, negOne] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, negOne, one] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, one, negOne] x) +
    (-4) * (zero.kernel x * hpl [zero, one, zero, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s66W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s66W (i8Psi4s66dW x) x := by
  unfold i8Psi4s66W i8Psi4s66dW
  exact ((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero, negOne] hx).const_mul (-4)))

/-- The piece `Ψ₄⁽66⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s66 (x : ℝ) : ℝ :=
  (i8Psi4s66N0 x + x * i8Psi4s66N1 x + x ^ 2 * i8Psi4s66N2 x + x ^ 3 * i8Psi4s66N3 x +
    x ^ 4 * i8Psi4s66N4 x) / x ^ 2 + i8Psi4s66W x

/-- The derivative of `Ψ₄⁽66⁾`. -/
noncomputable def i8Psi4s66D (x : ℝ) : ℝ :=
  ((i8Psi4s66dN0 x + (i8Psi4s66N1 x + x * i8Psi4s66dN1 x) + (2 * x * i8Psi4s66N2 x +
    x ^ 2 * i8Psi4s66dN2 x) + (3 * x ^ 2 * i8Psi4s66N3 x + x ^ 3 * i8Psi4s66dN3 x) +
    (4 * x ^ 3 * i8Psi4s66N4 x + x ^ 4 * i8Psi4s66dN4 x)) * x ^ 2 - (i8Psi4s66N0 x +
    x * i8Psi4s66N1 x + x ^ 2 * i8Psi4s66N2 x + x ^ 3 * i8Psi4s66N3 x +
    x ^ 4 * i8Psi4s66N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s66dW x

theorem hasDerivAt_i8Psi4s66 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s66 (i8Psi4s66D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s66N0 hx).add (X.mul (hasDerivAt_i8Psi4s66N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s66N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s66N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s66N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s66W hx)
  unfold i8Psi4s66
  refine e.congr_deriv ?_
  unfold i8Psi4s66D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 66 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s66 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 - x) * (-hpl [zero, zero, negOne] x)))

/-- **`(Ψ₄⁽66⁾)'(ξ) ξ' = p₄⁽66⁾`**, in terms of `ξ`. -/
theorem i8Psi4s66D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s66D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s66 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s66D i8Psi4s66N0 i8Psi4s66N1 i8Psi4s66N2 i8Psi4s66N3 i8Psi4s66N4 i8Psi4s66dN0
    i8Psi4s66dN1 i8Psi4s66dN2 i8Psi4s66dN3 i8Psi4s66dN4 i8Psi4s66dW i8P4s66
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, i13hw_1m hx, i13hw_10m hx, i13hw_010m
    hx, i13hw_100m hx, i13_log_one_sub_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
