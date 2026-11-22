/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P0

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 2 to 5

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s2`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s2D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s2`, `QED.ThreeLoopD.i8Psi4s2D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽2⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s2N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s2N0`. -/
noncomputable def i8Psi4s2dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s2N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s2N0 (i8Psi4s2dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽2⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s2N1 (x : ℝ) : ℝ :=
    (28 - 2 / 3 * π ^ 2) +
    (12) * hpl [zero] x +
    (-8) * hpl [negOne, zero] x +
    (4) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s2N1`. -/
noncomputable def i8Psi4s2dN1 (x : ℝ) : ℝ :=
    0 +
    (12) * (zero.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s2N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s2N1 (i8Psi4s2dN1 x) x := by
  unfold i8Psi4s2N1 i8Psi4s2dN1
  exact ((((hasDerivAt_const x (28 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽2⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s2N2 (x : ℝ) : ℝ :=
    (16 + 2 / 3 * π ^ 2) * hpl [zero] x +
    (-12) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s2N2`. -/
noncomputable def i8Psi4s2dN2 (x : ℝ) : ℝ :=
    (16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-12) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s2N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s2N2 (i8Psi4s2dN2 x) x := by
  unfold i8Psi4s2N2 i8Psi4s2dN2
  exact (((hasDerivAt_hpl_cons zero [] hx).const_mul (16 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽2⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s2N3 (x : ℝ) : ℝ :=
    (8 - 2 / 3 * π ^ 2) +
    (8) * hpl [zero] x +
    (-8) * hpl [negOne, zero] x +
    (4) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s2N3`. -/
noncomputable def i8Psi4s2dN3 (x : ℝ) : ℝ :=
    0 +
    (8) * (zero.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s2N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s2N3 (i8Psi4s2dN3 x) x := by
  unfold i8Psi4s2N3 i8Psi4s2dN3
  exact ((((hasDerivAt_const x (8 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽2⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s2N4 (x : ℝ) : ℝ :=
    (-21 / 2 - π ^ 2 / 3) +
    (5) * hpl [zero] x +
    (-4) * hpl [negOne, zero] x +
    (2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s2N4`. -/
noncomputable def i8Psi4s2dN4 (x : ℝ) : ℝ :=
    0 +
    (5) * (zero.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s2N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s2N4 (i8Psi4s2dN4 x) x := by
  unfold i8Psi4s2N4 i8Psi4s2dN4
  exact ((((hasDerivAt_const x (-21 / 2 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2)))

/-- The part of `Ψ₄⁽2⁾` with constant coefficients. -/
noncomputable def i8Psi4s2W (x : ℝ) : ℝ :=
    (8) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s2W`. -/
noncomputable def i8Psi4s2dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s2W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s2W (i8Psi4s2dW x) x := by
  unfold i8Psi4s2W i8Psi4s2dW
  exact (((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-4)))

/-- The piece `Ψ₄⁽2⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s2 (x : ℝ) : ℝ :=
  (i8Psi4s2N0 x + x * i8Psi4s2N1 x + x ^ 2 * i8Psi4s2N2 x + x ^ 3 * i8Psi4s2N3 x +
    x ^ 4 * i8Psi4s2N4 x) / x ^ 2 + i8Psi4s2W x

/-- The derivative of `Ψ₄⁽2⁾`. -/
noncomputable def i8Psi4s2D (x : ℝ) : ℝ :=
  ((i8Psi4s2dN0 x + (i8Psi4s2N1 x + x * i8Psi4s2dN1 x) + (2 * x * i8Psi4s2N2 x +
    x ^ 2 * i8Psi4s2dN2 x) + (3 * x ^ 2 * i8Psi4s2N3 x + x ^ 3 * i8Psi4s2dN3 x) +
    (4 * x ^ 3 * i8Psi4s2N4 x + x ^ 4 * i8Psi4s2dN4 x)) * x ^ 2 - (i8Psi4s2N0 x +
    x * i8Psi4s2N1 x + x ^ 2 * i8Psi4s2N2 x + x ^ 3 * i8Psi4s2N3 x +
    x ^ 4 * i8Psi4s2N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s2dW x

theorem hasDerivAt_i8Psi4s2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s2 (i8Psi4s2D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s2N0 hx).add (X.mul (hasDerivAt_i8Psi4s2N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s2N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s2N3 hx))).add ((X.pow
    4).mul (hasDerivAt_i8Psi4s2N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add (hasDerivAt_i8Psi4s2W
    hx)
  unfold i8Psi4s2
  refine e.congr_deriv ?_
  unfold i8Psi4s2D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 2 of `p₄` in `ξ`: from `t B2 A2 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s2 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * i13Be2x x * ((1 + x) / (1 - x) * (2 * x / (1 + x)))

/-- **`(Ψ₄⁽2⁾)'(ξ) ξ' = p₄⁽2⁾`**, in terms of `ξ`. -/
theorem i8Psi4s2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s2 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s2D i8Psi4s2N0 i8Psi4s2N1 i8Psi4s2N2 i8Psi4s2N3 i8Psi4s2N4 i8Psi4s2dN0 i8Psi4s2dN1
    i8Psi4s2dN2 i8Psi4s2dN3 i8Psi4s2dN4 i8Psi4s2dW i8P4s2 i13Be2x
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13_Li₂_neg_eq
    hx, i13_log_one_add_eq hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽3⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s3N0 (x : ℝ) : ℝ :=
    (-21 / 4 + π ^ 2 / 6) * hpl [negOne] x +
    (-5 / 2) * hpl [negOne, zero] x +
    (-5 / 2) * hpl [zero, negOne] x +
    (4) * hpl [negOne, negOne, zero] x +
    (2) * hpl [negOne, zero, negOne] x +
    (-1) * hpl [negOne, zero, zero] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s3N0`. -/
noncomputable def i8Psi4s3dN0 (x : ℝ) : ℝ :=
    (-21 / 4 + π ^ 2 / 6) * (negOne.kernel x * hpl [] x) +
    (-5 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-5 / 2) * (zero.kernel x * hpl [negOne] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s3N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s3N0 (i8Psi4s3dN0 x) x := by
  unfold i8Psi4s3N0 i8Psi4s3dN0
  exact (((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-21 / 4 + π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽3⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s3N1 (x : ℝ) : ℝ :=
    (-35 / 4 + π ^ 2 / 6) +
    (-10 + 2 / 3 * π ^ 2) * hpl [negOne] x +
    (-7 / 2) * hpl [zero] x +
    (-8) * hpl [negOne, zero] x +
    (-10) * hpl [zero, negOne] x +
    (-1) * hpl [zero, zero] x +
    (16) * hpl [negOne, negOne, zero] x +
    (8) * hpl [negOne, zero, negOne] x +
    (-4) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s3N1`. -/
noncomputable def i8Psi4s3dN1 (x : ℝ) : ℝ :=
    0 +
    (-10 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-7 / 2) * (zero.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (-10) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (zero.kernel x * hpl [zero] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s3N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s3N1 (i8Psi4s3dN1 x) x := by
  unfold i8Psi4s3N1 i8Psi4s3dN1
  exact (((((((((((hasDerivAt_const x (-35 / 4 + π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-10 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽3⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s3N2 (x : ℝ) : ℝ :=
    (π ^ 2) * hpl [negOne] x +
    (19 / 4 - π ^ 2 / 2) * hpl [zero] x +
    (-18) * hpl [negOne, zero] x +
    (-16) * hpl [zero, negOne] x +
    (11 / 2) * hpl [zero, zero] x +
    (24) * hpl [negOne, negOne, zero] x +
    (12) * hpl [negOne, zero, negOne] x +
    (-6) * hpl [negOne, zero, zero] x +
    (-12) * hpl [zero, negOne, zero] x +
    (-6) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s3N2`. -/
noncomputable def i8Psi4s3dN2 (x : ℝ) : ℝ :=
    (π ^ 2) * (negOne.kernel x * hpl [] x) +
    (19 / 4 - π ^ 2 / 2) * (zero.kernel x * hpl [] x) +
    (-18) * (negOne.kernel x * hpl [zero] x) +
    (-16) * (zero.kernel x * hpl [negOne] x) +
    (11 / 2) * (zero.kernel x * hpl [zero] x) +
    (24) * (negOne.kernel x * hpl [negOne, zero] x) +
    (12) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-6) * (negOne.kernel x * hpl [zero, zero] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s3N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s3N2 (i8Psi4s3dN2 x) x := by
  unfold i8Psi4s3N2 i8Psi4s3dN2
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (19 / 4 - π ^ 2 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (11 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-6)))

/-- The part of `ξ² Ψ₄⁽3⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s3N3 (x : ℝ) : ℝ :=
    (-57 / 4 - π ^ 2 / 2) +
    (10 + 2 / 3 * π ^ 2) * hpl [negOne] x +
    (19 / 2) * hpl [zero] x +
    (-16) * hpl [negOne, zero] x +
    (-10) * hpl [zero, negOne] x +
    (3) * hpl [zero, zero] x +
    (16) * hpl [negOne, negOne, zero] x +
    (8) * hpl [negOne, zero, negOne] x +
    (-4) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s3N3`. -/
noncomputable def i8Psi4s3dN3 (x : ℝ) : ℝ :=
    0 +
    (10 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (19 / 2) * (zero.kernel x * hpl [] x) +
    (-16) * (negOne.kernel x * hpl [zero] x) +
    (-10) * (zero.kernel x * hpl [negOne] x) +
    (3) * (zero.kernel x * hpl [zero] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s3N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s3N3 (i8Psi4s3dN3 x) x := by
  unfold i8Psi4s3N3 i8Psi4s3dN3
  exact (((((((((((hasDerivAt_const x (-57 / 4 - π ^ 2 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (10 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (19 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽3⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s3N4 (x : ℝ) : ℝ :=
    (-27 / 8 - π ^ 2 / 12) +
    (21 / 4 + π ^ 2 / 6) * hpl [negOne] x +
    (3 / 2) * hpl [zero] x +
    (-7 / 2) * hpl [negOne, zero] x +
    (-5 / 2) * hpl [zero, negOne] x +
    (1 / 2) * hpl [zero, zero] x +
    (4) * hpl [negOne, negOne, zero] x +
    (2) * hpl [negOne, zero, negOne] x +
    (-1) * hpl [negOne, zero, zero] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s3N4`. -/
noncomputable def i8Psi4s3dN4 (x : ℝ) : ℝ :=
    0 +
    (21 / 4 + π ^ 2 / 6) * (negOne.kernel x * hpl [] x) +
    (3 / 2) * (zero.kernel x * hpl [] x) +
    (-7 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-5 / 2) * (zero.kernel x * hpl [negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [zero] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s3N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s3N4 (i8Psi4s3dN4 x) x := by
  unfold i8Psi4s3N4 i8Psi4s3dN4
  exact (((((((((((hasDerivAt_const x (-27 / 8 - π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (21 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1)))

/-- The part of `Ψ₄⁽3⁾` with constant coefficients. -/
noncomputable def i8Psi4s3W (x : ℝ) : ℝ :=
    (3) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s3W`. -/
noncomputable def i8Psi4s3dW (x : ℝ) : ℝ :=
    (3) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s3W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s3W (i8Psi4s3dW x) x := by
  unfold i8Psi4s3W i8Psi4s3dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (3))

/-- The piece `Ψ₄⁽3⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s3 (x : ℝ) : ℝ :=
  (i8Psi4s3N0 x + x * i8Psi4s3N1 x + x ^ 2 * i8Psi4s3N2 x + x ^ 3 * i8Psi4s3N3 x +
    x ^ 4 * i8Psi4s3N4 x) / x ^ 2 + i8Psi4s3W x

/-- The derivative of `Ψ₄⁽3⁾`. -/
noncomputable def i8Psi4s3D (x : ℝ) : ℝ :=
  ((i8Psi4s3dN0 x + (i8Psi4s3N1 x + x * i8Psi4s3dN1 x) + (2 * x * i8Psi4s3N2 x +
    x ^ 2 * i8Psi4s3dN2 x) + (3 * x ^ 2 * i8Psi4s3N3 x + x ^ 3 * i8Psi4s3dN3 x) +
    (4 * x ^ 3 * i8Psi4s3N4 x + x ^ 4 * i8Psi4s3dN4 x)) * x ^ 2 - (i8Psi4s3N0 x +
    x * i8Psi4s3N1 x + x ^ 2 * i8Psi4s3N2 x + x ^ 3 * i8Psi4s3N3 x +
    x ^ 4 * i8Psi4s3N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s3dW x

theorem hasDerivAt_i8Psi4s3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s3 (i8Psi4s3D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s3N0 hx).add (X.mul (hasDerivAt_i8Psi4s3N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s3N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s3N3 hx))).add ((X.pow
    4).mul (hasDerivAt_i8Psi4s3N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add (hasDerivAt_i8Psi4s3W
    hx)
  unfold i8Psi4s3
  refine e.congr_deriv ?_
  unfold i8Psi4s3D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 3 of `p₄` in `ξ`: from `t B2 A2 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s3 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * i13Be2x x * ((1 + x) / (1 - x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽3⁾)'(ξ) ξ' = p₄⁽3⁾`**, in terms of `ξ`. -/
theorem i8Psi4s3D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s3D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s3 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s3D i8Psi4s3N0 i8Psi4s3N1 i8Psi4s3N2 i8Psi4s3N3 i8Psi4s3N4 i8Psi4s3dN0 i8Psi4s3dN1
    i8Psi4s3dN2 i8Psi4s3dN3 i8Psi4s3dN4 i8Psi4s3dW i8P4s3 i13Be2x
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_0m0 hx,
    i13hw_m00 hx, i13hw_m0m hx, i13hw_mm0 hx, i13_Li₂_neg_eq hx, i13_log_one_add_eq hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽4⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s4N0 (x : ℝ) : ℝ :=
    (-27 / 8 + π ^ 2 / 12) * hpl [negOne] x +
    (-3 / 2) * hpl [negOne, zero] x +
    (-27 / 4 + π ^ 2 / 6) * hpl [zero, negOne] x +
    (2) * hpl [negOne, negOne, zero] x +
    (1) * hpl [negOne, zero, negOne] x +
    (-1 / 2) * hpl [negOne, zero, zero] x +
    (-3) * hpl [zero, negOne, zero] x +
    (-11 / 2) * hpl [zero, zero, negOne] x +
    (2) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [negOne, zero, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (2) * hpl [zero, negOne, zero, negOne] x +
    (-1) * hpl [zero, negOne, zero, zero] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s4N0`. -/
noncomputable def i8Psi4s4dN0 (x : ℝ) : ℝ :=
    (-27 / 8 + π ^ 2 / 12) * (negOne.kernel x * hpl [] x) +
    (-3 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-27 / 4 + π ^ 2 / 6) * (zero.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-3) * (zero.kernel x * hpl [negOne, zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s4N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s4N0 (i8Psi4s4dN0 x) x := by
  unfold i8Psi4s4N0 i8Psi4s4dN0
  exact ((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-27 / 8 + π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-27 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3)))

/-- The part of `ξ² Ψ₄⁽4⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s4N1 (x : ℝ) : ℝ :=
    (-43 / 8 + π ^ 2 / 12) +
    (-23 + 2 / 3 * π ^ 2) * hpl [negOne] x +
    (-2) * hpl [zero] x +
    (-12) * hpl [negOne, zero] x +
    (-23 + 2 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [zero, zero] x +
    (16) * hpl [negOne, negOne, zero] x +
    (8) * hpl [negOne, zero, negOne] x +
    (-4) * hpl [negOne, zero, zero] x +
    (-14) * hpl [zero, negOne, zero] x +
    (-24) * hpl [zero, zero, negOne] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (16) * hpl [negOne, zero, zero, negOne] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (8) * hpl [zero, negOne, zero, negOne] x +
    (-4) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s4N1`. -/
noncomputable def i8Psi4s4dN1 (x : ℝ) : ℝ :=
    0 +
    (-23 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [] x) +
    (-12) * (negOne.kernel x * hpl [zero] x) +
    (-23 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-14) * (zero.kernel x * hpl [negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, negOne] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s4N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s4N1 (i8Psi4s4dN1 x) x := by
  unfold i8Psi4s4N1 i8Psi4s4dN1
  exact ((((((((((((((((((hasDerivAt_const x (-43 / 8 + π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-23 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-23 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽4⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s4N2 (x : ℝ) : ℝ :=
    (-157 / 4) * hpl [negOne] x +
    (157 / 8 - 7 / 12 * π ^ 2) * hpl [zero] x +
    (15 / 2) * hpl [negOne, zero] x +
    (21 / 2) * hpl [zero, zero] x +
    (-14) * hpl [zero, negOne, zero] x +
    (-23) * hpl [zero, zero, negOne] x +
    (12) * hpl [negOne, zero, negOne, zero] x +
    (24) * hpl [negOne, zero, zero, negOne] x +
    (-6) * hpl [zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s4N2`. -/
noncomputable def i8Psi4s4dN2 (x : ℝ) : ℝ :=
    (-157 / 4) * (negOne.kernel x * hpl [] x) +
    (157 / 8 - 7 / 12 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (15 / 2) * (negOne.kernel x * hpl [zero] x) +
    (21 / 2) * (zero.kernel x * hpl [zero] x) +
    (-14) * (zero.kernel x * hpl [negOne, zero] x) +
    (-23) * (zero.kernel x * hpl [zero, negOne] x) +
    (12) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-6) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s4N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s4N2 (i8Psi4s4dN2 x) x := by
  unfold i8Psi4s4N2 i8Psi4s4dN2
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-157 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (157 / 8 - 7 / 12 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (15 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (21 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-23))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽4⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s4N3 (x : ℝ) : ℝ :=
    (273 / 8 + 7 / 12 * π ^ 2) +
    (-23 - 2 / 3 * π ^ 2) * hpl [negOne] x +
    (-29 / 2) * hpl [zero] x +
    (20) * hpl [negOne, zero] x +
    (23 + 2 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (-7 / 2) * hpl [zero, zero] x +
    (-16) * hpl [negOne, negOne, zero] x +
    (-8) * hpl [negOne, zero, negOne] x +
    (4) * hpl [negOne, zero, zero] x +
    (-6) * hpl [zero, negOne, zero] x +
    (-16) * hpl [zero, zero, negOne] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (16) * hpl [negOne, zero, zero, negOne] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (8) * hpl [zero, negOne, zero, negOne] x +
    (-4) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s4N3`. -/
noncomputable def i8Psi4s4dN3 (x : ℝ) : ℝ :=
    0 +
    (-23 - 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-29 / 2) * (zero.kernel x * hpl [] x) +
    (20) * (negOne.kernel x * hpl [zero] x) +
    (23 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (-7 / 2) * (zero.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, negOne] x) +
    (4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-6) * (zero.kernel x * hpl [negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, negOne] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s4N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s4N3 (i8Psi4s4dN3 x) x := by
  unfold i8Psi4s4N3 i8Psi4s4dN3
  exact ((((((((((((((((((hasDerivAt_const x (273 / 8 + 7 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-23 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-29 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (23 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽4⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s4N4 (x : ℝ) : ℝ :=
    (17 / 8 + π ^ 2 / 24) +
    (-27 / 8 - π ^ 2 / 12) * hpl [negOne] x +
    (-7 / 8) * hpl [zero] x +
    (2) * hpl [negOne, zero] x +
    (27 / 4 + π ^ 2 / 6) * hpl [zero, negOne] x +
    (-1 / 4) * hpl [zero, zero] x +
    (-2) * hpl [negOne, negOne, zero] x +
    (-1) * hpl [negOne, zero, negOne] x +
    (1 / 2) * hpl [negOne, zero, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-9 / 2) * hpl [zero, zero, negOne] x +
    (2) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [negOne, zero, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (2) * hpl [zero, negOne, zero, negOne] x +
    (-1) * hpl [zero, negOne, zero, zero] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s4N4`. -/
noncomputable def i8Psi4s4dN4 (x : ℝ) : ℝ :=
    0 +
    (-27 / 8 - π ^ 2 / 12) * (negOne.kernel x * hpl [] x) +
    (-7 / 8) * (zero.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [zero] x) +
    (27 / 4 + π ^ 2 / 6) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-9 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s4N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s4N4 (i8Psi4s4dN4 x) x := by
  unfold i8Psi4s4N4 i8Psi4s4dN4
  exact ((((((((((((((((((hasDerivAt_const x (17 / 8 + π ^ 2 / 24)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-27 / 8 - π ^ 2 / 12))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-7 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (27 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-9 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3)))

/-- The part of `Ψ₄⁽4⁾` with constant coefficients. -/
noncomputable def i8Psi4s4W (x : ℝ) : ℝ :=
    (7 / 2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s4W`. -/
noncomputable def i8Psi4s4dW (x : ℝ) : ℝ :=
    (7 / 2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s4W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s4W (i8Psi4s4dW x) x := by
  unfold i8Psi4s4W i8Psi4s4dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (7 / 2))

/-- The piece `Ψ₄⁽4⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s4 (x : ℝ) : ℝ :=
  (i8Psi4s4N0 x + x * i8Psi4s4N1 x + x ^ 2 * i8Psi4s4N2 x + x ^ 3 * i8Psi4s4N3 x +
    x ^ 4 * i8Psi4s4N4 x) / x ^ 2 + i8Psi4s4W x

/-- The derivative of `Ψ₄⁽4⁾`. -/
noncomputable def i8Psi4s4D (x : ℝ) : ℝ :=
  ((i8Psi4s4dN0 x + (i8Psi4s4N1 x + x * i8Psi4s4dN1 x) + (2 * x * i8Psi4s4N2 x +
    x ^ 2 * i8Psi4s4dN2 x) + (3 * x ^ 2 * i8Psi4s4N3 x + x ^ 3 * i8Psi4s4dN3 x) +
    (4 * x ^ 3 * i8Psi4s4N4 x + x ^ 4 * i8Psi4s4dN4 x)) * x ^ 2 - (i8Psi4s4N0 x +
    x * i8Psi4s4N1 x + x ^ 2 * i8Psi4s4N2 x + x ^ 3 * i8Psi4s4N3 x +
    x ^ 4 * i8Psi4s4N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s4dW x

theorem hasDerivAt_i8Psi4s4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s4 (i8Psi4s4D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s4N0 hx).add (X.mul (hasDerivAt_i8Psi4s4N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s4N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s4N3 hx))).add ((X.pow
    4).mul (hasDerivAt_i8Psi4s4N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add (hasDerivAt_i8Psi4s4W
    hx)
  unfold i8Psi4s4
  refine e.congr_deriv ?_
  unfold i8Psi4s4D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 4 of `p₄` in `ξ`: from `t B2 A2 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s4 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * i13Be2x x * ((1 + x) / (1 - x) * (-hpl [zero, negOne] x))

/-- **`(Ψ₄⁽4⁾)'(ξ) ξ' = p₄⁽4⁾`**, in terms of `ξ`. -/
theorem i8Psi4s4D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s4D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s4 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s4D i8Psi4s4N0 i8Psi4s4N1 i8Psi4s4N2 i8Psi4s4N3 i8Psi4s4N4 i8Psi4s4dN0 i8Psi4s4dN1
    i8Psi4s4dN2 i8Psi4s4dN3 i8Psi4s4dN4 i8Psi4s4dW i8P4s4 i13Be2x
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_0m0 hx,
    i13hw_m00 hx, i13hw_m0m hx, i13hw_mm0 hx, i13hw_00m0 hx, i13hw_0m00 hx, i13hw_0m0m hx,
    i13hw_0mm0 hx, i13hw_m00m hx, i13hw_m0m0 hx, i13_Li₂_neg_eq hx, i13_log_one_add_eq hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽5⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s5N0 (x : ℝ) : ℝ :=
    (21 / 2 - π ^ 2 / 3) * hpl [negOne, negOne] x +
    (5) * hpl [negOne, negOne, zero] x +
    (5) * hpl [negOne, zero, negOne] x +
    (5) * hpl [zero, negOne, negOne] x +
    (-12) * hpl [negOne, negOne, negOne, zero] x +
    (-8) * hpl [negOne, negOne, zero, negOne] x +
    (2) * hpl [negOne, negOne, zero, zero] x +
    (-4) * hpl [negOne, zero, negOne, negOne] x +
    (2) * hpl [negOne, zero, negOne, zero] x +
    (2) * hpl [negOne, zero, zero, negOne] x +
    (2) * hpl [zero, negOne, negOne, zero] x +
    (2) * hpl [zero, negOne, zero, negOne] x +
    (2) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s5N0`. -/
noncomputable def i8Psi4s5dN0 (x : ℝ) : ℝ :=
    (21 / 2 - π ^ 2 / 3) * (negOne.kernel x * hpl [negOne] x) +
    (5) * (negOne.kernel x * hpl [negOne, zero] x) +
    (5) * (negOne.kernel x * hpl [zero, negOne] x) +
    (5) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-12) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-8) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s5N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5N0 (i8Psi4s5dN0 x) x := by
  unfold i8Psi4s5N0 i8Psi4s5dN0
  exact ((((((((((((((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (21 / 2 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽5⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s5N1 (x : ℝ) : ℝ :=
    (35 / 2 - π ^ 2 / 3) * hpl [negOne] x +
    (20 - 4 / 3 * π ^ 2) * hpl [negOne, negOne] x +
    (7) * hpl [negOne, zero] x +
    (7) * hpl [zero, negOne] x +
    (12) * hpl [negOne, negOne, zero] x +
    (16) * hpl [negOne, zero, negOne] x +
    (2) * hpl [negOne, zero, zero] x +
    (20) * hpl [zero, negOne, negOne] x +
    (2) * hpl [zero, negOne, zero] x +
    (2) * hpl [zero, zero, negOne] x +
    (-48) * hpl [negOne, negOne, negOne, zero] x +
    (-32) * hpl [negOne, negOne, zero, negOne] x +
    (8) * hpl [negOne, negOne, zero, zero] x +
    (-16) * hpl [negOne, zero, negOne, negOne] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (8) * hpl [negOne, zero, zero, negOne] x +
    (8) * hpl [zero, negOne, negOne, zero] x +
    (8) * hpl [zero, negOne, zero, negOne] x +
    (8) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s5N1`. -/
noncomputable def i8Psi4s5dN1 (x : ℝ) : ℝ :=
    (35 / 2 - π ^ 2 / 3) * (negOne.kernel x * hpl [] x) +
    (20 - 4 / 3 * π ^ 2) * (negOne.kernel x * hpl [negOne] x) +
    (7) * (negOne.kernel x * hpl [zero] x) +
    (7) * (zero.kernel x * hpl [negOne] x) +
    (12) * (negOne.kernel x * hpl [negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, zero] x) +
    (20) * (zero.kernel x * hpl [negOne, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-48) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-32) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s5N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5N1 (i8Psi4s5dN1 x) x := by
  unfold i8Psi4s5N1 i8Psi4s5dN1
  exact ((((((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (35 / 2 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (20 - 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (8)))

/-- Chunk 0 of `i8Psi4s5N2`. -/
noncomputable def i8Psi4s5N2c0 (x : ℝ) : ℝ :=
    (157 / 4 + π ^ 2 / 2) * hpl [negOne] x +
    (-35 / 2 + π ^ 2 / 3) * hpl [zero] x +
    (-2 * π ^ 2) * hpl [negOne, negOne] x +
    (-18) * hpl [negOne, zero] x +
    (-19 / 2 + π ^ 2) * hpl [zero, negOne] x +
    (-7) * hpl [zero, zero] x +
    (42) * hpl [negOne, negOne, zero] x +
    (36) * hpl [negOne, zero, negOne] x +
    (-3) * hpl [negOne, zero, zero] x +
    (32) * hpl [zero, negOne, negOne] x +
    (-7) * hpl [zero, negOne, zero] x +
    (-11) * hpl [zero, zero, negOne] x +
    (-72) * hpl [negOne, negOne, negOne, zero] x +
    (-48) * hpl [negOne, negOne, zero, negOne] x +
    (12) * hpl [negOne, negOne, zero, zero] x +
    (-24) * hpl [negOne, zero, negOne, negOne] x +
    (12) * hpl [negOne, zero, negOne, zero] x +
    (12) * hpl [negOne, zero, zero, negOne] x +
    (36) * hpl [zero, negOne, negOne, zero] x +
    (24) * hpl [zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s5N2c0`. -/
noncomputable def i8Psi4s5dN2c0 (x : ℝ) : ℝ :=
    (157 / 4 + π ^ 2 / 2) * (negOne.kernel x * hpl [] x) +
    (-35 / 2 + π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (-2 * π ^ 2) * (negOne.kernel x * hpl [negOne] x) +
    (-18) * (negOne.kernel x * hpl [zero] x) +
    (-19 / 2 + π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (-7) * (zero.kernel x * hpl [zero] x) +
    (42) * (negOne.kernel x * hpl [negOne, zero] x) +
    (36) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-3) * (negOne.kernel x * hpl [zero, zero] x) +
    (32) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-7) * (zero.kernel x * hpl [negOne, zero] x) +
    (-11) * (zero.kernel x * hpl [zero, negOne] x) +
    (-72) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-48) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (12) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (12) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (12) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (36) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (24) * (zero.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s5N2c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5N2c0 (i8Psi4s5dN2c0 x) x := by
  unfold i8Psi4s5N2c0 i8Psi4s5dN2c0
  exact (((((((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (157 / 4 + π ^ 2 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-35 / 2 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-19 / 2 + π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (42))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-72))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (24)))

/-- Chunk 1 of `i8Psi4s5N2`. -/
noncomputable def i8Psi4s5N2c1 (x : ℝ) : ℝ :=
    (12) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s5N2c1`. -/
noncomputable def i8Psi4s5dN2c1 (x : ℝ) : ℝ :=
    (12) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s5N2c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5N2c1 (i8Psi4s5dN2c1 x) x := by
  unfold i8Psi4s5N2c1 i8Psi4s5dN2c1
  exact ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (12))

/-- The part of `ξ² Ψ₄⁽5⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s5N2 (x : ℝ) : ℝ :=
    i8Psi4s5N2c0 x + i8Psi4s5N2c1 x

/-- The derivative of `i8Psi4s5N2`. -/
noncomputable def i8Psi4s5dN2 (x : ℝ) : ℝ :=
    i8Psi4s5dN2c0 x + i8Psi4s5dN2c1 x

theorem hasDerivAt_i8Psi4s5N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5N2 (i8Psi4s5dN2 x) x := by
  unfold i8Psi4s5N2 i8Psi4s5dN2
  exact ((hasDerivAt_i8Psi4s5N2c0 hx).add (hasDerivAt_i8Psi4s5N2c1 hx))

/-- Chunk 0 of `i8Psi4s5N3`. -/
noncomputable def i8Psi4s5N3c0 (x : ℝ) : ℝ :=
    (-167 / 4 - 5 / 6 * π ^ 2) +
    (57 / 2 + π ^ 2) * hpl [negOne] x +
    (20) * hpl [zero] x +
    (-20 - 4 / 3 * π ^ 2) * hpl [negOne, negOne] x +
    (-29) * hpl [negOne, zero] x +
    (-19) * hpl [zero, negOne] x +
    (5) * hpl [zero, zero] x +
    (44) * hpl [negOne, negOne, zero] x +
    (32) * hpl [negOne, zero, negOne] x +
    (-6) * hpl [negOne, zero, zero] x +
    (20) * hpl [zero, negOne, negOne] x +
    (-6) * hpl [zero, negOne, zero] x +
    (-6) * hpl [zero, zero, negOne] x +
    (-48) * hpl [negOne, negOne, negOne, zero] x +
    (-32) * hpl [negOne, negOne, zero, negOne] x +
    (8) * hpl [negOne, negOne, zero, zero] x +
    (-16) * hpl [negOne, zero, negOne, negOne] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (8) * hpl [negOne, zero, zero, negOne] x +
    (8) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s5N3c0`. -/
noncomputable def i8Psi4s5dN3c0 (x : ℝ) : ℝ :=
    0 +
    (57 / 2 + π ^ 2) * (negOne.kernel x * hpl [] x) +
    (20) * (zero.kernel x * hpl [] x) +
    (-20 - 4 / 3 * π ^ 2) * (negOne.kernel x * hpl [negOne] x) +
    (-29) * (negOne.kernel x * hpl [zero] x) +
    (-19) * (zero.kernel x * hpl [negOne] x) +
    (5) * (zero.kernel x * hpl [zero] x) +
    (44) * (negOne.kernel x * hpl [negOne, zero] x) +
    (32) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-6) * (negOne.kernel x * hpl [zero, zero] x) +
    (20) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-6) * (zero.kernel x * hpl [negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, negOne] x) +
    (-48) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-32) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s5N3c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5N3c0 (i8Psi4s5dN3c0 x) x := by
  unfold i8Psi4s5N3c0 i8Psi4s5dN3c0
  exact ((((((((((((((((((((hasDerivAt_const x (-167 / 4 - 5 / 6 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (57 / 2 + π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-20 - 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-29))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-19))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (44))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (8)))

/-- Chunk 1 of `i8Psi4s5N3`. -/
noncomputable def i8Psi4s5N3c1 (x : ℝ) : ℝ :=
    (8) * hpl [zero, negOne, zero, negOne] x +
    (8) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s5N3c1`. -/
noncomputable def i8Psi4s5dN3c1 (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s5N3c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5N3c1 (i8Psi4s5dN3c1 x) x := by
  unfold i8Psi4s5N3c1 i8Psi4s5dN3c1
  exact (((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽5⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s5N3 (x : ℝ) : ℝ :=
    i8Psi4s5N3c0 x + i8Psi4s5N3c1 x

/-- The derivative of `i8Psi4s5N3`. -/
noncomputable def i8Psi4s5dN3 (x : ℝ) : ℝ :=
    i8Psi4s5dN3c0 x + i8Psi4s5dN3c1 x

theorem hasDerivAt_i8Psi4s5N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5N3 (i8Psi4s5dN3 x) x := by
  unfold i8Psi4s5N3 i8Psi4s5dN3
  exact ((hasDerivAt_i8Psi4s5N3c0 hx).add (hasDerivAt_i8Psi4s5N3c1 hx))

/-- Chunk 0 of `i8Psi4s5N4`. -/
noncomputable def i8Psi4s5N4c0 (x : ℝ) : ℝ :=
    (-17 / 4 - π ^ 2 / 12) +
    (27 / 4 + π ^ 2 / 6) * hpl [negOne] x +
    (7 / 4) * hpl [zero] x +
    (-21 / 2 - π ^ 2 / 3) * hpl [negOne, negOne] x +
    (-4) * hpl [negOne, zero] x +
    (-3) * hpl [zero, negOne] x +
    (1 / 2) * hpl [zero, zero] x +
    (9) * hpl [negOne, negOne, zero] x +
    (7) * hpl [negOne, zero, negOne] x +
    (-1) * hpl [negOne, zero, zero] x +
    (5) * hpl [zero, negOne, negOne] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-1) * hpl [zero, zero, negOne] x +
    (-12) * hpl [negOne, negOne, negOne, zero] x +
    (-8) * hpl [negOne, negOne, zero, negOne] x +
    (2) * hpl [negOne, negOne, zero, zero] x +
    (-4) * hpl [negOne, zero, negOne, negOne] x +
    (2) * hpl [negOne, zero, negOne, zero] x +
    (2) * hpl [negOne, zero, zero, negOne] x +
    (2) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s5N4c0`. -/
noncomputable def i8Psi4s5dN4c0 (x : ℝ) : ℝ :=
    0 +
    (27 / 4 + π ^ 2 / 6) * (negOne.kernel x * hpl [] x) +
    (7 / 4) * (zero.kernel x * hpl [] x) +
    (-21 / 2 - π ^ 2 / 3) * (negOne.kernel x * hpl [negOne] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (-3) * (zero.kernel x * hpl [negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [zero] x) +
    (9) * (negOne.kernel x * hpl [negOne, zero] x) +
    (7) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero, zero] x) +
    (5) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne] x) +
    (-12) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-8) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s5N4c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5N4c0 (i8Psi4s5dN4c0 x) x := by
  unfold i8Psi4s5N4c0 i8Psi4s5dN4c0
  exact ((((((((((((((((((((hasDerivAt_const x (-17 / 4 - π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (27 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (7 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-21 / 2 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (2)))

/-- Chunk 1 of `i8Psi4s5N4`. -/
noncomputable def i8Psi4s5N4c1 (x : ℝ) : ℝ :=
    (2) * hpl [zero, negOne, zero, negOne] x +
    (2) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s5N4c1`. -/
noncomputable def i8Psi4s5dN4c1 (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s5N4c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5N4c1 (i8Psi4s5dN4c1 x) x := by
  unfold i8Psi4s5N4c1 i8Psi4s5dN4c1
  exact (((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽5⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s5N4 (x : ℝ) : ℝ :=
    i8Psi4s5N4c0 x + i8Psi4s5N4c1 x

/-- The derivative of `i8Psi4s5N4`. -/
noncomputable def i8Psi4s5dN4 (x : ℝ) : ℝ :=
    i8Psi4s5dN4c0 x + i8Psi4s5dN4c1 x

theorem hasDerivAt_i8Psi4s5N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5N4 (i8Psi4s5dN4 x) x := by
  unfold i8Psi4s5N4 i8Psi4s5dN4
  exact ((hasDerivAt_i8Psi4s5N4c0 hx).add (hasDerivAt_i8Psi4s5N4c1 hx))

/-- The part of `Ψ₄⁽5⁾` with constant coefficients. -/
noncomputable def i8Psi4s5W (x : ℝ) : ℝ :=
    (-2) * hpl [zero, zero, zero] x +
    (-6) * hpl [zero, negOne, zero, zero] x +
    (-6) * hpl [zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s5W`. -/
noncomputable def i8Psi4s5dW (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [zero, zero] x) +
    (-6) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s5W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5W (i8Psi4s5dW x) x := by
  unfold i8Psi4s5W i8Psi4s5dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-6)))

/-- The piece `Ψ₄⁽5⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s5 (x : ℝ) : ℝ :=
  (i8Psi4s5N0 x + x * i8Psi4s5N1 x + x ^ 2 * i8Psi4s5N2 x + x ^ 3 * i8Psi4s5N3 x +
    x ^ 4 * i8Psi4s5N4 x) / x ^ 2 + i8Psi4s5W x

/-- The derivative of `Ψ₄⁽5⁾`. -/
noncomputable def i8Psi4s5D (x : ℝ) : ℝ :=
  ((i8Psi4s5dN0 x + (i8Psi4s5N1 x + x * i8Psi4s5dN1 x) + (2 * x * i8Psi4s5N2 x +
    x ^ 2 * i8Psi4s5dN2 x) + (3 * x ^ 2 * i8Psi4s5N3 x + x ^ 3 * i8Psi4s5dN3 x) +
    (4 * x ^ 3 * i8Psi4s5N4 x + x ^ 4 * i8Psi4s5dN4 x)) * x ^ 2 - (i8Psi4s5N0 x +
    x * i8Psi4s5N1 x + x ^ 2 * i8Psi4s5N2 x + x ^ 3 * i8Psi4s5N3 x +
    x ^ 4 * i8Psi4s5N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s5dW x

theorem hasDerivAt_i8Psi4s5 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s5 (i8Psi4s5D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s5N0 hx).add (X.mul (hasDerivAt_i8Psi4s5N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s5N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s5N3 hx))).add ((X.pow
    4).mul (hasDerivAt_i8Psi4s5N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add (hasDerivAt_i8Psi4s5W
    hx)
  unfold i8Psi4s5
  refine e.congr_deriv ?_
  unfold i8Psi4s5D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 5 of `p₄` in `ξ`: from `t B2 A2 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s5 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * i13Be2x x * ((1 + x) / (1 - x) * (2 * hpl [negOne, negOne] x))

/-- **`(Ψ₄⁽5⁾)'(ξ) ξ' = p₄⁽5⁾`**, in terms of `ξ`. -/
theorem i8Psi4s5D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s5D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s5 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s5D i8Psi4s5N0 i8Psi4s5N1 i8Psi4s5N2 i8Psi4s5N3 i8Psi4s5N4 i8Psi4s5dN0 i8Psi4s5dN1
    i8Psi4s5dN2 i8Psi4s5dN3 i8Psi4s5dN4 i8Psi4s5dW i8Psi4s5N2c0 i8Psi4s5dN2c0 i8Psi4s5N2c1
    i8Psi4s5dN2c1 i8Psi4s5N3c0 i8Psi4s5dN3c0 i8Psi4s5N3c1 i8Psi4s5dN3c1 i8Psi4s5N4c0 i8Psi4s5dN4c0
    i8Psi4s5N4c1 i8Psi4s5dN4c1 i8P4s5 i13Be2x
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_mm hx,
    i13hw_0m0 hx, i13hw_m00 hx, i13hw_m0m hx, i13hw_mm0 hx, i8hw_mm0m hx, i13hw_0m0m hx, i13hw_0mm0
    hx, i13hw_m00m hx, i13hw_m0m0 hx, i13hw_m0mm hx, i13hw_mm00 hx, i13hw_mmm0 hx, i13_Li₂_neg_eq
    hx, i13_log_one_add_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
