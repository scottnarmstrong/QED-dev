/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P8

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 50 to 55

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s50`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s50D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s50`, `QED.ThreeLoopD.i8Psi4s50D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽50⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s50N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s50N0`. -/
noncomputable def i8Psi4s50dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s50N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s50N0 (i8Psi4s50dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽50⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s50N1 (x : ℝ) : ℝ :=
    (66 - 7 / 3 * π ^ 2 + π ^ 2 ^ 2 / 36) +
    (50 - π ^ 2) * hpl [zero] x +
    (-28 + 2 / 3 * π ^ 2) * hpl [negOne, zero] x +
    (34 - π ^ 2 / 3) * hpl [zero, zero] x +
    (-24) * hpl [negOne, zero, zero] x +
    (-12) * hpl [zero, negOne, zero] x +
    (18) * hpl [zero, zero, zero] x +
    (16) * hpl [negOne, negOne, zero, zero] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (-12) * hpl [negOne, zero, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-4) * hpl [zero, zero, negOne, zero] x +
    (6) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s50N1`. -/
noncomputable def i8Psi4s50dN1 (x : ℝ) : ℝ :=
    0 +
    (50 - π ^ 2) * (zero.kernel x * hpl [] x) +
    (-28 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (34 - π ^ 2 / 3) * (zero.kernel x * hpl [zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, zero] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero] x) +
    (18) * (zero.kernel x * hpl [zero, zero] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s50N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s50N1 (i8Psi4s50dN1 x) x := by
  unfold i8Psi4s50N1 i8Psi4s50dN1
  exact (((((((((((((hasDerivAt_const x (66 - 7 / 3 * π ^ 2 + π ^ 2 ^ 2 / 36)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (50 - π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-28 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (34 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (6)))

/-- The part of `ξ² Ψ₄⁽50⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s50N2 (x : ℝ) : ℝ :=
    (16 - π ^ 2 ^ 2 / 12 + 4 / 3 * π ^ 2) * hpl [zero] x +
    (-131 / 2 - π ^ 2) * hpl [negOne, zero] x +
    (12 + 4 / 3 * π ^ 2) * hpl [zero, zero] x +
    (30) * hpl [negOne, zero, zero] x +
    (16 - 2 * π ^ 2) * hpl [zero, negOne, zero] x +
    (-8 + π ^ 2) * hpl [zero, zero, zero] x +
    (-24) * hpl [negOne, negOne, zero, zero] x +
    (-12) * hpl [negOne, zero, negOne, zero] x +
    (18) * hpl [negOne, zero, zero, zero] x +
    (32) * hpl [zero, negOne, zero, zero] x +
    (16) * hpl [zero, zero, negOne, zero] x +
    (-24) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s50N2`. -/
noncomputable def i8Psi4s50dN2 (x : ℝ) : ℝ :=
    (16 - π ^ 2 ^ 2 / 12 + 4 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-131 / 2 - π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (12 + 4 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (30) * (negOne.kernel x * hpl [zero, zero] x) +
    (16 - 2 * π ^ 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8 + π ^ 2) * (zero.kernel x * hpl [zero, zero] x) +
    (-24) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (18) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (32) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (16) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s50N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s50N2 (i8Psi4s50dN2 x) x := by
  unfold i8Psi4s50N2 i8Psi4s50dN2
  exact (((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (16 - π ^ 2 ^ 2 / 12 +
    4 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-131 / 2 - π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (12 + 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (30))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (16 - 2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-8 + π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽50⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s50N3 (x : ℝ) : ℝ :=
    (-119 / 2 - 4 * π ^ 2 - π ^ 2 ^ 2 / 12) +
    (151 / 2 + 8 / 3 * π ^ 2) * hpl [zero] x +
    (-48 - 2 * π ^ 2) * hpl [negOne, zero] x +
    (-22 + π ^ 2) * hpl [zero, zero] x +
    (64) * hpl [negOne, zero, zero] x +
    (32) * hpl [zero, negOne, zero] x +
    (-48) * hpl [zero, zero, zero] x +
    (-48) * hpl [negOne, negOne, zero, zero] x +
    (-24) * hpl [negOne, zero, negOne, zero] x +
    (36) * hpl [negOne, zero, zero, zero] x +
    (24) * hpl [zero, negOne, zero, zero] x +
    (12) * hpl [zero, zero, negOne, zero] x +
    (-18) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s50N3`. -/
noncomputable def i8Psi4s50dN3 (x : ℝ) : ℝ :=
    0 +
    (151 / 2 + 8 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-48 - 2 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (-22 + π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (64) * (negOne.kernel x * hpl [zero, zero] x) +
    (32) * (zero.kernel x * hpl [negOne, zero] x) +
    (-48) * (zero.kernel x * hpl [zero, zero] x) +
    (-48) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (36) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (24) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (12) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-18) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s50N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s50N3 (i8Psi4s50dN3 x) x := by
  unfold i8Psi4s50N3 i8Psi4s50dN3
  exact (((((((((((((hasDerivAt_const x (-119 / 2 - 4 * π ^ 2 - π ^ 2 ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (151 / 2 + 8 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-48 - 2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-22 + π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (64))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-18)))

/-- The part of `ξ² Ψ₄⁽50⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s50N4 (x : ℝ) : ℝ :=
    (-239 / 16 - 7 / 8 * π ^ 2 - π ^ 2 ^ 2 / 72) +
    (111 / 8 + 5 / 12 * π ^ 2) * hpl [zero] x +
    (-21 / 2 - π ^ 2 / 3) * hpl [negOne, zero] x +
    (-5 / 4 + π ^ 2 / 6) * hpl [zero, zero] x +
    (10) * hpl [negOne, zero, zero] x +
    (5) * hpl [zero, negOne, zero] x +
    (-15 / 2) * hpl [zero, zero, zero] x +
    (-8) * hpl [negOne, negOne, zero, zero] x +
    (-4) * hpl [negOne, zero, negOne, zero] x +
    (6) * hpl [negOne, zero, zero, zero] x +
    (4) * hpl [zero, negOne, zero, zero] x +
    (2) * hpl [zero, zero, negOne, zero] x +
    (-3) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s50N4`. -/
noncomputable def i8Psi4s50dN4 (x : ℝ) : ℝ :=
    0 +
    (111 / 8 + 5 / 12 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-21 / 2 - π ^ 2 / 3) * (negOne.kernel x * hpl [zero] x) +
    (-5 / 4 + π ^ 2 / 6) * (zero.kernel x * hpl [zero] x) +
    (10) * (negOne.kernel x * hpl [zero, zero] x) +
    (5) * (zero.kernel x * hpl [negOne, zero] x) +
    (-15 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (-8) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (6) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s50N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s50N4 (i8Psi4s50dN4 x) x := by
  unfold i8Psi4s50N4 i8Psi4s50dN4
  exact (((((((((((((hasDerivAt_const x (-239 / 16 - 7 / 8 * π ^ 2 - π ^ 2 ^ 2 / 72)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (111 / 8 + 5 / 12 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-21 / 2 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-5 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-15 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-3)))

/-- The part of `Ψ₄⁽50⁾` with constant coefficients. -/
noncomputable def i8Psi4s50W (x : ℝ) : ℝ :=
    (-48) * hpl [zero, negOne, negOne, zero, zero] x +
    (-24) * hpl [zero, negOne, zero, negOne, zero] x +
    (36) * hpl [zero, negOne, zero, zero, zero] x +
    (24) * hpl [zero, zero, negOne, zero, zero] x +
    (12) * hpl [zero, zero, zero, negOne, zero] x +
    (-18) * hpl [zero, zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s50W`. -/
noncomputable def i8Psi4s50dW (x : ℝ) : ℝ :=
    (-48) * (zero.kernel x * hpl [negOne, negOne, zero, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero, negOne, zero] x) +
    (36) * (zero.kernel x * hpl [negOne, zero, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, negOne, zero, zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero, negOne, zero] x) +
    (-18) * (zero.kernel x * hpl [zero, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s50W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s50W (i8Psi4s50dW x) x := by
  unfold i8Psi4s50W i8Psi4s50dW
  exact (((((((hasDerivAt_hpl_cons zero [negOne, negOne, zero, zero] hx).const_mul (-48)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, zero] hx).const_mul (-18)))

/-- The piece `Ψ₄⁽50⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s50 (x : ℝ) : ℝ :=
  (i8Psi4s50N0 x + x * i8Psi4s50N1 x + x ^ 2 * i8Psi4s50N2 x + x ^ 3 * i8Psi4s50N3 x +
    x ^ 4 * i8Psi4s50N4 x) / x ^ 2 + i8Psi4s50W x

/-- The derivative of `Ψ₄⁽50⁾`. -/
noncomputable def i8Psi4s50D (x : ℝ) : ℝ :=
  ((i8Psi4s50dN0 x + (i8Psi4s50N1 x + x * i8Psi4s50dN1 x) + (2 * x * i8Psi4s50N2 x +
    x ^ 2 * i8Psi4s50dN2 x) + (3 * x ^ 2 * i8Psi4s50N3 x + x ^ 3 * i8Psi4s50dN3 x) +
    (4 * x ^ 3 * i8Psi4s50N4 x + x ^ 4 * i8Psi4s50dN4 x)) * x ^ 2 - (i8Psi4s50N0 x +
    x * i8Psi4s50N1 x + x ^ 2 * i8Psi4s50N2 x + x ^ 3 * i8Psi4s50N3 x +
    x ^ 4 * i8Psi4s50N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s50dW x

theorem hasDerivAt_i8Psi4s50 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s50 (i8Psi4s50D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s50N0 hx).add (X.mul (hasDerivAt_i8Psi4s50N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s50N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s50N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s50N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s50W hx)
  unfold i8Psi4s50
  refine e.congr_deriv ?_
  unfold i8Psi4s50D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 50 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s50 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * i13Be2x x * i13Be2x x * (x / (1 - x))

/-- **`(Ψ₄⁽50⁾)'(ξ) ξ' = p₄⁽50⁾`**, in terms of `ξ`. -/
theorem i8Psi4s50D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s50D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s50 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s50D i8Psi4s50N0 i8Psi4s50N1 i8Psi4s50N2 i8Psi4s50N3 i8Psi4s50N4 i8Psi4s50dN0
    i8Psi4s50dN1 i8Psi4s50dN2 i8Psi4s50dN3 i8Psi4s50dN4 i8Psi4s50dW i8P4s50 i13Be2x
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_000,
    i13hw_0m0 hx, i13hw_m00 hx, i13hw_0000, i13hw_00m0 hx, i13hw_0m00 hx, i13hw_m000 hx, i13hw_m0m0
    hx, i13hw_mm00 hx, i13_Li₂_neg_eq hx, i13_log_one_add_eq hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽51⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s51N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s51N0`. -/
noncomputable def i8Psi4s51dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s51N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s51N0 (i8Psi4s51dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽51⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s51N1 (x : ℝ) : ℝ :=
    (4) +
    (4) * hpl [zero] x

/-- The derivative of `i8Psi4s51N1`. -/
noncomputable def i8Psi4s51dN1 (x : ℝ) : ℝ :=
    0 +
    (4) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s51N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s51N1 (i8Psi4s51dN1 x) x := by
  unfold i8Psi4s51N1 i8Psi4s51dN1
  exact ((hasDerivAt_const x (4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽51⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s51N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s51N2`. -/
noncomputable def i8Psi4s51dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s51N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s51N2 (i8Psi4s51dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽51⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s51N3 (x : ℝ) : ℝ :=
    (-4) +
    (4) * hpl [zero] x

/-- The derivative of `i8Psi4s51N3`. -/
noncomputable def i8Psi4s51dN3 (x : ℝ) : ℝ :=
    0 +
    (4) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s51N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s51N3 (i8Psi4s51dN3 x) x := by
  unfold i8Psi4s51N3 i8Psi4s51dN3
  exact ((hasDerivAt_const x (-4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽51⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s51N4 (x : ℝ) : ℝ :=
    (1) +
    (-2) * hpl [zero] x

/-- The derivative of `i8Psi4s51N4`. -/
noncomputable def i8Psi4s51dN4 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s51N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s51N4 (i8Psi4s51dN4 x) x := by
  unfold i8Psi4s51N4 i8Psi4s51dN4
  exact ((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽51⁾` with constant coefficients. -/
noncomputable def i8Psi4s51W (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s51W`. -/
noncomputable def i8Psi4s51dW (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s51W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s51W (i8Psi4s51dW x) x := by
  unfold i8Psi4s51W i8Psi4s51dW
  exact ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4))

/-- The piece `Ψ₄⁽51⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s51 (x : ℝ) : ℝ :=
  (i8Psi4s51N0 x + x * i8Psi4s51N1 x + x ^ 2 * i8Psi4s51N2 x + x ^ 3 * i8Psi4s51N3 x +
    x ^ 4 * i8Psi4s51N4 x) / x ^ 2 + i8Psi4s51W x

/-- The derivative of `Ψ₄⁽51⁾`. -/
noncomputable def i8Psi4s51D (x : ℝ) : ℝ :=
  ((i8Psi4s51dN0 x + (i8Psi4s51N1 x + x * i8Psi4s51dN1 x) + (2 * x * i8Psi4s51N2 x +
    x ^ 2 * i8Psi4s51dN2 x) + (3 * x ^ 2 * i8Psi4s51N3 x + x ^ 3 * i8Psi4s51dN3 x) +
    (4 * x ^ 3 * i8Psi4s51N4 x + x ^ 4 * i8Psi4s51dN4 x)) * x ^ 2 - (i8Psi4s51N0 x +
    x * i8Psi4s51N1 x + x ^ 2 * i8Psi4s51N2 x + x ^ 3 * i8Psi4s51N3 x +
    x ^ 4 * i8Psi4s51N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s51dW x

theorem hasDerivAt_i8Psi4s51 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s51 (i8Psi4s51D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s51N0 hx).add (X.mul (hasDerivAt_i8Psi4s51N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s51N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s51N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s51N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s51W hx)
  unfold i8Psi4s51
  refine e.congr_deriv ?_
  unfold i8Psi4s51D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 51 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s51 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 - x) * (4 * x / (1 + x)))

/-- **`(Ψ₄⁽51⁾)'(ξ) ξ' = p₄⁽51⁾`**, in terms of `ξ`. -/
theorem i8Psi4s51D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s51D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s51 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s51D i8Psi4s51N0 i8Psi4s51N1 i8Psi4s51N2 i8Psi4s51N3 i8Psi4s51N4 i8Psi4s51dN0
    i8Psi4s51dN1 i8Psi4s51dN2 i8Psi4s51dN3 i8Psi4s51dN4 i8Psi4s51dW i8P4s51
  simp only [kernel_zero, hpl_nil, hpl_zero]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽52⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s52N0 (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [negOne] x +
    (-1) * hpl [negOne, zero] x +
    (-1) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s52N0`. -/
noncomputable def i8Psi4s52dN0 (x : ℝ) : ℝ :=
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s52N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s52N0 (i8Psi4s52dN0 x) x := by
  unfold i8Psi4s52N0 i8Psi4s52dN0
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽52⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s52N1 (x : ℝ) : ℝ :=
    (-3 / 2) +
    (-1) * hpl [zero] x

/-- The derivative of `i8Psi4s52N1`. -/
noncomputable def i8Psi4s52dN1 (x : ℝ) : ℝ :=
    0 +
    (-1) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s52N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s52N1 (i8Psi4s52dN1 x) x := by
  unfold i8Psi4s52N1 i8Psi4s52dN1
  exact ((hasDerivAt_const x (-3 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽52⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s52N2 (x : ℝ) : ℝ :=
    (1) * hpl [negOne] x +
    (-1 / 2) * hpl [zero] x

/-- The derivative of `i8Psi4s52N2`. -/
noncomputable def i8Psi4s52dN2 (x : ℝ) : ℝ :=
    (1) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s52N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s52N2 (i8Psi4s52dN2 x) x := by
  unfold i8Psi4s52N2 i8Psi4s52dN2
  exact (((hasDerivAt_hpl_cons negOne [] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2)))

/-- The part of `ξ² Ψ₄⁽52⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s52N3 (x : ℝ) : ℝ :=
    (-3 / 2) +
    (1) * hpl [zero] x

/-- The derivative of `i8Psi4s52N3`. -/
noncomputable def i8Psi4s52dN3 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s52N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s52N3 (i8Psi4s52dN3 x) x := by
  unfold i8Psi4s52N3 i8Psi4s52dN3
  exact ((hasDerivAt_const x (-3 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽52⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s52N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 2) * hpl [negOne] x +
    (-1 / 2) * hpl [zero] x +
    (1) * hpl [negOne, zero] x +
    (1) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s52N4`. -/
noncomputable def i8Psi4s52dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s52N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s52N4 (i8Psi4s52dN4 x) x := by
  unfold i8Psi4s52N4 i8Psi4s52dN4
  exact (((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1)))

/-- The part of `Ψ₄⁽52⁾` with constant coefficients. -/
noncomputable def i8Psi4s52W (x : ℝ) : ℝ :=
    (-1) * hpl [zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s52W`. -/
noncomputable def i8Psi4s52dW (x : ℝ) : ℝ :=
    (-1) * (zero.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s52W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s52W (i8Psi4s52dW x) x := by
  unfold i8Psi4s52W i8Psi4s52dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-4)))

/-- The piece `Ψ₄⁽52⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s52 (x : ℝ) : ℝ :=
  (i8Psi4s52N0 x + x * i8Psi4s52N1 x + x ^ 2 * i8Psi4s52N2 x + x ^ 3 * i8Psi4s52N3 x +
    x ^ 4 * i8Psi4s52N4 x) / x ^ 2 + i8Psi4s52W x

/-- The derivative of `Ψ₄⁽52⁾`. -/
noncomputable def i8Psi4s52D (x : ℝ) : ℝ :=
  ((i8Psi4s52dN0 x + (i8Psi4s52N1 x + x * i8Psi4s52dN1 x) + (2 * x * i8Psi4s52N2 x +
    x ^ 2 * i8Psi4s52dN2 x) + (3 * x ^ 2 * i8Psi4s52N3 x + x ^ 3 * i8Psi4s52dN3 x) +
    (4 * x ^ 3 * i8Psi4s52N4 x + x ^ 4 * i8Psi4s52dN4 x)) * x ^ 2 - (i8Psi4s52N0 x +
    x * i8Psi4s52N1 x + x ^ 2 * i8Psi4s52N2 x + x ^ 3 * i8Psi4s52N3 x +
    x ^ 4 * i8Psi4s52N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s52dW x

theorem hasDerivAt_i8Psi4s52 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s52 (i8Psi4s52D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s52N0 hx).add (X.mul (hasDerivAt_i8Psi4s52N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s52N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s52N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s52N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s52W hx)
  unfold i8Psi4s52
  refine e.congr_deriv ?_
  unfold i8Psi4s52D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 52 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s52 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 - x) * (-2 * hpl [negOne] x))

/-- **`(Ψ₄⁽52⁾)'(ξ) ξ' = p₄⁽52⁾`**, in terms of `ξ`. -/
theorem i8Psi4s52D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s52D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s52 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s52D i8Psi4s52N0 i8Psi4s52N1 i8Psi4s52N2 i8Psi4s52N3 i8Psi4s52N4 i8Psi4s52dN0
    i8Psi4s52dN1 i8Psi4s52dN2 i8Psi4s52dN3 i8Psi4s52dN4 i8Psi4s52dW i8P4s52
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽53⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s53N0 (x : ℝ) : ℝ :=
    (1 / 2) * hpl [negOne, negOne] x +
    (1) * hpl [negOne, negOne, zero] x +
    (1) * hpl [negOne, zero, negOne] x +
    (1) * hpl [zero, negOne, negOne] x

/-- The derivative of `i8Psi4s53N0`. -/
noncomputable def i8Psi4s53dN0 (x : ℝ) : ℝ :=
    (1 / 2) * (negOne.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [negOne, zero] x) +
    (1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s53N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s53N0 (i8Psi4s53dN0 x) x := by
  unfold i8Psi4s53N0 i8Psi4s53dN0
  exact (((((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽53⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s53N1 (x : ℝ) : ℝ :=
    (3 / 2) * hpl [negOne] x +
    (1) * hpl [negOne, zero] x +
    (1) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s53N1`. -/
noncomputable def i8Psi4s53dN1 (x : ℝ) : ℝ :=
    (3 / 2) * (negOne.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s53N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s53N1 (i8Psi4s53dN1 x) x := by
  unfold i8Psi4s53N1 i8Psi4s53dN1
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽53⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s53N2 (x : ℝ) : ℝ :=
    (7 / 2) * hpl [negOne] x +
    (-3 / 2) * hpl [zero] x +
    (-1) * hpl [negOne, negOne] x +
    (-1 / 2) * hpl [negOne, zero] x +
    (1 / 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s53N2`. -/
noncomputable def i8Psi4s53dN2 (x : ℝ) : ℝ :=
    (7 / 2) * (negOne.kernel x * hpl [] x) +
    (-3 / 2) * (zero.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [negOne] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s53N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s53N2 (i8Psi4s53dN2 x) x := by
  unfold i8Psi4s53N2 i8Psi4s53dN2
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (7 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽53⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s53N3 (x : ℝ) : ℝ :=
    (-7 / 2) +
    (3 / 2) * hpl [negOne] x +
    (3 / 2) * hpl [zero] x +
    (-1) * hpl [negOne, zero] x +
    (-1) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s53N3`. -/
noncomputable def i8Psi4s53dN3 (x : ℝ) : ℝ :=
    0 +
    (3 / 2) * (negOne.kernel x * hpl [] x) +
    (3 / 2) * (zero.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s53N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s53N3 (i8Psi4s53dN3 x) x := by
  unfold i8Psi4s53N3 i8Psi4s53dN3
  exact (((((hasDerivAt_const x (-7 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽53⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s53N4 (x : ℝ) : ℝ :=
    (3 / 8) +
    (-1 / 2) * hpl [negOne] x +
    (-1 / 4) * hpl [zero] x +
    (1 / 2) * hpl [negOne, negOne] x +
    (1 / 2) * hpl [negOne, zero] x +
    (1 / 2) * hpl [zero, negOne] x +
    (-1) * hpl [negOne, negOne, zero] x +
    (-1) * hpl [negOne, zero, negOne] x +
    (-1) * hpl [zero, negOne, negOne] x

/-- The derivative of `i8Psi4s53N4`. -/
noncomputable def i8Psi4s53dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [negOne] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s53N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s53N4 (i8Psi4s53dN4 x) x := by
  unfold i8Psi4s53N4 i8Psi4s53dN4
  exact (((((((((hasDerivAt_const x (3 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-1)))

/-- The part of `Ψ₄⁽53⁾` with constant coefficients. -/
noncomputable def i8Psi4s53W (x : ℝ) : ℝ :=
    (-1) * hpl [zero, zero] x +
    (1) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, negOne] x +
    (4) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s53W`. -/
noncomputable def i8Psi4s53dW (x : ℝ) : ℝ :=
    (-1) * (zero.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s53W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s53W (i8Psi4s53dW x) x := by
  unfold i8Psi4s53W i8Psi4s53dW
  exact (((((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (4)))

/-- The piece `Ψ₄⁽53⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s53 (x : ℝ) : ℝ :=
  (i8Psi4s53N0 x + x * i8Psi4s53N1 x + x ^ 2 * i8Psi4s53N2 x + x ^ 3 * i8Psi4s53N3 x +
    x ^ 4 * i8Psi4s53N4 x) / x ^ 2 + i8Psi4s53W x

/-- The derivative of `Ψ₄⁽53⁾`. -/
noncomputable def i8Psi4s53D (x : ℝ) : ℝ :=
  ((i8Psi4s53dN0 x + (i8Psi4s53N1 x + x * i8Psi4s53dN1 x) + (2 * x * i8Psi4s53N2 x +
    x ^ 2 * i8Psi4s53dN2 x) + (3 * x ^ 2 * i8Psi4s53N3 x + x ^ 3 * i8Psi4s53dN3 x) +
    (4 * x ^ 3 * i8Psi4s53N4 x + x ^ 4 * i8Psi4s53dN4 x)) * x ^ 2 - (i8Psi4s53N0 x +
    x * i8Psi4s53N1 x + x ^ 2 * i8Psi4s53N2 x + x ^ 3 * i8Psi4s53N3 x +
    x ^ 4 * i8Psi4s53N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s53dW x

theorem hasDerivAt_i8Psi4s53 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s53 (i8Psi4s53D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s53N0 hx).add (X.mul (hasDerivAt_i8Psi4s53N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s53N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s53N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s53N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s53W hx)
  unfold i8Psi4s53
  refine e.congr_deriv ?_
  unfold i8Psi4s53D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 53 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s53 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 - x) * (2 * hpl [negOne, negOne] x))

/-- **`(Ψ₄⁽53⁾)'(ξ) ξ' = p₄⁽53⁾`**, in terms of `ξ`. -/
theorem i8Psi4s53D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s53D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s53 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s53D i8Psi4s53N0 i8Psi4s53N1 i8Psi4s53N2 i8Psi4s53N3 i8Psi4s53N4 i8Psi4s53dN0
    i8Psi4s53dN1 i8Psi4s53dN2 i8Psi4s53dN3 i8Psi4s53dN4 i8Psi4s53dW i8P4s53
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_mm hx, i13hw_m0m hx,
    i13hw_mm0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽54⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s54N0 (x : ℝ) : ℝ :=
    (-1 / 4) * hpl [negOne] x +
    (-1 / 4) * hpl [negOne, zero] x +
    (-1 / 2) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [zero, negOne, zero] x +
    (-1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s54N0`. -/
noncomputable def i8Psi4s54dN0 (x : ℝ) : ℝ :=
    (-1 / 4) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s54N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s54N0 (i8Psi4s54dN0 x) x := by
  unfold i8Psi4s54N0 i8Psi4s54dN0
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 4)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽54⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s54N1 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (-1 / 4) * hpl [zero] x

/-- The derivative of `i8Psi4s54N1`. -/
noncomputable def i8Psi4s54dN1 (x : ℝ) : ℝ :=
    0 +
    (-1 / 4) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s54N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s54N1 (i8Psi4s54dN1 x) x := by
  unfold i8Psi4s54N1 i8Psi4s54dN1
  exact ((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4)))

/-- The part of `ξ² Ψ₄⁽54⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s54N2 (x : ℝ) : ℝ :=
    (-1 / 4) * hpl [zero] x +
    (1 / 2) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s54N2`. -/
noncomputable def i8Psi4s54dN2 (x : ℝ) : ℝ :=
    (-1 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s54N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s54N2 (i8Psi4s54dN2 x) x := by
  unfold i8Psi4s54N2 i8Psi4s54dN2
  exact (((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽54⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s54N3 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 4) * hpl [zero] x

/-- The derivative of `i8Psi4s54N3`. -/
noncomputable def i8Psi4s54dN3 (x : ℝ) : ℝ :=
    0 +
    (-1 / 4) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s54N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s54N3 (i8Psi4s54dN3 x) x := by
  unfold i8Psi4s54N3 i8Psi4s54dN3
  exact ((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4)))

/-- The part of `ξ² Ψ₄⁽54⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s54N4 (x : ℝ) : ℝ :=
    (-3 / 16) +
    (1 / 4) * hpl [negOne] x +
    (1 / 8) * hpl [zero] x +
    (-1 / 4) * hpl [negOne, zero] x +
    (-1 / 2) * hpl [zero, negOne] x +
    (1 / 2) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s54N4`. -/
noncomputable def i8Psi4s54dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 4) * (negOne.kernel x * hpl [] x) +
    (1 / 8) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s54N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s54N4 (i8Psi4s54dN4 x) x := by
  unfold i8Psi4s54N4 i8Psi4s54dN4
  exact (((((((hasDerivAt_const x (-3 / 16)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1)))

/-- The part of `Ψ₄⁽54⁾` with constant coefficients. -/
noncomputable def i8Psi4s54W (x : ℝ) : ℝ :=
    (-1 / 4) * hpl [zero, zero] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-4) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s54W`. -/
noncomputable def i8Psi4s54dW (x : ℝ) : ℝ :=
    (-1 / 4) * (zero.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s54W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s54W (i8Psi4s54dW x) x := by
  unfold i8Psi4s54W i8Psi4s54dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 4)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-4)))

/-- The piece `Ψ₄⁽54⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s54 (x : ℝ) : ℝ :=
  (i8Psi4s54N0 x + x * i8Psi4s54N1 x + x ^ 2 * i8Psi4s54N2 x + x ^ 3 * i8Psi4s54N3 x +
    x ^ 4 * i8Psi4s54N4 x) / x ^ 2 + i8Psi4s54W x

/-- The derivative of `Ψ₄⁽54⁾`. -/
noncomputable def i8Psi4s54D (x : ℝ) : ℝ :=
  ((i8Psi4s54dN0 x + (i8Psi4s54N1 x + x * i8Psi4s54dN1 x) + (2 * x * i8Psi4s54N2 x +
    x ^ 2 * i8Psi4s54dN2 x) + (3 * x ^ 2 * i8Psi4s54N3 x + x ^ 3 * i8Psi4s54dN3 x) +
    (4 * x ^ 3 * i8Psi4s54N4 x + x ^ 4 * i8Psi4s54dN4 x)) * x ^ 2 - (i8Psi4s54N0 x +
    x * i8Psi4s54N1 x + x ^ 2 * i8Psi4s54N2 x + x ^ 3 * i8Psi4s54N3 x +
    x ^ 4 * i8Psi4s54N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s54dW x

theorem hasDerivAt_i8Psi4s54 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s54 (i8Psi4s54D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s54N0 hx).add (X.mul (hasDerivAt_i8Psi4s54N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s54N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s54N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s54N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s54W hx)
  unfold i8Psi4s54
  refine e.congr_deriv ?_
  unfold i8Psi4s54D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 54 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s54 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 - x) * (-hpl [zero, negOne] x))

/-- **`(Ψ₄⁽54⁾)'(ξ) ξ' = p₄⁽54⁾`**, in terms of `ξ`. -/
theorem i8Psi4s54D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s54D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s54 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s54D i8Psi4s54N0 i8Psi4s54N1 i8Psi4s54N2 i8Psi4s54N3 i8Psi4s54N4 i8Psi4s54dN0
    i8Psi4s54dN1 i8Psi4s54dN2 i8Psi4s54dN3 i8Psi4s54dN4 i8Psi4s54dW i8P4s54
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_0m0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽55⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s55N0 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne, negOne, negOne] x +
    (-2) * hpl [negOne, negOne, negOne, zero] x +
    (-2) * hpl [negOne, negOne, zero, negOne] x +
    (-2) * hpl [negOne, zero, negOne, negOne] x +
    (-2) * hpl [zero, negOne, negOne, negOne] x

/-- The derivative of `i8Psi4s55N0`. -/
noncomputable def i8Psi4s55dN0 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-2) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s55N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s55N0 (i8Psi4s55dN0 x) x := by
  unfold i8Psi4s55N0 i8Psi4s55dN0
  exact ((((((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽55⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s55N1 (x : ℝ) : ℝ :=
    (-3) * hpl [negOne, negOne] x +
    (-2) * hpl [negOne, negOne, zero] x +
    (-2) * hpl [negOne, zero, negOne] x +
    (-2) * hpl [zero, negOne, negOne] x

/-- The derivative of `i8Psi4s55N1`. -/
noncomputable def i8Psi4s55dN1 (x : ℝ) : ℝ :=
    (-3) * (negOne.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s55N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s55N1 (i8Psi4s55dN1 x) x := by
  unfold i8Psi4s55N1 i8Psi4s55dN1
  exact (((((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-3)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽55⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s55N2 (x : ℝ) : ℝ :=
    (31 / 4) * hpl [negOne] x +
    (-7) * hpl [negOne, negOne] x +
    (-7 / 2) * hpl [negOne, zero] x +
    (3) * hpl [zero, negOne] x +
    (2) * hpl [negOne, negOne, negOne] x +
    (1) * hpl [negOne, negOne, zero] x +
    (1) * hpl [negOne, zero, negOne] x +
    (-1) * hpl [zero, negOne, negOne] x

/-- The derivative of `i8Psi4s55N2`. -/
noncomputable def i8Psi4s55dN2 (x : ℝ) : ℝ :=
    (31 / 4) * (negOne.kernel x * hpl [] x) +
    (-7) * (negOne.kernel x * hpl [negOne] x) +
    (-7 / 2) * (negOne.kernel x * hpl [zero] x) +
    (3) * (zero.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (1) * (negOne.kernel x * hpl [negOne, zero] x) +
    (1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s55N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s55N2 (i8Psi4s55dN2 x) x := by
  unfold i8Psi4s55N2 i8Psi4s55dN2
  exact (((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (31 / 4)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽55⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s55N3 (x : ℝ) : ℝ :=
    (-45 / 4) +
    (7) * hpl [negOne] x +
    (7 / 2) * hpl [zero] x +
    (-3) * hpl [negOne, negOne] x +
    (-3) * hpl [negOne, zero] x +
    (-3) * hpl [zero, negOne] x +
    (2) * hpl [negOne, negOne, zero] x +
    (2) * hpl [negOne, zero, negOne] x +
    (2) * hpl [zero, negOne, negOne] x

/-- The derivative of `i8Psi4s55N3`. -/
noncomputable def i8Psi4s55dN3 (x : ℝ) : ℝ :=
    0 +
    (7) * (negOne.kernel x * hpl [] x) +
    (7 / 2) * (zero.kernel x * hpl [] x) +
    (-3) * (negOne.kernel x * hpl [negOne] x) +
    (-3) * (negOne.kernel x * hpl [zero] x) +
    (-3) * (zero.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s55N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s55N3 (i8Psi4s55dN3 x) x := by
  unfold i8Psi4s55N3 i8Psi4s55dN3
  exact (((((((((hasDerivAt_const x (-45 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽55⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s55N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-3 / 4) * hpl [negOne] x +
    (-1 / 4) * hpl [zero] x +
    (1) * hpl [negOne, negOne] x +
    (1 / 2) * hpl [negOne, zero] x +
    (1 / 2) * hpl [zero, negOne] x +
    (-1) * hpl [negOne, negOne, negOne] x +
    (-1) * hpl [negOne, negOne, zero] x +
    (-1) * hpl [negOne, zero, negOne] x +
    (-1) * hpl [zero, negOne, negOne] x +
    (2) * hpl [negOne, negOne, negOne, zero] x +
    (2) * hpl [negOne, negOne, zero, negOne] x +
    (2) * hpl [negOne, zero, negOne, negOne] x +
    (2) * hpl [zero, negOne, negOne, negOne] x

/-- The derivative of `i8Psi4s55N4`. -/
noncomputable def i8Psi4s55dN4 (x : ℝ) : ℝ :=
    0 +
    (-3 / 4) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [negOne] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (-1) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s55N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s55N4 (i8Psi4s55dN4 x) x := by
  unfold i8Psi4s55N4 i8Psi4s55dN4
  exact ((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (2)))

/-- The part of `Ψ₄⁽55⁾` with constant coefficients. -/
noncomputable def i8Psi4s55W (x : ℝ) : ℝ :=
    (2) * hpl [zero, negOne, zero] x +
    (2) * hpl [zero, zero, negOne] x +
    (-2) * hpl [zero, negOne, negOne, zero] x +
    (-2) * hpl [zero, negOne, zero, negOne] x +
    (-2) * hpl [zero, zero, negOne, negOne] x +
    (-8) * hpl [zero, negOne, negOne, negOne, zero] x +
    (-8) * hpl [zero, negOne, negOne, zero, negOne] x +
    (-8) * hpl [zero, negOne, zero, negOne, negOne] x +
    (-8) * hpl [zero, zero, negOne, negOne, negOne] x

/-- The derivative of `i8Psi4s55W`. -/
noncomputable def i8Psi4s55dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (-8) * (zero.kernel x * hpl [negOne, negOne, negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, negOne, zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, negOne, negOne] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s55W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s55W (i8Psi4s55dW x) x := by
  unfold i8Psi4s55W i8Psi4s55dW
  exact ((((((((((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne, negOne] hx).const_mul (-8)))

/-- The piece `Ψ₄⁽55⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s55 (x : ℝ) : ℝ :=
  (i8Psi4s55N0 x + x * i8Psi4s55N1 x + x ^ 2 * i8Psi4s55N2 x + x ^ 3 * i8Psi4s55N3 x +
    x ^ 4 * i8Psi4s55N4 x) / x ^ 2 + i8Psi4s55W x

/-- The derivative of `Ψ₄⁽55⁾`. -/
noncomputable def i8Psi4s55D (x : ℝ) : ℝ :=
  ((i8Psi4s55dN0 x + (i8Psi4s55N1 x + x * i8Psi4s55dN1 x) + (2 * x * i8Psi4s55N2 x +
    x ^ 2 * i8Psi4s55dN2 x) + (3 * x ^ 2 * i8Psi4s55N3 x + x ^ 3 * i8Psi4s55dN3 x) +
    (4 * x ^ 3 * i8Psi4s55N4 x + x ^ 4 * i8Psi4s55dN4 x)) * x ^ 2 - (i8Psi4s55N0 x +
    x * i8Psi4s55N1 x + x ^ 2 * i8Psi4s55N2 x + x ^ 3 * i8Psi4s55N3 x +
    x ^ 4 * i8Psi4s55N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s55dW x

theorem hasDerivAt_i8Psi4s55 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s55 (i8Psi4s55D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s55N0 hx).add (X.mul (hasDerivAt_i8Psi4s55N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s55N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s55N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s55N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s55W hx)
  unfold i8Psi4s55
  refine e.congr_deriv ?_
  unfold i8Psi4s55D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 55 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s55 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 - x) * (-4 * hpl [negOne, negOne, negOne] x))

/-- **`(Ψ₄⁽55⁾)'(ξ) ξ' = p₄⁽55⁾`**, in terms of `ξ`. -/
theorem i8Psi4s55D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s55D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s55 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s55D i8Psi4s55N0 i8Psi4s55N1 i8Psi4s55N2 i8Psi4s55N3 i8Psi4s55N4 i8Psi4s55dN0
    i8Psi4s55dN1 i8Psi4s55dN2 i8Psi4s55dN3 i8Psi4s55dN4 i8Psi4s55dW i8P4s55
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_mm hx, i13hw_m0m hx,
    i13hw_mm0 hx, i13hw_mmm hx, i8hw_mm0m hx, i13hw_m0mm hx, i13hw_mmm0 hx]
  field_simp
  ring

end QED.ThreeLoopD
