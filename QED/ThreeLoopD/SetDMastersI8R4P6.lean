/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P5

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 27 to 34

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s27`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s27D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s27`, `QED.ThreeLoopD.i8Psi4s27D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽27⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s27N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s27N0`. -/
noncomputable def i8Psi4s27dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s27N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s27N0 (i8Psi4s27dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽27⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s27N1 (x : ℝ) : ℝ :=
    (-4 / 3 * π ^ 2) * hpl [negOne, negOne] x

/-- The derivative of `i8Psi4s27N1`. -/
noncomputable def i8Psi4s27dN1 (x : ℝ) : ℝ :=
    (-4 / 3 * π ^ 2) * (negOne.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s27N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s27N1 (i8Psi4s27dN1 x) x := by
  unfold i8Psi4s27N1 i8Psi4s27dN1
  exact ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-4 / 3 * π ^ 2))

/-- The part of `ξ² Ψ₄⁽27⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s27N2 (x : ℝ) : ℝ :=
    (π ^ 2 / 3) * hpl [negOne] x +
    (-2 * π ^ 2) * hpl [negOne, negOne] x

/-- The derivative of `i8Psi4s27N2`. -/
noncomputable def i8Psi4s27dN2 (x : ℝ) : ℝ :=
    (π ^ 2 / 3) * (negOne.kernel x * hpl [] x) +
    (-2 * π ^ 2) * (negOne.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s27N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s27N2 (i8Psi4s27dN2 x) x := by
  unfold i8Psi4s27N2 i8Psi4s27dN2
  exact (((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-2 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽27⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s27N3 (x : ℝ) : ℝ :=
    (-π ^ 2 / 3) +
    (2 / 3 * π ^ 2) * hpl [negOne] x +
    (-4 / 3 * π ^ 2) * hpl [negOne, negOne] x

/-- The derivative of `i8Psi4s27N3`. -/
noncomputable def i8Psi4s27dN3 (x : ℝ) : ℝ :=
    0 +
    (2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-4 / 3 * π ^ 2) * (negOne.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s27N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s27N3 (i8Psi4s27dN3 x) x := by
  unfold i8Psi4s27N3 i8Psi4s27dN3
  exact (((hasDerivAt_const x (-π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-4 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽27⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s27N4 (x : ℝ) : ℝ :=
    (-π ^ 2 / 6) +
    (π ^ 2 / 3) * hpl [negOne] x +
    (-2 / 3 * π ^ 2) * hpl [negOne, negOne] x

/-- The derivative of `i8Psi4s27N4`. -/
noncomputable def i8Psi4s27dN4 (x : ℝ) : ℝ :=
    0 +
    (π ^ 2 / 3) * (negOne.kernel x * hpl [] x) +
    (-2 / 3 * π ^ 2) * (negOne.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s27N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s27N4 (i8Psi4s27dN4 x) x := by
  unfold i8Psi4s27N4 i8Psi4s27dN4
  exact (((hasDerivAt_const x (-π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-2 / 3 * π ^ 2)))

/-- The part of `Ψ₄⁽27⁾` with constant coefficients. -/
noncomputable def i8Psi4s27W (x : ℝ) : ℝ :=
    (4 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (4 / 3 * π ^ 2) * hpl [zero, negOne, negOne] x

/-- The derivative of `i8Psi4s27W`. -/
noncomputable def i8Psi4s27dW (x : ℝ) : ℝ :=
    (4 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (4 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s27W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s27W (i8Psi4s27dW x) x := by
  unfold i8Psi4s27W i8Psi4s27dW
  exact (((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (4 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (4 / 3 * π ^ 2)))

/-- The piece `Ψ₄⁽27⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s27 (x : ℝ) : ℝ :=
  (i8Psi4s27N0 x + x * i8Psi4s27N1 x + x ^ 2 * i8Psi4s27N2 x + x ^ 3 * i8Psi4s27N3 x +
    x ^ 4 * i8Psi4s27N4 x) / x ^ 2 + i8Psi4s27W x

/-- The derivative of `Ψ₄⁽27⁾`. -/
noncomputable def i8Psi4s27D (x : ℝ) : ℝ :=
  ((i8Psi4s27dN0 x + (i8Psi4s27N1 x + x * i8Psi4s27dN1 x) + (2 * x * i8Psi4s27N2 x +
    x ^ 2 * i8Psi4s27dN2 x) + (3 * x ^ 2 * i8Psi4s27N3 x + x ^ 3 * i8Psi4s27dN3 x) +
    (4 * x ^ 3 * i8Psi4s27N4 x + x ^ 4 * i8Psi4s27dN4 x)) * x ^ 2 - (i8Psi4s27N0 x +
    x * i8Psi4s27N1 x + x ^ 2 * i8Psi4s27N2 x + x ^ 3 * i8Psi4s27N3 x +
    x ^ 4 * i8Psi4s27N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s27dW x

theorem hasDerivAt_i8Psi4s27 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s27 (i8Psi4s27D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s27N0 hx).add (X.mul (hasDerivAt_i8Psi4s27N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s27N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s27N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s27N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s27W hx)
  unfold i8Psi4s27
  refine e.congr_deriv ?_
  unfold i8Psi4s27D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 27 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s27 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((((-2) * π ^ 2) / 3) * hpl [negOne, negOne] x)) * (x /
    (1 - x))

/-- **`(Ψ₄⁽27⁾)'(ξ) ξ' = p₄⁽27⁾`**, in terms of `ξ`. -/
theorem i8Psi4s27D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s27D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s27 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s27D i8Psi4s27N0 i8Psi4s27N1 i8Psi4s27N2 i8Psi4s27N3 i8Psi4s27N4 i8Psi4s27dN0
    i8Psi4s27dN1 i8Psi4s27dN2 i8Psi4s27dN3 i8Psi4s27dN4 i8Psi4s27dW i8P4s27
  simp only [kernel_zero, kernel_negOne, hpl_nil, i13hw_mm hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽28⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s28N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s28N0`. -/
noncomputable def i8Psi4s28dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s28N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s28N0 (i8Psi4s28dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽28⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s28N1 (x : ℝ) : ℝ :=
    (2 / 3 * π ^ 2) * hpl [negOne] x +
    (2 / 3 * π ^ 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s28N1`. -/
noncomputable def i8Psi4s28dN1 (x : ℝ) : ℝ :=
    (2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s28N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s28N1 (i8Psi4s28dN1 x) x := by
  unfold i8Psi4s28N1 i8Psi4s28dN1
  exact (((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽28⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s28N2 (x : ℝ) : ℝ :=
    (π ^ 2 / 6) * hpl [negOne] x

/-- The derivative of `i8Psi4s28N2`. -/
noncomputable def i8Psi4s28dN2 (x : ℝ) : ℝ :=
    (π ^ 2 / 6) * (negOne.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s28N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s28N2 (i8Psi4s28dN2 x) x := by
  unfold i8Psi4s28N2 i8Psi4s28dN2
  exact ((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2 / 6))

/-- The part of `ξ² Ψ₄⁽28⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s28N3 (x : ℝ) : ℝ :=
    (π ^ 2 / 2) +
    (-2 / 3 * π ^ 2) * hpl [negOne] x +
    (2 / 3 * π ^ 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s28N3`. -/
noncomputable def i8Psi4s28dN3 (x : ℝ) : ℝ :=
    0 +
    (-2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s28N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s28N3 (i8Psi4s28dN3 x) x := by
  unfold i8Psi4s28N3 i8Psi4s28dN3
  exact (((hasDerivAt_const x (π ^ 2 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽28⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s28N4 (x : ℝ) : ℝ :=
    (π ^ 2 / 12) +
    (-π ^ 2 / 6) * hpl [negOne] x +
    (π ^ 2 / 3) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s28N4`. -/
noncomputable def i8Psi4s28dN4 (x : ℝ) : ℝ :=
    0 +
    (-π ^ 2 / 6) * (negOne.kernel x * hpl [] x) +
    (π ^ 2 / 3) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s28N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s28N4 (i8Psi4s28dN4 x) x := by
  unfold i8Psi4s28N4 i8Psi4s28dN4
  exact (((hasDerivAt_const x (π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (π ^ 2 / 3)))

/-- The part of `Ψ₄⁽28⁾` with constant coefficients. -/
noncomputable def i8Psi4s28W (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * hpl [zero] x +
    (-2 / 3 * π ^ 2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s28W`. -/
noncomputable def i8Psi4s28dW (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s28W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s28W (i8Psi4s28dW x) x := by
  unfold i8Psi4s28W i8Psi4s28dW
  exact (((hasDerivAt_hpl_cons zero [] hx).const_mul (-2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2 / 3 * π ^ 2)))

/-- The piece `Ψ₄⁽28⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s28 (x : ℝ) : ℝ :=
  (i8Psi4s28N0 x + x * i8Psi4s28N1 x + x ^ 2 * i8Psi4s28N2 x + x ^ 3 * i8Psi4s28N3 x +
    x ^ 4 * i8Psi4s28N4 x) / x ^ 2 + i8Psi4s28W x

/-- The derivative of `Ψ₄⁽28⁾`. -/
noncomputable def i8Psi4s28D (x : ℝ) : ℝ :=
  ((i8Psi4s28dN0 x + (i8Psi4s28N1 x + x * i8Psi4s28dN1 x) + (2 * x * i8Psi4s28N2 x +
    x ^ 2 * i8Psi4s28dN2 x) + (3 * x ^ 2 * i8Psi4s28N3 x + x ^ 3 * i8Psi4s28dN3 x) +
    (4 * x ^ 3 * i8Psi4s28N4 x + x ^ 4 * i8Psi4s28dN4 x)) * x ^ 2 - (i8Psi4s28N0 x +
    x * i8Psi4s28N1 x + x ^ 2 * i8Psi4s28N2 x + x ^ 3 * i8Psi4s28N3 x +
    x ^ 4 * i8Psi4s28N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s28dW x

theorem hasDerivAt_i8Psi4s28 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s28 (i8Psi4s28D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s28N0 hx).add (X.mul (hasDerivAt_i8Psi4s28N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s28N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s28N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s28N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s28W hx)
  unfold i8Psi4s28
  refine e.congr_deriv ?_
  unfold i8Psi4s28D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 28 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s28 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((π ^ 2 / 3) * hpl [zero, negOne] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽28⁾)'(ξ) ξ' = p₄⁽28⁾`**, in terms of `ξ`. -/
theorem i8Psi4s28D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s28D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s28 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s28D i8Psi4s28N0 i8Psi4s28N1 i8Psi4s28N2 i8Psi4s28N3 i8Psi4s28N4 i8Psi4s28dN0
    i8Psi4s28dN1 i8Psi4s28dN2 i8Psi4s28dN3 i8Psi4s28dN4 i8Psi4s28dW i8P4s28
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽29⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s29N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s29N0`. -/
noncomputable def i8Psi4s29dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s29N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s29N0 (i8Psi4s29dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽29⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s29N1 (x : ℝ) : ℝ :=
    (-4) * hpl [negOne, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s29N1`. -/
noncomputable def i8Psi4s29dN1 (x : ℝ) : ℝ :=
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s29N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s29N1 (i8Psi4s29dN1 x) x := by
  unfold i8Psi4s29N1 i8Psi4s29dN1
  exact ((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽29⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s29N2 (x : ℝ) : ℝ :=
    (-15 / 2) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s29N2`. -/
noncomputable def i8Psi4s29dN2 (x : ℝ) : ℝ :=
    (-15 / 2) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s29N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s29N2 (i8Psi4s29dN2 x) x := by
  unfold i8Psi4s29N2 i8Psi4s29dN2
  exact ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-15 / 2))

/-- The part of `ξ² Ψ₄⁽29⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s29N3 (x : ℝ) : ℝ :=
    (-7 / 2) +
    (7 / 2) * hpl [zero] x +
    (-4) * hpl [negOne, zero] x +
    (4) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s29N3`. -/
noncomputable def i8Psi4s29dN3 (x : ℝ) : ℝ :=
    0 +
    (7 / 2) * (zero.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s29N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s29N3 (i8Psi4s29dN3 x) x := by
  unfold i8Psi4s29N3 i8Psi4s29dN3
  exact (((((hasDerivAt_const x (-7 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽29⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s29N4 (x : ℝ) : ℝ :=
    (-1 / 8) +
    (1 / 4) * hpl [zero] x +
    (-1 / 2) * hpl [negOne, zero] x +
    (1) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s29N4`. -/
noncomputable def i8Psi4s29dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 4) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s29N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s29N4 (i8Psi4s29dN4 x) x := by
  unfold i8Psi4s29N4 i8Psi4s29dN4
  exact (((((hasDerivAt_const x (-1 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽29⁾` with constant coefficients. -/
noncomputable def i8Psi4s29W (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero] x +
    (4) * hpl [zero, zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s29W`. -/
noncomputable def i8Psi4s29dW (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero, zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s29W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s29W (i8Psi4s29dW x) x := by
  unfold i8Psi4s29W i8Psi4s29dW
  exact (((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (4)))

/-- The piece `Ψ₄⁽29⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s29 (x : ℝ) : ℝ :=
  (i8Psi4s29N0 x + x * i8Psi4s29N1 x + x ^ 2 * i8Psi4s29N2 x + x ^ 3 * i8Psi4s29N3 x +
    x ^ 4 * i8Psi4s29N4 x) / x ^ 2 + i8Psi4s29W x

/-- The derivative of `Ψ₄⁽29⁾`. -/
noncomputable def i8Psi4s29D (x : ℝ) : ℝ :=
  ((i8Psi4s29dN0 x + (i8Psi4s29N1 x + x * i8Psi4s29dN1 x) + (2 * x * i8Psi4s29N2 x +
    x ^ 2 * i8Psi4s29dN2 x) + (3 * x ^ 2 * i8Psi4s29N3 x + x ^ 3 * i8Psi4s29dN3 x) +
    (4 * x ^ 3 * i8Psi4s29N4 x + x ^ 4 * i8Psi4s29dN4 x)) * x ^ 2 - (i8Psi4s29N0 x +
    x * i8Psi4s29N1 x + x ^ 2 * i8Psi4s29N2 x + x ^ 3 * i8Psi4s29N3 x +
    x ^ 4 * i8Psi4s29N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s29dW x

theorem hasDerivAt_i8Psi4s29 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s29 (i8Psi4s29D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s29N0 hx).add (X.mul (hasDerivAt_i8Psi4s29N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s29N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s29N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s29N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s29W hx)
  unfold i8Psi4s29
  refine e.congr_deriv ?_
  unfold i8Psi4s29D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 29 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s29 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((-2) * hpl [zero, zero, negOne, zero] x)) * (x / (1 -
    x))

/-- **`(Ψ₄⁽29⁾)'(ξ) ξ' = p₄⁽29⁾`**, in terms of `ξ`. -/
theorem i8Psi4s29D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s29D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s29 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s29D i8Psi4s29N0 i8Psi4s29N1 i8Psi4s29N2 i8Psi4s29N3 i8Psi4s29N4 i8Psi4s29dN0
    i8Psi4s29dN1 i8Psi4s29dN2 i8Psi4s29dN3 i8Psi4s29dN4 i8Psi4s29dW i8P4s29
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_0m0 hx, i13hw_00m0
    hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽30⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s30N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s30N0`. -/
noncomputable def i8Psi4s30dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s30N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s30N0 (i8Psi4s30dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽30⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s30N1 (x : ℝ) : ℝ :=
    (8) * hpl [negOne, zero, negOne, zero] x

/-- The derivative of `i8Psi4s30N1`. -/
noncomputable def i8Psi4s30dN1 (x : ℝ) : ℝ :=
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s30N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s30N1 (i8Psi4s30dN1 x) x := by
  unfold i8Psi4s30N1 i8Psi4s30dN1
  exact ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))

/-- The part of `ξ² Ψ₄⁽30⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s30N2 (x : ℝ) : ℝ :=
    (3) * hpl [negOne, zero] x +
    (12) * hpl [negOne, zero, negOne, zero] x

/-- The derivative of `i8Psi4s30N2`. -/
noncomputable def i8Psi4s30dN2 (x : ℝ) : ℝ :=
    (3) * (negOne.kernel x * hpl [zero] x) +
    (12) * (negOne.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s30N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s30N2 (i8Psi4s30dN2 x) x := by
  unfold i8Psi4s30N2 i8Psi4s30dN2
  exact (((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (3)).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽30⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s30N3 (x : ℝ) : ℝ :=
    (3) +
    (-3) * hpl [zero] x +
    (4) * hpl [negOne, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (8) * hpl [negOne, zero, negOne, zero] x

/-- The derivative of `i8Psi4s30N3`. -/
noncomputable def i8Psi4s30dN3 (x : ℝ) : ℝ :=
    0 +
    (-3) * (zero.kernel x * hpl [] x) +
    (4) * (negOne.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s30N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s30N3 (i8Psi4s30dN3 x) x := by
  unfold i8Psi4s30N3 i8Psi4s30dN3
  exact (((((hasDerivAt_const x (3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽30⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s30N4 (x : ℝ) : ℝ :=
    (1 / 4) +
    (-1 / 2) * hpl [zero] x +
    (1) * hpl [negOne, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (4) * hpl [negOne, zero, negOne, zero] x

/-- The derivative of `i8Psi4s30N4`. -/
noncomputable def i8Psi4s30dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s30N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s30N4 (i8Psi4s30dN4 x) x := by
  unfold i8Psi4s30N4 i8Psi4s30dN4
  exact (((((hasDerivAt_const x (1 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽30⁾` with constant coefficients. -/
noncomputable def i8Psi4s30W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, negOne, zero] x +
    (-8) * hpl [zero, negOne, zero, negOne, zero] x

/-- The derivative of `i8Psi4s30W`. -/
noncomputable def i8Psi4s30dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s30W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s30W (i8Psi4s30dW x) x := by
  unfold i8Psi4s30W i8Psi4s30dW
  exact (((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, zero] hx).const_mul (-8)))

/-- The piece `Ψ₄⁽30⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s30 (x : ℝ) : ℝ :=
  (i8Psi4s30N0 x + x * i8Psi4s30N1 x + x ^ 2 * i8Psi4s30N2 x + x ^ 3 * i8Psi4s30N3 x +
    x ^ 4 * i8Psi4s30N4 x) / x ^ 2 + i8Psi4s30W x

/-- The derivative of `Ψ₄⁽30⁾`. -/
noncomputable def i8Psi4s30D (x : ℝ) : ℝ :=
  ((i8Psi4s30dN0 x + (i8Psi4s30N1 x + x * i8Psi4s30dN1 x) + (2 * x * i8Psi4s30N2 x +
    x ^ 2 * i8Psi4s30dN2 x) + (3 * x ^ 2 * i8Psi4s30N3 x + x ^ 3 * i8Psi4s30dN3 x) +
    (4 * x ^ 3 * i8Psi4s30N4 x + x ^ 4 * i8Psi4s30dN4 x)) * x ^ 2 - (i8Psi4s30N0 x +
    x * i8Psi4s30N1 x + x ^ 2 * i8Psi4s30N2 x + x ^ 3 * i8Psi4s30N3 x +
    x ^ 4 * i8Psi4s30N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s30dW x

theorem hasDerivAt_i8Psi4s30 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s30 (i8Psi4s30D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s30N0 hx).add (X.mul (hasDerivAt_i8Psi4s30N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s30N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s30N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s30N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s30W hx)
  unfold i8Psi4s30
  refine e.congr_deriv ?_
  unfold i8Psi4s30D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 30 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s30 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 -
    x) * (4 * hpl [negOne, zero, negOne, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽30⁾)'(ξ) ξ' = p₄⁽30⁾`**, in terms of `ξ`. -/
theorem i8Psi4s30D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s30D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s30 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s30D i8Psi4s30N0 i8Psi4s30N1 i8Psi4s30N2 i8Psi4s30N3 i8Psi4s30N4 i8Psi4s30dN0
    i8Psi4s30dN1 i8Psi4s30dN2 i8Psi4s30dN3 i8Psi4s30dN4 i8Psi4s30dW i8P4s30
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_0m0 hx, i13hw_m0m0
    hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽31⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s31N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s31N0`. -/
noncomputable def i8Psi4s31dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s31N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s31N0 (i8Psi4s31dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽31⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s31N1 (x : ℝ) : ℝ :=
    (-16) * hpl [negOne, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s31N1`. -/
noncomputable def i8Psi4s31dN1 (x : ℝ) : ℝ :=
    (-16) * (negOne.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s31N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s31N1 (i8Psi4s31dN1 x) x := by
  unfold i8Psi4s31N1 i8Psi4s31dN1
  exact ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-16))

/-- The part of `ξ² Ψ₄⁽31⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s31N2 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne, zero] x +
    (4) * hpl [negOne, negOne, zero] x +
    (-24) * hpl [negOne, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s31N2`. -/
noncomputable def i8Psi4s31dN2 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-24) * (negOne.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s31N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s31N2 (i8Psi4s31dN2 x) x := by
  unfold i8Psi4s31N2 i8Psi4s31dN2
  exact ((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽31⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s31N3 (x : ℝ) : ℝ :=
    (-2) +
    (2) * hpl [zero] x +
    (-4) * hpl [negOne, zero] x +
    (8) * hpl [negOne, negOne, zero] x +
    (-16) * hpl [negOne, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s31N3`. -/
noncomputable def i8Psi4s31dN3 (x : ℝ) : ℝ :=
    0 +
    (2) * (zero.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-16) * (negOne.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s31N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s31N3 (i8Psi4s31dN3 x) x := by
  unfold i8Psi4s31N3 i8Psi4s31dN3
  exact (((((hasDerivAt_const x (-2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽31⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s31N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (1) * hpl [zero] x +
    (-2) * hpl [negOne, zero] x +
    (4) * hpl [negOne, negOne, zero] x +
    (-8) * hpl [negOne, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s31N4`. -/
noncomputable def i8Psi4s31dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-8) * (negOne.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s31N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s31N4 (i8Psi4s31dN4 x) x := by
  unfold i8Psi4s31N4 i8Psi4s31dN4
  exact (((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-8)))

/-- The part of `Ψ₄⁽31⁾` with constant coefficients. -/
noncomputable def i8Psi4s31W (x : ℝ) : ℝ :=
    (16) * hpl [zero, negOne, negOne, zero] x +
    (16) * hpl [zero, negOne, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s31W`. -/
noncomputable def i8Psi4s31dW (x : ℝ) : ℝ :=
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s31W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s31W (i8Psi4s31dW x) x := by
  unfold i8Psi4s31W i8Psi4s31dW
  exact (((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne, zero] hx).const_mul (16)))

/-- The piece `Ψ₄⁽31⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s31 (x : ℝ) : ℝ :=
  (i8Psi4s31N0 x + x * i8Psi4s31N1 x + x ^ 2 * i8Psi4s31N2 x + x ^ 3 * i8Psi4s31N3 x +
    x ^ 4 * i8Psi4s31N4 x) / x ^ 2 + i8Psi4s31W x

/-- The derivative of `Ψ₄⁽31⁾`. -/
noncomputable def i8Psi4s31D (x : ℝ) : ℝ :=
  ((i8Psi4s31dN0 x + (i8Psi4s31N1 x + x * i8Psi4s31dN1 x) + (2 * x * i8Psi4s31N2 x +
    x ^ 2 * i8Psi4s31dN2 x) + (3 * x ^ 2 * i8Psi4s31N3 x + x ^ 3 * i8Psi4s31dN3 x) +
    (4 * x ^ 3 * i8Psi4s31N4 x + x ^ 4 * i8Psi4s31dN4 x)) * x ^ 2 - (i8Psi4s31N0 x +
    x * i8Psi4s31N1 x + x ^ 2 * i8Psi4s31N2 x + x ^ 3 * i8Psi4s31N3 x +
    x ^ 4 * i8Psi4s31N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s31dW x

theorem hasDerivAt_i8Psi4s31 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s31 (i8Psi4s31D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s31N0 hx).add (X.mul (hasDerivAt_i8Psi4s31N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s31N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s31N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s31N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s31W hx)
  unfold i8Psi4s31
  refine e.congr_deriv ?_
  unfold i8Psi4s31D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 31 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s31 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 -
    x) * ((-8) * hpl [negOne, negOne, negOne, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽31⁾)'(ξ) ξ' = p₄⁽31⁾`**, in terms of `ξ`. -/
theorem i8Psi4s31D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s31D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s31 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s31D i8Psi4s31N0 i8Psi4s31N1 i8Psi4s31N2 i8Psi4s31N3 i8Psi4s31N4 i8Psi4s31dN0
    i8Psi4s31dN1 i8Psi4s31dN2 i8Psi4s31dN3 i8Psi4s31dN4 i8Psi4s31dW i8P4s31
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_mm0 hx, i13hw_mmm0
    hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽32⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s32N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s32N0`. -/
noncomputable def i8Psi4s32dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s32N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s32N0 (i8Psi4s32dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽32⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s32N1 (x : ℝ) : ℝ :=
    (8) * hpl [negOne, negOne, zero] x +
    (8) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s32N1`. -/
noncomputable def i8Psi4s32dN1 (x : ℝ) : ℝ :=
    (8) * (negOne.kernel x * hpl [negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s32N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s32N1 (i8Psi4s32dN1 x) x := by
  unfold i8Psi4s32N1 i8Psi4s32dN1
  exact (((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽32⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s32N2 (x : ℝ) : ℝ :=
    (5) * hpl [negOne, zero] x +
    (2) * hpl [negOne, negOne, zero] x

/-- The derivative of `i8Psi4s32N2`. -/
noncomputable def i8Psi4s32dN2 (x : ℝ) : ℝ :=
    (5) * (negOne.kernel x * hpl [zero] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s32N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s32N2 (i8Psi4s32dN2 x) x := by
  unfold i8Psi4s32N2 i8Psi4s32dN2
  exact (((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (5)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽32⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s32N3 (x : ℝ) : ℝ :=
    (5) +
    (-5) * hpl [zero] x +
    (6) * hpl [negOne, zero] x +
    (-8) * hpl [negOne, negOne, zero] x +
    (8) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s32N3`. -/
noncomputable def i8Psi4s32dN3 (x : ℝ) : ℝ :=
    0 +
    (-5) * (zero.kernel x * hpl [] x) +
    (6) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s32N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s32N3 (i8Psi4s32dN3 x) x := by
  unfold i8Psi4s32N3 i8Psi4s32dN3
  exact (((((hasDerivAt_const x (5)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽32⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s32N4 (x : ℝ) : ℝ :=
    (1 / 4) +
    (-1 / 2) * hpl [zero] x +
    (1) * hpl [negOne, zero] x +
    (-2) * hpl [negOne, negOne, zero] x +
    (4) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s32N4`. -/
noncomputable def i8Psi4s32dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s32N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s32N4 (i8Psi4s32dN4 x) x := by
  unfold i8Psi4s32N4 i8Psi4s32dN4
  exact (((((hasDerivAt_const x (1 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽32⁾` with constant coefficients. -/
noncomputable def i8Psi4s32W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s32W`. -/
noncomputable def i8Psi4s32dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s32W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s32W (i8Psi4s32dW x) x := by
  unfold i8Psi4s32W i8Psi4s32dW
  exact (((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne, zero] hx).const_mul (-8)))

/-- The piece `Ψ₄⁽32⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s32 (x : ℝ) : ℝ :=
  (i8Psi4s32N0 x + x * i8Psi4s32N1 x + x ^ 2 * i8Psi4s32N2 x + x ^ 3 * i8Psi4s32N3 x +
    x ^ 4 * i8Psi4s32N4 x) / x ^ 2 + i8Psi4s32W x

/-- The derivative of `Ψ₄⁽32⁾`. -/
noncomputable def i8Psi4s32D (x : ℝ) : ℝ :=
  ((i8Psi4s32dN0 x + (i8Psi4s32N1 x + x * i8Psi4s32dN1 x) + (2 * x * i8Psi4s32N2 x +
    x ^ 2 * i8Psi4s32dN2 x) + (3 * x ^ 2 * i8Psi4s32N3 x + x ^ 3 * i8Psi4s32dN3 x) +
    (4 * x ^ 3 * i8Psi4s32N4 x + x ^ 4 * i8Psi4s32dN4 x)) * x ^ 2 - (i8Psi4s32N0 x +
    x * i8Psi4s32N1 x + x ^ 2 * i8Psi4s32N2 x + x ^ 3 * i8Psi4s32N3 x +
    x ^ 4 * i8Psi4s32N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s32dW x

theorem hasDerivAt_i8Psi4s32 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s32 (i8Psi4s32D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s32N0 hx).add (X.mul (hasDerivAt_i8Psi4s32N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s32N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s32N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s32N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s32W hx)
  unfold i8Psi4s32
  refine e.congr_deriv ?_
  unfold i8Psi4s32D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 32 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s32 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 -
    x) * (4 * hpl [zero, negOne, negOne, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽32⁾)'(ξ) ξ' = p₄⁽32⁾`**, in terms of `ξ`. -/
theorem i8Psi4s32D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s32D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s32 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s32D i8Psi4s32N0 i8Psi4s32N1 i8Psi4s32N2 i8Psi4s32N3 i8Psi4s32N4 i8Psi4s32dN0
    i8Psi4s32dN1 i8Psi4s32dN2 i8Psi4s32dN3 i8Psi4s32dN4 i8Psi4s32dW i8P4s32
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_mm0 hx, i13hw_0mm0
    hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽33⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s33N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s33N0`. -/
noncomputable def i8Psi4s33dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s33N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s33N0 (i8Psi4s33dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽33⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s33N1 (x : ℝ) : ℝ :=
    (2) +
    (2) * hpl [zero] x +
    (2) * hpl [zero, zero] x +
    (2) * hpl [zero, zero, zero] x +
    (2) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s33N1`. -/
noncomputable def i8Psi4s33dN1 (x : ℝ) : ℝ :=
    0 +
    (2) * (zero.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s33N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s33N1 (i8Psi4s33dN1 x) x := by
  unfold i8Psi4s33N1 i8Psi4s33dN1
  exact (((((hasDerivAt_const x (2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽33⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s33N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s33N2`. -/
noncomputable def i8Psi4s33dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s33N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s33N2 (i8Psi4s33dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽33⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s33N3 (x : ℝ) : ℝ :=
    (2) +
    (-2) * hpl [zero] x +
    (2) * hpl [zero, zero] x +
    (-2) * hpl [zero, zero, zero] x +
    (2) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s33N3`. -/
noncomputable def i8Psi4s33dN3 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s33N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s33N3 (i8Psi4s33dN3 x) x := by
  unfold i8Psi4s33N3 i8Psi4s33dN3
  exact (((((hasDerivAt_const x (2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽33⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s33N4 (x : ℝ) : ℝ :=
    (1 / 16) +
    (-1 / 8) * hpl [zero] x +
    (1 / 4) * hpl [zero, zero] x +
    (-1 / 2) * hpl [zero, zero, zero] x +
    (1) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s33N4`. -/
noncomputable def i8Psi4s33dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 8) * (zero.kernel x * hpl [] x) +
    (1 / 4) * (zero.kernel x * hpl [zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (1) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s33N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s33N4 (i8Psi4s33dN4 x) x := by
  unfold i8Psi4s33N4 i8Psi4s33dN4
  exact (((((hasDerivAt_const x (1 / 16)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (1)))

/-- The part of `Ψ₄⁽33⁾` with constant coefficients. -/
noncomputable def i8Psi4s33W (x : ℝ) : ℝ :=
    (-2) * hpl [zero, zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s33W`. -/
noncomputable def i8Psi4s33dW (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [zero, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s33W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s33W (i8Psi4s33dW x) x := by
  unfold i8Psi4s33W i8Psi4s33dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero, zero] hx).const_mul (-2))

/-- The piece `Ψ₄⁽33⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s33 (x : ℝ) : ℝ :=
  (i8Psi4s33N0 x + x * i8Psi4s33N1 x + x ^ 2 * i8Psi4s33N2 x + x ^ 3 * i8Psi4s33N3 x +
    x ^ 4 * i8Psi4s33N4 x) / x ^ 2 + i8Psi4s33W x

/-- The derivative of `Ψ₄⁽33⁾`. -/
noncomputable def i8Psi4s33D (x : ℝ) : ℝ :=
  ((i8Psi4s33dN0 x + (i8Psi4s33N1 x + x * i8Psi4s33dN1 x) + (2 * x * i8Psi4s33N2 x +
    x ^ 2 * i8Psi4s33dN2 x) + (3 * x ^ 2 * i8Psi4s33N3 x + x ^ 3 * i8Psi4s33dN3 x) +
    (4 * x ^ 3 * i8Psi4s33N4 x + x ^ 4 * i8Psi4s33dN4 x)) * x ^ 2 - (i8Psi4s33N0 x +
    x * i8Psi4s33N1 x + x ^ 2 * i8Psi4s33N2 x + x ^ 3 * i8Psi4s33N3 x +
    x ^ 4 * i8Psi4s33N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s33dW x

theorem hasDerivAt_i8Psi4s33 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s33 (i8Psi4s33D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s33N0 hx).add (X.mul (hasDerivAt_i8Psi4s33N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s33N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s33N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s33N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s33W hx)
  unfold i8Psi4s33
  refine e.congr_deriv ?_
  unfold i8Psi4s33D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 33 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s33 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * (1 * hpl [zero, zero, zero, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽33⁾)'(ξ) ξ' = p₄⁽33⁾`**, in terms of `ξ`. -/
theorem i8Psi4s33D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s33D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s33 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s33D i8Psi4s33N0 i8Psi4s33N1 i8Psi4s33N2 i8Psi4s33N3 i8Psi4s33N4 i8Psi4s33dN0
    i8Psi4s33dN1 i8Psi4s33dN2 i8Psi4s33dN3 i8Psi4s33dN4 i8Psi4s33dW i8P4s33
  simp only [kernel_zero, hpl_nil, hpl_zero, i13hw_00, i13hw_000, i13hw_0000]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽34⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s34N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s34N0`. -/
noncomputable def i8Psi4s34dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s34N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s34N0 (i8Psi4s34dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽34⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s34N1 (x : ℝ) : ℝ :=
    (-4) * hpl [negOne, zero, zero, zero] x

/-- The derivative of `i8Psi4s34N1`. -/
noncomputable def i8Psi4s34dN1 (x : ℝ) : ℝ :=
    (-4) * (negOne.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s34N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s34N1 (i8Psi4s34dN1 x) x := by
  unfold i8Psi4s34N1 i8Psi4s34dN1
  exact ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-4))

/-- The part of `ξ² Ψ₄⁽34⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s34N2 (x : ℝ) : ℝ :=
    (-6) * hpl [negOne, zero, zero, zero] x

/-- The derivative of `i8Psi4s34N2`. -/
noncomputable def i8Psi4s34dN2 (x : ℝ) : ℝ :=
    (-6) * (negOne.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s34N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s34N2 (i8Psi4s34dN2 x) x := by
  unfold i8Psi4s34N2 i8Psi4s34dN2
  exact ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-6))

/-- The part of `ξ² Ψ₄⁽34⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s34N3 (x : ℝ) : ℝ :=
    (-2) +
    (2) * hpl [zero] x +
    (-2) * hpl [zero, zero] x +
    (2) * hpl [zero, zero, zero] x +
    (-4) * hpl [negOne, zero, zero, zero] x

/-- The derivative of `i8Psi4s34N3`. -/
noncomputable def i8Psi4s34dN3 (x : ℝ) : ℝ :=
    0 +
    (2) * (zero.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s34N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s34N3 (i8Psi4s34dN3 x) x := by
  unfold i8Psi4s34N3 i8Psi4s34dN3
  exact (((((hasDerivAt_const x (-2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽34⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s34N4 (x : ℝ) : ℝ :=
    (-1 / 8) +
    (1 / 4) * hpl [zero] x +
    (-1 / 2) * hpl [zero, zero] x +
    (1) * hpl [zero, zero, zero] x +
    (-2) * hpl [negOne, zero, zero, zero] x

/-- The derivative of `i8Psi4s34N4`. -/
noncomputable def i8Psi4s34dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 4) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [zero, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s34N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s34N4 (i8Psi4s34dN4 x) x := by
  unfold i8Psi4s34N4 i8Psi4s34dN4
  exact (((((hasDerivAt_const x (-1 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽34⁾` with constant coefficients. -/
noncomputable def i8Psi4s34W (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero, zero, zero] x +
    (4) * hpl [zero, negOne, zero, zero, zero] x

/-- The derivative of `i8Psi4s34W`. -/
noncomputable def i8Psi4s34dW (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s34W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s34W (i8Psi4s34dW x) x := by
  unfold i8Psi4s34W i8Psi4s34dW
  exact (((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, zero] hx).const_mul (4)))

/-- The piece `Ψ₄⁽34⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s34 (x : ℝ) : ℝ :=
  (i8Psi4s34N0 x + x * i8Psi4s34N1 x + x ^ 2 * i8Psi4s34N2 x + x ^ 3 * i8Psi4s34N3 x +
    x ^ 4 * i8Psi4s34N4 x) / x ^ 2 + i8Psi4s34W x

/-- The derivative of `Ψ₄⁽34⁾`. -/
noncomputable def i8Psi4s34D (x : ℝ) : ℝ :=
  ((i8Psi4s34dN0 x + (i8Psi4s34N1 x + x * i8Psi4s34dN1 x) + (2 * x * i8Psi4s34N2 x +
    x ^ 2 * i8Psi4s34dN2 x) + (3 * x ^ 2 * i8Psi4s34N3 x + x ^ 3 * i8Psi4s34dN3 x) +
    (4 * x ^ 3 * i8Psi4s34N4 x + x ^ 4 * i8Psi4s34dN4 x)) * x ^ 2 - (i8Psi4s34N0 x +
    x * i8Psi4s34N1 x + x ^ 2 * i8Psi4s34N2 x + x ^ 3 * i8Psi4s34N3 x +
    x ^ 4 * i8Psi4s34N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s34dW x

theorem hasDerivAt_i8Psi4s34 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s34 (i8Psi4s34D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s34N0 hx).add (X.mul (hasDerivAt_i8Psi4s34N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s34N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s34N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s34N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s34W hx)
  unfold i8Psi4s34
  refine e.congr_deriv ?_
  unfold i8Psi4s34D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 34 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s34 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((-2) * hpl [negOne, zero, zero, zero] x)) * (x / (1 -
    x))

/-- **`(Ψ₄⁽34⁾)'(ξ) ξ' = p₄⁽34⁾`**, in terms of `ξ`. -/
theorem i8Psi4s34D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s34D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s34 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s34D i8Psi4s34N0 i8Psi4s34N1 i8Psi4s34N2 i8Psi4s34N3 i8Psi4s34N4 i8Psi4s34dN0
    i8Psi4s34dN1 i8Psi4s34dN2 i8Psi4s34dN3 i8Psi4s34dN4 i8Psi4s34dW i8P4s34
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_000, i13hw_m000 hx]
  field_simp
  ring

end QED.ThreeLoopD
