/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P6

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 35 to 42

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s35`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s35D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s35`, `QED.ThreeLoopD.i8Psi4s35D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽35⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s35N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s35N0`. -/
noncomputable def i8Psi4s35dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s35N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s35N0 (i8Psi4s35dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽35⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s35N1 (x : ℝ) : ℝ :=
    (-4) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s35N1`. -/
noncomputable def i8Psi4s35dN1 (x : ℝ) : ℝ :=
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s35N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s35N1 (i8Psi4s35dN1 x) x := by
  unfold i8Psi4s35N1 i8Psi4s35dN1
  exact (((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽35⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s35N2 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne, zero, zero] x

/-- The derivative of `i8Psi4s35N2`. -/
noncomputable def i8Psi4s35dN2 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s35N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s35N2 (i8Psi4s35dN2 x) x := by
  unfold i8Psi4s35N2 i8Psi4s35dN2
  exact ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1))

/-- The part of `ξ² Ψ₄⁽35⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s35N3 (x : ℝ) : ℝ :=
    (-3) +
    (3) * hpl [zero] x +
    (-3) * hpl [zero, zero] x +
    (4) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s35N3`. -/
noncomputable def i8Psi4s35dN3 (x : ℝ) : ℝ :=
    0 +
    (3) * (zero.kernel x * hpl [] x) +
    (-3) * (zero.kernel x * hpl [zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s35N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s35N3 (i8Psi4s35dN3 x) x := by
  unfold i8Psi4s35N3 i8Psi4s35dN3
  exact (((((hasDerivAt_const x (-3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽35⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s35N4 (x : ℝ) : ℝ :=
    (-1 / 8) +
    (1 / 4) * hpl [zero] x +
    (-1 / 2) * hpl [zero, zero] x +
    (1) * hpl [negOne, zero, zero] x +
    (-2) * hpl [zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s35N4`. -/
noncomputable def i8Psi4s35dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 4) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s35N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s35N4 (i8Psi4s35dN4 x) x := by
  unfold i8Psi4s35N4 i8Psi4s35dN4
  exact (((((hasDerivAt_const x (-1 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽35⁾` with constant coefficients. -/
noncomputable def i8Psi4s35W (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero, zero] x +
    (4) * hpl [zero, zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s35W`. -/
noncomputable def i8Psi4s35dW (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s35W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s35W (i8Psi4s35dW x) x := by
  unfold i8Psi4s35W i8Psi4s35dW
  exact (((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (4)))

/-- The piece `Ψ₄⁽35⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s35 (x : ℝ) : ℝ :=
  (i8Psi4s35N0 x + x * i8Psi4s35N1 x + x ^ 2 * i8Psi4s35N2 x + x ^ 3 * i8Psi4s35N3 x +
    x ^ 4 * i8Psi4s35N4 x) / x ^ 2 + i8Psi4s35W x

/-- The derivative of `Ψ₄⁽35⁾`. -/
noncomputable def i8Psi4s35D (x : ℝ) : ℝ :=
  ((i8Psi4s35dN0 x + (i8Psi4s35N1 x + x * i8Psi4s35dN1 x) + (2 * x * i8Psi4s35N2 x +
    x ^ 2 * i8Psi4s35dN2 x) + (3 * x ^ 2 * i8Psi4s35N3 x + x ^ 3 * i8Psi4s35dN3 x) +
    (4 * x ^ 3 * i8Psi4s35N4 x + x ^ 4 * i8Psi4s35dN4 x)) * x ^ 2 - (i8Psi4s35N0 x +
    x * i8Psi4s35N1 x + x ^ 2 * i8Psi4s35N2 x + x ^ 3 * i8Psi4s35N3 x +
    x ^ 4 * i8Psi4s35N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s35dW x

theorem hasDerivAt_i8Psi4s35 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s35 (i8Psi4s35D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s35N0 hx).add (X.mul (hasDerivAt_i8Psi4s35N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s35N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s35N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s35N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s35W hx)
  unfold i8Psi4s35
  refine e.congr_deriv ?_
  unfold i8Psi4s35D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 35 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s35 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((-2) * hpl [zero, negOne, zero, zero] x)) * (x / (1 -
    x))

/-- **`(Ψ₄⁽35⁾)'(ξ) ξ' = p₄⁽35⁾`**, in terms of `ξ`. -/
theorem i8Psi4s35D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s35D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s35 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s35D i8Psi4s35N0 i8Psi4s35N1 i8Psi4s35N2 i8Psi4s35N3 i8Psi4s35N4 i8Psi4s35dN0
    i8Psi4s35dN1 i8Psi4s35dN2 i8Psi4s35dN3 i8Psi4s35dN4 i8Psi4s35dW i8P4s35
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m00 hx, i13hw_0m00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽36⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s36N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s36N0`. -/
noncomputable def i8Psi4s36dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s36N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s36N0 (i8Psi4s36dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽36⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s36N1 (x : ℝ) : ℝ :=
    (8) * hpl [negOne, negOne, zero, zero] x

/-- The derivative of `i8Psi4s36N1`. -/
noncomputable def i8Psi4s36dN1 (x : ℝ) : ℝ :=
    (8) * (negOne.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s36N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s36N1 (i8Psi4s36dN1 x) x := by
  unfold i8Psi4s36N1 i8Psi4s36dN1
  exact ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (8))

/-- The part of `ξ² Ψ₄⁽36⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s36N2 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne, zero, zero] x +
    (12) * hpl [negOne, negOne, zero, zero] x

/-- The derivative of `i8Psi4s36N2`. -/
noncomputable def i8Psi4s36dN2 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (12) * (negOne.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s36N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s36N2 (i8Psi4s36dN2 x) x := by
  unfold i8Psi4s36N2 i8Psi4s36dN2
  exact (((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽36⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s36N3 (x : ℝ) : ℝ :=
    (2) +
    (-2) * hpl [zero] x +
    (2) * hpl [zero, zero] x +
    (-4) * hpl [negOne, zero, zero] x +
    (8) * hpl [negOne, negOne, zero, zero] x

/-- The derivative of `i8Psi4s36N3`. -/
noncomputable def i8Psi4s36dN3 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s36N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s36N3 (i8Psi4s36dN3 x) x := by
  unfold i8Psi4s36N3 i8Psi4s36dN3
  exact (((((hasDerivAt_const x (2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽36⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s36N4 (x : ℝ) : ℝ :=
    (1 / 4) +
    (-1 / 2) * hpl [zero] x +
    (1) * hpl [zero, zero] x +
    (-2) * hpl [negOne, zero, zero] x +
    (4) * hpl [negOne, negOne, zero, zero] x

/-- The derivative of `i8Psi4s36N4`. -/
noncomputable def i8Psi4s36dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s36N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s36N4 (i8Psi4s36dN4 x) x := by
  unfold i8Psi4s36N4 i8Psi4s36dN4
  exact (((((hasDerivAt_const x (1 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽36⁾` with constant coefficients. -/
noncomputable def i8Psi4s36W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, negOne, zero, zero] x

/-- The derivative of `i8Psi4s36W`. -/
noncomputable def i8Psi4s36dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s36W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s36W (i8Psi4s36dW x) x := by
  unfold i8Psi4s36W i8Psi4s36dW
  exact (((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero, zero] hx).const_mul (-8)))

/-- The piece `Ψ₄⁽36⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s36 (x : ℝ) : ℝ :=
  (i8Psi4s36N0 x + x * i8Psi4s36N1 x + x ^ 2 * i8Psi4s36N2 x + x ^ 3 * i8Psi4s36N3 x +
    x ^ 4 * i8Psi4s36N4 x) / x ^ 2 + i8Psi4s36W x

/-- The derivative of `Ψ₄⁽36⁾`. -/
noncomputable def i8Psi4s36D (x : ℝ) : ℝ :=
  ((i8Psi4s36dN0 x + (i8Psi4s36N1 x + x * i8Psi4s36dN1 x) + (2 * x * i8Psi4s36N2 x +
    x ^ 2 * i8Psi4s36dN2 x) + (3 * x ^ 2 * i8Psi4s36N3 x + x ^ 3 * i8Psi4s36dN3 x) +
    (4 * x ^ 3 * i8Psi4s36N4 x + x ^ 4 * i8Psi4s36dN4 x)) * x ^ 2 - (i8Psi4s36N0 x +
    x * i8Psi4s36N1 x + x ^ 2 * i8Psi4s36N2 x + x ^ 3 * i8Psi4s36N3 x +
    x ^ 4 * i8Psi4s36N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s36dW x

theorem hasDerivAt_i8Psi4s36 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s36 (i8Psi4s36D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s36N0 hx).add (X.mul (hasDerivAt_i8Psi4s36N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s36N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s36N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s36N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s36W hx)
  unfold i8Psi4s36
  refine e.congr_deriv ?_
  unfold i8Psi4s36D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 36 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s36 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 -
    x) * (4 * hpl [negOne, negOne, zero, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽36⁾)'(ξ) ξ' = p₄⁽36⁾`**, in terms of `ξ`. -/
theorem i8Psi4s36D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s36D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s36 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s36D i8Psi4s36N0 i8Psi4s36N1 i8Psi4s36N2 i8Psi4s36N3 i8Psi4s36N4 i8Psi4s36dN0
    i8Psi4s36dN1 i8Psi4s36dN2 i8Psi4s36dN3 i8Psi4s36dN4 i8Psi4s36dW i8P4s36
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m00 hx, i13hw_mm00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽37⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s37N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s37N0`. -/
noncomputable def i8Psi4s37dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s37N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s37N0 (i8Psi4s37dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽37⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s37N1 (x : ℝ) : ℝ :=
    (-8) * hpl [negOne, zero] x +
    (-8) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s37N1`. -/
noncomputable def i8Psi4s37dN1 (x : ℝ) : ℝ :=
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s37N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s37N1 (i8Psi4s37dN1 x) x := by
  unfold i8Psi4s37N1 i8Psi4s37dN1
  exact (((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽37⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s37N2 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s37N2`. -/
noncomputable def i8Psi4s37dN2 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s37N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s37N2 (i8Psi4s37dN2 x) x := by
  unfold i8Psi4s37N2 i8Psi4s37dN2
  exact ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))

/-- The part of `ξ² Ψ₄⁽37⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s37N3 (x : ℝ) : ℝ :=
    (6) +
    (-6) * hpl [zero] x +
    (8) * hpl [negOne, zero] x +
    (-8) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s37N3`. -/
noncomputable def i8Psi4s37dN3 (x : ℝ) : ℝ :=
    0 +
    (-6) * (zero.kernel x * hpl [] x) +
    (8) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s37N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s37N3 (i8Psi4s37dN3 x) x := by
  unfold i8Psi4s37N3 i8Psi4s37dN3
  exact ((((hasDerivAt_const x (6)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽37⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s37N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1) * hpl [zero] x +
    (2) * hpl [negOne, zero] x +
    (-4) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s37N4`. -/
noncomputable def i8Psi4s37dN4 (x : ℝ) : ℝ :=
    0 +
    (-1) * (zero.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s37N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s37N4 (i8Psi4s37dN4 x) x := by
  unfold i8Psi4s37N4 i8Psi4s37dN4
  exact ((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽37⁾` with constant coefficients. -/
noncomputable def i8Psi4s37W (x : ℝ) : ℝ :=
    (8) * hpl [zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s37W`. -/
noncomputable def i8Psi4s37dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s37W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s37W (i8Psi4s37dW x) x := by
  unfold i8Psi4s37W i8Psi4s37dW
  exact (((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (8)))

/-- The piece `Ψ₄⁽37⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s37 (x : ℝ) : ℝ :=
  (i8Psi4s37N0 x + x * i8Psi4s37N1 x + x ^ 2 * i8Psi4s37N2 x + x ^ 3 * i8Psi4s37N3 x +
    x ^ 4 * i8Psi4s37N4 x) / x ^ 2 + i8Psi4s37W x

/-- The derivative of `Ψ₄⁽37⁾`. -/
noncomputable def i8Psi4s37D (x : ℝ) : ℝ :=
  ((i8Psi4s37dN0 x + (i8Psi4s37N1 x + x * i8Psi4s37dN1 x) + (2 * x * i8Psi4s37N2 x +
    x ^ 2 * i8Psi4s37dN2 x) + (3 * x ^ 2 * i8Psi4s37N3 x + x ^ 3 * i8Psi4s37dN3 x) +
    (4 * x ^ 3 * i8Psi4s37N4 x + x ^ 4 * i8Psi4s37dN4 x)) * x ^ 2 - (i8Psi4s37N0 x +
    x * i8Psi4s37N1 x + x ^ 2 * i8Psi4s37N2 x + x ^ 3 * i8Psi4s37N3 x +
    x ^ 4 * i8Psi4s37N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s37dW x

theorem hasDerivAt_i8Psi4s37 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s37 (i8Psi4s37D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s37N0 hx).add (X.mul (hasDerivAt_i8Psi4s37N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s37N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s37N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s37N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s37W hx)
  unfold i8Psi4s37
  refine e.congr_deriv ?_
  unfold i8Psi4s37D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 37 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s37 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((-4) * hpl [zero, negOne, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽37⁾)'(ξ) ξ' = p₄⁽37⁾`**, in terms of `ξ`. -/
theorem i8Psi4s37D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s37D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s37 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s37D i8Psi4s37N0 i8Psi4s37N1 i8Psi4s37N2 i8Psi4s37N3 i8Psi4s37N4 i8Psi4s37dN0
    i8Psi4s37dN1 i8Psi4s37dN2 i8Psi4s37dN3 i8Psi4s37dN4 i8Psi4s37dW i8P4s37
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_0m0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽38⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s38N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s38N0`. -/
noncomputable def i8Psi4s38dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s38N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s38N0 (i8Psi4s38dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽38⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s38N1 (x : ℝ) : ℝ :=
    (16) * hpl [negOne, negOne, zero] x

/-- The derivative of `i8Psi4s38N1`. -/
noncomputable def i8Psi4s38dN1 (x : ℝ) : ℝ :=
    (16) * (negOne.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s38N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s38N1 (i8Psi4s38dN1 x) x := by
  unfold i8Psi4s38N1 i8Psi4s38dN1
  exact ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (16))

/-- The part of `ξ² Ψ₄⁽38⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s38N2 (x : ℝ) : ℝ :=
    (-4) * hpl [negOne, zero] x +
    (24) * hpl [negOne, negOne, zero] x

/-- The derivative of `i8Psi4s38N2`. -/
noncomputable def i8Psi4s38dN2 (x : ℝ) : ℝ :=
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (24) * (negOne.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s38N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s38N2 (i8Psi4s38dN2 x) x := by
  unfold i8Psi4s38N2 i8Psi4s38dN2
  exact (((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (24)))

/-- The part of `ξ² Ψ₄⁽38⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s38N3 (x : ℝ) : ℝ :=
    (-4) +
    (4) * hpl [zero] x +
    (-8) * hpl [negOne, zero] x +
    (16) * hpl [negOne, negOne, zero] x

/-- The derivative of `i8Psi4s38N3`. -/
noncomputable def i8Psi4s38dN3 (x : ℝ) : ℝ :=
    0 +
    (4) * (zero.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s38N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s38N3 (i8Psi4s38dN3 x) x := by
  unfold i8Psi4s38N3 i8Psi4s38dN3
  exact ((((hasDerivAt_const x (-4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽38⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s38N4 (x : ℝ) : ℝ :=
    (-1) +
    (2) * hpl [zero] x +
    (-4) * hpl [negOne, zero] x +
    (8) * hpl [negOne, negOne, zero] x

/-- The derivative of `i8Psi4s38N4`. -/
noncomputable def i8Psi4s38dN4 (x : ℝ) : ℝ :=
    0 +
    (2) * (zero.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s38N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s38N4 (i8Psi4s38dN4 x) x := by
  unfold i8Psi4s38N4 i8Psi4s38dN4
  exact ((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (8)))

/-- The part of `Ψ₄⁽38⁾` with constant coefficients. -/
noncomputable def i8Psi4s38W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, negOne, zero] x +
    (-16) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s38W`. -/
noncomputable def i8Psi4s38dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s38W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s38W (i8Psi4s38dW x) x := by
  unfold i8Psi4s38W i8Psi4s38dW
  exact (((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-16)))

/-- The piece `Ψ₄⁽38⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s38 (x : ℝ) : ℝ :=
  (i8Psi4s38N0 x + x * i8Psi4s38N1 x + x ^ 2 * i8Psi4s38N2 x + x ^ 3 * i8Psi4s38N3 x +
    x ^ 4 * i8Psi4s38N4 x) / x ^ 2 + i8Psi4s38W x

/-- The derivative of `Ψ₄⁽38⁾`. -/
noncomputable def i8Psi4s38D (x : ℝ) : ℝ :=
  ((i8Psi4s38dN0 x + (i8Psi4s38N1 x + x * i8Psi4s38dN1 x) + (2 * x * i8Psi4s38N2 x +
    x ^ 2 * i8Psi4s38dN2 x) + (3 * x ^ 2 * i8Psi4s38N3 x + x ^ 3 * i8Psi4s38dN3 x) +
    (4 * x ^ 3 * i8Psi4s38N4 x + x ^ 4 * i8Psi4s38dN4 x)) * x ^ 2 - (i8Psi4s38N0 x +
    x * i8Psi4s38N1 x + x ^ 2 * i8Psi4s38N2 x + x ^ 3 * i8Psi4s38N3 x +
    x ^ 4 * i8Psi4s38N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s38dW x

theorem hasDerivAt_i8Psi4s38 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s38 (i8Psi4s38D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s38N0 hx).add (X.mul (hasDerivAt_i8Psi4s38N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s38N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s38N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s38N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s38W hx)
  unfold i8Psi4s38
  refine e.congr_deriv ?_
  unfold i8Psi4s38D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 38 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s38 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * (8 * hpl [negOne, negOne, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽38⁾)'(ξ) ξ' = p₄⁽38⁾`**, in terms of `ξ`. -/
theorem i8Psi4s38D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s38D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s38 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s38D i8Psi4s38N0 i8Psi4s38N1 i8Psi4s38N2 i8Psi4s38N3 i8Psi4s38N4 i8Psi4s38dN0
    i8Psi4s38dN1 i8Psi4s38dN2 i8Psi4s38dN3 i8Psi4s38dN4 i8Psi4s38dW i8P4s38
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_mm0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽39⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s39N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s39N0`. -/
noncomputable def i8Psi4s39dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s39N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s39N0 (i8Psi4s39dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽39⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s39N1 (x : ℝ) : ℝ :=
    (-8) * hpl [negOne, zero, zero] x

/-- The derivative of `i8Psi4s39N1`. -/
noncomputable def i8Psi4s39dN1 (x : ℝ) : ℝ :=
    (-8) * (negOne.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s39N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s39N1 (i8Psi4s39dN1 x) x := by
  unfold i8Psi4s39N1 i8Psi4s39dN1
  exact ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))

/-- The part of `ξ² Ψ₄⁽39⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s39N2 (x : ℝ) : ℝ :=
    (-12) * hpl [negOne, zero, zero] x

/-- The derivative of `i8Psi4s39N2`. -/
noncomputable def i8Psi4s39dN2 (x : ℝ) : ℝ :=
    (-12) * (negOne.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s39N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s39N2 (i8Psi4s39dN2 x) x := by
  unfold i8Psi4s39N2 i8Psi4s39dN2
  exact ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12))

/-- The part of `ξ² Ψ₄⁽39⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s39N3 (x : ℝ) : ℝ :=
    (4) +
    (-4) * hpl [zero] x +
    (4) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x

/-- The derivative of `i8Psi4s39N3`. -/
noncomputable def i8Psi4s39dN3 (x : ℝ) : ℝ :=
    0 +
    (-4) * (zero.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s39N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s39N3 (i8Psi4s39dN3 x) x := by
  unfold i8Psi4s39N3 i8Psi4s39dN3
  exact ((((hasDerivAt_const x (4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽39⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s39N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1) * hpl [zero] x +
    (2) * hpl [zero, zero] x +
    (-4) * hpl [negOne, zero, zero] x

/-- The derivative of `i8Psi4s39N4`. -/
noncomputable def i8Psi4s39dN4 (x : ℝ) : ℝ :=
    0 +
    (-1) * (zero.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s39N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s39N4 (i8Psi4s39dN4 x) x := by
  unfold i8Psi4s39N4 i8Psi4s39dN4
  exact ((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽39⁾` with constant coefficients. -/
noncomputable def i8Psi4s39W (x : ℝ) : ℝ :=
    (8) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s39W`. -/
noncomputable def i8Psi4s39dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s39W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s39W (i8Psi4s39dW x) x := by
  unfold i8Psi4s39W i8Psi4s39dW
  exact (((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (8)))

/-- The piece `Ψ₄⁽39⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s39 (x : ℝ) : ℝ :=
  (i8Psi4s39N0 x + x * i8Psi4s39N1 x + x ^ 2 * i8Psi4s39N2 x + x ^ 3 * i8Psi4s39N3 x +
    x ^ 4 * i8Psi4s39N4 x) / x ^ 2 + i8Psi4s39W x

/-- The derivative of `Ψ₄⁽39⁾`. -/
noncomputable def i8Psi4s39D (x : ℝ) : ℝ :=
  ((i8Psi4s39dN0 x + (i8Psi4s39N1 x + x * i8Psi4s39dN1 x) + (2 * x * i8Psi4s39N2 x +
    x ^ 2 * i8Psi4s39dN2 x) + (3 * x ^ 2 * i8Psi4s39N3 x + x ^ 3 * i8Psi4s39dN3 x) +
    (4 * x ^ 3 * i8Psi4s39N4 x + x ^ 4 * i8Psi4s39dN4 x)) * x ^ 2 - (i8Psi4s39N0 x +
    x * i8Psi4s39N1 x + x ^ 2 * i8Psi4s39N2 x + x ^ 3 * i8Psi4s39N3 x +
    x ^ 4 * i8Psi4s39N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s39dW x

theorem hasDerivAt_i8Psi4s39 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s39 (i8Psi4s39D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s39N0 hx).add (X.mul (hasDerivAt_i8Psi4s39N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s39N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s39N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s39N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s39W hx)
  unfold i8Psi4s39
  refine e.congr_deriv ?_
  unfold i8Psi4s39D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 39 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s39 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((-4) * hpl [negOne, zero, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽39⁾)'(ξ) ξ' = p₄⁽39⁾`**, in terms of `ξ`. -/
theorem i8Psi4s39D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s39D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s39 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s39D i8Psi4s39N0 i8Psi4s39N1 i8Psi4s39N2 i8Psi4s39N3 i8Psi4s39N4 i8Psi4s39dN0
    i8Psi4s39dN1 i8Psi4s39dN2 i8Psi4s39dN3 i8Psi4s39dN4 i8Psi4s39dW i8P4s39
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽40⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s40N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s40N0`. -/
noncomputable def i8Psi4s40dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s40N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s40N0 (i8Psi4s40dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽40⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s40N1 (x : ℝ) : ℝ :=
    (4) +
    (4) * hpl [zero] x +
    (4) * hpl [zero, zero] x +
    (4) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s40N1`. -/
noncomputable def i8Psi4s40dN1 (x : ℝ) : ℝ :=
    0 +
    (4) * (zero.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s40N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s40N1 (i8Psi4s40dN1 x) x := by
  unfold i8Psi4s40N1 i8Psi4s40dN1
  exact ((((hasDerivAt_const x (4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽40⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s40N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s40N2`. -/
noncomputable def i8Psi4s40dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s40N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s40N2 (i8Psi4s40dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽40⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s40N3 (x : ℝ) : ℝ :=
    (-4) +
    (4) * hpl [zero] x +
    (-4) * hpl [zero, zero] x +
    (4) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s40N3`. -/
noncomputable def i8Psi4s40dN3 (x : ℝ) : ℝ :=
    0 +
    (4) * (zero.kernel x * hpl [] x) +
    (-4) * (zero.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s40N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s40N3 (i8Psi4s40dN3 x) x := by
  unfold i8Psi4s40N3 i8Psi4s40dN3
  exact ((((hasDerivAt_const x (-4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽40⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s40N4 (x : ℝ) : ℝ :=
    (-1 / 4) +
    (1 / 2) * hpl [zero] x +
    (-1) * hpl [zero, zero] x +
    (2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s40N4`. -/
noncomputable def i8Psi4s40dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s40N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s40N4 (i8Psi4s40dN4 x) x := by
  unfold i8Psi4s40N4 i8Psi4s40dN4
  exact ((((hasDerivAt_const x (-1 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2)))

/-- The part of `Ψ₄⁽40⁾` with constant coefficients. -/
noncomputable def i8Psi4s40W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s40W`. -/
noncomputable def i8Psi4s40dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s40W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s40W (i8Psi4s40dW x) x := by
  unfold i8Psi4s40W i8Psi4s40dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-4))

/-- The piece `Ψ₄⁽40⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s40 (x : ℝ) : ℝ :=
  (i8Psi4s40N0 x + x * i8Psi4s40N1 x + x ^ 2 * i8Psi4s40N2 x + x ^ 3 * i8Psi4s40N3 x +
    x ^ 4 * i8Psi4s40N4 x) / x ^ 2 + i8Psi4s40W x

/-- The derivative of `Ψ₄⁽40⁾`. -/
noncomputable def i8Psi4s40D (x : ℝ) : ℝ :=
  ((i8Psi4s40dN0 x + (i8Psi4s40N1 x + x * i8Psi4s40dN1 x) + (2 * x * i8Psi4s40N2 x +
    x ^ 2 * i8Psi4s40dN2 x) + (3 * x ^ 2 * i8Psi4s40N3 x + x ^ 3 * i8Psi4s40dN3 x) +
    (4 * x ^ 3 * i8Psi4s40N4 x + x ^ 4 * i8Psi4s40dN4 x)) * x ^ 2 - (i8Psi4s40N0 x +
    x * i8Psi4s40N1 x + x ^ 2 * i8Psi4s40N2 x + x ^ 3 * i8Psi4s40N3 x +
    x ^ 4 * i8Psi4s40N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s40dW x

theorem hasDerivAt_i8Psi4s40 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s40 (i8Psi4s40D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s40N0 hx).add (X.mul (hasDerivAt_i8Psi4s40N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s40N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s40N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s40N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s40W hx)
  unfold i8Psi4s40
  refine e.congr_deriv ?_
  unfold i8Psi4s40D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 40 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s40 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * (2 * hpl [zero, zero, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽40⁾)'(ξ) ξ' = p₄⁽40⁾`**, in terms of `ξ`. -/
theorem i8Psi4s40D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s40D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s40 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s40D i8Psi4s40N0 i8Psi4s40N1 i8Psi4s40N2 i8Psi4s40N3 i8Psi4s40N4 i8Psi4s40dN0
    i8Psi4s40dN1 i8Psi4s40dN2 i8Psi4s40dN3 i8Psi4s40dN4 i8Psi4s40dW i8P4s40
  simp only [kernel_zero, hpl_nil, hpl_zero, i13hw_00, i13hw_000]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽41⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s41N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s41N0`. -/
noncomputable def i8Psi4s41dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s41N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s41N0 (i8Psi4s41dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽41⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s41N1 (x : ℝ) : ℝ :=
    (48 - 12 * zeta3 - 2 * π ^ 2) +
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) * hpl [zero] x

/-- The derivative of `i8Psi4s41N1`. -/
noncomputable def i8Psi4s41dN1 (x : ℝ) : ℝ :=
    0 +
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s41N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s41N1 (i8Psi4s41dN1 x) x := by
  unfold i8Psi4s41N1 i8Psi4s41dN1
  exact ((hasDerivAt_const x (48 - 12 * zeta3 - 2 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (16 - 4 * zeta3 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽41⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s41N2 (x : ℝ) : ℝ :=
    (32 + 8 * zeta3 + 4 / 3 * π ^ 2) * hpl [zero] x

/-- The derivative of `i8Psi4s41N2`. -/
noncomputable def i8Psi4s41dN2 (x : ℝ) : ℝ :=
    (32 + 8 * zeta3 + 4 / 3 * π ^ 2) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s41N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s41N2 (i8Psi4s41dN2 x) x := by
  unfold i8Psi4s41N2 i8Psi4s41dN2
  exact ((hasDerivAt_hpl_cons zero [] hx).const_mul (32 + 8 * zeta3 + 4 / 3 * π ^ 2))

/-- The part of `ξ² Ψ₄⁽41⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s41N3 (x : ℝ) : ℝ :=
    (16 - 20 * zeta3 - 10 / 3 * π ^ 2) +
    (16 + 2 * π ^ 2 + 12 * zeta3) * hpl [zero] x

/-- The derivative of `i8Psi4s41N3`. -/
noncomputable def i8Psi4s41dN3 (x : ℝ) : ℝ :=
    0 +
    (16 + 2 * π ^ 2 + 12 * zeta3) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s41N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s41N3 (i8Psi4s41dN3 x) x := by
  unfold i8Psi4s41N3 i8Psi4s41dN3
  exact ((hasDerivAt_const x (16 - 20 * zeta3 - 10 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (16 + 2 * π ^ 2 + 12 * zeta3)))

/-- The part of `ξ² Ψ₄⁽41⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s41N4 (x : ℝ) : ℝ :=
    (-20 - 5 * zeta3 - 5 / 6 * π ^ 2) +
    (8 + 2 * zeta3 + π ^ 2 / 3) * hpl [zero] x

/-- The derivative of `i8Psi4s41N4`. -/
noncomputable def i8Psi4s41dN4 (x : ℝ) : ℝ :=
    0 +
    (8 + 2 * zeta3 + π ^ 2 / 3) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s41N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s41N4 (i8Psi4s41dN4 x) x := by
  unfold i8Psi4s41N4 i8Psi4s41dN4
  exact ((hasDerivAt_const x (-20 - 5 * zeta3 - 5 / 6 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (8 + 2 * zeta3 + π ^ 2 / 3)))

/-- The part of `Ψ₄⁽41⁾` with constant coefficients. -/
noncomputable def i8Psi4s41W (x : ℝ) : ℝ :=
    (-16 + 2 * π ^ 2 + 12 * zeta3) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s41W`. -/
noncomputable def i8Psi4s41dW (x : ℝ) : ℝ :=
    (-16 + 2 * π ^ 2 + 12 * zeta3) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s41W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s41W (i8Psi4s41dW x) x := by
  unfold i8Psi4s41W i8Psi4s41dW
  exact ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-16 + 2 * π ^ 2 + 12 * zeta3))

/-- The piece `Ψ₄⁽41⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s41 (x : ℝ) : ℝ :=
  (i8Psi4s41N0 x + x * i8Psi4s41N1 x + x ^ 2 * i8Psi4s41N2 x + x ^ 3 * i8Psi4s41N3 x +
    x ^ 4 * i8Psi4s41N4 x) / x ^ 2 + i8Psi4s41W x

/-- The derivative of `Ψ₄⁽41⁾`. -/
noncomputable def i8Psi4s41D (x : ℝ) : ℝ :=
  ((i8Psi4s41dN0 x + (i8Psi4s41N1 x + x * i8Psi4s41dN1 x) + (2 * x * i8Psi4s41N2 x +
    x ^ 2 * i8Psi4s41dN2 x) + (3 * x ^ 2 * i8Psi4s41N3 x + x ^ 3 * i8Psi4s41dN3 x) +
    (4 * x ^ 3 * i8Psi4s41N4 x + x ^ 4 * i8Psi4s41dN4 x)) * x ^ 2 - (i8Psi4s41N0 x +
    x * i8Psi4s41N1 x + x ^ 2 * i8Psi4s41N2 x + x ^ 3 * i8Psi4s41N3 x +
    x ^ 4 * i8Psi4s41N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s41dW x

theorem hasDerivAt_i8Psi4s41 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s41 (i8Psi4s41D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s41N0 hx).add (X.mul (hasDerivAt_i8Psi4s41N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s41N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s41N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s41N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s41W hx)
  unfold i8Psi4s41
  refine e.congr_deriv ?_
  unfold i8Psi4s41D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 41 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s41 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 - x) * ((24 +
    ((-1) * π ^ 2) + ((-24) * x) + ((-6) * zeta3) + ((-1) * π ^ 2 * x) +
    ((-6) * x * zeta3)) / (3 + (3 * x)))) * (x / (1 - x))

/-- **`(Ψ₄⁽41⁾)'(ξ) ξ' = p₄⁽41⁾`**, in terms of `ξ`. -/
theorem i8Psi4s41D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s41D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s41 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s41D i8Psi4s41N0 i8Psi4s41N1 i8Psi4s41N2 i8Psi4s41N3 i8Psi4s41N4 i8Psi4s41dN0
    i8Psi4s41dN1 i8Psi4s41dN2 i8Psi4s41dN3 i8Psi4s41dN4 i8Psi4s41dW i8P4s41
  simp only [kernel_zero, hpl_nil, hpl_zero]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽42⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s42N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s42N0`. -/
noncomputable def i8Psi4s42dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s42N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s42N0 (i8Psi4s42dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽42⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s42N1 (x : ℝ) : ℝ :=
    (32 - 4 / 3 * π ^ 2) +
    (32 - 4 / 3 * π ^ 2) * hpl [zero] x +
    (16 - 2 / 3 * π ^ 2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s42N1`. -/
noncomputable def i8Psi4s42dN1 (x : ℝ) : ℝ :=
    0 +
    (32 - 4 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (16 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s42N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s42N1 (i8Psi4s42dN1 x) x := by
  unfold i8Psi4s42N1 i8Psi4s42dN1
  exact (((hasDerivAt_const x (32 - 4 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (32 - 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (16 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽42⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s42N2 (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s42N2`. -/
noncomputable def i8Psi4s42dN2 (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s42N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s42N2 (i8Psi4s42dN2 x) x := by
  unfold i8Psi4s42N2 i8Psi4s42dN2
  exact ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-16 + 2 / 3 * π ^ 2))

/-- The part of `ξ² Ψ₄⁽42⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s42N3 (x : ℝ) : ℝ :=
    (-64 + 8 / 3 * π ^ 2) +
    (64 - 8 / 3 * π ^ 2) * hpl [zero] x +
    (-48 + 2 * π ^ 2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s42N3`. -/
noncomputable def i8Psi4s42dN3 (x : ℝ) : ℝ :=
    0 +
    (64 - 8 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-48 + 2 * π ^ 2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s42N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s42N3 (i8Psi4s42dN3 x) x := by
  unfold i8Psi4s42N3 i8Psi4s42dN3
  exact (((hasDerivAt_const x (-64 + 8 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (64 - 8 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-48 + 2 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽42⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s42N4 (x : ℝ) : ℝ :=
    (-6 + π ^ 2 / 4) +
    (12 - π ^ 2 / 2) * hpl [zero] x +
    (-8 + π ^ 2 / 3) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s42N4`. -/
noncomputable def i8Psi4s42dN4 (x : ℝ) : ℝ :=
    0 +
    (12 - π ^ 2 / 2) * (zero.kernel x * hpl [] x) +
    (-8 + π ^ 2 / 3) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s42N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s42N4 (i8Psi4s42dN4 x) x := by
  unfold i8Psi4s42N4 i8Psi4s42dN4
  exact (((hasDerivAt_const x (-6 + π ^ 2 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (12 - π ^ 2 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-8 + π ^ 2 / 3)))

/-- The part of `Ψ₄⁽42⁾` with constant coefficients. -/
noncomputable def i8Psi4s42W (x : ℝ) : ℝ :=
    (-48 + 2 * π ^ 2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s42W`. -/
noncomputable def i8Psi4s42dW (x : ℝ) : ℝ :=
    (-48 + 2 * π ^ 2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s42W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s42W (i8Psi4s42dW x) x := by
  unfold i8Psi4s42W i8Psi4s42dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-48 + 2 * π ^ 2))

/-- The piece `Ψ₄⁽42⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s42 (x : ℝ) : ℝ :=
  (i8Psi4s42N0 x + x * i8Psi4s42N1 x + x ^ 2 * i8Psi4s42N2 x + x ^ 3 * i8Psi4s42N3 x +
    x ^ 4 * i8Psi4s42N4 x) / x ^ 2 + i8Psi4s42W x

/-- The derivative of `Ψ₄⁽42⁾`. -/
noncomputable def i8Psi4s42D (x : ℝ) : ℝ :=
  ((i8Psi4s42dN0 x + (i8Psi4s42N1 x + x * i8Psi4s42dN1 x) + (2 * x * i8Psi4s42N2 x +
    x ^ 2 * i8Psi4s42dN2 x) + (3 * x ^ 2 * i8Psi4s42N3 x + x ^ 3 * i8Psi4s42dN3 x) +
    (4 * x ^ 3 * i8Psi4s42N4 x + x ^ 4 * i8Psi4s42dN4 x)) * x ^ 2 - (i8Psi4s42N0 x +
    x * i8Psi4s42N1 x + x ^ 2 * i8Psi4s42N2 x + x ^ 3 * i8Psi4s42N3 x +
    x ^ 4 * i8Psi4s42N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s42dW x

theorem hasDerivAt_i8Psi4s42 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s42 (i8Psi4s42D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s42N0 hx).add (X.mul (hasDerivAt_i8Psi4s42N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s42N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s42N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s42N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s42W hx)
  unfold i8Psi4s42
  refine e.congr_deriv ?_
  unfold i8Psi4s42D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 42 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s42 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 - x) * (((24 +
    ((-1) * π ^ 2)) / 6) * hpl [zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽42⁾)'(ξ) ξ' = p₄⁽42⁾`**, in terms of `ξ`. -/
theorem i8Psi4s42D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s42D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s42 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s42D i8Psi4s42N0 i8Psi4s42N1 i8Psi4s42N2 i8Psi4s42N3 i8Psi4s42N4 i8Psi4s42dN0
    i8Psi4s42dN1 i8Psi4s42dN2 i8Psi4s42dN3 i8Psi4s42dN4 i8Psi4s42dW i8P4s42
  simp only [kernel_zero, hpl_nil, hpl_zero, i13hw_00]
  field_simp
  ring

end QED.ThreeLoopD
