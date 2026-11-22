/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P3

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 17 to 20

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s17`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s17D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s17`, `QED.ThreeLoopD.i8Psi4s17D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽17⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s17N0 (x : ℝ) : ℝ :=
    (4) * hpl [negOne, negOne, zero, zero] x +
    (2) * hpl [negOne, zero, negOne, zero] x +
    (2) * hpl [negOne, zero, zero, negOne] x

/-- The derivative of `i8Psi4s17N0`. -/
noncomputable def i8Psi4s17dN0 (x : ℝ) : ℝ :=
    (4) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s17N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s17N0 (i8Psi4s17dN0 x) x := by
  unfold i8Psi4s17N0 i8Psi4s17dN0
  exact ((((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽17⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s17N1 (x : ℝ) : ℝ :=
    (2) * hpl [negOne] x +
    (2) * hpl [negOne, zero] x +
    (2) * hpl [zero, negOne] x +
    (4) * hpl [negOne, zero, zero] x +
    (2) * hpl [zero, negOne, zero] x +
    (2) * hpl [zero, zero, negOne] x +
    (16) * hpl [negOne, negOne, zero, zero] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (8) * hpl [negOne, zero, zero, negOne] x

/-- The derivative of `i8Psi4s17N1`. -/
noncomputable def i8Psi4s17dN1 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [negOne] x) +
    (4) * (negOne.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (zero.kernel x * hpl [zero, negOne] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s17N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s17N1 (i8Psi4s17dN1 x) x := by
  unfold i8Psi4s17N1 i8Psi4s17dN1
  exact ((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽17⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s17N2 (x : ℝ) : ℝ :=
    (-15 / 4) * hpl [negOne] x +
    (-2) * hpl [zero] x +
    (15 / 2) * hpl [negOne, zero] x +
    (-2) * hpl [zero, zero] x +
    (-6) * hpl [negOne, zero, zero] x +
    (24) * hpl [negOne, negOne, zero, zero] x +
    (12) * hpl [negOne, zero, negOne, zero] x +
    (12) * hpl [negOne, zero, zero, negOne] x

/-- The derivative of `i8Psi4s17N2`. -/
noncomputable def i8Psi4s17dN2 (x : ℝ) : ℝ :=
    (-15 / 4) * (negOne.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [] x) +
    (15 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [zero] x) +
    (-6) * (negOne.kernel x * hpl [zero, zero] x) +
    (24) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (12) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (12) * (negOne.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s17N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s17N2 (i8Psi4s17dN2 x) x := by
  unfold i8Psi4s17N2 i8Psi4s17dN2
  exact (((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-15 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (15 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽17⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s17N3 (x : ℝ) : ℝ :=
    (85 / 4) +
    (-6) * hpl [negOne] x +
    (-31 / 2) * hpl [zero] x +
    (6) * hpl [negOne, zero] x +
    (6) * hpl [zero, negOne] x +
    (10) * hpl [zero, zero] x +
    (-12) * hpl [negOne, zero, zero] x +
    (-6) * hpl [zero, negOne, zero] x +
    (-6) * hpl [zero, zero, negOne] x +
    (16) * hpl [negOne, negOne, zero, zero] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (8) * hpl [negOne, zero, zero, negOne] x

/-- The derivative of `i8Psi4s17N3`. -/
noncomputable def i8Psi4s17dN3 (x : ℝ) : ℝ :=
    0 +
    (-6) * (negOne.kernel x * hpl [] x) +
    (-31 / 2) * (zero.kernel x * hpl [] x) +
    (6) * (negOne.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [negOne] x) +
    (10) * (zero.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero] x) +
    (-6) * (zero.kernel x * hpl [negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, negOne] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s17N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s17N3 (i8Psi4s17dN3 x) x := by
  unfold i8Psi4s17N3 i8Psi4s17dN3
  exact ((((((((((((hasDerivAt_const x (85 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-31 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽17⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s17N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 4) * hpl [negOne] x +
    (-3 / 4) * hpl [zero] x +
    (1 / 2) * hpl [negOne, zero] x +
    (1 / 2) * hpl [zero, negOne] x +
    (1) * hpl [zero, zero] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-1) * hpl [zero, zero, negOne] x +
    (4) * hpl [negOne, negOne, zero, zero] x +
    (2) * hpl [negOne, zero, negOne, zero] x +
    (2) * hpl [negOne, zero, zero, negOne] x

/-- The derivative of `i8Psi4s17N4`. -/
noncomputable def i8Psi4s17dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 4) * (negOne.kernel x * hpl [] x) +
    (-3 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s17N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s17N4 (i8Psi4s17dN4 x) x := by
  unfold i8Psi4s17N4 i8Psi4s17dN4
  exact ((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (2)))

/-- The part of `Ψ₄⁽17⁾` with constant coefficients. -/
noncomputable def i8Psi4s17W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, zero, zero] x +
    (-12) * hpl [zero, negOne, zero, zero] x +
    (-6) * hpl [zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s17W`. -/
noncomputable def i8Psi4s17dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [zero, zero] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s17W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s17W (i8Psi4s17dW x) x := by
  unfold i8Psi4s17W i8Psi4s17dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-6)))

/-- The piece `Ψ₄⁽17⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s17 (x : ℝ) : ℝ :=
  (i8Psi4s17N0 x + x * i8Psi4s17N1 x + x ^ 2 * i8Psi4s17N2 x + x ^ 3 * i8Psi4s17N3 x +
    x ^ 4 * i8Psi4s17N4 x) / x ^ 2 + i8Psi4s17W x

/-- The derivative of `Ψ₄⁽17⁾`. -/
noncomputable def i8Psi4s17D (x : ℝ) : ℝ :=
  ((i8Psi4s17dN0 x + (i8Psi4s17N1 x + x * i8Psi4s17dN1 x) + (2 * x * i8Psi4s17N2 x +
    x ^ 2 * i8Psi4s17dN2 x) + (3 * x ^ 2 * i8Psi4s17N3 x + x ^ 3 * i8Psi4s17dN3 x) +
    (4 * x ^ 3 * i8Psi4s17N4 x + x ^ 4 * i8Psi4s17dN4 x)) * x ^ 2 - (i8Psi4s17N0 x +
    x * i8Psi4s17N1 x + x ^ 2 * i8Psi4s17N2 x + x ^ 3 * i8Psi4s17N3 x +
    x ^ 4 * i8Psi4s17N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s17dW x

theorem hasDerivAt_i8Psi4s17 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s17 (i8Psi4s17D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s17N0 hx).add (X.mul (hasDerivAt_i8Psi4s17N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s17N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s17N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s17N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s17W hx)
  unfold i8Psi4s17
  refine e.congr_deriv ?_
  unfold i8Psi4s17D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 17 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s17 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((-2) * hpl [negOne, zero, zero] x)) * ((1 +
    x) / (1 - x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽17⁾)'(ξ) ξ' = p₄⁽17⁾`**, in terms of `ξ`. -/
theorem i8Psi4s17D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s17D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s17 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s17D i8Psi4s17N0 i8Psi4s17N1 i8Psi4s17N2 i8Psi4s17N3 i8Psi4s17N4 i8Psi4s17dN0
    i8Psi4s17dN1 i8Psi4s17dN2 i8Psi4s17dN3 i8Psi4s17dN4 i8Psi4s17dW i8P4s17
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_0m0 hx,
    i13hw_m00 hx, i13hw_m00m hx, i13hw_m0m0 hx, i13hw_mm00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽18⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s18N0 (x : ℝ) : ℝ :=
    (8) * hpl [negOne, negOne, zero] x +
    (4) * hpl [negOne, zero, negOne] x

/-- The derivative of `i8Psi4s18N0`. -/
noncomputable def i8Psi4s18dN0 (x : ℝ) : ℝ :=
    (8) * (negOne.kernel x * hpl [negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s18N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s18N0 (i8Psi4s18dN0 x) x := by
  unfold i8Psi4s18N0 i8Psi4s18dN0
  exact (((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽18⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s18N1 (x : ℝ) : ℝ :=
    (4) * hpl [negOne] x +
    (8) * hpl [negOne, zero] x +
    (4) * hpl [zero, negOne] x +
    (32) * hpl [negOne, negOne, zero] x +
    (16) * hpl [negOne, zero, negOne] x

/-- The derivative of `i8Psi4s18N1`. -/
noncomputable def i8Psi4s18dN1 (x : ℝ) : ℝ :=
    (4) * (negOne.kernel x * hpl [] x) +
    (8) * (negOne.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [negOne] x) +
    (32) * (negOne.kernel x * hpl [negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s18N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s18N1 (i8Psi4s18dN1 x) x := by
  unfold i8Psi4s18N1 i8Psi4s18dN1
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽18⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s18N2 (x : ℝ) : ℝ :=
    (15) * hpl [negOne] x +
    (-4) * hpl [zero] x +
    (-12) * hpl [negOne, zero] x +
    (48) * hpl [negOne, negOne, zero] x +
    (24) * hpl [negOne, zero, negOne] x

/-- The derivative of `i8Psi4s18N2`. -/
noncomputable def i8Psi4s18dN2 (x : ℝ) : ℝ :=
    (15) * (negOne.kernel x * hpl [] x) +
    (-4) * (zero.kernel x * hpl [] x) +
    (-12) * (negOne.kernel x * hpl [zero] x) +
    (48) * (negOne.kernel x * hpl [negOne, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s18N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s18N2 (i8Psi4s18dN2 x) x := by
  unfold i8Psi4s18N2 i8Psi4s18dN2
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (15)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (24)))

/-- The part of `ξ² Ψ₄⁽18⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s18N3 (x : ℝ) : ℝ :=
    (-31) +
    (12) * hpl [negOne] x +
    (20) * hpl [zero] x +
    (-24) * hpl [negOne, zero] x +
    (-12) * hpl [zero, negOne] x +
    (32) * hpl [negOne, negOne, zero] x +
    (16) * hpl [negOne, zero, negOne] x

/-- The derivative of `i8Psi4s18N3`. -/
noncomputable def i8Psi4s18dN3 (x : ℝ) : ℝ :=
    0 +
    (12) * (negOne.kernel x * hpl [] x) +
    (20) * (zero.kernel x * hpl [] x) +
    (-24) * (negOne.kernel x * hpl [zero] x) +
    (-12) * (zero.kernel x * hpl [negOne] x) +
    (32) * (negOne.kernel x * hpl [negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s18N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s18N3 (i8Psi4s18dN3 x) x := by
  unfold i8Psi4s18N3 i8Psi4s18dN3
  exact (((((((hasDerivAt_const x (-31)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽18⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s18N4 (x : ℝ) : ℝ :=
    (-3 / 2) +
    (1) * hpl [negOne] x +
    (2) * hpl [zero] x +
    (-4) * hpl [negOne, zero] x +
    (-2) * hpl [zero, negOne] x +
    (8) * hpl [negOne, negOne, zero] x +
    (4) * hpl [negOne, zero, negOne] x

/-- The derivative of `i8Psi4s18N4`. -/
noncomputable def i8Psi4s18dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (negOne.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [negOne] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s18N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s18N4 (i8Psi4s18dN4 x) x := by
  unfold i8Psi4s18N4 i8Psi4s18dN4
  exact (((((((hasDerivAt_const x (-3 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (4)))

/-- The part of `Ψ₄⁽18⁾` with constant coefficients. -/
noncomputable def i8Psi4s18W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero] x +
    (-24) * hpl [zero, negOne, zero] x +
    (-12) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s18W`. -/
noncomputable def i8Psi4s18dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s18W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s18W (i8Psi4s18dW x) x := by
  unfold i8Psi4s18W i8Psi4s18dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-12)))

/-- The piece `Ψ₄⁽18⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s18 (x : ℝ) : ℝ :=
  (i8Psi4s18N0 x + x * i8Psi4s18N1 x + x ^ 2 * i8Psi4s18N2 x + x ^ 3 * i8Psi4s18N3 x +
    x ^ 4 * i8Psi4s18N4 x) / x ^ 2 + i8Psi4s18W x

/-- The derivative of `Ψ₄⁽18⁾`. -/
noncomputable def i8Psi4s18D (x : ℝ) : ℝ :=
  ((i8Psi4s18dN0 x + (i8Psi4s18N1 x + x * i8Psi4s18dN1 x) + (2 * x * i8Psi4s18N2 x +
    x ^ 2 * i8Psi4s18dN2 x) + (3 * x ^ 2 * i8Psi4s18N3 x + x ^ 3 * i8Psi4s18dN3 x) +
    (4 * x ^ 3 * i8Psi4s18N4 x + x ^ 4 * i8Psi4s18dN4 x)) * x ^ 2 - (i8Psi4s18N0 x +
    x * i8Psi4s18N1 x + x ^ 2 * i8Psi4s18N2 x + x ^ 3 * i8Psi4s18N3 x +
    x ^ 4 * i8Psi4s18N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s18dW x

theorem hasDerivAt_i8Psi4s18 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s18 (i8Psi4s18D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s18N0 hx).add (X.mul (hasDerivAt_i8Psi4s18N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s18N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s18N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s18N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s18W hx)
  unfold i8Psi4s18
  refine e.congr_deriv ?_
  unfold i8Psi4s18D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 18 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s18 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((-4) * hpl [negOne, zero] x)) * ((1 + x) / (1 -
    x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽18⁾)'(ξ) ξ' = p₄⁽18⁾`**, in terms of `ξ`. -/
theorem i8Psi4s18D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s18D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s18 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s18D i8Psi4s18N0 i8Psi4s18N1 i8Psi4s18N2 i8Psi4s18N3 i8Psi4s18N4 i8Psi4s18dN0
    i8Psi4s18dN1 i8Psi4s18dN2 i8Psi4s18dN3 i8Psi4s18dN4 i8Psi4s18dW i8P4s18
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_m0m hx, i13hw_mm0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽19⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s19N0 (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [negOne] x +
    (-1) * hpl [negOne, zero] x +
    (-1) * hpl [zero, negOne] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s19N0`. -/
noncomputable def i8Psi4s19dN0 (x : ℝ) : ℝ :=
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s19N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s19N0 (i8Psi4s19dN0 x) x := by
  unfold i8Psi4s19N0 i8Psi4s19dN0
  exact (((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽19⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s19N1 (x : ℝ) : ℝ :=
    (-7 / 2) +
    (-8) * hpl [negOne] x +
    (-3) * hpl [zero] x +
    (-8) * hpl [negOne, zero] x +
    (-8) * hpl [zero, negOne] x +
    (-2) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s19N1`. -/
noncomputable def i8Psi4s19dN1 (x : ℝ) : ℝ :=
    0 +
    (-8) * (negOne.kernel x * hpl [] x) +
    (-3) * (zero.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s19N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s19N1 (i8Psi4s19dN1 x) x := by
  unfold i8Psi4s19N1 i8Psi4s19dN1
  exact (((((((((hasDerivAt_const x (-7 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽19⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s19N2 (x : ℝ) : ℝ :=
    (-15) * hpl [negOne] x +
    (15 / 2) * hpl [zero] x +
    (7) * hpl [zero, zero] x +
    (-12) * hpl [negOne, zero, zero] x

/-- The derivative of `i8Psi4s19N2`. -/
noncomputable def i8Psi4s19dN2 (x : ℝ) : ℝ :=
    (-15) * (negOne.kernel x * hpl [] x) +
    (15 / 2) * (zero.kernel x * hpl [] x) +
    (7) * (zero.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s19N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s19N2 (i8Psi4s19dN2 x) x := by
  unfold i8Psi4s19N2 i8Psi4s19dN2
  exact (((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-15)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (15 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽19⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s19N3 (x : ℝ) : ℝ :=
    (41 / 2) +
    (-8) * hpl [negOne] x +
    (-13) * hpl [zero] x +
    (8) * hpl [negOne, zero] x +
    (8) * hpl [zero, negOne] x +
    (6) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s19N3`. -/
noncomputable def i8Psi4s19dN3 (x : ℝ) : ℝ :=
    0 +
    (-8) * (negOne.kernel x * hpl [] x) +
    (-13) * (zero.kernel x * hpl [] x) +
    (8) * (negOne.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [negOne] x) +
    (6) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s19N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s19N3 (i8Psi4s19dN3 x) x := by
  unfold i8Psi4s19N3 i8Psi4s19dN3
  exact (((((((((hasDerivAt_const x (41 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-13))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽19⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s19N4 (x : ℝ) : ℝ :=
    (3 / 4) +
    (-1 / 2) * hpl [negOne] x +
    (-1) * hpl [zero] x +
    (1) * hpl [negOne, zero] x +
    (1) * hpl [zero, negOne] x +
    (1) * hpl [zero, zero] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s19N4`. -/
noncomputable def i8Psi4s19dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s19N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s19N4 (i8Psi4s19dN4 x) x := by
  unfold i8Psi4s19N4 i8Psi4s19dN4
  exact (((((((((hasDerivAt_const x (3 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽19⁾` with constant coefficients. -/
noncomputable def i8Psi4s19W (x : ℝ) : ℝ :=
    (6) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s19W`. -/
noncomputable def i8Psi4s19dW (x : ℝ) : ℝ :=
    (6) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s19W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s19W (i8Psi4s19dW x) x := by
  unfold i8Psi4s19W i8Psi4s19dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6))

/-- The piece `Ψ₄⁽19⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s19 (x : ℝ) : ℝ :=
  (i8Psi4s19N0 x + x * i8Psi4s19N1 x + x ^ 2 * i8Psi4s19N2 x + x ^ 3 * i8Psi4s19N3 x +
    x ^ 4 * i8Psi4s19N4 x) / x ^ 2 + i8Psi4s19W x

/-- The derivative of `Ψ₄⁽19⁾`. -/
noncomputable def i8Psi4s19D (x : ℝ) : ℝ :=
  ((i8Psi4s19dN0 x + (i8Psi4s19N1 x + x * i8Psi4s19dN1 x) + (2 * x * i8Psi4s19N2 x +
    x ^ 2 * i8Psi4s19dN2 x) + (3 * x ^ 2 * i8Psi4s19N3 x + x ^ 3 * i8Psi4s19dN3 x) +
    (4 * x ^ 3 * i8Psi4s19N4 x + x ^ 4 * i8Psi4s19dN4 x)) * x ^ 2 - (i8Psi4s19N0 x +
    x * i8Psi4s19N1 x + x ^ 2 * i8Psi4s19N2 x + x ^ 3 * i8Psi4s19N3 x +
    x ^ 4 * i8Psi4s19N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s19dW x

theorem hasDerivAt_i8Psi4s19 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s19 (i8Psi4s19D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s19N0 hx).add (X.mul (hasDerivAt_i8Psi4s19N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s19N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s19N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s19N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s19W hx)
  unfold i8Psi4s19
  refine e.congr_deriv ?_
  unfold i8Psi4s19D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 19 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s19 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * (2 * hpl [zero, zero] x)) * ((1 + x) / (1 -
    x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽19⁾)'(ξ) ξ' = p₄⁽19⁾`**, in terms of `ξ`. -/
theorem i8Psi4s19D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s19D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s19 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s19D i8Psi4s19N0 i8Psi4s19N1 i8Psi4s19N2 i8Psi4s19N3 i8Psi4s19N4 i8Psi4s19dN0
    i8Psi4s19dN1 i8Psi4s19dN2 i8Psi4s19dN3 i8Psi4s19dN4 i8Psi4s19dW i8P4s19
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_0m0 hx,
    i13hw_m00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽20⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s20N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s20N0`. -/
noncomputable def i8Psi4s20dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s20N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s20N0 (i8Psi4s20dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽20⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s20N1 (x : ℝ) : ℝ :=
    (50 - π ^ 2) +
    (34 - π ^ 2 / 3) * hpl [zero] x +
    (-12) * hpl [negOne, zero] x +
    (18) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (6) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s20N1`. -/
noncomputable def i8Psi4s20dN1 (x : ℝ) : ℝ :=
    0 +
    (34 - π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (-12) * (negOne.kernel x * hpl [zero] x) +
    (18) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s20N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s20N1 (i8Psi4s20dN1 x) x := by
  unfold i8Psi4s20N1 i8Psi4s20dN1
  exact (((((((hasDerivAt_const x (50 - π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (34 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6)))

/-- The part of `ξ² Ψ₄⁽20⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s20N2 (x : ℝ) : ℝ :=
    (16 + 2 / 3 * π ^ 2) * hpl [zero] x +
    (-27) * hpl [negOne, zero] x +
    (-4 + π ^ 2) * hpl [zero, zero] x +
    (12) * hpl [negOne, zero, zero] x +
    (8) * hpl [zero, negOne, zero] x +
    (-20) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s20N2`. -/
noncomputable def i8Psi4s20dN2 (x : ℝ) : ℝ :=
    (16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-27) * (negOne.kernel x * hpl [zero] x) +
    (-4 + π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (12) * (negOne.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-20) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s20N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s20N2 (i8Psi4s20dN2 x) x := by
  unfold i8Psi4s20N2 i8Psi4s20dN2
  exact (((((((hasDerivAt_hpl_cons zero [] hx).const_mul (16 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-27))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-4 + π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-20)))

/-- The part of `ξ² Ψ₄⁽20⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s20N3 (x : ℝ) : ℝ :=
    (-37 - 5 / 3 * π ^ 2) +
    (53 + π ^ 2) * hpl [zero] x +
    (-20) * hpl [negOne, zero] x +
    (-22) * hpl [zero, zero] x +
    (24) * hpl [negOne, zero, zero] x +
    (12) * hpl [zero, negOne, zero] x +
    (-18) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s20N3`. -/
noncomputable def i8Psi4s20dN3 (x : ℝ) : ℝ :=
    0 +
    (53 + π ^ 2) * (zero.kernel x * hpl [] x) +
    (-20) * (negOne.kernel x * hpl [zero] x) +
    (-22) * (zero.kernel x * hpl [zero] x) +
    (24) * (negOne.kernel x * hpl [zero, zero] x) +
    (12) * (zero.kernel x * hpl [negOne, zero] x) +
    (-18) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s20N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s20N3 (i8Psi4s20dN3 x) x := by
  unfold i8Psi4s20N3 i8Psi4s20dN3
  exact (((((((hasDerivAt_const x (-37 - 5 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (53 + π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-18)))

/-- The part of `ξ² Ψ₄⁽20⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s20N4 (x : ℝ) : ℝ :=
    (-111 / 8 - 5 / 12 * π ^ 2) +
    (47 / 4 + π ^ 2 / 6) * hpl [zero] x +
    (-5) * hpl [negOne, zero] x +
    (-5 / 2) * hpl [zero, zero] x +
    (4) * hpl [negOne, zero, zero] x +
    (2) * hpl [zero, negOne, zero] x +
    (-3) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s20N4`. -/
noncomputable def i8Psi4s20dN4 (x : ℝ) : ℝ :=
    0 +
    (47 / 4 + π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (-5) * (negOne.kernel x * hpl [zero] x) +
    (-5 / 2) * (zero.kernel x * hpl [zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s20N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s20N4 (i8Psi4s20dN4 x) x := by
  unfold i8Psi4s20N4 i8Psi4s20dN4
  exact (((((((hasDerivAt_const x (-111 / 8 - 5 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (47 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-3)))

/-- The part of `Ψ₄⁽20⁾` with constant coefficients. -/
noncomputable def i8Psi4s20W (x : ℝ) : ℝ :=
    (24) * hpl [zero, negOne, zero, zero] x +
    (12) * hpl [zero, zero, negOne, zero] x +
    (-18) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s20W`. -/
noncomputable def i8Psi4s20dW (x : ℝ) : ℝ :=
    (24) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (12) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-18) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s20W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s20W (i8Psi4s20dW x) x := by
  unfold i8Psi4s20W i8Psi4s20dW
  exact ((((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (24)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-18)))

/-- The piece `Ψ₄⁽20⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s20 (x : ℝ) : ℝ :=
  (i8Psi4s20N0 x + x * i8Psi4s20N1 x + x ^ 2 * i8Psi4s20N2 x + x ^ 3 * i8Psi4s20N3 x +
    x ^ 4 * i8Psi4s20N4 x) / x ^ 2 + i8Psi4s20W x

/-- The derivative of `Ψ₄⁽20⁾`. -/
noncomputable def i8Psi4s20D (x : ℝ) : ℝ :=
  ((i8Psi4s20dN0 x + (i8Psi4s20N1 x + x * i8Psi4s20dN1 x) + (2 * x * i8Psi4s20N2 x +
    x ^ 2 * i8Psi4s20dN2 x) + (3 * x ^ 2 * i8Psi4s20N3 x + x ^ 3 * i8Psi4s20dN3 x) +
    (4 * x ^ 3 * i8Psi4s20N4 x + x ^ 4 * i8Psi4s20dN4 x)) * x ^ 2 - (i8Psi4s20N0 x +
    x * i8Psi4s20N1 x + x ^ 2 * i8Psi4s20N2 x + x ^ 3 * i8Psi4s20N3 x +
    x ^ 4 * i8Psi4s20N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s20dW x

theorem hasDerivAt_i8Psi4s20 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s20 (i8Psi4s20D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s20N0 hx).add (X.mul (hasDerivAt_i8Psi4s20N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s20N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s20N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s20N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s20W hx)
  unfold i8Psi4s20
  refine e.congr_deriv ?_
  unfold i8Psi4s20D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 20 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s20 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * i13Be2x x * ((1 + x) / (1 -
    x) * (x / (1 + x)))

/-- **`(Ψ₄⁽20⁾)'(ξ) ξ' = p₄⁽20⁾`**, in terms of `ξ`. -/
theorem i8Psi4s20D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s20D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s20 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s20D i8Psi4s20N0 i8Psi4s20N1 i8Psi4s20N2 i8Psi4s20N3 i8Psi4s20N4 i8Psi4s20dN0
    i8Psi4s20dN1 i8Psi4s20dN2 i8Psi4s20dN3 i8Psi4s20dN4 i8Psi4s20dW i8P4s20 i13Be2x
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_000,
    i13hw_0m0 hx, i13hw_m00 hx, i13_Li₂_neg_eq hx, i13_log_one_add_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
