/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P7

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 43 to 49

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s43`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s43D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s43`, `QED.ThreeLoopD.i8Psi4s43D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽43⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s43N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s43N0`. -/
noncomputable def i8Psi4s43dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s43N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s43N0 (i8Psi4s43dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽43⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s43N1 (x : ℝ) : ℝ :=
    (2 * π ^ 2) * hpl [negOne] x +
    (2 / 3 * π ^ 2) * hpl [negOne, zero] x +
    (2 / 3 * π ^ 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s43N1`. -/
noncomputable def i8Psi4s43dN1 (x : ℝ) : ℝ :=
    (2 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (2 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s43N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s43N1 (i8Psi4s43dN1 x) x := by
  unfold i8Psi4s43N1 i8Psi4s43dN1
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽43⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s43N2 (x : ℝ) : ℝ :=
    (9 / 2 * π ^ 2) * hpl [negOne] x +
    (-2 * π ^ 2) * hpl [zero] x +
    (-π ^ 2) * hpl [negOne, zero] x +
    (-4 / 3 * π ^ 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s43N2`. -/
noncomputable def i8Psi4s43dN2 (x : ℝ) : ℝ :=
    (9 / 2 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-2 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (-4 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s43N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s43N2 (i8Psi4s43dN2 x) x := by
  unfold i8Psi4s43N2 i8Psi4s43dN2
  exact (((((hasDerivAt_hpl_cons negOne [] hx).const_mul (9 / 2 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽43⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s43N3 (x : ℝ) : ℝ :=
    (-25 / 6 * π ^ 2) +
    (10 / 3 * π ^ 2) * hpl [negOne] x +
    (5 / 3 * π ^ 2) * hpl [zero] x +
    (-2 * π ^ 2) * hpl [negOne, zero] x +
    (-2 * π ^ 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s43N3`. -/
noncomputable def i8Psi4s43dN3 (x : ℝ) : ℝ :=
    0 +
    (10 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (5 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-2 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (-2 * π ^ 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s43N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s43N3 (i8Psi4s43dN3 x) x := by
  unfold i8Psi4s43N3 i8Psi4s43dN3
  exact (((((hasDerivAt_const x (-25 / 6 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (10 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (5 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽43⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s43N4 (x : ℝ) : ℝ :=
    (-π ^ 2 / 2) +
    (5 / 6 * π ^ 2) * hpl [negOne] x +
    (π ^ 2 / 6) * hpl [zero] x +
    (-π ^ 2 / 3) * hpl [negOne, zero] x +
    (-π ^ 2 / 3) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s43N4`. -/
noncomputable def i8Psi4s43dN4 (x : ℝ) : ℝ :=
    0 +
    (5 / 6 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (-π ^ 2 / 3) * (negOne.kernel x * hpl [zero] x) +
    (-π ^ 2 / 3) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s43N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s43N4 (i8Psi4s43dN4 x) x := by
  unfold i8Psi4s43N4 i8Psi4s43dN4
  exact (((((hasDerivAt_const x (-π ^ 2 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (5 / 6 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-π ^ 2 / 3)))

/-- The part of `Ψ₄⁽43⁾` with constant coefficients. -/
noncomputable def i8Psi4s43W (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (-2 * π ^ 2) * hpl [zero, negOne, zero] x +
    (-2 * π ^ 2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s43W`. -/
noncomputable def i8Psi4s43dW (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (-2 * π ^ 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2 * π ^ 2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s43W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s43W (i8Psi4s43dW x) x := by
  unfold i8Psi4s43W i8Psi4s43dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2 * π ^ 2)))

/-- The piece `Ψ₄⁽43⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s43 (x : ℝ) : ℝ :=
  (i8Psi4s43N0 x + x * i8Psi4s43N1 x + x ^ 2 * i8Psi4s43N2 x + x ^ 3 * i8Psi4s43N3 x +
    x ^ 4 * i8Psi4s43N4 x) / x ^ 2 + i8Psi4s43W x

/-- The derivative of `Ψ₄⁽43⁾`. -/
noncomputable def i8Psi4s43D (x : ℝ) : ℝ :=
  ((i8Psi4s43dN0 x + (i8Psi4s43N1 x + x * i8Psi4s43dN1 x) + (2 * x * i8Psi4s43N2 x +
    x ^ 2 * i8Psi4s43dN2 x) + (3 * x ^ 2 * i8Psi4s43N3 x + x ^ 3 * i8Psi4s43dN3 x) +
    (4 * x ^ 3 * i8Psi4s43N4 x + x ^ 4 * i8Psi4s43dN4 x)) * x ^ 2 - (i8Psi4s43N0 x +
    x * i8Psi4s43N1 x + x ^ 2 * i8Psi4s43N2 x + x ^ 3 * i8Psi4s43N3 x +
    x ^ 4 * i8Psi4s43N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s43dW x

theorem hasDerivAt_i8Psi4s43 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s43 (i8Psi4s43D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s43N0 hx).add (X.mul (hasDerivAt_i8Psi4s43N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s43N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s43N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s43N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s43W hx)
  unfold i8Psi4s43
  refine e.congr_deriv ?_
  unfold i8Psi4s43D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 43 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s43 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * ((π ^ 2 / 3) * hpl [negOne] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽43⁾)'(ξ) ξ' = p₄⁽43⁾`**, in terms of `ξ`. -/
theorem i8Psi4s43D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s43D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s43 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s43D i8Psi4s43N0 i8Psi4s43N1 i8Psi4s43N2 i8Psi4s43N3 i8Psi4s43N4 i8Psi4s43dN0
    i8Psi4s43dN1 i8Psi4s43dN2 i8Psi4s43dN3 i8Psi4s43dN4 i8Psi4s43dW i8P4s43
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽44⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s44N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s44N0`. -/
noncomputable def i8Psi4s44dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s44N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s44N0 (i8Psi4s44dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽44⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s44N1 (x : ℝ) : ℝ :=
    (-16) * hpl [negOne, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-16) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s44N1`. -/
noncomputable def i8Psi4s44dN1 (x : ℝ) : ℝ :=
    (-16) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s44N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s44N1 (i8Psi4s44dN1 x) x := by
  unfold i8Psi4s44N1 i8Psi4s44dN1
  exact ((((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽44⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s44N2 (x : ℝ) : ℝ :=
    (13) * hpl [negOne, zero] x +
    (16) * hpl [zero, zero] x +
    (-30) * hpl [negOne, zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s44N2`. -/
noncomputable def i8Psi4s44dN2 (x : ℝ) : ℝ :=
    (13) * (negOne.kernel x * hpl [zero] x) +
    (16) * (zero.kernel x * hpl [zero] x) +
    (-30) * (negOne.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s44N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s44N2 (i8Psi4s44dN2 x) x := by
  unfold i8Psi4s44N2 i8Psi4s44dN2
  exact (((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (13)).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽44⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s44N3 (x : ℝ) : ℝ :=
    (51) +
    (-51) * hpl [zero] x +
    (32) * hpl [negOne, zero] x +
    (22) * hpl [zero, zero] x +
    (-24) * hpl [negOne, zero, zero] x +
    (-32) * hpl [zero, negOne, zero] x +
    (24) * hpl [zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s44N3`. -/
noncomputable def i8Psi4s44dN3 (x : ℝ) : ℝ :=
    0 +
    (-51) * (zero.kernel x * hpl [] x) +
    (32) * (negOne.kernel x * hpl [zero] x) +
    (22) * (zero.kernel x * hpl [zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, zero] x) +
    (-32) * (zero.kernel x * hpl [negOne, zero] x) +
    (24) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s44N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s44N3 (i8Psi4s44dN3 x) x := by
  unfold i8Psi4s44N3 i8Psi4s44dN3
  exact ((((((((hasDerivAt_const x (51)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-51))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (22))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (24)))

/-- The part of `ξ² Ψ₄⁽44⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s44N4 (x : ℝ) : ℝ :=
    (1) +
    (-2) * hpl [zero] x +
    (3) * hpl [negOne, zero] x +
    (1) * hpl [zero, zero] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-6) * hpl [zero, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, zero] x +
    (4) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s44N4`. -/
noncomputable def i8Psi4s44dN4 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x) +
    (3) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-6) * (zero.kernel x * hpl [negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s44N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s44N4 (i8Psi4s44dN4 x) x := by
  unfold i8Psi4s44N4 i8Psi4s44dN4
  exact ((((((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽44⁾` with constant coefficients. -/
noncomputable def i8Psi4s44W (x : ℝ) : ℝ :=
    (8) * hpl [zero, zero, zero] x +
    (24) * hpl [zero, zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s44W`. -/
noncomputable def i8Psi4s44dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, negOne, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s44W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s44W (i8Psi4s44dW x) x := by
  unfold i8Psi4s44W i8Psi4s44dW
  exact ((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (24)))

/-- The piece `Ψ₄⁽44⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s44 (x : ℝ) : ℝ :=
  (i8Psi4s44N0 x + x * i8Psi4s44N1 x + x ^ 2 * i8Psi4s44N2 x + x ^ 3 * i8Psi4s44N3 x +
    x ^ 4 * i8Psi4s44N4 x) / x ^ 2 + i8Psi4s44W x

/-- The derivative of `Ψ₄⁽44⁾`. -/
noncomputable def i8Psi4s44D (x : ℝ) : ℝ :=
  ((i8Psi4s44dN0 x + (i8Psi4s44N1 x + x * i8Psi4s44dN1 x) + (2 * x * i8Psi4s44N2 x +
    x ^ 2 * i8Psi4s44dN2 x) + (3 * x ^ 2 * i8Psi4s44N3 x + x ^ 3 * i8Psi4s44dN3 x) +
    (4 * x ^ 3 * i8Psi4s44N4 x + x ^ 4 * i8Psi4s44dN4 x)) * x ^ 2 - (i8Psi4s44N0 x +
    x * i8Psi4s44N1 x + x ^ 2 * i8Psi4s44N2 x + x ^ 3 * i8Psi4s44N3 x +
    x ^ 4 * i8Psi4s44N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s44dW x

theorem hasDerivAt_i8Psi4s44 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s44 (i8Psi4s44D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s44N0 hx).add (X.mul (hasDerivAt_i8Psi4s44N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s44N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s44N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s44N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s44W hx)
  unfold i8Psi4s44
  refine e.congr_deriv ?_
  unfold i8Psi4s44D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 44 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s44 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * ((-2) * hpl [zero, negOne, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽44⁾)'(ξ) ξ' = p₄⁽44⁾`**, in terms of `ξ`. -/
theorem i8Psi4s44D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s44D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s44 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s44D i8Psi4s44N0 i8Psi4s44N1 i8Psi4s44N2 i8Psi4s44N3 i8Psi4s44N4 i8Psi4s44dN0
    i8Psi4s44dN1 i8Psi4s44dN2 i8Psi4s44dN3 i8Psi4s44dN4 i8Psi4s44dW i8P4s44
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_0m0 hx,
    i13hw_m00 hx, i13hw_00m0 hx, i13hw_0m00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽45⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s45N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s45N0`. -/
noncomputable def i8Psi4s45dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s45N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s45N0 (i8Psi4s45dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽45⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s45N1 (x : ℝ) : ℝ :=
    (24) * hpl [negOne, negOne, zero] x +
    (16) * hpl [negOne, negOne, zero, zero] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (8) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s45N1`. -/
noncomputable def i8Psi4s45dN1 (x : ℝ) : ℝ :=
    (24) * (negOne.kernel x * hpl [negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s45N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s45N1 (i8Psi4s45dN1 x) x := by
  unfold i8Psi4s45N1 i8Psi4s45dN1
  exact (((((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (24)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽45⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s45N2 (x : ℝ) : ℝ :=
    (-44) * hpl [negOne, zero] x +
    (54) * hpl [negOne, negOne, zero] x +
    (36) * hpl [negOne, zero, zero] x +
    (-24) * hpl [zero, negOne, zero] x +
    (-24) * hpl [negOne, negOne, zero, zero] x +
    (-12) * hpl [negOne, zero, negOne, zero] x +
    (-16) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s45N2`. -/
noncomputable def i8Psi4s45dN2 (x : ℝ) : ℝ :=
    (-44) * (negOne.kernel x * hpl [zero] x) +
    (54) * (negOne.kernel x * hpl [negOne, zero] x) +
    (36) * (negOne.kernel x * hpl [zero, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero] x) +
    (-24) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s45N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s45N2 (i8Psi4s45dN2 x) x := by
  unfold i8Psi4s45N2 i8Psi4s45dN2
  exact ((((((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-44)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (54))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽45⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s45N3 (x : ℝ) : ℝ :=
    (-80) +
    (80) * hpl [zero] x +
    (-50) * hpl [negOne, zero] x +
    (-36) * hpl [zero, zero] x +
    (40) * hpl [negOne, negOne, zero] x +
    (40) * hpl [negOne, zero, zero] x +
    (20) * hpl [zero, negOne, zero] x +
    (-48) * hpl [negOne, negOne, zero, zero] x +
    (-24) * hpl [negOne, zero, negOne, zero] x +
    (-24) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s45N3`. -/
noncomputable def i8Psi4s45dN3 (x : ℝ) : ℝ :=
    0 +
    (80) * (zero.kernel x * hpl [] x) +
    (-50) * (negOne.kernel x * hpl [zero] x) +
    (-36) * (zero.kernel x * hpl [zero] x) +
    (40) * (negOne.kernel x * hpl [negOne, zero] x) +
    (40) * (negOne.kernel x * hpl [zero, zero] x) +
    (20) * (zero.kernel x * hpl [negOne, zero] x) +
    (-48) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s45N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s45N3 (i8Psi4s45dN3 x) x := by
  unfold i8Psi4s45N3 i8Psi4s45dN3
  exact ((((((((((hasDerivAt_const x (-80)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (80))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-50))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽45⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s45N4 (x : ℝ) : ℝ :=
    (-2) +
    (4) * hpl [zero] x +
    (-6) * hpl [negOne, zero] x +
    (-2) * hpl [zero, zero] x +
    (10) * hpl [negOne, negOne, zero] x +
    (4) * hpl [negOne, zero, zero] x +
    (2) * hpl [zero, negOne, zero] x +
    (-8) * hpl [negOne, negOne, zero, zero] x +
    (-4) * hpl [negOne, zero, negOne, zero] x +
    (-4) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s45N4`. -/
noncomputable def i8Psi4s45dN4 (x : ℝ) : ℝ :=
    0 +
    (4) * (zero.kernel x * hpl [] x) +
    (-6) * (negOne.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [zero] x) +
    (10) * (negOne.kernel x * hpl [negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s45N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s45N4 (i8Psi4s45dN4 x) x := by
  unfold i8Psi4s45N4 i8Psi4s45dN4
  exact ((((((((((hasDerivAt_const x (-2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽45⁾` with constant coefficients. -/
noncomputable def i8Psi4s45W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x +
    (-48) * hpl [zero, negOne, negOne, zero, zero] x +
    (-24) * hpl [zero, negOne, zero, negOne, zero] x +
    (-24) * hpl [zero, zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s45W`. -/
noncomputable def i8Psi4s45dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-48) * (zero.kernel x * hpl [negOne, negOne, zero, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s45W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s45W (i8Psi4s45dW x) x := by
  unfold i8Psi4s45W i8Psi4s45dW
  exact ((((((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero, zero] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne, zero] hx).const_mul (-24)))

/-- The piece `Ψ₄⁽45⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s45 (x : ℝ) : ℝ :=
  (i8Psi4s45N0 x + x * i8Psi4s45N1 x + x ^ 2 * i8Psi4s45N2 x + x ^ 3 * i8Psi4s45N3 x +
    x ^ 4 * i8Psi4s45N4 x) / x ^ 2 + i8Psi4s45W x

/-- The derivative of `Ψ₄⁽45⁾`. -/
noncomputable def i8Psi4s45D (x : ℝ) : ℝ :=
  ((i8Psi4s45dN0 x + (i8Psi4s45N1 x + x * i8Psi4s45dN1 x) + (2 * x * i8Psi4s45N2 x +
    x ^ 2 * i8Psi4s45dN2 x) + (3 * x ^ 2 * i8Psi4s45N3 x + x ^ 3 * i8Psi4s45dN3 x) +
    (4 * x ^ 3 * i8Psi4s45N4 x + x ^ 4 * i8Psi4s45dN4 x)) * x ^ 2 - (i8Psi4s45N0 x +
    x * i8Psi4s45N1 x + x ^ 2 * i8Psi4s45N2 x + x ^ 3 * i8Psi4s45N3 x +
    x ^ 4 * i8Psi4s45N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s45dW x

theorem hasDerivAt_i8Psi4s45 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s45 (i8Psi4s45D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s45N0 hx).add (X.mul (hasDerivAt_i8Psi4s45N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s45N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s45N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s45N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s45W hx)
  unfold i8Psi4s45
  refine e.congr_deriv ?_
  unfold i8Psi4s45D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 45 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s45 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * (4 * hpl [negOne, negOne, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽45⁾)'(ξ) ξ' = p₄⁽45⁾`**, in terms of `ξ`. -/
theorem i8Psi4s45D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s45D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s45 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s45D i8Psi4s45N0 i8Psi4s45N1 i8Psi4s45N2 i8Psi4s45N3 i8Psi4s45N4 i8Psi4s45dN0
    i8Psi4s45dN1 i8Psi4s45dN2 i8Psi4s45dN3 i8Psi4s45dN4 i8Psi4s45dW i8P4s45
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_0m0 hx,
    i13hw_m00 hx, i13hw_mm0 hx, i13hw_0mm0 hx, i13hw_m0m0 hx, i13hw_mm00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽46⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s46N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s46N0`. -/
noncomputable def i8Psi4s46dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s46N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s46N0 (i8Psi4s46dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽46⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s46N1 (x : ℝ) : ℝ :=
    (12) +
    (12) * hpl [zero] x +
    (12) * hpl [zero, zero] x +
    (12) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s46N1`. -/
noncomputable def i8Psi4s46dN1 (x : ℝ) : ℝ :=
    0 +
    (12) * (zero.kernel x * hpl [] x) +
    (12) * (zero.kernel x * hpl [zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s46N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s46N1 (i8Psi4s46dN1 x) x := by
  unfold i8Psi4s46N1 i8Psi4s46dN1
  exact (((((hasDerivAt_const x (12)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽46⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s46N2 (x : ℝ) : ℝ :=
    (-4) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s46N2`. -/
noncomputable def i8Psi4s46dN2 (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s46N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s46N2 (i8Psi4s46dN2 x) x := by
  unfold i8Psi4s46N2 i8Psi4s46dN2
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-4))

/-- The part of `ξ² Ψ₄⁽46⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s46N3 (x : ℝ) : ℝ :=
    (-28) +
    (28) * hpl [zero] x +
    (-28) * hpl [zero, zero] x +
    (28) * hpl [zero, zero, zero] x +
    (-24) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s46N3`. -/
noncomputable def i8Psi4s46dN3 (x : ℝ) : ℝ :=
    0 +
    (28) * (zero.kernel x * hpl [] x) +
    (-28) * (zero.kernel x * hpl [zero] x) +
    (28) * (zero.kernel x * hpl [zero, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s46N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s46N3 (i8Psi4s46dN3 x) x := by
  unfold i8Psi4s46N3 i8Psi4s46dN3
  exact (((((hasDerivAt_const x (-28)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽46⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s46N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (1) * hpl [zero] x +
    (-2) * hpl [zero, zero] x +
    (4) * hpl [zero, zero, zero] x +
    (-4) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s46N4`. -/
noncomputable def i8Psi4s46dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s46N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s46N4 (i8Psi4s46dN4 x) x := by
  unfold i8Psi4s46N4 i8Psi4s46dN4
  exact (((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽46⁾` with constant coefficients. -/
noncomputable def i8Psi4s46W (x : ℝ) : ℝ :=
    (-24) * hpl [zero, zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s46W`. -/
noncomputable def i8Psi4s46dW (x : ℝ) : ℝ :=
    (-24) * (zero.kernel x * hpl [zero, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s46W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s46W (i8Psi4s46dW x) x := by
  unfold i8Psi4s46W i8Psi4s46dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero, zero] hx).const_mul (-24))

/-- The piece `Ψ₄⁽46⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s46 (x : ℝ) : ℝ :=
  (i8Psi4s46N0 x + x * i8Psi4s46N1 x + x ^ 2 * i8Psi4s46N2 x + x ^ 3 * i8Psi4s46N3 x +
    x ^ 4 * i8Psi4s46N4 x) / x ^ 2 + i8Psi4s46W x

/-- The derivative of `Ψ₄⁽46⁾`. -/
noncomputable def i8Psi4s46D (x : ℝ) : ℝ :=
  ((i8Psi4s46dN0 x + (i8Psi4s46N1 x + x * i8Psi4s46dN1 x) + (2 * x * i8Psi4s46N2 x +
    x ^ 2 * i8Psi4s46dN2 x) + (3 * x ^ 2 * i8Psi4s46N3 x + x ^ 3 * i8Psi4s46dN3 x) +
    (4 * x ^ 3 * i8Psi4s46N4 x + x ^ 4 * i8Psi4s46dN4 x)) * x ^ 2 - (i8Psi4s46N0 x +
    x * i8Psi4s46N1 x + x ^ 2 * i8Psi4s46N2 x + x ^ 3 * i8Psi4s46N3 x +
    x ^ 4 * i8Psi4s46N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s46dW x

theorem hasDerivAt_i8Psi4s46 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s46 (i8Psi4s46D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s46N0 hx).add (X.mul (hasDerivAt_i8Psi4s46N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s46N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s46N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s46N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s46W hx)
  unfold i8Psi4s46
  refine e.congr_deriv ?_
  unfold i8Psi4s46D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 46 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s46 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * (1 * hpl [zero, zero, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽46⁾)'(ξ) ξ' = p₄⁽46⁾`**, in terms of `ξ`. -/
theorem i8Psi4s46D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s46D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s46 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s46D i8Psi4s46N0 i8Psi4s46N1 i8Psi4s46N2 i8Psi4s46N3 i8Psi4s46N4 i8Psi4s46dN0
    i8Psi4s46dN1 i8Psi4s46dN2 i8Psi4s46dN3 i8Psi4s46dN4 i8Psi4s46dW i8P4s46
  simp only [kernel_zero, hpl_nil, hpl_zero, i13hw_00, i13hw_000, i13hw_0000]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽47⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s47N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s47N0`. -/
noncomputable def i8Psi4s47dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s47N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s47N0 (i8Psi4s47dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽47⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s47N1 (x : ℝ) : ℝ :=
    (-12) * hpl [negOne, zero, zero] x +
    (-12) * hpl [negOne, zero, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s47N1`. -/
noncomputable def i8Psi4s47dN1 (x : ℝ) : ℝ :=
    (-12) * (negOne.kernel x * hpl [zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s47N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s47N1 (i8Psi4s47dN1 x) x := by
  unfold i8Psi4s47N1 i8Psi4s47dN1
  exact ((((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12)).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽47⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s47N2 (x : ℝ) : ℝ :=
    (-27) * hpl [negOne, zero, zero] x +
    (12) * hpl [zero, zero, zero] x +
    (18) * hpl [negOne, zero, zero, zero] x +
    (8) * hpl [zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s47N2`. -/
noncomputable def i8Psi4s47dN2 (x : ℝ) : ℝ :=
    (-27) * (negOne.kernel x * hpl [zero, zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero] x) +
    (18) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s47N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s47N2 (i8Psi4s47dN2 x) x := by
  unfold i8Psi4s47N2 i8Psi4s47dN2
  exact (((((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-27)).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽47⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s47N3 (x : ℝ) : ℝ :=
    (45) +
    (-45) * hpl [zero] x +
    (45) * hpl [zero, zero] x +
    (-20) * hpl [negOne, zero, zero] x +
    (-30) * hpl [zero, zero, zero] x +
    (36) * hpl [negOne, zero, zero, zero] x +
    (12) * hpl [zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s47N3`. -/
noncomputable def i8Psi4s47dN3 (x : ℝ) : ℝ :=
    0 +
    (-45) * (zero.kernel x * hpl [] x) +
    (45) * (zero.kernel x * hpl [zero] x) +
    (-20) * (negOne.kernel x * hpl [zero, zero] x) +
    (-30) * (zero.kernel x * hpl [zero, zero] x) +
    (36) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (12) * (zero.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s47N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s47N3 (i8Psi4s47dN3 x) x := by
  unfold i8Psi4s47N3 i8Psi4s47dN3
  exact (((((((hasDerivAt_const x (45)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-45))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (45))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽47⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s47N4 (x : ℝ) : ℝ :=
    (1) +
    (-2) * hpl [zero] x +
    (4) * hpl [zero, zero] x +
    (-5) * hpl [negOne, zero, zero] x +
    (-3) * hpl [zero, zero, zero] x +
    (6) * hpl [negOne, zero, zero, zero] x +
    (2) * hpl [zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s47N4`. -/
noncomputable def i8Psi4s47dN4 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [zero] x) +
    (-5) * (negOne.kernel x * hpl [zero, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero] x) +
    (6) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s47N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s47N4 (i8Psi4s47dN4 x) x := by
  unfold i8Psi4s47N4 i8Psi4s47dN4
  exact (((((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (2)))

/-- The part of `Ψ₄⁽47⁾` with constant coefficients. -/
noncomputable def i8Psi4s47W (x : ℝ) : ℝ :=
    (12) * hpl [zero, zero, zero, zero] x +
    (36) * hpl [zero, negOne, zero, zero, zero] x +
    (12) * hpl [zero, zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s47W`. -/
noncomputable def i8Psi4s47dW (x : ℝ) : ℝ :=
    (12) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (36) * (zero.kernel x * hpl [negOne, zero, zero, zero] x) +
    (12) * (zero.kernel x * hpl [zero, negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s47W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s47W (i8Psi4s47dW x) x := by
  unfold i8Psi4s47W i8Psi4s47dW
  exact ((((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (12)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (12)))

/-- The piece `Ψ₄⁽47⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s47 (x : ℝ) : ℝ :=
  (i8Psi4s47N0 x + x * i8Psi4s47N1 x + x ^ 2 * i8Psi4s47N2 x + x ^ 3 * i8Psi4s47N3 x +
    x ^ 4 * i8Psi4s47N4 x) / x ^ 2 + i8Psi4s47W x

/-- The derivative of `Ψ₄⁽47⁾`. -/
noncomputable def i8Psi4s47D (x : ℝ) : ℝ :=
  ((i8Psi4s47dN0 x + (i8Psi4s47N1 x + x * i8Psi4s47dN1 x) + (2 * x * i8Psi4s47N2 x +
    x ^ 2 * i8Psi4s47dN2 x) + (3 * x ^ 2 * i8Psi4s47N3 x + x ^ 3 * i8Psi4s47dN3 x) +
    (4 * x ^ 3 * i8Psi4s47N4 x + x ^ 4 * i8Psi4s47dN4 x)) * x ^ 2 - (i8Psi4s47N0 x +
    x * i8Psi4s47N1 x + x ^ 2 * i8Psi4s47N2 x + x ^ 3 * i8Psi4s47N3 x +
    x ^ 4 * i8Psi4s47N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s47dW x

theorem hasDerivAt_i8Psi4s47 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s47 (i8Psi4s47D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s47N0 hx).add (X.mul (hasDerivAt_i8Psi4s47N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s47N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s47N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s47N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s47W hx)
  unfold i8Psi4s47
  refine e.congr_deriv ?_
  unfold i8Psi4s47D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 47 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s47 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * ((-2) * hpl [negOne, zero, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽47⁾)'(ξ) ξ' = p₄⁽47⁾`**, in terms of `ξ`. -/
theorem i8Psi4s47D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s47D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s47 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s47D i8Psi4s47N0 i8Psi4s47N1 i8Psi4s47N2 i8Psi4s47N3 i8Psi4s47N4 i8Psi4s47dN0
    i8Psi4s47dN1 i8Psi4s47dN2 i8Psi4s47dN3 i8Psi4s47dN4 i8Psi4s47dW i8P4s47
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_000, i13hw_m00 hx,
    i13hw_0m00 hx, i13hw_m000 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽48⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s48N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s48N0`. -/
noncomputable def i8Psi4s48dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s48N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s48N0 (i8Psi4s48dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽48⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s48N1 (x : ℝ) : ℝ :=
    (-24) * hpl [negOne, zero] x +
    (-16) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s48N1`. -/
noncomputable def i8Psi4s48dN1 (x : ℝ) : ℝ :=
    (-24) * (negOne.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s48N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s48N1 (i8Psi4s48dN1 x) x := by
  unfold i8Psi4s48N1 i8Psi4s48dN1
  exact ((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-24)).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽48⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s48N2 (x : ℝ) : ℝ :=
    (-54) * hpl [negOne, zero] x +
    (24) * hpl [zero, zero] x +
    (24) * hpl [negOne, zero, zero] x +
    (16) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s48N2`. -/
noncomputable def i8Psi4s48dN2 (x : ℝ) : ℝ :=
    (-54) * (negOne.kernel x * hpl [zero] x) +
    (24) * (zero.kernel x * hpl [zero] x) +
    (24) * (negOne.kernel x * hpl [zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s48N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s48N2 (i8Psi4s48dN2 x) x := by
  unfold i8Psi4s48N2 i8Psi4s48dN2
  exact (((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-54)).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽48⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s48N3 (x : ℝ) : ℝ :=
    (-70) +
    (70) * hpl [zero] x +
    (-40) * hpl [negOne, zero] x +
    (-40) * hpl [zero, zero] x +
    (48) * hpl [negOne, zero, zero] x +
    (24) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s48N3`. -/
noncomputable def i8Psi4s48dN3 (x : ℝ) : ℝ :=
    0 +
    (70) * (zero.kernel x * hpl [] x) +
    (-40) * (negOne.kernel x * hpl [zero] x) +
    (-40) * (zero.kernel x * hpl [zero] x) +
    (48) * (negOne.kernel x * hpl [zero, zero] x) +
    (24) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s48N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s48N3 (i8Psi4s48dN3 x) x := by
  unfold i8Psi4s48N3 i8Psi4s48dN3
  exact ((((((hasDerivAt_const x (-70)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (70))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (24)))

/-- The part of `ξ² Ψ₄⁽48⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s48N4 (x : ℝ) : ℝ :=
    (-7 / 2) +
    (7) * hpl [zero] x +
    (-10) * hpl [negOne, zero] x +
    (-4) * hpl [zero, zero] x +
    (8) * hpl [negOne, zero, zero] x +
    (4) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s48N4`. -/
noncomputable def i8Psi4s48dN4 (x : ℝ) : ℝ :=
    0 +
    (7) * (zero.kernel x * hpl [] x) +
    (-10) * (negOne.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s48N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s48N4 (i8Psi4s48dN4 x) x := by
  unfold i8Psi4s48N4 i8Psi4s48dN4
  exact ((((((hasDerivAt_const x (-7 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽48⁾` with constant coefficients. -/
noncomputable def i8Psi4s48W (x : ℝ) : ℝ :=
    (16) * hpl [zero, zero, zero] x +
    (48) * hpl [zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s48W`. -/
noncomputable def i8Psi4s48dW (x : ℝ) : ℝ :=
    (16) * (zero.kernel x * hpl [zero, zero] x) +
    (48) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s48W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s48W (i8Psi4s48dW x) x := by
  unfold i8Psi4s48W i8Psi4s48dW
  exact ((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (24)))

/-- The piece `Ψ₄⁽48⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s48 (x : ℝ) : ℝ :=
  (i8Psi4s48N0 x + x * i8Psi4s48N1 x + x ^ 2 * i8Psi4s48N2 x + x ^ 3 * i8Psi4s48N3 x +
    x ^ 4 * i8Psi4s48N4 x) / x ^ 2 + i8Psi4s48W x

/-- The derivative of `Ψ₄⁽48⁾`. -/
noncomputable def i8Psi4s48D (x : ℝ) : ℝ :=
  ((i8Psi4s48dN0 x + (i8Psi4s48N1 x + x * i8Psi4s48dN1 x) + (2 * x * i8Psi4s48N2 x +
    x ^ 2 * i8Psi4s48dN2 x) + (3 * x ^ 2 * i8Psi4s48N3 x + x ^ 3 * i8Psi4s48dN3 x) +
    (4 * x ^ 3 * i8Psi4s48N4 x + x ^ 4 * i8Psi4s48dN4 x)) * x ^ 2 - (i8Psi4s48N0 x +
    x * i8Psi4s48N1 x + x ^ 2 * i8Psi4s48N2 x + x ^ 3 * i8Psi4s48N3 x +
    x ^ 4 * i8Psi4s48N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s48dW x

theorem hasDerivAt_i8Psi4s48 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s48 (i8Psi4s48D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s48N0 hx).add (X.mul (hasDerivAt_i8Psi4s48N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s48N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s48N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s48N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s48W hx)
  unfold i8Psi4s48
  refine e.congr_deriv ?_
  unfold i8Psi4s48D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 48 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s48 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * ((-4) * hpl [negOne, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽48⁾)'(ξ) ξ' = p₄⁽48⁾`**, in terms of `ξ`. -/
theorem i8Psi4s48D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s48D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s48 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s48D i8Psi4s48N0 i8Psi4s48N1 i8Psi4s48N2 i8Psi4s48N3 i8Psi4s48N4 i8Psi4s48dN0
    i8Psi4s48dN1 i8Psi4s48dN2 i8Psi4s48dN3 i8Psi4s48dN4 i8Psi4s48dW i8P4s48
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_0m0 hx,
    i13hw_m00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽49⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s49N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s49N0`. -/
noncomputable def i8Psi4s49dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s49N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s49N0 (i8Psi4s49dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽49⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s49N1 (x : ℝ) : ℝ :=
    (20) +
    (20) * hpl [zero] x +
    (20) * hpl [zero, zero] x +
    (12) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s49N1`. -/
noncomputable def i8Psi4s49dN1 (x : ℝ) : ℝ :=
    0 +
    (20) * (zero.kernel x * hpl [] x) +
    (20) * (zero.kernel x * hpl [zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s49N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s49N1 (i8Psi4s49dN1 x) x := by
  unfold i8Psi4s49N1 i8Psi4s49dN1
  exact ((((hasDerivAt_const x (20)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽49⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s49N2 (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s49N2`. -/
noncomputable def i8Psi4s49dN2 (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s49N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s49N2 (i8Psi4s49dN2 x) x := by
  unfold i8Psi4s49N2 i8Psi4s49dN2
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-8))

/-- The part of `ξ² Ψ₄⁽49⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s49N3 (x : ℝ) : ℝ :=
    (44) +
    (-44) * hpl [zero] x +
    (44) * hpl [zero, zero] x +
    (-36) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s49N3`. -/
noncomputable def i8Psi4s49dN3 (x : ℝ) : ℝ :=
    0 +
    (-44) * (zero.kernel x * hpl [] x) +
    (44) * (zero.kernel x * hpl [zero] x) +
    (-36) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s49N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s49N3 (i8Psi4s49dN3 x) x := by
  unfold i8Psi4s49N3 i8Psi4s49dN3
  exact ((((hasDerivAt_const x (44)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-44))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (44))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-36)))

/-- The part of `ξ² Ψ₄⁽49⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s49N4 (x : ℝ) : ℝ :=
    (7 / 4) +
    (-7 / 2) * hpl [zero] x +
    (7) * hpl [zero, zero] x +
    (-6) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s49N4`. -/
noncomputable def i8Psi4s49dN4 (x : ℝ) : ℝ :=
    0 +
    (-7 / 2) * (zero.kernel x * hpl [] x) +
    (7) * (zero.kernel x * hpl [zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s49N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s49N4 (i8Psi4s49dN4 x) x := by
  unfold i8Psi4s49N4 i8Psi4s49dN4
  exact ((((hasDerivAt_const x (7 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-6)))

/-- The part of `Ψ₄⁽49⁾` with constant coefficients. -/
noncomputable def i8Psi4s49W (x : ℝ) : ℝ :=
    (-36) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s49W`. -/
noncomputable def i8Psi4s49dW (x : ℝ) : ℝ :=
    (-36) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s49W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s49W (i8Psi4s49dW x) x := by
  unfold i8Psi4s49W i8Psi4s49dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-36))

/-- The piece `Ψ₄⁽49⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s49 (x : ℝ) : ℝ :=
  (i8Psi4s49N0 x + x * i8Psi4s49N1 x + x ^ 2 * i8Psi4s49N2 x + x ^ 3 * i8Psi4s49N3 x +
    x ^ 4 * i8Psi4s49N4 x) / x ^ 2 + i8Psi4s49W x

/-- The derivative of `Ψ₄⁽49⁾`. -/
noncomputable def i8Psi4s49D (x : ℝ) : ℝ :=
  ((i8Psi4s49dN0 x + (i8Psi4s49N1 x + x * i8Psi4s49dN1 x) + (2 * x * i8Psi4s49N2 x +
    x ^ 2 * i8Psi4s49dN2 x) + (3 * x ^ 2 * i8Psi4s49N3 x + x ^ 3 * i8Psi4s49dN3 x) +
    (4 * x ^ 3 * i8Psi4s49N4 x + x ^ 4 * i8Psi4s49dN4 x)) * x ^ 2 - (i8Psi4s49N0 x +
    x * i8Psi4s49N1 x + x ^ 2 * i8Psi4s49N2 x + x ^ 3 * i8Psi4s49N3 x +
    x ^ 4 * i8Psi4s49N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s49dW x

theorem hasDerivAt_i8Psi4s49 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s49 (i8Psi4s49D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s49N0 hx).add (X.mul (hasDerivAt_i8Psi4s49N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s49N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s49N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s49N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s49W hx)
  unfold i8Psi4s49
  refine e.congr_deriv ?_
  unfold i8Psi4s49D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 49 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s49 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * (2 * hpl [zero, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽49⁾)'(ξ) ξ' = p₄⁽49⁾`**, in terms of `ξ`. -/
theorem i8Psi4s49D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s49D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s49 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s49D i8Psi4s49N0 i8Psi4s49N1 i8Psi4s49N2 i8Psi4s49N3 i8Psi4s49N4 i8Psi4s49dN0
    i8Psi4s49dN1 i8Psi4s49dN2 i8Psi4s49dN3 i8Psi4s49dN4 i8Psi4s49dW i8P4s49
  simp only [kernel_zero, hpl_nil, hpl_zero, i13hw_00, i13hw_000]
  field_simp
  ring

end QED.ThreeLoopD
