/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4W

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 0 to 1

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s0`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s0D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s0`, `QED.ThreeLoopD.i8Psi4s0D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽0⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s0N0 (x : ℝ) : ℝ :=
    (-43 / 16) * hpl [negOne] x +
    (11 / 4) * hpl [negOne, negOne] x +
    (-11 / 8) * hpl [zero, negOne] x +
    (-3) * hpl [negOne, negOne, negOne] x +
    (3 / 2) * hpl [negOne, zero, negOne] x +
    (3 / 2) * hpl [zero, negOne, negOne] x +
    (-3 / 4) * hpl [zero, zero, negOne] x +
    (4) * hpl [negOne, negOne, negOne, negOne] x +
    (-2) * hpl [negOne, negOne, zero, negOne] x +
    (-2) * hpl [negOne, zero, negOne, negOne] x +
    (1) * hpl [negOne, zero, zero, negOne] x +
    (-2) * hpl [zero, negOne, negOne, negOne] x +
    (1) * hpl [zero, negOne, zero, negOne] x +
    (1) * hpl [zero, zero, negOne, negOne] x +
    (-1 / 2) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s0N0`. -/
noncomputable def i8Psi4s0dN0 (x : ℝ) : ℝ :=
    (-43 / 16) * (negOne.kernel x * hpl [] x) +
    (11 / 4) * (negOne.kernel x * hpl [negOne] x) +
    (-11 / 8) * (zero.kernel x * hpl [negOne] x) +
    (-3) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (3 / 2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (3 / 2) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-3 / 4) * (zero.kernel x * hpl [zero, negOne] x) +
    (4) * (negOne.kernel x * hpl [negOne, negOne, negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (1) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (1) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s0N0 (i8Psi4s0dN0 x) x := by
  unfold i8Psi4s0N0 i8Psi4s0dN0
  exact ((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-43 / 16)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (11 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-11 / 8))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-1 / 2)))

/-- The part of `ξ² Ψ₄⁽0⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s0N1 (x : ℝ) : ℝ :=
    (85 / 16) +
    (21 / 4) * hpl [negOne] x +
    (-5) * hpl [negOne, negOne] x +
    (5 / 2) * hpl [zero, negOne] x +
    (4) * hpl [negOne, negOne, negOne] x +
    (-2) * hpl [negOne, zero, negOne] x +
    (-2) * hpl [zero, negOne, negOne] x +
    (1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s0N1`. -/
noncomputable def i8Psi4s0dN1 (x : ℝ) : ℝ :=
    0 +
    (21 / 4) * (negOne.kernel x * hpl [] x) +
    (-5) * (negOne.kernel x * hpl [negOne] x) +
    (5 / 2) * (zero.kernel x * hpl [negOne] x) +
    (4) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s0N1 (i8Psi4s0dN1 x) x := by
  unfold i8Psi4s0N1 i8Psi4s0dN1
  exact ((((((((hasDerivAt_const x (85 / 16)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (21 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽0⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s0N2 (x : ℝ) : ℝ :=
    (-1 / 4) * hpl [zero, negOne] x +
    (1) * hpl [zero, negOne, negOne] x +
    (-1 / 2) * hpl [zero, zero, negOne] x +
    (-4) * hpl [zero, negOne, negOne, negOne] x +
    (2) * hpl [zero, negOne, zero, negOne] x +
    (2) * hpl [zero, zero, negOne, negOne] x +
    (-1) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s0N2`. -/
noncomputable def i8Psi4s0dN2 (x : ℝ) : ℝ :=
    (-1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-4) * (zero.kernel x * hpl [negOne, negOne, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (-1) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s0N2 (i8Psi4s0dN2 x) x := by
  unfold i8Psi4s0N2 i8Psi4s0dN2
  exact ((((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 4)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽0⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s0N3 (x : ℝ) : ℝ :=
    (255 / 16) +
    (-21 / 4) * hpl [negOne] x +
    (5) * hpl [negOne, negOne] x +
    (-5 / 2) * hpl [zero, negOne] x +
    (-4) * hpl [negOne, negOne, negOne] x +
    (2) * hpl [negOne, zero, negOne] x +
    (2) * hpl [zero, negOne, negOne] x +
    (-1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s0N3`. -/
noncomputable def i8Psi4s0dN3 (x : ℝ) : ℝ :=
    0 +
    (-21 / 4) * (negOne.kernel x * hpl [] x) +
    (5) * (negOne.kernel x * hpl [negOne] x) +
    (-5 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-4) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s0N3 (i8Psi4s0dN3 x) x := by
  unfold i8Psi4s0N3 i8Psi4s0dN3
  exact ((((((((hasDerivAt_const x (255 / 16)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-21 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽0⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s0N4 (x : ℝ) : ℝ :=
    (-171 / 32) +
    (43 / 16) * hpl [negOne] x +
    (-11 / 4) * hpl [negOne, negOne] x +
    (11 / 8) * hpl [zero, negOne] x +
    (3) * hpl [negOne, negOne, negOne] x +
    (-3 / 2) * hpl [negOne, zero, negOne] x +
    (-3 / 2) * hpl [zero, negOne, negOne] x +
    (3 / 4) * hpl [zero, zero, negOne] x +
    (-4) * hpl [negOne, negOne, negOne, negOne] x +
    (2) * hpl [negOne, negOne, zero, negOne] x +
    (2) * hpl [negOne, zero, negOne, negOne] x +
    (-1) * hpl [negOne, zero, zero, negOne] x +
    (2) * hpl [zero, negOne, negOne, negOne] x +
    (-1) * hpl [zero, negOne, zero, negOne] x +
    (-1) * hpl [zero, zero, negOne, negOne] x +
    (1 / 2) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s0N4`. -/
noncomputable def i8Psi4s0dN4 (x : ℝ) : ℝ :=
    0 +
    (43 / 16) * (negOne.kernel x * hpl [] x) +
    (-11 / 4) * (negOne.kernel x * hpl [negOne] x) +
    (11 / 8) * (zero.kernel x * hpl [negOne] x) +
    (3) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (-3 / 2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-3 / 2) * (zero.kernel x * hpl [negOne, negOne] x) +
    (3 / 4) * (zero.kernel x * hpl [zero, negOne] x) +
    (-4) * (negOne.kernel x * hpl [negOne, negOne, negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s0N4 (i8Psi4s0dN4 x) x := by
  unfold i8Psi4s0N4 i8Psi4s0dN4
  exact ((((((((((((((((hasDerivAt_const x (-171 / 32)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (43 / 16))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-11 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (11 / 8))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (3 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (1 / 2)))

/-- The part of `Ψ₄⁽0⁾` with constant coefficients. -/
noncomputable def i8Psi4s0W (x : ℝ) : ℝ :=
    (1 / 16) * hpl [zero] x +
    (16) * hpl [zero, negOne, negOne, negOne, negOne] x +
    (-8) * hpl [zero, negOne, negOne, zero, negOne] x +
    (-8) * hpl [zero, negOne, zero, negOne, negOne] x +
    (4) * hpl [zero, negOne, zero, zero, negOne] x +
    (-8) * hpl [zero, zero, negOne, negOne, negOne] x +
    (4) * hpl [zero, zero, negOne, zero, negOne] x +
    (4) * hpl [zero, zero, zero, negOne, negOne] x +
    (-2) * hpl [zero, zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s0W`. -/
noncomputable def i8Psi4s0dW (x : ℝ) : ℝ :=
    (1 / 16) * (zero.kernel x * hpl [] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, negOne, negOne] x) +
    (-8) * (zero.kernel x * hpl [negOne, negOne, zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, negOne, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, negOne, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, zero, negOne, negOne] x) +
    (-2) * (zero.kernel x * hpl [zero, zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s0W (i8Psi4s0dW x) x := by
  unfold i8Psi4s0W i8Psi4s0dW
  exact ((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 16)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, negOne] hx).const_mul (-2)))

/-- The piece `Ψ₄⁽0⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s0 (x : ℝ) : ℝ :=
  (i8Psi4s0N0 x + x * i8Psi4s0N1 x + x ^ 2 * i8Psi4s0N2 x + x ^ 3 * i8Psi4s0N3 x +
    x ^ 4 * i8Psi4s0N4 x) / x ^ 2 + i8Psi4s0W x

/-- The derivative of `Ψ₄⁽0⁾`. -/
noncomputable def i8Psi4s0D (x : ℝ) : ℝ :=
  ((i8Psi4s0dN0 x + (i8Psi4s0N1 x + x * i8Psi4s0dN1 x) + (2 * x * i8Psi4s0N2 x +
    x ^ 2 * i8Psi4s0dN2 x) + (3 * x ^ 2 * i8Psi4s0N3 x + x ^ 3 * i8Psi4s0dN3 x) +
    (4 * x ^ 3 * i8Psi4s0N4 x + x ^ 4 * i8Psi4s0dN4 x)) * x ^ 2 - (i8Psi4s0N0 x +
    x * i8Psi4s0N1 x + x ^ 2 * i8Psi4s0N2 x + x ^ 3 * i8Psi4s0N3 x +
    x ^ 4 * i8Psi4s0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s0dW x

theorem hasDerivAt_i8Psi4s0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s0 (i8Psi4s0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s0N0 hx).add (X.mul (hasDerivAt_i8Psi4s0N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s0N3 hx))).add ((X.pow
    4).mul (hasDerivAt_i8Psi4s0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add (hasDerivAt_i8Psi4s0W
    hx)
  unfold i8Psi4s0
  refine e.congr_deriv ?_
  unfold i8Psi4s0D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 0 of `p₄` in `ξ`: from `t B0 A4 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s0 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * (8 * x / (1 + x) - 4 * hpl [negOne] x +
    4 * hpl [negOne, negOne] x - 2 * hpl [zero, negOne] x - 4 * hpl [negOne, negOne, negOne] x +
    2 * hpl [negOne, zero, negOne] x + 2 * hpl [zero, negOne, negOne] x -
    hpl [zero, zero, negOne] x + 8 * hpl [negOne, negOne, negOne, negOne] x -
    4 * hpl [negOne, negOne, zero, negOne] x - 4 * hpl [negOne, zero, negOne, negOne] x +
    2 * hpl [negOne, zero, zero, negOne] x - 4 * hpl [zero, negOne, negOne, negOne] x +
    2 * hpl [zero, negOne, zero, negOne] x + 2 * hpl [zero, zero, negOne, negOne] x -
    hpl [zero, zero, zero, negOne] x))

/-- **`(Ψ₄⁽0⁾)'(ξ) ξ' = p₄⁽0⁾`**, in terms of `ξ`. -/
theorem i8Psi4s0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s0D i8Psi4s0N0 i8Psi4s0N1 i8Psi4s0N2 i8Psi4s0N3 i8Psi4s0N4 i8Psi4s0dN0 i8Psi4s0dN1
    i8Psi4s0dN2 i8Psi4s0dN3 i8Psi4s0dN4 i8Psi4s0dW i8P4s0
  simp only [kernel_zero, kernel_negOne, hpl_nil, i13hw_mm hx, i13hw_m0m hx, i13hw_mmm hx, i8hw_mm0m
    hx, i8hw_mmmm hx, i13hw_0m0m hx, i13hw_m00m hx, i13hw_m0mm hx]
  field_simp
  ring

/-- Chunk 0 of `i8Psi4s1N0`. -/
noncomputable def i8Psi4s1N0c0 (x : ℝ) : ℝ :=
    (-59 / 8) * hpl [negOne] x +
    (8) * hpl [negOne, negOne] x +
    (-11 / 4) * hpl [negOne, zero] x +
    (-27 / 4) * hpl [zero, negOne] x +
    (-10) * hpl [negOne, negOne, negOne] x +
    (3) * hpl [negOne, negOne, zero] x +
    (8) * hpl [negOne, zero, negOne] x +
    (8) * hpl [zero, negOne, negOne] x +
    (-3 / 2) * hpl [zero, negOne, zero] x +
    (-11 / 2) * hpl [zero, zero, negOne] x +
    (-4) * hpl [negOne, negOne, negOne, zero] x +
    (-4) * hpl [negOne, negOne, zero, negOne] x +
    (-4) * hpl [negOne, zero, negOne, negOne] x +
    (2) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [negOne, zero, zero, negOne] x +
    (-4) * hpl [zero, negOne, negOne, negOne] x +
    (2) * hpl [zero, negOne, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, negOne] x +
    (4) * hpl [zero, zero, negOne, negOne] x +
    (-1) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s1N0c0`. -/
noncomputable def i8Psi4s1dN0c0 (x : ℝ) : ℝ :=
    (-59 / 8) * (negOne.kernel x * hpl [] x) +
    (8) * (negOne.kernel x * hpl [negOne] x) +
    (-11 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-27 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-10) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (3) * (negOne.kernel x * hpl [negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-3 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-4) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (-4) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-4) * (zero.kernel x * hpl [negOne, negOne, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s1N0c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N0c0 (i8Psi4s1dN0c0 x) x := by
  unfold i8Psi4s1N0c0 i8Psi4s1dN0c0
  exact (((((((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-59 / 8)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-11 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-27 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-1)))

/-- Chunk 1 of `i8Psi4s1N0`. -/
noncomputable def i8Psi4s1N0c1 (x : ℝ) : ℝ :=
    (-3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s1N0c1`. -/
noncomputable def i8Psi4s1dN0c1 (x : ℝ) : ℝ :=
    (-3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s1N0c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N0c1 (i8Psi4s1dN0c1 x) x := by
  unfold i8Psi4s1N0c1 i8Psi4s1dN0c1
  exact ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3))

/-- The part of `ξ² Ψ₄⁽1⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s1N0 (x : ℝ) : ℝ :=
    i8Psi4s1N0c0 x + i8Psi4s1N0c1 x

/-- The derivative of `i8Psi4s1N0`. -/
noncomputable def i8Psi4s1dN0 (x : ℝ) : ℝ :=
    i8Psi4s1dN0c0 x + i8Psi4s1dN0c1 x

theorem hasDerivAt_i8Psi4s1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N0 (i8Psi4s1dN0 x) x := by
  unfold i8Psi4s1N0 i8Psi4s1dN0
  exact ((hasDerivAt_i8Psi4s1N0c0 hx).add (hasDerivAt_i8Psi4s1N0c1 hx))

/-- Chunk 0 of `i8Psi4s1N1`. -/
noncomputable def i8Psi4s1N1c0 (x : ℝ) : ℝ :=
    (111 / 8) +
    (-8) * hpl [negOne] x +
    (21 / 4) * hpl [zero] x +
    (10) * hpl [negOne, negOne] x +
    (-11) * hpl [negOne, zero] x +
    (-16) * hpl [zero, negOne] x +
    (-16) * hpl [negOne, negOne, negOne] x +
    (12) * hpl [negOne, negOne, zero] x +
    (20) * hpl [negOne, zero, negOne] x +
    (20) * hpl [zero, negOne, negOne] x +
    (-6) * hpl [zero, negOne, zero] x +
    (-16) * hpl [zero, zero, negOne] x +
    (-16) * hpl [negOne, negOne, negOne, zero] x +
    (-16) * hpl [negOne, negOne, zero, negOne] x +
    (-16) * hpl [negOne, zero, negOne, negOne] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (16) * hpl [negOne, zero, zero, negOne] x +
    (-16) * hpl [zero, negOne, negOne, negOne] x +
    (8) * hpl [zero, negOne, negOne, zero] x +
    (16) * hpl [zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s1N1c0`. -/
noncomputable def i8Psi4s1dN1c0 (x : ℝ) : ℝ :=
    0 +
    (-8) * (negOne.kernel x * hpl [] x) +
    (21 / 4) * (zero.kernel x * hpl [] x) +
    (10) * (negOne.kernel x * hpl [negOne] x) +
    (-11) * (negOne.kernel x * hpl [zero] x) +
    (-16) * (zero.kernel x * hpl [negOne] x) +
    (-16) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (12) * (negOne.kernel x * hpl [negOne, zero] x) +
    (20) * (negOne.kernel x * hpl [zero, negOne] x) +
    (20) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-6) * (zero.kernel x * hpl [negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, negOne] x) +
    (-16) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-16) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (-16) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-16) * (zero.kernel x * hpl [negOne, negOne, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s1N1c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N1c0 (i8Psi4s1dN1c0 x) x := by
  unfold i8Psi4s1N1c0 i8Psi4s1dN1c0
  exact ((((((((((((((((((((hasDerivAt_const x (111 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (21 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (16)))

/-- Chunk 1 of `i8Psi4s1N1`. -/
noncomputable def i8Psi4s1N1c1 (x : ℝ) : ℝ :=
    (16) * hpl [zero, zero, negOne, negOne] x +
    (-4) * hpl [zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s1N1c1`. -/
noncomputable def i8Psi4s1dN1c1 (x : ℝ) : ℝ :=
    (16) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s1N1c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N1c1 (i8Psi4s1dN1c1 x) x := by
  unfold i8Psi4s1N1c1 i8Psi4s1dN1c1
  exact ((((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽1⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s1N1 (x : ℝ) : ℝ :=
    i8Psi4s1N1c0 x + i8Psi4s1N1c1 x

/-- The derivative of `i8Psi4s1N1`. -/
noncomputable def i8Psi4s1dN1 (x : ℝ) : ℝ :=
    i8Psi4s1dN1c0 x + i8Psi4s1dN1c1 x

theorem hasDerivAt_i8Psi4s1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N1 (i8Psi4s1dN1 x) x := by
  unfold i8Psi4s1N1 i8Psi4s1dN1
  exact ((hasDerivAt_i8Psi4s1N1c0 hx).add (hasDerivAt_i8Psi4s1N1c1 hx))

/-- The part of `ξ² Ψ₄⁽1⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s1N2 (x : ℝ) : ℝ :=
    (133 / 8) * hpl [zero] x +
    (-33 / 2) * hpl [negOne, zero] x +
    (-18) * hpl [zero, negOne] x +
    (18) * hpl [negOne, negOne, zero] x +
    (18) * hpl [negOne, zero, negOne] x +
    (22) * hpl [zero, negOne, negOne] x +
    (-9) * hpl [zero, negOne, zero] x +
    (-20) * hpl [zero, zero, negOne] x +
    (-24) * hpl [negOne, negOne, negOne, zero] x +
    (-24) * hpl [negOne, negOne, zero, negOne] x +
    (-24) * hpl [negOne, zero, negOne, negOne] x +
    (12) * hpl [negOne, zero, negOne, zero] x +
    (24) * hpl [negOne, zero, zero, negOne] x +
    (-32) * hpl [zero, negOne, negOne, negOne] x +
    (12) * hpl [zero, negOne, negOne, zero] x +
    (28) * hpl [zero, negOne, zero, negOne] x +
    (28) * hpl [zero, zero, negOne, negOne] x +
    (-6) * hpl [zero, zero, negOne, zero] x +
    (-20) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s1N2`. -/
noncomputable def i8Psi4s1dN2 (x : ℝ) : ℝ :=
    (133 / 8) * (zero.kernel x * hpl [] x) +
    (-33 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-18) * (zero.kernel x * hpl [negOne] x) +
    (18) * (negOne.kernel x * hpl [negOne, zero] x) +
    (18) * (negOne.kernel x * hpl [zero, negOne] x) +
    (22) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-9) * (zero.kernel x * hpl [negOne, zero] x) +
    (-20) * (zero.kernel x * hpl [zero, negOne] x) +
    (-24) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-24) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (-24) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (12) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-32) * (zero.kernel x * hpl [negOne, negOne, negOne] x) +
    (12) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (28) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (28) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (-6) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-20) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N2 (i8Psi4s1dN2 x) x := by
  unfold i8Psi4s1N2 i8Psi4s1dN2
  exact ((((((((((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (133 / 8)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-33 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (22))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-9))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-20)))

/-- Chunk 0 of `i8Psi4s1N3`. -/
noncomputable def i8Psi4s1N3c0 (x : ℝ) : ℝ :=
    (-7 / 8) +
    (8) * hpl [negOne] x +
    (65 / 4) * hpl [zero] x +
    (-10) * hpl [negOne, negOne] x +
    (-11) * hpl [negOne, zero] x +
    (-6) * hpl [zero, negOne] x +
    (16) * hpl [negOne, negOne, negOne] x +
    (12) * hpl [negOne, negOne, zero] x +
    (4) * hpl [negOne, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne] x +
    (-6) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne] x +
    (-16) * hpl [negOne, negOne, negOne, zero] x +
    (-16) * hpl [negOne, negOne, zero, negOne] x +
    (-16) * hpl [negOne, zero, negOne, negOne] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (16) * hpl [negOne, zero, zero, negOne] x +
    (-16) * hpl [zero, negOne, negOne, negOne] x +
    (8) * hpl [zero, negOne, negOne, zero] x +
    (16) * hpl [zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s1N3c0`. -/
noncomputable def i8Psi4s1dN3c0 (x : ℝ) : ℝ :=
    0 +
    (8) * (negOne.kernel x * hpl [] x) +
    (65 / 4) * (zero.kernel x * hpl [] x) +
    (-10) * (negOne.kernel x * hpl [negOne] x) +
    (-11) * (negOne.kernel x * hpl [zero] x) +
    (-6) * (zero.kernel x * hpl [negOne] x) +
    (16) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (12) * (negOne.kernel x * hpl [negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-6) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne] x) +
    (-16) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-16) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (-16) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-16) * (zero.kernel x * hpl [negOne, negOne, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s1N3c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N3c0 (i8Psi4s1dN3c0 x) x := by
  unfold i8Psi4s1N3c0 i8Psi4s1dN3c0
  exact ((((((((((((((((((((hasDerivAt_const x (-7 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (65 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (16)))

/-- Chunk 1 of `i8Psi4s1N3`. -/
noncomputable def i8Psi4s1N3c1 (x : ℝ) : ℝ :=
    (16) * hpl [zero, zero, negOne, negOne] x +
    (-4) * hpl [zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s1N3c1`. -/
noncomputable def i8Psi4s1dN3c1 (x : ℝ) : ℝ :=
    (16) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s1N3c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N3c1 (i8Psi4s1dN3c1 x) x := by
  unfold i8Psi4s1N3c1 i8Psi4s1dN3c1
  exact ((((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽1⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s1N3 (x : ℝ) : ℝ :=
    i8Psi4s1N3c0 x + i8Psi4s1N3c1 x

/-- The derivative of `i8Psi4s1N3`. -/
noncomputable def i8Psi4s1dN3 (x : ℝ) : ℝ :=
    i8Psi4s1dN3c0 x + i8Psi4s1dN3c1 x

theorem hasDerivAt_i8Psi4s1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N3 (i8Psi4s1dN3 x) x := by
  unfold i8Psi4s1N3 i8Psi4s1dN3
  exact ((hasDerivAt_i8Psi4s1N3c0 hx).add (hasDerivAt_i8Psi4s1N3c1 hx))

/-- Chunk 0 of `i8Psi4s1N4`. -/
noncomputable def i8Psi4s1N4c0 (x : ℝ) : ℝ :=
    (-115 / 8) +
    (59 / 8) * hpl [negOne] x +
    (43 / 8) * hpl [zero] x +
    (-8) * hpl [negOne, negOne] x +
    (-11 / 4) * hpl [negOne, zero] x +
    (5 / 4) * hpl [zero, negOne] x +
    (10) * hpl [negOne, negOne, negOne] x +
    (3) * hpl [negOne, negOne, zero] x +
    (-2) * hpl [negOne, zero, negOne] x +
    (-2) * hpl [zero, negOne, negOne] x +
    (-3 / 2) * hpl [zero, negOne, zero] x +
    (-1 / 2) * hpl [zero, zero, negOne] x +
    (-4) * hpl [negOne, negOne, negOne, zero] x +
    (-4) * hpl [negOne, negOne, zero, negOne] x +
    (-4) * hpl [negOne, zero, negOne, negOne] x +
    (2) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [negOne, zero, zero, negOne] x +
    (-4) * hpl [zero, negOne, negOne, negOne] x +
    (2) * hpl [zero, negOne, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s1N4c0`. -/
noncomputable def i8Psi4s1dN4c0 (x : ℝ) : ℝ :=
    0 +
    (59 / 8) * (negOne.kernel x * hpl [] x) +
    (43 / 8) * (zero.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [negOne] x) +
    (-11 / 4) * (negOne.kernel x * hpl [zero] x) +
    (5 / 4) * (zero.kernel x * hpl [negOne] x) +
    (10) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (3) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-3 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-4) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [negOne, zero, negOne] x) +
    (-4) * (negOne.kernel x * hpl [zero, negOne, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-4) * (zero.kernel x * hpl [negOne, negOne, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s1N4c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N4c0 (i8Psi4s1dN4c0 x) x := by
  unfold i8Psi4s1N4c0 i8Psi4s1dN4c0
  exact ((((((((((((((((((((hasDerivAt_const x (-115 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (59 / 8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (43 / 8))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-11 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (5 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (4)))

/-- Chunk 1 of `i8Psi4s1N4`. -/
noncomputable def i8Psi4s1N4c1 (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero, negOne, negOne] x +
    (-1) * hpl [zero, zero, negOne, zero] x +
    (-3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s1N4c1`. -/
noncomputable def i8Psi4s1dN4c1 (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s1N4c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N4c1 (i8Psi4s1dN4c1 x) x := by
  unfold i8Psi4s1N4c1 i8Psi4s1dN4c1
  exact ((((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3)))

/-- The part of `ξ² Ψ₄⁽1⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s1N4 (x : ℝ) : ℝ :=
    i8Psi4s1N4c0 x + i8Psi4s1N4c1 x

/-- The derivative of `i8Psi4s1N4`. -/
noncomputable def i8Psi4s1dN4 (x : ℝ) : ℝ :=
    i8Psi4s1dN4c0 x + i8Psi4s1dN4c1 x

theorem hasDerivAt_i8Psi4s1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1N4 (i8Psi4s1dN4 x) x := by
  unfold i8Psi4s1N4 i8Psi4s1dN4
  exact ((hasDerivAt_i8Psi4s1N4c0 hx).add (hasDerivAt_i8Psi4s1N4c1 hx))

/-- The part of `Ψ₄⁽1⁾` with constant coefficients. -/
noncomputable def i8Psi4s1W (x : ℝ) : ℝ :=
    (1 / 4) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s1W`. -/
noncomputable def i8Psi4s1dW (x : ℝ) : ℝ :=
    (1 / 4) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1W (i8Psi4s1dW x) x := by
  unfold i8Psi4s1W i8Psi4s1dW
  exact ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 4))

/-- The piece `Ψ₄⁽1⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s1 (x : ℝ) : ℝ :=
  (i8Psi4s1N0 x + x * i8Psi4s1N1 x + x ^ 2 * i8Psi4s1N2 x + x ^ 3 * i8Psi4s1N3 x +
    x ^ 4 * i8Psi4s1N4 x) / x ^ 2 + i8Psi4s1W x

/-- The derivative of `Ψ₄⁽1⁾`. -/
noncomputable def i8Psi4s1D (x : ℝ) : ℝ :=
  ((i8Psi4s1dN0 x + (i8Psi4s1N1 x + x * i8Psi4s1dN1 x) + (2 * x * i8Psi4s1N2 x +
    x ^ 2 * i8Psi4s1dN2 x) + (3 * x ^ 2 * i8Psi4s1N3 x + x ^ 3 * i8Psi4s1dN3 x) +
    (4 * x ^ 3 * i8Psi4s1N4 x + x ^ 4 * i8Psi4s1dN4 x)) * x ^ 2 - (i8Psi4s1N0 x +
    x * i8Psi4s1N1 x + x ^ 2 * i8Psi4s1N2 x + x ^ 3 * i8Psi4s1N3 x +
    x ^ 4 * i8Psi4s1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s1dW x

theorem hasDerivAt_i8Psi4s1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s1 (i8Psi4s1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s1N0 hx).add (X.mul (hasDerivAt_i8Psi4s1N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s1N3 hx))).add ((X.pow
    4).mul (hasDerivAt_i8Psi4s1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add (hasDerivAt_i8Psi4s1W
    hx)
  unfold i8Psi4s1
  refine e.congr_deriv ?_
  unfold i8Psi4s1D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 1 of `p₄` in `ξ`: from `t B1 A3 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s1 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 - x) * (4 * x / (1 +
    x) - 2 * hpl [negOne] x + 2 * hpl [negOne, negOne] x - hpl [zero, negOne] x -
    4 * hpl [negOne, negOne, negOne] x + 2 * hpl [negOne, zero, negOne] x +
    2 * hpl [zero, negOne, negOne] x - hpl [zero, zero, negOne] x))

/-- **`(Ψ₄⁽1⁾)'(ξ) ξ' = p₄⁽1⁾`**, in terms of `ξ`. -/
theorem i8Psi4s1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s1D i8Psi4s1N0 i8Psi4s1N1 i8Psi4s1N2 i8Psi4s1N3 i8Psi4s1N4 i8Psi4s1dN0 i8Psi4s1dN1
    i8Psi4s1dN2 i8Psi4s1dN3 i8Psi4s1dN4 i8Psi4s1dW i8Psi4s1N0c0 i8Psi4s1dN0c0 i8Psi4s1N0c1
    i8Psi4s1dN0c1 i8Psi4s1N1c0 i8Psi4s1dN1c0 i8Psi4s1N1c1 i8Psi4s1dN1c1 i8Psi4s1N3c0 i8Psi4s1dN3c0
    i8Psi4s1N3c1 i8Psi4s1dN3c1 i8Psi4s1N4c0 i8Psi4s1dN4c0 i8Psi4s1N4c1 i8Psi4s1dN4c1 i8P4s1
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_mm hx, i13hw_0m0 hx,
    i13hw_m0m hx, i13hw_mm0 hx, i13hw_mmm hx, i8hw_mm0m hx, i13hw_00m0 hx, i13hw_0m0m hx, i13hw_0mm0
    hx, i13hw_m00m hx, i13hw_m0m0 hx, i13hw_m0mm hx, i13hw_mmm0 hx]
  field_simp
  ring

end QED.ThreeLoopD
