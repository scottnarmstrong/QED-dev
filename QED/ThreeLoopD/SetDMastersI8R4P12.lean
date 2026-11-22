/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P11

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 67 to 71

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s67`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s67D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s67`, `QED.ThreeLoopD.i8Psi4s67D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽67⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s67N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s67N0`. -/
noncomputable def i8Psi4s67dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s67N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s67N0 (i8Psi4s67dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽67⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s67N1 (x : ℝ) : ℝ :=
    (16) +
    (16) * hpl [zero] x +
    (8) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s67N1`. -/
noncomputable def i8Psi4s67dN1 (x : ℝ) : ℝ :=
    0 +
    (16) * (zero.kernel x * hpl [] x) +
    (8) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s67N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s67N1 (i8Psi4s67dN1 x) x := by
  unfold i8Psi4s67N1 i8Psi4s67dN1
  exact (((hasDerivAt_const x (16)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽67⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s67N2 (x : ℝ) : ℝ :=
    (8) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s67N2`. -/
noncomputable def i8Psi4s67dN2 (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s67N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s67N2 (i8Psi4s67dN2 x) x := by
  unfold i8Psi4s67N2 i8Psi4s67dN2
  exact ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8))

/-- The part of `ξ² Ψ₄⁽67⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s67N3 (x : ℝ) : ℝ :=
    (8) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s67N3`. -/
noncomputable def i8Psi4s67dN3 (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s67N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s67N3 (i8Psi4s67dN3 x) x := by
  unfold i8Psi4s67N3 i8Psi4s67dN3
  exact ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8))

/-- The part of `ξ² Ψ₄⁽67⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s67N4 (x : ℝ) : ℝ :=
    (3) +
    (-6) * hpl [zero] x +
    (4) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s67N4`. -/
noncomputable def i8Psi4s67dN4 (x : ℝ) : ℝ :=
    0 +
    (-6) * (zero.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s67N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s67N4 (i8Psi4s67dN4 x) x := by
  unfold i8Psi4s67N4 i8Psi4s67dN4
  exact (((hasDerivAt_const x (3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽67⁾` with constant coefficients. -/
noncomputable def i8Psi4s67W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s67W`. -/
noncomputable def i8Psi4s67dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s67W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s67W (i8Psi4s67dW x) x := by
  unfold i8Psi4s67W i8Psi4s67dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-8))

/-- The piece `Ψ₄⁽67⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s67 (x : ℝ) : ℝ :=
  (i8Psi4s67N0 x + x * i8Psi4s67N1 x + x ^ 2 * i8Psi4s67N2 x + x ^ 3 * i8Psi4s67N3 x +
    x ^ 4 * i8Psi4s67N4 x) / x ^ 2 + i8Psi4s67W x

/-- The derivative of `Ψ₄⁽67⁾`. -/
noncomputable def i8Psi4s67D (x : ℝ) : ℝ :=
  ((i8Psi4s67dN0 x + (i8Psi4s67N1 x + x * i8Psi4s67dN1 x) + (2 * x * i8Psi4s67N2 x +
    x ^ 2 * i8Psi4s67dN2 x) + (3 * x ^ 2 * i8Psi4s67N3 x + x ^ 3 * i8Psi4s67dN3 x) +
    (4 * x ^ 3 * i8Psi4s67N4 x + x ^ 4 * i8Psi4s67dN4 x)) * x ^ 2 - (i8Psi4s67N0 x +
    x * i8Psi4s67N1 x + x ^ 2 * i8Psi4s67N2 x + x ^ 3 * i8Psi4s67N3 x +
    x ^ 4 * i8Psi4s67N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s67dW x

theorem hasDerivAt_i8Psi4s67 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s67 (i8Psi4s67D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s67N0 hx).add (X.mul (hasDerivAt_i8Psi4s67N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s67N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s67N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s67N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s67W hx)
  unfold i8Psi4s67
  refine e.congr_deriv ?_
  unfold i8Psi4s67D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 67 of `p₄` in `ξ`: from `t B1 A2 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s67 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * (2 * x / (1 + x)))

/-- **`(Ψ₄⁽67⁾)'(ξ) ξ' = p₄⁽67⁾`**, in terms of `ξ`. -/
theorem i8Psi4s67D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s67D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s67 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s67D i8Psi4s67N0 i8Psi4s67N1 i8Psi4s67N2 i8Psi4s67N3 i8Psi4s67N4 i8Psi4s67dN0
    i8Psi4s67dN1 i8Psi4s67dN2 i8Psi4s67dN3 i8Psi4s67dN4 i8Psi4s67dW i8P4s67
  simp only [kernel_zero, hpl_nil, hpl_zero, i13hw_00]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽68⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s68N0 (x : ℝ) : ℝ :=
    (-3 / 2) * hpl [negOne] x +
    (-3) * hpl [negOne, zero] x +
    (-3) * hpl [zero, negOne] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s68N0`. -/
noncomputable def i8Psi4s68dN0 (x : ℝ) : ℝ :=
    (-3 / 2) * (negOne.kernel x * hpl [] x) +
    (-3) * (negOne.kernel x * hpl [zero] x) +
    (-3) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s68N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s68N0 (i8Psi4s68dN0 x) x := by
  unfold i8Psi4s68N0 i8Psi4s68dN0
  exact (((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽68⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s68N1 (x : ℝ) : ℝ :=
    (-13 / 2) +
    (-8) * hpl [negOne] x +
    (-5) * hpl [zero] x +
    (-8) * hpl [negOne, zero] x +
    (-8) * hpl [zero, negOne] x +
    (-2) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s68N1`. -/
noncomputable def i8Psi4s68dN1 (x : ℝ) : ℝ :=
    0 +
    (-8) * (negOne.kernel x * hpl [] x) +
    (-5) * (zero.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s68N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s68N1 (i8Psi4s68dN1 x) x := by
  unfold i8Psi4s68N1 i8Psi4s68dN1
  exact (((((((((hasDerivAt_const x (-13 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽68⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s68N2 (x : ℝ) : ℝ :=
    (-13) * hpl [negOne] x +
    (13 / 2) * hpl [zero] x +
    (5) * hpl [zero, zero] x +
    (-12) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s68N2`. -/
noncomputable def i8Psi4s68dN2 (x : ℝ) : ℝ :=
    (-13) * (negOne.kernel x * hpl [] x) +
    (13 / 2) * (zero.kernel x * hpl [] x) +
    (5) * (zero.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s68N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s68N2 (i8Psi4s68dN2 x) x := by
  unfold i8Psi4s68N2 i8Psi4s68dN2
  exact (((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-13)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (13 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽68⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s68N3 (x : ℝ) : ℝ :=
    (35 / 2) +
    (-8) * hpl [negOne] x +
    (-11) * hpl [zero] x +
    (8) * hpl [negOne, zero] x +
    (8) * hpl [zero, negOne] x +
    (6) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s68N3`. -/
noncomputable def i8Psi4s68dN3 (x : ℝ) : ℝ :=
    0 +
    (-8) * (negOne.kernel x * hpl [] x) +
    (-11) * (zero.kernel x * hpl [] x) +
    (8) * (negOne.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [negOne] x) +
    (6) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s68N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s68N3 (i8Psi4s68dN3 x) x := by
  unfold i8Psi4s68N3 i8Psi4s68dN3
  exact (((((((((hasDerivAt_const x (35 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽68⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s68N4 (x : ℝ) : ℝ :=
    (7 / 4) +
    (-3 / 2) * hpl [negOne] x +
    (-2) * hpl [zero] x +
    (3) * hpl [negOne, zero] x +
    (3) * hpl [zero, negOne] x +
    (1) * hpl [zero, zero] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s68N4`. -/
noncomputable def i8Psi4s68dN4 (x : ℝ) : ℝ :=
    0 +
    (-3 / 2) * (negOne.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [] x) +
    (3) * (negOne.kernel x * hpl [zero] x) +
    (3) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s68N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s68N4 (i8Psi4s68dN4 x) x := by
  unfold i8Psi4s68N4 i8Psi4s68dN4
  exact (((((((((hasDerivAt_const x (7 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽68⁾` with constant coefficients. -/
noncomputable def i8Psi4s68W (x : ℝ) : ℝ :=
    (6) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s68W`. -/
noncomputable def i8Psi4s68dW (x : ℝ) : ℝ :=
    (6) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s68W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s68W (i8Psi4s68dW x) x := by
  unfold i8Psi4s68W i8Psi4s68dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6))

/-- The piece `Ψ₄⁽68⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s68 (x : ℝ) : ℝ :=
  (i8Psi4s68N0 x + x * i8Psi4s68N1 x + x ^ 2 * i8Psi4s68N2 x + x ^ 3 * i8Psi4s68N3 x +
    x ^ 4 * i8Psi4s68N4 x) / x ^ 2 + i8Psi4s68W x

/-- The derivative of `Ψ₄⁽68⁾`. -/
noncomputable def i8Psi4s68D (x : ℝ) : ℝ :=
  ((i8Psi4s68dN0 x + (i8Psi4s68N1 x + x * i8Psi4s68dN1 x) + (2 * x * i8Psi4s68N2 x +
    x ^ 2 * i8Psi4s68dN2 x) + (3 * x ^ 2 * i8Psi4s68N3 x + x ^ 3 * i8Psi4s68dN3 x) +
    (4 * x ^ 3 * i8Psi4s68N4 x + x ^ 4 * i8Psi4s68dN4 x)) * x ^ 2 - (i8Psi4s68N0 x +
    x * i8Psi4s68N1 x + x ^ 2 * i8Psi4s68N2 x + x ^ 3 * i8Psi4s68N3 x +
    x ^ 4 * i8Psi4s68N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s68dW x

theorem hasDerivAt_i8Psi4s68 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s68 (i8Psi4s68D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s68N0 hx).add (X.mul (hasDerivAt_i8Psi4s68N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s68N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s68N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s68N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s68W hx)
  unfold i8Psi4s68
  refine e.congr_deriv ?_
  unfold i8Psi4s68D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 68 of `p₄` in `ξ`: from `t B1 A2 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s68 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽68⁾)'(ξ) ξ' = p₄⁽68⁾`**, in terms of `ξ`. -/
theorem i8Psi4s68D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s68D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s68 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s68D i8Psi4s68N0 i8Psi4s68N1 i8Psi4s68N2 i8Psi4s68N3 i8Psi4s68N4 i8Psi4s68dN0
    i8Psi4s68dN1 i8Psi4s68dN2 i8Psi4s68dN3 i8Psi4s68dN4 i8Psi4s68dW i8P4s68
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_0m0 hx,
    i13hw_m00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽69⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s69N0 (x : ℝ) : ℝ :=
    (-7 / 4) * hpl [negOne] x +
    (-2) * hpl [negOne, zero] x +
    (-7 / 2) * hpl [zero, negOne] x +
    (-1) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-7) * hpl [zero, zero, negOne] x +
    (-2) * hpl [zero, negOne, zero, zero] x +
    (-4) * hpl [zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s69N0`. -/
noncomputable def i8Psi4s69dN0 (x : ℝ) : ℝ :=
    (-7 / 4) * (negOne.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (-7 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-7) * (zero.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s69N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s69N0 (i8Psi4s69dN0 x) x := by
  unfold i8Psi4s69N0 i8Psi4s69dN0
  exact ((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-7 / 4)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-6)))

/-- The part of `ξ² Ψ₄⁽69⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s69N1 (x : ℝ) : ℝ :=
    (-19 / 4) +
    (-24) * hpl [negOne] x +
    (-3) * hpl [zero] x +
    (-16) * hpl [negOne, zero] x +
    (-24) * hpl [zero, negOne] x +
    (-1) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-16) * hpl [zero, negOne, zero] x +
    (-24) * hpl [zero, zero, negOne] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-16) * hpl [zero, zero, negOne, zero] x +
    (-24) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s69N1`. -/
noncomputable def i8Psi4s69dN1 (x : ℝ) : ℝ :=
    0 +
    (-24) * (negOne.kernel x * hpl [] x) +
    (-3) * (zero.kernel x * hpl [] x) +
    (-16) * (negOne.kernel x * hpl [zero] x) +
    (-24) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s69N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s69N1 (i8Psi4s69dN1 x) x := by
  unfold i8Psi4s69N1 i8Psi4s69dN1
  exact ((((((((((((hasDerivAt_const x (-19 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽69⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s69N2 (x : ℝ) : ℝ :=
    (89 / 4) * hpl [zero] x +
    (-28) * hpl [negOne, zero] x +
    (14) * hpl [zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x +
    (-16) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s69N2`. -/
noncomputable def i8Psi4s69dN2 (x : ℝ) : ℝ :=
    (89 / 4) * (zero.kernel x * hpl [] x) +
    (-28) * (negOne.kernel x * hpl [zero] x) +
    (14) * (zero.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s69N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s69N2 (i8Psi4s69dN2 x) x := by
  unfold i8Psi4s69N2 i8Psi4s69dN2
  exact ((((((hasDerivAt_hpl_cons zero [] hx).const_mul (89 / 4)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽69⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s69N3 (x : ℝ) : ℝ :=
    (-173 / 4) +
    (24) * hpl [negOne] x +
    (21) * hpl [zero] x +
    (-16) * hpl [negOne, zero] x +
    (-24) * hpl [zero, negOne] x +
    (-7) * hpl [zero, zero] x +
    (8) * hpl [negOne, zero, zero] x +
    (16) * hpl [zero, negOne, zero] x +
    (24) * hpl [zero, zero, negOne] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-16) * hpl [zero, zero, negOne, zero] x +
    (-24) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s69N3`. -/
noncomputable def i8Psi4s69dN3 (x : ℝ) : ℝ :=
    0 +
    (24) * (negOne.kernel x * hpl [] x) +
    (21) * (zero.kernel x * hpl [] x) +
    (-16) * (negOne.kernel x * hpl [zero] x) +
    (-24) * (zero.kernel x * hpl [negOne] x) +
    (-7) * (zero.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero] x) +
    (24) * (zero.kernel x * hpl [zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s69N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s69N3 (i8Psi4s69dN3 x) x := by
  unfold i8Psi4s69N3 i8Psi4s69dN3
  exact ((((((((((((hasDerivAt_const x (-173 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (21))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽69⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s69N4 (x : ℝ) : ℝ :=
    (-3 / 2) +
    (7 / 4) * hpl [negOne] x +
    (5 / 4) * hpl [zero] x +
    (-2) * hpl [negOne, zero] x +
    (-7 / 2) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [zero, zero] x +
    (1) * hpl [negOne, zero, zero] x +
    (4) * hpl [zero, negOne, zero] x +
    (7) * hpl [zero, zero, negOne] x +
    (-2) * hpl [zero, negOne, zero, zero] x +
    (-4) * hpl [zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s69N4`. -/
noncomputable def i8Psi4s69dN4 (x : ℝ) : ℝ :=
    0 +
    (7 / 4) * (negOne.kernel x * hpl [] x) +
    (5 / 4) * (zero.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (-7 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero] x) +
    (7) * (zero.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s69N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s69N4 (i8Psi4s69dN4 x) x := by
  unfold i8Psi4s69N4 i8Psi4s69dN4
  exact ((((((((((((hasDerivAt_const x (-3 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (7 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (5 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-6)))

/-- The part of `Ψ₄⁽69⁾` with constant coefficients. -/
noncomputable def i8Psi4s69W (x : ℝ) : ℝ :=
    (7) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s69W`. -/
noncomputable def i8Psi4s69dW (x : ℝ) : ℝ :=
    (7) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s69W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s69W (i8Psi4s69dW x) x := by
  unfold i8Psi4s69W i8Psi4s69dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (7))

/-- The piece `Ψ₄⁽69⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s69 (x : ℝ) : ℝ :=
  (i8Psi4s69N0 x + x * i8Psi4s69N1 x + x ^ 2 * i8Psi4s69N2 x + x ^ 3 * i8Psi4s69N3 x +
    x ^ 4 * i8Psi4s69N4 x) / x ^ 2 + i8Psi4s69W x

/-- The derivative of `Ψ₄⁽69⁾`. -/
noncomputable def i8Psi4s69D (x : ℝ) : ℝ :=
  ((i8Psi4s69dN0 x + (i8Psi4s69N1 x + x * i8Psi4s69dN1 x) + (2 * x * i8Psi4s69N2 x +
    x ^ 2 * i8Psi4s69dN2 x) + (3 * x ^ 2 * i8Psi4s69N3 x + x ^ 3 * i8Psi4s69dN3 x) +
    (4 * x ^ 3 * i8Psi4s69N4 x + x ^ 4 * i8Psi4s69dN4 x)) * x ^ 2 - (i8Psi4s69N0 x +
    x * i8Psi4s69N1 x + x ^ 2 * i8Psi4s69N2 x + x ^ 3 * i8Psi4s69N3 x +
    x ^ 4 * i8Psi4s69N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s69dW x

theorem hasDerivAt_i8Psi4s69 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s69 (i8Psi4s69D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s69N0 hx).add (X.mul (hasDerivAt_i8Psi4s69N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s69N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s69N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s69N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s69W hx)
  unfold i8Psi4s69
  refine e.congr_deriv ?_
  unfold i8Psi4s69D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 69 of `p₄` in `ξ`: from `t B1 A2 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s69 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * (-hpl [zero, negOne] x))

/-- **`(Ψ₄⁽69⁾)'(ξ) ξ' = p₄⁽69⁾`**, in terms of `ξ`. -/
theorem i8Psi4s69D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s69D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s69 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s69D i8Psi4s69N0 i8Psi4s69N1 i8Psi4s69N2 i8Psi4s69N3 i8Psi4s69N4 i8Psi4s69dN0
    i8Psi4s69dN1 i8Psi4s69dN2 i8Psi4s69dN3 i8Psi4s69dN4 i8Psi4s69dW i8P4s69
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_0m0 hx,
    i13hw_m00 hx, i13hw_00m0 hx, i13hw_0m00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽70⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s70N0 (x : ℝ) : ℝ :=
    (3) * hpl [negOne, negOne] x +
    (6) * hpl [negOne, negOne, zero] x +
    (6) * hpl [negOne, zero, negOne] x +
    (6) * hpl [zero, negOne, negOne] x +
    (4) * hpl [negOne, negOne, zero, zero] x +
    (4) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [negOne, zero, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, negOne] x +
    (4) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s70N0`. -/
noncomputable def i8Psi4s70dN0 (x : ℝ) : ℝ :=
    (3) * (negOne.kernel x * hpl [negOne] x) +
    (6) * (negOne.kernel x * hpl [negOne, zero] x) +
    (6) * (negOne.kernel x * hpl [zero, negOne] x) +
    (6) * (zero.kernel x * hpl [negOne, negOne] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s70N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s70N0 (i8Psi4s70dN0 x) x := by
  unfold i8Psi4s70N0 i8Psi4s70dN0
  exact (((((((((((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (3)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽70⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s70N1 (x : ℝ) : ℝ :=
    (13) * hpl [negOne] x +
    (16) * hpl [negOne, negOne] x +
    (10) * hpl [negOne, zero] x +
    (10) * hpl [zero, negOne] x +
    (16) * hpl [negOne, negOne, zero] x +
    (16) * hpl [negOne, zero, negOne] x +
    (4) * hpl [negOne, zero, zero] x +
    (16) * hpl [zero, negOne, negOne] x +
    (4) * hpl [zero, negOne, zero] x +
    (4) * hpl [zero, zero, negOne] x +
    (16) * hpl [negOne, negOne, zero, zero] x +
    (16) * hpl [negOne, zero, negOne, zero] x +
    (16) * hpl [negOne, zero, zero, negOne] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (16) * hpl [zero, negOne, zero, negOne] x +
    (16) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s70N1`. -/
noncomputable def i8Psi4s70dN1 (x : ℝ) : ℝ :=
    (13) * (negOne.kernel x * hpl [] x) +
    (16) * (negOne.kernel x * hpl [negOne] x) +
    (10) * (negOne.kernel x * hpl [zero] x) +
    (10) * (zero.kernel x * hpl [negOne] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, negOne] x) +
    (4) * (negOne.kernel x * hpl [zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s70N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s70N1 (i8Psi4s70dN1 x) x := by
  unfold i8Psi4s70N1 i8Psi4s70dN1
  exact (((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (13)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽70⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s70N2 (x : ℝ) : ℝ :=
    (-37 / 2) * hpl [negOne] x +
    (-13) * hpl [zero] x +
    (26) * hpl [negOne, negOne] x +
    (28) * hpl [negOne, zero] x +
    (-13) * hpl [zero, negOne] x +
    (-10) * hpl [zero, zero] x +
    (-6) * hpl [negOne, zero, zero] x +
    (-10) * hpl [zero, negOne, zero] x +
    (-10) * hpl [zero, zero, negOne] x +
    (24) * hpl [negOne, negOne, zero, zero] x +
    (24) * hpl [negOne, zero, negOne, zero] x +
    (24) * hpl [negOne, zero, zero, negOne] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (16) * hpl [zero, negOne, zero, negOne] x +
    (16) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s70N2`. -/
noncomputable def i8Psi4s70dN2 (x : ℝ) : ℝ :=
    (-37 / 2) * (negOne.kernel x * hpl [] x) +
    (-13) * (zero.kernel x * hpl [] x) +
    (26) * (negOne.kernel x * hpl [negOne] x) +
    (28) * (negOne.kernel x * hpl [zero] x) +
    (-13) * (zero.kernel x * hpl [negOne] x) +
    (-10) * (zero.kernel x * hpl [zero] x) +
    (-6) * (negOne.kernel x * hpl [zero, zero] x) +
    (-10) * (zero.kernel x * hpl [negOne, zero] x) +
    (-10) * (zero.kernel x * hpl [zero, negOne] x) +
    (24) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s70N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s70N2 (i8Psi4s70dN2 x) x := by
  unfold i8Psi4s70N2 i8Psi4s70dN2
  exact ((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-37 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-13))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (26))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-13))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽70⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s70N3 (x : ℝ) : ℝ :=
    (119 / 2) +
    (-35) * hpl [negOne] x +
    (-28) * hpl [zero] x +
    (16) * hpl [negOne, negOne] x +
    (22) * hpl [negOne, zero] x +
    (22) * hpl [zero, negOne] x +
    (10) * hpl [zero, zero] x +
    (-16) * hpl [negOne, negOne, zero] x +
    (-16) * hpl [negOne, zero, negOne] x +
    (-12) * hpl [negOne, zero, zero] x +
    (-16) * hpl [zero, negOne, negOne] x +
    (-12) * hpl [zero, negOne, zero] x +
    (-12) * hpl [zero, zero, negOne] x +
    (16) * hpl [negOne, negOne, zero, zero] x +
    (16) * hpl [negOne, zero, negOne, zero] x +
    (16) * hpl [negOne, zero, zero, negOne] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (16) * hpl [zero, negOne, zero, negOne] x +
    (16) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s70N3`. -/
noncomputable def i8Psi4s70dN3 (x : ℝ) : ℝ :=
    0 +
    (-35) * (negOne.kernel x * hpl [] x) +
    (-28) * (zero.kernel x * hpl [] x) +
    (16) * (negOne.kernel x * hpl [negOne] x) +
    (22) * (negOne.kernel x * hpl [zero] x) +
    (22) * (zero.kernel x * hpl [negOne] x) +
    (10) * (zero.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, negOne] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s70N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s70N3 (i8Psi4s70dN3 x) x := by
  unfold i8Psi4s70N3 i8Psi4s70dN3
  exact (((((((((((((((((((hasDerivAt_const x (119 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-35))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (22))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (22))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽70⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s70N4 (x : ℝ) : ℝ :=
    (3) +
    (-7 / 2) * hpl [negOne] x +
    (-5 / 2) * hpl [zero] x +
    (3) * hpl [negOne, negOne] x +
    (4) * hpl [negOne, zero] x +
    (4) * hpl [zero, negOne] x +
    (1) * hpl [zero, zero] x +
    (-6) * hpl [negOne, negOne, zero] x +
    (-6) * hpl [negOne, zero, negOne] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-6) * hpl [zero, negOne, negOne] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, zero, negOne] x +
    (4) * hpl [negOne, negOne, zero, zero] x +
    (4) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [negOne, zero, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, negOne] x +
    (4) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s70N4`. -/
noncomputable def i8Psi4s70dN4 (x : ℝ) : ℝ :=
    0 +
    (-7 / 2) * (negOne.kernel x * hpl [] x) +
    (-5 / 2) * (zero.kernel x * hpl [] x) +
    (3) * (negOne.kernel x * hpl [negOne] x) +
    (4) * (negOne.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-6) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-6) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-6) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s70N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s70N4 (i8Psi4s70dN4 x) x := by
  unfold i8Psi4s70N4 i8Psi4s70dN4
  exact (((((((((((((((((((hasDerivAt_const x (3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (4)))

/-- The part of `Ψ₄⁽70⁾` with constant coefficients. -/
noncomputable def i8Psi4s70W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, zero, zero] x +
    (-12) * hpl [zero, negOne, zero, zero] x +
    (-12) * hpl [zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s70W`. -/
noncomputable def i8Psi4s70dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [zero, zero] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s70W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s70W (i8Psi4s70dW x) x := by
  unfold i8Psi4s70W i8Psi4s70dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-12)))

/-- The piece `Ψ₄⁽70⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s70 (x : ℝ) : ℝ :=
  (i8Psi4s70N0 x + x * i8Psi4s70N1 x + x ^ 2 * i8Psi4s70N2 x + x ^ 3 * i8Psi4s70N3 x +
    x ^ 4 * i8Psi4s70N4 x) / x ^ 2 + i8Psi4s70W x

/-- The derivative of `Ψ₄⁽70⁾`. -/
noncomputable def i8Psi4s70D (x : ℝ) : ℝ :=
  ((i8Psi4s70dN0 x + (i8Psi4s70N1 x + x * i8Psi4s70dN1 x) + (2 * x * i8Psi4s70N2 x +
    x ^ 2 * i8Psi4s70dN2 x) + (3 * x ^ 2 * i8Psi4s70N3 x + x ^ 3 * i8Psi4s70dN3 x) +
    (4 * x ^ 3 * i8Psi4s70N4 x + x ^ 4 * i8Psi4s70dN4 x)) * x ^ 2 - (i8Psi4s70N0 x +
    x * i8Psi4s70N1 x + x ^ 2 * i8Psi4s70N2 x + x ^ 3 * i8Psi4s70N3 x +
    x ^ 4 * i8Psi4s70N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s70dW x

theorem hasDerivAt_i8Psi4s70 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s70 (i8Psi4s70D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s70N0 hx).add (X.mul (hasDerivAt_i8Psi4s70N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s70N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s70N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s70N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s70W hx)
  unfold i8Psi4s70
  refine e.congr_deriv ?_
  unfold i8Psi4s70D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 70 of `p₄` in `ξ`: from `t B1 A2 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s70 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * (2 * hpl [negOne, negOne] x))

/-- **`(Ψ₄⁽70⁾)'(ξ) ξ' = p₄⁽70⁾`**, in terms of `ξ`. -/
theorem i8Psi4s70D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s70D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s70 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s70D i8Psi4s70N0 i8Psi4s70N1 i8Psi4s70N2 i8Psi4s70N3 i8Psi4s70N4 i8Psi4s70dN0
    i8Psi4s70dN1 i8Psi4s70dN2 i8Psi4s70dN3 i8Psi4s70dN4 i8Psi4s70dW i8P4s70
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_mm hx,
    i13hw_0m0 hx, i13hw_m00 hx, i13hw_m0m hx, i13hw_mm0 hx, i13hw_0m0m hx, i13hw_0mm0 hx, i13hw_m00m
    hx, i13hw_m0m0 hx, i13hw_mm00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽71⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s71N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s71N0`. -/
noncomputable def i8Psi4s71dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s71N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s71N0 (i8Psi4s71dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽71⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s71N1 (x : ℝ) : ℝ :=
    (24) * hpl [one] x +
    (8) * hpl [zero, one] x +
    (8) * hpl [one, zero] x

/-- The derivative of `i8Psi4s71N1`. -/
noncomputable def i8Psi4s71dN1 (x : ℝ) : ℝ :=
    (24) * (one.kernel x * hpl [] x) +
    (8) * (zero.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s71N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s71N1 (i8Psi4s71dN1 x) x := by
  unfold i8Psi4s71N1 i8Psi4s71dN1
  exact ((((hasDerivAt_hpl_cons one [] hx).const_mul (24)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽71⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s71N2 (x : ℝ) : ℝ :=
    (-24) * hpl [zero] x +
    (-22) * hpl [one] x +
    (16) * hpl [zero, one] x +
    (-20) * hpl [one, zero] x

/-- The derivative of `i8Psi4s71N2`. -/
noncomputable def i8Psi4s71dN2 (x : ℝ) : ℝ :=
    (-24) * (zero.kernel x * hpl [] x) +
    (-22) * (one.kernel x * hpl [] x) +
    (16) * (zero.kernel x * hpl [one] x) +
    (-20) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s71N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s71N2 (i8Psi4s71dN2 x) x := by
  unfold i8Psi4s71N2 i8Psi4s71dN2
  exact (((((hasDerivAt_hpl_cons zero [] hx).const_mul (-24)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-20)))

/-- The part of `ξ² Ψ₄⁽71⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s71N3 (x : ℝ) : ℝ :=
    (-14) +
    (12) * hpl [zero] x +
    (8) * hpl [one] x +
    (8) * hpl [zero, one] x +
    (8) * hpl [one, zero] x

/-- The derivative of `i8Psi4s71N3`. -/
noncomputable def i8Psi4s71dN3 (x : ℝ) : ℝ :=
    0 +
    (12) * (zero.kernel x * hpl [] x) +
    (8) * (one.kernel x * hpl [] x) +
    (8) * (zero.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s71N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s71N3 (i8Psi4s71dN3 x) x := by
  unfold i8Psi4s71N3 i8Psi4s71dN3
  exact (((((hasDerivAt_const x (-14)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽71⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s71N4 (x : ℝ) : ℝ :=
    (-6) +
    (2) * hpl [zero] x +
    (-10) * hpl [one] x +
    (4) * hpl [zero, one] x +
    (4) * hpl [one, zero] x

/-- The derivative of `i8Psi4s71N4`. -/
noncomputable def i8Psi4s71dN4 (x : ℝ) : ℝ :=
    0 +
    (2) * (zero.kernel x * hpl [] x) +
    (-10) * (one.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s71N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s71N4 (i8Psi4s71dN4 x) x := by
  unfold i8Psi4s71N4 i8Psi4s71dN4
  exact (((((hasDerivAt_const x (-6)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽71⁾` with constant coefficients. -/
noncomputable def i8Psi4s71W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero] x +
    (-8) * hpl [zero, zero, one] x +
    (-8) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s71W`. -/
noncomputable def i8Psi4s71dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [zero, one] x) +
    (-8) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s71W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s71W (i8Psi4s71dW x) x := by
  unfold i8Psi4s71W i8Psi4s71dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-8)))

/-- The piece `Ψ₄⁽71⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s71 (x : ℝ) : ℝ :=
  (i8Psi4s71N0 x + x * i8Psi4s71N1 x + x ^ 2 * i8Psi4s71N2 x + x ^ 3 * i8Psi4s71N3 x +
    x ^ 4 * i8Psi4s71N4 x) / x ^ 2 + i8Psi4s71W x

/-- The derivative of `Ψ₄⁽71⁾`. -/
noncomputable def i8Psi4s71D (x : ℝ) : ℝ :=
  ((i8Psi4s71dN0 x + (i8Psi4s71N1 x + x * i8Psi4s71dN1 x) + (2 * x * i8Psi4s71N2 x +
    x ^ 2 * i8Psi4s71dN2 x) + (3 * x ^ 2 * i8Psi4s71N3 x + x ^ 3 * i8Psi4s71dN3 x) +
    (4 * x ^ 3 * i8Psi4s71N4 x + x ^ 4 * i8Psi4s71dN4 x)) * x ^ 2 - (i8Psi4s71N0 x +
    x * i8Psi4s71N1 x + x ^ 2 * i8Psi4s71N2 x + x ^ 3 * i8Psi4s71N3 x +
    x ^ 4 * i8Psi4s71N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s71dW x

theorem hasDerivAt_i8Psi4s71 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s71 (i8Psi4s71D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s71N0 hx).add (X.mul (hasDerivAt_i8Psi4s71N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s71N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s71N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s71N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s71W hx)
  unfold i8Psi4s71
  refine e.congr_deriv ?_
  unfold i8Psi4s71D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 71 of `p₄` in `ξ`: from `t B1 A2 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s71 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 +
    x) / (1 - x) * (2 * x / (1 + x))))

/-- **`(Ψ₄⁽71⁾)'(ξ) ξ' = p₄⁽71⁾`**, in terms of `ξ`. -/
theorem i8Psi4s71D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s71D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s71 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s71D i8Psi4s71N0 i8Psi4s71N1 i8Psi4s71N2 i8Psi4s71N3 i8Psi4s71N4 i8Psi4s71dN0
    i8Psi4s71dN1 i8Psi4s71dN2 i8Psi4s71dN3 i8Psi4s71dN4 i8Psi4s71dW i8P4s71
  simp only [kernel_zero, kernel_one, hpl_nil, hpl_zero, i13hw_10 hx, i13_log_one_sub_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
