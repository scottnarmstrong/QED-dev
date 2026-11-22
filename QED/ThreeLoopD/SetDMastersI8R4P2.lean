/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P1

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 6 to 10

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s6`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s6D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s6`, `QED.ThreeLoopD.i8Psi4s6D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽6⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s6N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s6N0`. -/
noncomputable def i8Psi4s6dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s6N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s6N0 (i8Psi4s6dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽6⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s6N1 (x : ℝ) : ℝ :=
    (20) +
    (12) * hpl [zero] x +
    (4) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s6N1`. -/
noncomputable def i8Psi4s6dN1 (x : ℝ) : ℝ :=
    0 +
    (12) * (zero.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s6N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s6N1 (i8Psi4s6dN1 x) x := by
  unfold i8Psi4s6N1 i8Psi4s6dN1
  exact (((hasDerivAt_const x (20)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽6⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s6N2 (x : ℝ) : ℝ :=
    (8) * hpl [zero] x +
    (-8) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s6N2`. -/
noncomputable def i8Psi4s6dN2 (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [] x) +
    (-8) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s6N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s6N2 (i8Psi4s6dN2 x) x := by
  unfold i8Psi4s6N2 i8Psi4s6dN2
  exact (((hasDerivAt_hpl_cons zero [] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽6⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s6N3 (x : ℝ) : ℝ :=
    (-12) +
    (20) * hpl [zero] x +
    (-12) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s6N3`. -/
noncomputable def i8Psi4s6dN3 (x : ℝ) : ℝ :=
    0 +
    (20) * (zero.kernel x * hpl [] x) +
    (-12) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s6N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s6N3 (i8Psi4s6dN3 x) x := by
  unfold i8Psi4s6N3 i8Psi4s6dN3
  exact (((hasDerivAt_const x (-12)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽6⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s6N4 (x : ℝ) : ℝ :=
    (-13 / 2) +
    (5) * hpl [zero] x +
    (-2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s6N4`. -/
noncomputable def i8Psi4s6dN4 (x : ℝ) : ℝ :=
    0 +
    (5) * (zero.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s6N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s6N4 (i8Psi4s6dN4 x) x := by
  unfold i8Psi4s6N4 i8Psi4s6dN4
  exact (((hasDerivAt_const x (-13 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽6⁾` with constant coefficients. -/
noncomputable def i8Psi4s6W (x : ℝ) : ℝ :=
    (-12) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s6W`. -/
noncomputable def i8Psi4s6dW (x : ℝ) : ℝ :=
    (-12) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s6W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s6W (i8Psi4s6dW x) x := by
  unfold i8Psi4s6W i8Psi4s6dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-12))

/-- The piece `Ψ₄⁽6⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s6 (x : ℝ) : ℝ :=
  (i8Psi4s6N0 x + x * i8Psi4s6N1 x + x ^ 2 * i8Psi4s6N2 x + x ^ 3 * i8Psi4s6N3 x +
    x ^ 4 * i8Psi4s6N4 x) / x ^ 2 + i8Psi4s6W x

/-- The derivative of `Ψ₄⁽6⁾`. -/
noncomputable def i8Psi4s6D (x : ℝ) : ℝ :=
  ((i8Psi4s6dN0 x + (i8Psi4s6N1 x + x * i8Psi4s6dN1 x) + (2 * x * i8Psi4s6N2 x +
    x ^ 2 * i8Psi4s6dN2 x) + (3 * x ^ 2 * i8Psi4s6N3 x + x ^ 3 * i8Psi4s6dN3 x) +
    (4 * x ^ 3 * i8Psi4s6N4 x + x ^ 4 * i8Psi4s6dN4 x)) * x ^ 2 - (i8Psi4s6N0 x +
    x * i8Psi4s6N1 x + x ^ 2 * i8Psi4s6N2 x + x ^ 3 * i8Psi4s6N3 x +
    x ^ 4 * i8Psi4s6N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s6dW x

theorem hasDerivAt_i8Psi4s6 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s6 (i8Psi4s6D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s6N0 hx).add (X.mul (hasDerivAt_i8Psi4s6N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s6N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s6N3 hx))).add ((X.pow
    4).mul (hasDerivAt_i8Psi4s6N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add (hasDerivAt_i8Psi4s6W
    hx)
  unfold i8Psi4s6
  refine e.congr_deriv ?_
  unfold i8Psi4s6D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 6 of `p₄` in `ξ`: from `t B2 A2 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s6 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * (2 + Real.log x * (1 + x) / (1 -
    x)) * ((1 + x) / (1 - x) * (2 * x / (1 + x)))

/-- **`(Ψ₄⁽6⁾)'(ξ) ξ' = p₄⁽6⁾`**, in terms of `ξ`. -/
theorem i8Psi4s6D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s6D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s6 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s6D i8Psi4s6N0 i8Psi4s6N1 i8Psi4s6N2 i8Psi4s6N3 i8Psi4s6N4 i8Psi4s6dN0 i8Psi4s6dN1
    i8Psi4s6dN2 i8Psi4s6dN3 i8Psi4s6dN4 i8Psi4s6dW i8P4s6
  simp only [kernel_zero, hpl_nil, hpl_zero, i13hw_00]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽7⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s7N0 (x : ℝ) : ℝ :=
    (-13 / 4) * hpl [negOne] x +
    (-5 / 2) * hpl [negOne, zero] x +
    (-5 / 2) * hpl [zero, negOne] x +
    (-1) * hpl [negOne, zero, zero] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s7N0`. -/
noncomputable def i8Psi4s7dN0 (x : ℝ) : ℝ :=
    (-13 / 4) * (negOne.kernel x * hpl [] x) +
    (-5 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-5 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s7N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s7N0 (i8Psi4s7dN0 x) x := by
  unfold i8Psi4s7N0 i8Psi4s7dN0
  exact (((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-13 / 4)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽7⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s7N1 (x : ℝ) : ℝ :=
    (-27 / 4) +
    (-16) * hpl [negOne] x +
    (-7 / 2) * hpl [zero] x +
    (-16) * hpl [negOne, zero] x +
    (-16) * hpl [zero, negOne] x +
    (-1) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s7N1`. -/
noncomputable def i8Psi4s7dN1 (x : ℝ) : ℝ :=
    0 +
    (-16) * (negOne.kernel x * hpl [] x) +
    (-7 / 2) * (zero.kernel x * hpl [] x) +
    (-16) * (negOne.kernel x * hpl [zero] x) +
    (-16) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s7N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s7N1 (i8Psi4s7dN1 x) x := by
  unfold i8Psi4s7N1 i8Psi4s7dN1
  exact (((((((((hasDerivAt_const x (-27 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽7⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s7N2 (x : ℝ) : ℝ :=
    (51 / 4) * hpl [zero] x +
    (-27) * hpl [negOne, zero] x +
    (-8) * hpl [zero, negOne] x +
    (27 / 2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s7N2`. -/
noncomputable def i8Psi4s7dN2 (x : ℝ) : ℝ :=
    (51 / 4) * (zero.kernel x * hpl [] x) +
    (-27) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [negOne] x) +
    (27 / 2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s7N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s7N2 (i8Psi4s7dN2 x) x := by
  unfold i8Psi4s7N2 i8Psi4s7dN2
  exact (((((hasDerivAt_hpl_cons zero [] hx).const_mul (51 / 4)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-27))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (27 / 2)))

/-- The part of `ξ² Ψ₄⁽7⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s7N3 (x : ℝ) : ℝ :=
    (-133 / 4) +
    (16) * hpl [negOne] x +
    (41 / 2) * hpl [zero] x +
    (-16) * hpl [negOne, zero] x +
    (-16) * hpl [zero, negOne] x +
    (-7) * hpl [zero, zero] x +
    (8) * hpl [negOne, zero, zero] x +
    (8) * hpl [zero, negOne, zero] x +
    (8) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s7N3`. -/
noncomputable def i8Psi4s7dN3 (x : ℝ) : ℝ :=
    0 +
    (16) * (negOne.kernel x * hpl [] x) +
    (41 / 2) * (zero.kernel x * hpl [] x) +
    (-16) * (negOne.kernel x * hpl [zero] x) +
    (-16) * (zero.kernel x * hpl [negOne] x) +
    (-7) * (zero.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s7N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s7N3 (i8Psi4s7dN3 x) x := by
  unfold i8Psi4s7N3 i8Psi4s7dN3
  exact (((((((((hasDerivAt_const x (-133 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (41 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽7⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s7N4 (x : ℝ) : ℝ :=
    (-19 / 8) +
    (13 / 4) * hpl [negOne] x +
    (3 / 2) * hpl [zero] x +
    (-5 / 2) * hpl [negOne, zero] x +
    (-5 / 2) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [zero, zero] x +
    (1) * hpl [negOne, zero, zero] x +
    (1) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s7N4`. -/
noncomputable def i8Psi4s7dN4 (x : ℝ) : ℝ :=
    0 +
    (13 / 4) * (negOne.kernel x * hpl [] x) +
    (3 / 2) * (zero.kernel x * hpl [] x) +
    (-5 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-5 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [zero, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s7N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s7N4 (i8Psi4s7dN4 x) x := by
  unfold i8Psi4s7N4 i8Psi4s7dN4
  exact (((((((((hasDerivAt_const x (-19 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (13 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1)))

/-- The part of `Ψ₄⁽7⁾` with constant coefficients. -/
noncomputable def i8Psi4s7W (x : ℝ) : ℝ :=
    (7) * hpl [zero, zero, zero] x +
    (12) * hpl [zero, negOne, zero, zero] x +
    (12) * hpl [zero, zero, negOne, zero] x +
    (12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s7W`. -/
noncomputable def i8Psi4s7dW (x : ℝ) : ℝ :=
    (7) * (zero.kernel x * hpl [zero, zero] x) +
    (12) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (12) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s7W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s7W (i8Psi4s7dW x) x := by
  unfold i8Psi4s7W i8Psi4s7dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (7)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (12)))

/-- The piece `Ψ₄⁽7⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s7 (x : ℝ) : ℝ :=
  (i8Psi4s7N0 x + x * i8Psi4s7N1 x + x ^ 2 * i8Psi4s7N2 x + x ^ 3 * i8Psi4s7N3 x +
    x ^ 4 * i8Psi4s7N4 x) / x ^ 2 + i8Psi4s7W x

/-- The derivative of `Ψ₄⁽7⁾`. -/
noncomputable def i8Psi4s7D (x : ℝ) : ℝ :=
  ((i8Psi4s7dN0 x + (i8Psi4s7N1 x + x * i8Psi4s7dN1 x) + (2 * x * i8Psi4s7N2 x +
    x ^ 2 * i8Psi4s7dN2 x) + (3 * x ^ 2 * i8Psi4s7N3 x + x ^ 3 * i8Psi4s7dN3 x) +
    (4 * x ^ 3 * i8Psi4s7N4 x + x ^ 4 * i8Psi4s7dN4 x)) * x ^ 2 - (i8Psi4s7N0 x +
    x * i8Psi4s7N1 x + x ^ 2 * i8Psi4s7N2 x + x ^ 3 * i8Psi4s7N3 x +
    x ^ 4 * i8Psi4s7N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s7dW x

theorem hasDerivAt_i8Psi4s7 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s7 (i8Psi4s7D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s7N0 hx).add (X.mul (hasDerivAt_i8Psi4s7N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s7N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s7N3 hx))).add ((X.pow
    4).mul (hasDerivAt_i8Psi4s7N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add (hasDerivAt_i8Psi4s7W
    hx)
  unfold i8Psi4s7
  refine e.congr_deriv ?_
  unfold i8Psi4s7D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 7 of `p₄` in `ξ`: from `t B2 A2 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s7 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * (2 + Real.log x * (1 + x) / (1 -
    x)) * ((1 + x) / (1 - x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽7⁾)'(ξ) ξ' = p₄⁽7⁾`**, in terms of `ξ`. -/
theorem i8Psi4s7D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s7D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s7 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s7D i8Psi4s7N0 i8Psi4s7N1 i8Psi4s7N2 i8Psi4s7N3 i8Psi4s7N4 i8Psi4s7dN0 i8Psi4s7dN1
    i8Psi4s7dN2 i8Psi4s7dN3 i8Psi4s7dN4 i8Psi4s7dW i8P4s7
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_0m0 hx,
    i13hw_m00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽8⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s8N0 (x : ℝ) : ℝ :=
    (13 / 2) * hpl [negOne, negOne] x +
    (5) * hpl [negOne, negOne, zero] x +
    (5) * hpl [negOne, zero, negOne] x +
    (5) * hpl [zero, negOne, negOne] x +
    (2) * hpl [negOne, negOne, zero, zero] x +
    (2) * hpl [negOne, zero, negOne, zero] x +
    (2) * hpl [negOne, zero, zero, negOne] x +
    (2) * hpl [zero, negOne, negOne, zero] x +
    (2) * hpl [zero, negOne, zero, negOne] x +
    (2) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s8N0`. -/
noncomputable def i8Psi4s8dN0 (x : ℝ) : ℝ :=
    (13 / 2) * (negOne.kernel x * hpl [negOne] x) +
    (5) * (negOne.kernel x * hpl [negOne, zero] x) +
    (5) * (negOne.kernel x * hpl [zero, negOne] x) +
    (5) * (zero.kernel x * hpl [negOne, negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s8N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s8N0 (i8Psi4s8dN0 x) x := by
  unfold i8Psi4s8N0 i8Psi4s8dN0
  exact (((((((((((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (13 / 2)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽8⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s8N1 (x : ℝ) : ℝ :=
    (27 / 2) * hpl [negOne] x +
    (32) * hpl [negOne, negOne] x +
    (7) * hpl [negOne, zero] x +
    (7) * hpl [zero, negOne] x +
    (32) * hpl [negOne, negOne, zero] x +
    (32) * hpl [negOne, zero, negOne] x +
    (2) * hpl [negOne, zero, zero] x +
    (32) * hpl [zero, negOne, negOne] x +
    (2) * hpl [zero, negOne, zero] x +
    (2) * hpl [zero, zero, negOne] x +
    (16) * hpl [negOne, negOne, zero, zero] x +
    (16) * hpl [negOne, zero, negOne, zero] x +
    (16) * hpl [negOne, zero, zero, negOne] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (16) * hpl [zero, negOne, zero, negOne] x +
    (16) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s8N1`. -/
noncomputable def i8Psi4s8dN1 (x : ℝ) : ℝ :=
    (27 / 2) * (negOne.kernel x * hpl [] x) +
    (32) * (negOne.kernel x * hpl [negOne] x) +
    (7) * (negOne.kernel x * hpl [zero] x) +
    (7) * (zero.kernel x * hpl [negOne] x) +
    (32) * (negOne.kernel x * hpl [negOne, zero] x) +
    (32) * (negOne.kernel x * hpl [zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, zero] x) +
    (32) * (zero.kernel x * hpl [negOne, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (zero.kernel x * hpl [zero, negOne] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s8N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s8N1 (i8Psi4s8dN1 x) x := by
  unfold i8Psi4s8N1 i8Psi4s8dN1
  exact (((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (27 / 2)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽8⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s8N2 (x : ℝ) : ℝ :=
    (301 / 4) * hpl [negOne] x +
    (-27 / 2) * hpl [zero] x +
    (-31) * hpl [negOne, zero] x +
    (-51 / 2) * hpl [zero, negOne] x +
    (-7) * hpl [zero, zero] x +
    (54) * hpl [negOne, negOne, zero] x +
    (54) * hpl [negOne, zero, negOne] x +
    (15) * hpl [negOne, zero, zero] x +
    (16) * hpl [zero, negOne, negOne] x +
    (-27) * hpl [zero, negOne, zero] x +
    (-27) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s8N2`. -/
noncomputable def i8Psi4s8dN2 (x : ℝ) : ℝ :=
    (301 / 4) * (negOne.kernel x * hpl [] x) +
    (-27 / 2) * (zero.kernel x * hpl [] x) +
    (-31) * (negOne.kernel x * hpl [zero] x) +
    (-51 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-7) * (zero.kernel x * hpl [zero] x) +
    (54) * (negOne.kernel x * hpl [negOne, zero] x) +
    (54) * (negOne.kernel x * hpl [zero, negOne] x) +
    (15) * (negOne.kernel x * hpl [zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-27) * (zero.kernel x * hpl [negOne, zero] x) +
    (-27) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s8N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s8N2 (i8Psi4s8dN2 x) x := by
  unfold i8Psi4s8N2 i8Psi4s8dN2
  exact ((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (301 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-27 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-31))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-51 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (54))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (54))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-27))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-27)))

/-- The part of `ξ² Ψ₄⁽8⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s8N3 (x : ℝ) : ℝ :=
    (-451 / 4) +
    (133 / 2) * hpl [negOne] x +
    (51) * hpl [zero] x +
    (-32) * hpl [negOne, negOne] x +
    (-41) * hpl [negOne, zero] x +
    (-41) * hpl [zero, negOne] x +
    (-13) * hpl [zero, zero] x +
    (32) * hpl [negOne, negOne, zero] x +
    (32) * hpl [negOne, zero, negOne] x +
    (14) * hpl [negOne, zero, zero] x +
    (32) * hpl [zero, negOne, negOne] x +
    (14) * hpl [zero, negOne, zero] x +
    (14) * hpl [zero, zero, negOne] x +
    (-16) * hpl [negOne, negOne, zero, zero] x +
    (-16) * hpl [negOne, zero, negOne, zero] x +
    (-16) * hpl [negOne, zero, zero, negOne] x +
    (-16) * hpl [zero, negOne, negOne, zero] x +
    (-16) * hpl [zero, negOne, zero, negOne] x +
    (-16) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s8N3`. -/
noncomputable def i8Psi4s8dN3 (x : ℝ) : ℝ :=
    0 +
    (133 / 2) * (negOne.kernel x * hpl [] x) +
    (51) * (zero.kernel x * hpl [] x) +
    (-32) * (negOne.kernel x * hpl [negOne] x) +
    (-41) * (negOne.kernel x * hpl [zero] x) +
    (-41) * (zero.kernel x * hpl [negOne] x) +
    (-13) * (zero.kernel x * hpl [zero] x) +
    (32) * (negOne.kernel x * hpl [negOne, zero] x) +
    (32) * (negOne.kernel x * hpl [zero, negOne] x) +
    (14) * (negOne.kernel x * hpl [zero, zero] x) +
    (32) * (zero.kernel x * hpl [negOne, negOne] x) +
    (14) * (zero.kernel x * hpl [negOne, zero] x) +
    (14) * (zero.kernel x * hpl [zero, negOne] x) +
    (-16) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-16) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s8N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s8N3 (i8Psi4s8dN3 x) x := by
  unfold i8Psi4s8N3 i8Psi4s8dN3
  exact (((((((((((((((((((hasDerivAt_const x (-451 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (133 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (51))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-41))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-41))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-13))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽8⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s8N4 (x : ℝ) : ℝ :=
    (-13 / 4) +
    (19 / 4) * hpl [negOne] x +
    (7 / 4) * hpl [zero] x +
    (-13 / 2) * hpl [negOne, negOne] x +
    (-3) * hpl [negOne, zero] x +
    (-3) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [zero, zero] x +
    (5) * hpl [negOne, negOne, zero] x +
    (5) * hpl [negOne, zero, negOne] x +
    (1) * hpl [negOne, zero, zero] x +
    (5) * hpl [zero, negOne, negOne] x +
    (1) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, negOne] x +
    (-2) * hpl [negOne, negOne, zero, zero] x +
    (-2) * hpl [negOne, zero, negOne, zero] x +
    (-2) * hpl [negOne, zero, zero, negOne] x +
    (-2) * hpl [zero, negOne, negOne, zero] x +
    (-2) * hpl [zero, negOne, zero, negOne] x +
    (-2) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s8N4`. -/
noncomputable def i8Psi4s8dN4 (x : ℝ) : ℝ :=
    0 +
    (19 / 4) * (negOne.kernel x * hpl [] x) +
    (7 / 4) * (zero.kernel x * hpl [] x) +
    (-13 / 2) * (negOne.kernel x * hpl [negOne] x) +
    (-3) * (negOne.kernel x * hpl [zero] x) +
    (-3) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (5) * (negOne.kernel x * hpl [negOne, zero] x) +
    (5) * (negOne.kernel x * hpl [zero, negOne] x) +
    (1) * (negOne.kernel x * hpl [zero, zero] x) +
    (5) * (zero.kernel x * hpl [negOne, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s8N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s8N4 (i8Psi4s8dN4 x) x := by
  unfold i8Psi4s8N4 i8Psi4s8dN4
  exact (((((((((((((((((((hasDerivAt_const x (-13 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (19 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (7 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-13 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽8⁾` with constant coefficients. -/
noncomputable def i8Psi4s8W (x : ℝ) : ℝ :=
    (-2) * hpl [zero, zero, zero] x +
    (-14) * hpl [zero, negOne, zero, zero] x +
    (-14) * hpl [zero, zero, negOne, zero] x +
    (-14) * hpl [zero, zero, zero, negOne] x +
    (-24) * hpl [zero, negOne, negOne, zero, zero] x +
    (-24) * hpl [zero, negOne, zero, negOne, zero] x +
    (-24) * hpl [zero, negOne, zero, zero, negOne] x +
    (-24) * hpl [zero, zero, negOne, negOne, zero] x +
    (-24) * hpl [zero, zero, negOne, zero, negOne] x +
    (-24) * hpl [zero, zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s8W`. -/
noncomputable def i8Psi4s8dW (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [zero, zero] x) +
    (-14) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-14) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-14) * (zero.kernel x * hpl [zero, zero, negOne] x) +
    (-24) * (zero.kernel x * hpl [negOne, negOne, zero, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero, zero, negOne] x) +
    (-24) * (zero.kernel x * hpl [zero, negOne, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, negOne, zero, negOne] x) +
    (-24) * (zero.kernel x * hpl [zero, zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s8W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s8W (i8Psi4s8dW x) x := by
  unfold i8Psi4s8W i8Psi4s8dW
  exact (((((((((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, negOne] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, negOne] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, negOne] hx).const_mul (-24)))

/-- The piece `Ψ₄⁽8⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s8 (x : ℝ) : ℝ :=
  (i8Psi4s8N0 x + x * i8Psi4s8N1 x + x ^ 2 * i8Psi4s8N2 x + x ^ 3 * i8Psi4s8N3 x +
    x ^ 4 * i8Psi4s8N4 x) / x ^ 2 + i8Psi4s8W x

/-- The derivative of `Ψ₄⁽8⁾`. -/
noncomputable def i8Psi4s8D (x : ℝ) : ℝ :=
  ((i8Psi4s8dN0 x + (i8Psi4s8N1 x + x * i8Psi4s8dN1 x) + (2 * x * i8Psi4s8N2 x +
    x ^ 2 * i8Psi4s8dN2 x) + (3 * x ^ 2 * i8Psi4s8N3 x + x ^ 3 * i8Psi4s8dN3 x) +
    (4 * x ^ 3 * i8Psi4s8N4 x + x ^ 4 * i8Psi4s8dN4 x)) * x ^ 2 - (i8Psi4s8N0 x +
    x * i8Psi4s8N1 x + x ^ 2 * i8Psi4s8N2 x + x ^ 3 * i8Psi4s8N3 x +
    x ^ 4 * i8Psi4s8N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s8dW x

theorem hasDerivAt_i8Psi4s8 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s8 (i8Psi4s8D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s8N0 hx).add (X.mul (hasDerivAt_i8Psi4s8N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s8N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s8N3 hx))).add ((X.pow
    4).mul (hasDerivAt_i8Psi4s8N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add (hasDerivAt_i8Psi4s8W
    hx)
  unfold i8Psi4s8
  refine e.congr_deriv ?_
  unfold i8Psi4s8D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 8 of `p₄` in `ξ`: from `t B2 A2 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s8 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * (2 + Real.log x * (1 + x) / (1 -
    x)) * ((1 + x) / (1 - x) * (2 * hpl [negOne, negOne] x))

/-- **`(Ψ₄⁽8⁾)'(ξ) ξ' = p₄⁽8⁾`**, in terms of `ξ`. -/
theorem i8Psi4s8D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s8D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s8 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s8D i8Psi4s8N0 i8Psi4s8N1 i8Psi4s8N2 i8Psi4s8N3 i8Psi4s8N4 i8Psi4s8dN0 i8Psi4s8dN1
    i8Psi4s8dN2 i8Psi4s8dN3 i8Psi4s8dN4 i8Psi4s8dW i8P4s8
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_mm hx,
    i13hw_0m0 hx, i13hw_m00 hx, i13hw_m0m hx, i13hw_mm0 hx, i13hw_0m0m hx, i13hw_0mm0 hx, i13hw_m00m
    hx, i13hw_m0m0 hx, i13hw_mm00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽9⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s9N0 (x : ℝ) : ℝ :=
    (-19 / 8) * hpl [negOne] x +
    (-3 / 2) * hpl [negOne, zero] x +
    (-19 / 4) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [negOne, zero, zero] x +
    (-3) * hpl [zero, negOne, zero] x +
    (-11 / 2) * hpl [zero, zero, negOne] x +
    (-1) * hpl [zero, negOne, zero, zero] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s9N0`. -/
noncomputable def i8Psi4s9dN0 (x : ℝ) : ℝ :=
    (-19 / 8) * (negOne.kernel x * hpl [] x) +
    (-3 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-19 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-3) * (zero.kernel x * hpl [negOne, zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s9N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s9N0 (i8Psi4s9dN0 x) x := by
  unfold i8Psi4s9N0 i8Psi4s9dN0
  exact ((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-19 / 8)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-19 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3)))

/-- The part of `ξ² Ψ₄⁽9⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s9N1 (x : ℝ) : ℝ :=
    (-35 / 8) +
    (-40) * hpl [negOne] x +
    (-2) * hpl [zero] x +
    (-24) * hpl [negOne, zero] x +
    (-40) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-24) * hpl [zero, negOne, zero] x +
    (-40) * hpl [zero, zero, negOne] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-16) * hpl [zero, zero, negOne, zero] x +
    (-24) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s9N1`. -/
noncomputable def i8Psi4s9dN1 (x : ℝ) : ℝ :=
    0 +
    (-40) * (negOne.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [] x) +
    (-24) * (negOne.kernel x * hpl [zero] x) +
    (-40) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero] x) +
    (-40) * (zero.kernel x * hpl [zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s9N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s9N1 (i8Psi4s9dN1 x) x := by
  unfold i8Psi4s9N1 i8Psi4s9dN1
  exact ((((((((((((hasDerivAt_const x (-35 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽9⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s9N2 (x : ℝ) : ℝ :=
    (-301 / 4) * hpl [negOne] x +
    (301 / 8) * hpl [zero] x +
    (45 / 2) * hpl [zero, zero] x +
    (-15) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s9N2`. -/
noncomputable def i8Psi4s9dN2 (x : ℝ) : ℝ :=
    (-301 / 4) * (negOne.kernel x * hpl [] x) +
    (301 / 8) * (zero.kernel x * hpl [] x) +
    (45 / 2) * (zero.kernel x * hpl [zero] x) +
    (-15) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s9N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s9N2 (i8Psi4s9dN2 x) x := by
  unfold i8Psi4s9N2 i8Psi4s9dN2
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-301 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (301 / 8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (45 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-15))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽9⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s9N3 (x : ℝ) : ℝ :=
    (541 / 8) +
    (-40) * hpl [negOne] x +
    (-30) * hpl [zero] x +
    (24) * hpl [negOne, zero] x +
    (40) * hpl [zero, negOne] x +
    (15 / 2) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-24) * hpl [zero, negOne, zero] x +
    (-40) * hpl [zero, zero, negOne] x +
    (8) * hpl [zero, negOne, zero, zero] x +
    (16) * hpl [zero, zero, negOne, zero] x +
    (24) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s9N3`. -/
noncomputable def i8Psi4s9dN3 (x : ℝ) : ℝ :=
    0 +
    (-40) * (negOne.kernel x * hpl [] x) +
    (-30) * (zero.kernel x * hpl [] x) +
    (24) * (negOne.kernel x * hpl [zero] x) +
    (40) * (zero.kernel x * hpl [negOne] x) +
    (15 / 2) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero] x) +
    (-40) * (zero.kernel x * hpl [zero, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (16) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (24) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s9N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s9N3 (i8Psi4s9dN3 x) x := by
  unfold i8Psi4s9N3 i8Psi4s9dN3
  exact ((((((((((((hasDerivAt_const x (541 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (15 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (24)))

/-- The part of `ξ² Ψ₄⁽9⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s9N4 (x : ℝ) : ℝ :=
    (13 / 8) +
    (-19 / 8) * hpl [negOne] x +
    (-7 / 8) * hpl [zero] x +
    (3 / 2) * hpl [negOne, zero] x +
    (19 / 4) * hpl [zero, negOne] x +
    (1 / 4) * hpl [zero, zero] x +
    (-1 / 2) * hpl [negOne, zero, zero] x +
    (-3) * hpl [zero, negOne, zero] x +
    (-11 / 2) * hpl [zero, zero, negOne] x +
    (1) * hpl [zero, negOne, zero, zero] x +
    (2) * hpl [zero, zero, negOne, zero] x +
    (3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s9N4`. -/
noncomputable def i8Psi4s9dN4 (x : ℝ) : ℝ :=
    0 +
    (-19 / 8) * (negOne.kernel x * hpl [] x) +
    (-7 / 8) * (zero.kernel x * hpl [] x) +
    (3 / 2) * (negOne.kernel x * hpl [zero] x) +
    (19 / 4) * (zero.kernel x * hpl [negOne] x) +
    (1 / 4) * (zero.kernel x * hpl [zero] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-3) * (zero.kernel x * hpl [negOne, zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s9N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s9N4 (i8Psi4s9dN4 x) x := by
  unfold i8Psi4s9N4 i8Psi4s9dN4
  exact ((((((((((((hasDerivAt_const x (13 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-19 / 8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-7 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (19 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (3)))

/-- The part of `Ψ₄⁽9⁾` with constant coefficients. -/
noncomputable def i8Psi4s9W (x : ℝ) : ℝ :=
    (15 / 2) * hpl [zero, zero, zero] x +
    (12) * hpl [zero, zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, zero, negOne, zero] x +
    (36) * hpl [zero, zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s9W`. -/
noncomputable def i8Psi4s9dW (x : ℝ) : ℝ :=
    (15 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (12) * (zero.kernel x * hpl [zero, negOne, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, zero, negOne, zero] x) +
    (36) * (zero.kernel x * hpl [zero, zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s9W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s9W (i8Psi4s9dW x) x := by
  unfold i8Psi4s9W i8Psi4s9dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (15 / 2)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, negOne] hx).const_mul (36)))

/-- The piece `Ψ₄⁽9⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s9 (x : ℝ) : ℝ :=
  (i8Psi4s9N0 x + x * i8Psi4s9N1 x + x ^ 2 * i8Psi4s9N2 x + x ^ 3 * i8Psi4s9N3 x +
    x ^ 4 * i8Psi4s9N4 x) / x ^ 2 + i8Psi4s9W x

/-- The derivative of `Ψ₄⁽9⁾`. -/
noncomputable def i8Psi4s9D (x : ℝ) : ℝ :=
  ((i8Psi4s9dN0 x + (i8Psi4s9N1 x + x * i8Psi4s9dN1 x) + (2 * x * i8Psi4s9N2 x +
    x ^ 2 * i8Psi4s9dN2 x) + (3 * x ^ 2 * i8Psi4s9N3 x + x ^ 3 * i8Psi4s9dN3 x) +
    (4 * x ^ 3 * i8Psi4s9N4 x + x ^ 4 * i8Psi4s9dN4 x)) * x ^ 2 - (i8Psi4s9N0 x +
    x * i8Psi4s9N1 x + x ^ 2 * i8Psi4s9N2 x + x ^ 3 * i8Psi4s9N3 x +
    x ^ 4 * i8Psi4s9N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s9dW x

theorem hasDerivAt_i8Psi4s9 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s9 (i8Psi4s9D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s9N0 hx).add (X.mul (hasDerivAt_i8Psi4s9N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s9N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s9N3 hx))).add ((X.pow
    4).mul (hasDerivAt_i8Psi4s9N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add (hasDerivAt_i8Psi4s9W
    hx)
  unfold i8Psi4s9
  refine e.congr_deriv ?_
  unfold i8Psi4s9D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 9 of `p₄` in `ξ`: from `t B2 A2 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s9 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * (2 + Real.log x * (1 + x) / (1 -
    x)) * ((1 + x) / (1 - x) * (-hpl [zero, negOne] x))

/-- **`(Ψ₄⁽9⁾)'(ξ) ξ' = p₄⁽9⁾`**, in terms of `ξ`. -/
theorem i8Psi4s9D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s9D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s9 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s9D i8Psi4s9N0 i8Psi4s9N1 i8Psi4s9N2 i8Psi4s9N3 i8Psi4s9N4 i8Psi4s9dN0 i8Psi4s9dN1
    i8Psi4s9dN2 i8Psi4s9dN3 i8Psi4s9dN4 i8Psi4s9dW i8P4s9
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_0m0 hx,
    i13hw_m00 hx, i13hw_00m0 hx, i13hw_0m00 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽10⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s10N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s10N0`. -/
noncomputable def i8Psi4s10dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s10N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s10N0 (i8Psi4s10dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽10⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s10N1 (x : ℝ) : ℝ :=
    (30 - π ^ 2 - 4 * zeta3) +
    (2 / 3 * π ^ 2) * hpl [negOne] x +
    (14 - π ^ 2 / 3) * hpl [zero] x +
    (-12) * hpl [negOne, zero] x +
    (6) * hpl [zero, zero] x +
    (8) * hpl [negOne, negOne, zero] x +
    (-4) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s10N1`. -/
noncomputable def i8Psi4s10dN1 (x : ℝ) : ℝ :=
    0 +
    (2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (14 - π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (-12) * (negOne.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s10N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s10N1 (i8Psi4s10dN1 x) x := by
  unfold i8Psi4s10N1 i8Psi4s10dN1
  exact (((((((((hasDerivAt_const x (30 - π ^ 2 - 4 * zeta3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (14 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽10⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s10N2 (x : ℝ) : ℝ :=
    (π ^ 2) * hpl [negOne] x +
    (16 + 4 * zeta3) * hpl [zero] x +
    (-15) * hpl [negOne, zero] x +
    (4 + π ^ 2 / 3) * hpl [zero, zero] x +
    (12) * hpl [negOne, negOne, zero] x +
    (-6) * hpl [negOne, zero, zero] x

/-- The derivative of `i8Psi4s10N2`. -/
noncomputable def i8Psi4s10dN2 (x : ℝ) : ℝ :=
    (π ^ 2) * (negOne.kernel x * hpl [] x) +
    (16 + 4 * zeta3) * (zero.kernel x * hpl [] x) +
    (-15) * (negOne.kernel x * hpl [zero] x) +
    (4 + π ^ 2 / 3) * (zero.kernel x * hpl [zero] x) +
    (12) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-6) * (negOne.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s10N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s10N2 (i8Psi4s10dN2 x) x := by
  unfold i8Psi4s10N2 i8Psi4s10dN2
  exact (((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (16 + 4 * zeta3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-15))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-6)))

/-- The part of `ξ² Ψ₄⁽10⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s10N3 (x : ℝ) : ℝ :=
    (9 - 4 * zeta3 - 2 / 3 * π ^ 2) +
    (2 / 3 * π ^ 2) * hpl [negOne] x +
    (7 - π ^ 2 / 3) * hpl [zero] x +
    (-8) * hpl [negOne, zero] x +
    (4) * hpl [zero, zero] x +
    (8) * hpl [negOne, negOne, zero] x +
    (-4) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s10N3`. -/
noncomputable def i8Psi4s10dN3 (x : ℝ) : ℝ :=
    0 +
    (2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (7 - π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s10N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s10N3 (i8Psi4s10dN3 x) x := by
  unfold i8Psi4s10N3 i8Psi4s10dN3
  exact (((((((((hasDerivAt_const x (9 - 4 * zeta3 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (7 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽10⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s10N4 (x : ℝ) : ℝ :=
    (-85 / 8 - 2 * zeta3 - 5 / 12 * π ^ 2) +
    (π ^ 2 / 3) * hpl [negOne] x +
    (21 / 4 - π ^ 2 / 6) * hpl [zero] x +
    (-5) * hpl [negOne, zero] x +
    (5 / 2) * hpl [zero, zero] x +
    (4) * hpl [negOne, negOne, zero] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s10N4`. -/
noncomputable def i8Psi4s10dN4 (x : ℝ) : ℝ :=
    0 +
    (π ^ 2 / 3) * (negOne.kernel x * hpl [] x) +
    (21 / 4 - π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (-5) * (negOne.kernel x * hpl [zero] x) +
    (5 / 2) * (zero.kernel x * hpl [zero] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s10N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s10N4 (i8Psi4s10dN4 x) x := by
  unfold i8Psi4s10N4 i8Psi4s10dN4
  exact (((((((((hasDerivAt_const x (-85 / 8 - 2 * zeta3 - 5 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (21 / 4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1)))

/-- The part of `Ψ₄⁽10⁾` with constant coefficients. -/
noncomputable def i8Psi4s10W (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (-8) * hpl [zero, negOne, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, zero] x +
    (4) * hpl [zero, zero, negOne, zero] x +
    (-2) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s10W`. -/
noncomputable def i8Psi4s10dW (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (-8) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s10W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s10W (i8Psi4s10dW x) x := by
  unfold i8Psi4s10W i8Psi4s10dW
  exact ((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-2)))

/-- The piece `Ψ₄⁽10⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s10 (x : ℝ) : ℝ :=
  (i8Psi4s10N0 x + x * i8Psi4s10N1 x + x ^ 2 * i8Psi4s10N2 x + x ^ 3 * i8Psi4s10N3 x +
    x ^ 4 * i8Psi4s10N4 x) / x ^ 2 + i8Psi4s10W x

/-- The derivative of `Ψ₄⁽10⁾`. -/
noncomputable def i8Psi4s10D (x : ℝ) : ℝ :=
  ((i8Psi4s10dN0 x + (i8Psi4s10N1 x + x * i8Psi4s10dN1 x) + (2 * x * i8Psi4s10N2 x +
    x ^ 2 * i8Psi4s10dN2 x) + (3 * x ^ 2 * i8Psi4s10N3 x + x ^ 3 * i8Psi4s10dN3 x) +
    (4 * x ^ 3 * i8Psi4s10N4 x + x ^ 4 * i8Psi4s10dN4 x)) * x ^ 2 - (i8Psi4s10N0 x +
    x * i8Psi4s10N1 x + x ^ 2 * i8Psi4s10N2 x + x ^ 3 * i8Psi4s10N3 x +
    x ^ 4 * i8Psi4s10N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s10dW x

theorem hasDerivAt_i8Psi4s10 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s10 (i8Psi4s10D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s10N0 hx).add (X.mul (hasDerivAt_i8Psi4s10N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s10N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s10N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s10N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s10W hx)
  unfold i8Psi4s10
  refine e.congr_deriv ?_
  unfold i8Psi4s10D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 10 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s10 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * (i13PB x - i13P1c)) * ((1 + x) / (1 -
    x) * (x / (1 + x)))

/-- **`(Ψ₄⁽10⁾)'(ξ) ξ' = p₄⁽10⁾`**, in terms of `ξ`. -/
theorem i8Psi4s10D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s10D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s10 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s10D i8Psi4s10N0 i8Psi4s10N1 i8Psi4s10N2 i8Psi4s10N3 i8Psi4s10N4 i8Psi4s10dN0
    i8Psi4s10dN1 i8Psi4s10dN2 i8Psi4s10dN3 i8Psi4s10dN4 i8Psi4s10dW i8P4s10 i13PB i13PBH i13P1c
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_000,
    i13hw_0m0 hx, i13hw_m00 hx, i13hw_mm0 hx]
  field_simp
  ring

end QED.ThreeLoopD
