/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P13

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 74 to 74

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s74`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s74D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s74`, `QED.ThreeLoopD.i8Psi4s74D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s74k0N0 (x : ℝ) : ℝ :=
    (4) * hpl [negOne, negOne, zero, one] x +
    (4) * hpl [negOne, negOne, one, zero] x +
    (4) * hpl [negOne, zero, negOne, one] x +
    (4) * hpl [negOne, zero, one, negOne] x

/-- The derivative of `i8Psi4s74k0N0`. -/
noncomputable def i8Psi4s74k0dN0 (x : ℝ) : ℝ :=
    (4) * (negOne.kernel x * hpl [negOne, zero, one] x) +
    (4) * (negOne.kernel x * hpl [negOne, one, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, negOne, one] x) +
    (4) * (negOne.kernel x * hpl [zero, one, negOne] x)

theorem hasDerivAt_i8Psi4s74k0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k0N0 (i8Psi4s74k0dN0 x) x := by
  unfold i8Psi4s74k0N0 i8Psi4s74k0dN0
  exact (((((hasDerivAt_hpl_cons negOne [negOne, zero, one] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, negOne] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s74k0N1 (x : ℝ) : ℝ :=
    (4) * hpl [negOne, one] x +
    (4) * hpl [one, negOne] x +
    (4) * hpl [negOne, zero, one] x +
    (4) * hpl [negOne, one, zero] x +
    (4) * hpl [zero, negOne, one] x +
    (4) * hpl [zero, one, negOne] x +
    (16) * hpl [negOne, negOne, zero, one] x +
    (16) * hpl [negOne, negOne, one, zero] x +
    (16) * hpl [negOne, zero, negOne, one] x +
    (16) * hpl [negOne, zero, one, negOne] x

/-- The derivative of `i8Psi4s74k0N1`. -/
noncomputable def i8Psi4s74k0dN1 (x : ℝ) : ℝ :=
    (4) * (negOne.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [negOne] x) +
    (4) * (negOne.kernel x * hpl [zero, one] x) +
    (4) * (negOne.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, one] x) +
    (4) * (zero.kernel x * hpl [one, negOne] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, one] x) +
    (16) * (negOne.kernel x * hpl [negOne, one, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, negOne, one] x) +
    (16) * (negOne.kernel x * hpl [zero, one, negOne] x)

theorem hasDerivAt_i8Psi4s74k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k0N1 (i8Psi4s74k0dN1 x) x := by
  unfold i8Psi4s74k0N1 i8Psi4s74k0dN1
  exact (((((((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s74k0N2 (x : ℝ) : ℝ :=
    (25 / 2) * hpl [negOne] x +
    (22) * hpl [one] x +
    (15) * hpl [negOne, one] x +
    (-4) * hpl [zero, one] x +
    (-17) * hpl [one, negOne] x +
    (-11) * hpl [one, zero] x +
    (-6) * hpl [negOne, zero, one] x +
    (-6) * hpl [negOne, one, zero] x +
    (24) * hpl [negOne, negOne, zero, one] x +
    (24) * hpl [negOne, negOne, one, zero] x +
    (24) * hpl [negOne, zero, negOne, one] x +
    (24) * hpl [negOne, zero, one, negOne] x

/-- The derivative of `i8Psi4s74k0N2`. -/
noncomputable def i8Psi4s74k0dN2 (x : ℝ) : ℝ :=
    (25 / 2) * (negOne.kernel x * hpl [] x) +
    (22) * (one.kernel x * hpl [] x) +
    (15) * (negOne.kernel x * hpl [one] x) +
    (-4) * (zero.kernel x * hpl [one] x) +
    (-17) * (one.kernel x * hpl [negOne] x) +
    (-11) * (one.kernel x * hpl [zero] x) +
    (-6) * (negOne.kernel x * hpl [zero, one] x) +
    (-6) * (negOne.kernel x * hpl [one, zero] x) +
    (24) * (negOne.kernel x * hpl [negOne, zero, one] x) +
    (24) * (negOne.kernel x * hpl [negOne, one, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, negOne, one] x) +
    (24) * (negOne.kernel x * hpl [zero, one, negOne] x)

theorem hasDerivAt_i8Psi4s74k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k0N2 (i8Psi4s74k0dN2 x) x := by
  unfold i8Psi4s74k0N2 i8Psi4s74k0dN2
  exact (((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (25 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (22))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-17))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, negOne] hx).const_mul (24)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s74k0N3 (x : ℝ) : ℝ :=
    (-91 / 2) +
    (13) * hpl [negOne] x +
    (11) * hpl [zero] x +
    (-21) * hpl [one] x +
    (12) * hpl [negOne, one] x +
    (10) * hpl [zero, one] x +
    (12) * hpl [one, negOne] x +
    (10) * hpl [one, zero] x +
    (-12) * hpl [negOne, zero, one] x +
    (-12) * hpl [negOne, one, zero] x +
    (-12) * hpl [zero, negOne, one] x +
    (-12) * hpl [zero, one, negOne] x +
    (16) * hpl [negOne, negOne, zero, one] x +
    (16) * hpl [negOne, negOne, one, zero] x +
    (16) * hpl [negOne, zero, negOne, one] x +
    (16) * hpl [negOne, zero, one, negOne] x

/-- The derivative of `i8Psi4s74k0N3`. -/
noncomputable def i8Psi4s74k0dN3 (x : ℝ) : ℝ :=
    0 +
    (13) * (negOne.kernel x * hpl [] x) +
    (11) * (zero.kernel x * hpl [] x) +
    (-21) * (one.kernel x * hpl [] x) +
    (12) * (negOne.kernel x * hpl [one] x) +
    (10) * (zero.kernel x * hpl [one] x) +
    (12) * (one.kernel x * hpl [negOne] x) +
    (10) * (one.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, one] x) +
    (-12) * (negOne.kernel x * hpl [one, zero] x) +
    (-12) * (zero.kernel x * hpl [negOne, one] x) +
    (-12) * (zero.kernel x * hpl [one, negOne] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, one] x) +
    (16) * (negOne.kernel x * hpl [negOne, one, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, negOne, one] x) +
    (16) * (negOne.kernel x * hpl [zero, one, negOne] x)

theorem hasDerivAt_i8Psi4s74k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k0N3 (i8Psi4s74k0dN3 x) x := by
  unfold i8Psi4s74k0N3 i8Psi4s74k0dN3
  exact ((((((((((((((((hasDerivAt_const x (-91 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (13))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (11))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-21))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s74k0N4 (x : ℝ) : ℝ :=
    (-1) +
    (1 / 2) * hpl [negOne] x +
    (1 / 2) * hpl [zero] x +
    (-1) * hpl [one] x +
    (1) * hpl [negOne, one] x +
    (1) * hpl [zero, one] x +
    (1) * hpl [one, negOne] x +
    (1) * hpl [one, zero] x +
    (-2) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, one, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, one, negOne] x +
    (4) * hpl [negOne, negOne, zero, one] x +
    (4) * hpl [negOne, negOne, one, zero] x +
    (4) * hpl [negOne, zero, negOne, one] x +
    (4) * hpl [negOne, zero, one, negOne] x

/-- The derivative of `i8Psi4s74k0N4`. -/
noncomputable def i8Psi4s74k0dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-1) * (one.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (1) * (one.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero, one] x) +
    (4) * (negOne.kernel x * hpl [negOne, one, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, negOne, one] x) +
    (4) * (negOne.kernel x * hpl [zero, one, negOne] x)

theorem hasDerivAt_i8Psi4s74k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k0N4 (i8Psi4s74k0dN4 x) x := by
  unfold i8Psi4s74k0N4 i8Psi4s74k0dN4
  exact ((((((((((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, negOne] hx).const_mul (4)))

/-- The part of `Ψ₄⁽74⁾` with constant coefficients. -/
noncomputable def i8Psi4s74k0W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, negOne] x +
    (-4) * hpl [zero, zero, one] x +
    (-4) * hpl [zero, one, zero] x +
    (-12) * hpl [zero, negOne, zero, one] x +
    (-12) * hpl [zero, negOne, one, zero] x +
    (-12) * hpl [zero, zero, negOne, one] x +
    (-12) * hpl [zero, zero, one, negOne] x

/-- The derivative of `i8Psi4s74k0W`. -/
noncomputable def i8Psi4s74k0dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [negOne] x) +
    (-4) * (zero.kernel x * hpl [zero, one] x) +
    (-4) * (zero.kernel x * hpl [one, zero] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (-12) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (-12) * (zero.kernel x * hpl [zero, one, negOne] x)

theorem hasDerivAt_i8Psi4s74k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k0W (i8Psi4s74k0dW x) x := by
  unfold i8Psi4s74k0W i8Psi4s74k0dW
  exact ((((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-12)))

/-- Chunk 0 of the piece `Ψ₄⁽74⁾`. -/
noncomputable def i8Psi4s74k0 (x : ℝ) : ℝ :=
  (i8Psi4s74k0N0 x + x * i8Psi4s74k0N1 x + x ^ 2 * i8Psi4s74k0N2 x + x ^ 3 * i8Psi4s74k0N3 x +
    x ^ 4 * i8Psi4s74k0N4 x) / x ^ 2 + i8Psi4s74k0W x

/-- The derivative of `i8Psi4s74k0`. -/
noncomputable def i8Psi4s74k0D (x : ℝ) : ℝ :=
  ((i8Psi4s74k0dN0 x + (i8Psi4s74k0N1 x + x * i8Psi4s74k0dN1 x) + (2 * x * i8Psi4s74k0N2 x +
    x ^ 2 * i8Psi4s74k0dN2 x) + (3 * x ^ 2 * i8Psi4s74k0N3 x + x ^ 3 * i8Psi4s74k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s74k0N4 x + x ^ 4 * i8Psi4s74k0dN4 x)) * x ^ 2 - (i8Psi4s74k0N0 x +
    x * i8Psi4s74k0N1 x + x ^ 2 * i8Psi4s74k0N2 x + x ^ 3 * i8Psi4s74k0N3 x +
    x ^ 4 * i8Psi4s74k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s74k0dW x

theorem hasDerivAt_i8Psi4s74k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k0 (i8Psi4s74k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s74k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s74k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s74k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s74k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s74k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s74k0W hx)
  unfold i8Psi4s74k0
  refine e.congr_deriv ?_
  unfold i8Psi4s74k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽74⁾` over words. -/
noncomputable def i8P4w74k0 (x : ℝ) : ℝ :=
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [negOne, negOne, zero, one] x +
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [negOne, negOne, one, zero] x +
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [negOne, zero, negOne, one] x +
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [negOne, zero, one, negOne] x

theorem i8Psi4s74k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s74k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w74k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s74k0D i8Psi4s74k0N0 i8Psi4s74k0N1 i8Psi4s74k0N2 i8Psi4s74k0N3 i8Psi4s74k0N4
    i8Psi4s74k0dN0 i8Psi4s74k0dN1 i8Psi4s74k0dN2 i8Psi4s74k0dN3 i8Psi4s74k0dN4 i8Psi4s74k0dW
    i8P4w74k0
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [negOne, negOne, zero, one] x = v0 at *
  generalize hpl [negOne, negOne, one, zero] x = v1 at *
  generalize hpl [negOne, zero, negOne, one] x = v2 at *
  generalize hpl [negOne, zero, one, negOne] x = v3 at *
  generalize hpl [zero, negOne, zero, one] x = v4 at *
  generalize hpl [zero, negOne, one, zero] x = v5 at *
  generalize hpl [zero, zero, negOne, one] x = v6 at *
  generalize hpl [zero, zero, one, negOne] x = v7 at *
  generalize hpl [negOne, zero, one] x = v8 at *
  generalize hpl [negOne, one, zero] x = v9 at *
  generalize hpl [zero, negOne, one] x = v10 at *
  generalize hpl [zero, zero, one] x = v11 at *
  generalize hpl [zero, one, negOne] x = v12 at *
  generalize hpl [zero, one, zero] x = v13 at *
  generalize hpl [negOne, one] x = v14 at *
  generalize hpl [zero, negOne] x = v15 at *
  generalize hpl [zero, one] x = v16 at *
  generalize hpl [one, negOne] x = v17 at *
  generalize hpl [one, zero] x = v18 at *
  generalize hpl [negOne] x = v19 at *
  generalize hpl [zero] x = v20 at *
  generalize hpl [one] x = v21 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s74k1N0 (x : ℝ) : ℝ :=
    (2) * hpl [negOne, negOne, one] x +
    (2) * hpl [negOne, one, negOne] x +
    (4) * hpl [negOne, one, negOne, zero] x +
    (4) * hpl [negOne, one, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne, one] x +
    (4) * hpl [zero, negOne, one, negOne] x

/-- The derivative of `i8Psi4s74k1N0`. -/
noncomputable def i8Psi4s74k1dN0 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [negOne, one] x) +
    (2) * (negOne.kernel x * hpl [one, negOne] x) +
    (4) * (negOne.kernel x * hpl [one, negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [one, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (4) * (zero.kernel x * hpl [negOne, one, negOne] x)

theorem hasDerivAt_i8Psi4s74k1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k1N0 (i8Psi4s74k1dN0 x) x := by
  unfold i8Psi4s74k1N0 i8Psi4s74k1dN0
  exact (((((((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s74k1N1 (x : ℝ) : ℝ :=
    (2) * hpl [negOne, one] x +
    (2) * hpl [one, negOne] x +
    (16) * hpl [negOne, negOne, one] x +
    (16) * hpl [negOne, one, negOne] x +
    (4) * hpl [one, negOne, zero] x +
    (4) * hpl [one, zero, negOne] x +
    (16) * hpl [negOne, one, negOne, zero] x +
    (16) * hpl [negOne, one, zero, negOne] x +
    (16) * hpl [zero, negOne, negOne, one] x +
    (16) * hpl [zero, negOne, one, negOne] x

/-- The derivative of `i8Psi4s74k1N1`. -/
noncomputable def i8Psi4s74k1dN1 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [negOne] x) +
    (16) * (negOne.kernel x * hpl [negOne, one] x) +
    (16) * (negOne.kernel x * hpl [one, negOne] x) +
    (4) * (one.kernel x * hpl [negOne, zero] x) +
    (4) * (one.kernel x * hpl [zero, negOne] x) +
    (16) * (negOne.kernel x * hpl [one, negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [one, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (16) * (zero.kernel x * hpl [negOne, one, negOne] x)

theorem hasDerivAt_i8Psi4s74k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k1N1 (i8Psi4s74k1dN1 x) x := by
  unfold i8Psi4s74k1N1 i8Psi4s74k1dN1
  exact (((((((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s74k1N2 (x : ℝ) : ℝ :=
    (28) * hpl [negOne] x +
    (27 / 2) * hpl [one] x +
    (-13) * hpl [negOne, zero] x +
    (15) * hpl [negOne, one] x +
    (-2) * hpl [zero, negOne] x +
    (-17) * hpl [one, negOne] x +
    (10) * hpl [one, negOne, zero] x +
    (10) * hpl [one, zero, negOne] x +
    (24) * hpl [negOne, one, negOne, zero] x +
    (24) * hpl [negOne, one, zero, negOne] x

/-- The derivative of `i8Psi4s74k1N2`. -/
noncomputable def i8Psi4s74k1dN2 (x : ℝ) : ℝ :=
    (28) * (negOne.kernel x * hpl [] x) +
    (27 / 2) * (one.kernel x * hpl [] x) +
    (-13) * (negOne.kernel x * hpl [zero] x) +
    (15) * (negOne.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [negOne] x) +
    (-17) * (one.kernel x * hpl [negOne] x) +
    (10) * (one.kernel x * hpl [negOne, zero] x) +
    (10) * (one.kernel x * hpl [zero, negOne] x) +
    (24) * (negOne.kernel x * hpl [one, negOne, zero] x) +
    (24) * (negOne.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s74k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k1N2 (i8Psi4s74k1dN2 x) x := by
  unfold i8Psi4s74k1N2 i8Psi4s74k1dN2
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (28)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (27 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-13))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-17))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, negOne] hx).const_mul (24)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s74k1N3 (x : ℝ) : ℝ :=
    (-109 / 2) +
    (29) * hpl [negOne] x +
    (13) * hpl [zero] x +
    (-13) * hpl [one] x +
    (-14) * hpl [negOne, zero] x +
    (14) * hpl [negOne, one] x +
    (-14) * hpl [zero, negOne] x +
    (14) * hpl [one, negOne] x +
    (-16) * hpl [negOne, negOne, one] x +
    (-16) * hpl [negOne, one, negOne] x +
    (-12) * hpl [one, negOne, zero] x +
    (-12) * hpl [one, zero, negOne] x +
    (16) * hpl [negOne, one, negOne, zero] x +
    (16) * hpl [negOne, one, zero, negOne] x +
    (16) * hpl [zero, negOne, negOne, one] x +
    (16) * hpl [zero, negOne, one, negOne] x

/-- The derivative of `i8Psi4s74k1N3`. -/
noncomputable def i8Psi4s74k1dN3 (x : ℝ) : ℝ :=
    0 +
    (29) * (negOne.kernel x * hpl [] x) +
    (13) * (zero.kernel x * hpl [] x) +
    (-13) * (one.kernel x * hpl [] x) +
    (-14) * (negOne.kernel x * hpl [zero] x) +
    (14) * (negOne.kernel x * hpl [one] x) +
    (-14) * (zero.kernel x * hpl [negOne] x) +
    (14) * (one.kernel x * hpl [negOne] x) +
    (-16) * (negOne.kernel x * hpl [negOne, one] x) +
    (-16) * (negOne.kernel x * hpl [one, negOne] x) +
    (-12) * (one.kernel x * hpl [negOne, zero] x) +
    (-12) * (one.kernel x * hpl [zero, negOne] x) +
    (16) * (negOne.kernel x * hpl [one, negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [one, zero, negOne] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (16) * (zero.kernel x * hpl [negOne, one, negOne] x)

theorem hasDerivAt_i8Psi4s74k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k1N3 (i8Psi4s74k1dN3 x) x := by
  unfold i8Psi4s74k1N3 i8Psi4s74k1dN3
  exact ((((((((((((((((hasDerivAt_const x (-109 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (29))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (13))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-13))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s74k1N4 (x : ℝ) : ℝ :=
    (-1) +
    (1) * hpl [negOne] x +
    (1 / 2) * hpl [zero] x +
    (-1 / 2) * hpl [one] x +
    (-1) * hpl [negOne, zero] x +
    (1) * hpl [negOne, one] x +
    (-1) * hpl [zero, negOne] x +
    (1) * hpl [one, negOne] x +
    (-2) * hpl [negOne, negOne, one] x +
    (-2) * hpl [negOne, one, negOne] x +
    (-2) * hpl [one, negOne, zero] x +
    (-2) * hpl [one, zero, negOne] x +
    (4) * hpl [negOne, one, negOne, zero] x +
    (4) * hpl [negOne, one, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne, one] x +
    (4) * hpl [zero, negOne, one, negOne] x

/-- The derivative of `i8Psi4s74k1N4`. -/
noncomputable def i8Psi4s74k1dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, one] x) +
    (-2) * (negOne.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x) +
    (4) * (negOne.kernel x * hpl [one, negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [one, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (4) * (zero.kernel x * hpl [negOne, one, negOne] x)

theorem hasDerivAt_i8Psi4s74k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k1N4 (i8Psi4s74k1dN4 x) x := by
  unfold i8Psi4s74k1N4 i8Psi4s74k1dN4
  exact ((((((((((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (4)))

/-- The part of `Ψ₄⁽74⁾` with constant coefficients. -/
noncomputable def i8Psi4s74k1W (x : ℝ) : ℝ :=
    (-2) * hpl [zero, one] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-14) * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, zero, negOne] x +
    (-14) * hpl [zero, one, negOne] x +
    (-12) * hpl [zero, one, negOne, zero] x +
    (-12) * hpl [zero, one, zero, negOne] x

/-- The derivative of `i8Psi4s74k1W`. -/
noncomputable def i8Psi4s74k1dW (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [one] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-14) * (zero.kernel x * hpl [negOne, one] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne] x) +
    (-14) * (zero.kernel x * hpl [one, negOne] x) +
    (-12) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s74k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k1W (i8Psi4s74k1dW x) x := by
  unfold i8Psi4s74k1W i8Psi4s74k1dW
  exact ((((((((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-12)))

/-- Chunk 1 of the piece `Ψ₄⁽74⁾`. -/
noncomputable def i8Psi4s74k1 (x : ℝ) : ℝ :=
  (i8Psi4s74k1N0 x + x * i8Psi4s74k1N1 x + x ^ 2 * i8Psi4s74k1N2 x + x ^ 3 * i8Psi4s74k1N3 x +
    x ^ 4 * i8Psi4s74k1N4 x) / x ^ 2 + i8Psi4s74k1W x

/-- The derivative of `i8Psi4s74k1`. -/
noncomputable def i8Psi4s74k1D (x : ℝ) : ℝ :=
  ((i8Psi4s74k1dN0 x + (i8Psi4s74k1N1 x + x * i8Psi4s74k1dN1 x) + (2 * x * i8Psi4s74k1N2 x +
    x ^ 2 * i8Psi4s74k1dN2 x) + (3 * x ^ 2 * i8Psi4s74k1N3 x + x ^ 3 * i8Psi4s74k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s74k1N4 x + x ^ 4 * i8Psi4s74k1dN4 x)) * x ^ 2 - (i8Psi4s74k1N0 x +
    x * i8Psi4s74k1N1 x + x ^ 2 * i8Psi4s74k1N2 x + x ^ 3 * i8Psi4s74k1N3 x +
    x ^ 4 * i8Psi4s74k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s74k1dW x

theorem hasDerivAt_i8Psi4s74k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k1 (i8Psi4s74k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s74k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s74k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s74k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s74k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s74k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s74k1W hx)
  unfold i8Psi4s74k1
  refine e.congr_deriv ?_
  unfold i8Psi4s74k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽74⁾` over words. -/
noncomputable def i8P4w74k1 (x : ℝ) : ℝ :=
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [negOne, one, negOne, zero] x +
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [negOne, one, zero, negOne] x +
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [zero, negOne, negOne, one] x +
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [zero, negOne, one, negOne] x

theorem i8Psi4s74k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s74k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w74k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s74k1D i8Psi4s74k1N0 i8Psi4s74k1N1 i8Psi4s74k1N2 i8Psi4s74k1N3 i8Psi4s74k1N4
    i8Psi4s74k1dN0 i8Psi4s74k1dN1 i8Psi4s74k1dN2 i8Psi4s74k1dN3 i8Psi4s74k1dN4 i8Psi4s74k1dW
    i8P4w74k1
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [negOne, one, negOne, zero] x = v0 at *
  generalize hpl [negOne, one, zero, negOne] x = v1 at *
  generalize hpl [zero, negOne, negOne, one] x = v2 at *
  generalize hpl [zero, negOne, one, negOne] x = v3 at *
  generalize hpl [zero, one, negOne, zero] x = v4 at *
  generalize hpl [zero, one, zero, negOne] x = v5 at *
  generalize hpl [negOne, negOne, one] x = v6 at *
  generalize hpl [negOne, one, negOne] x = v7 at *
  generalize hpl [zero, negOne, zero] x = v8 at *
  generalize hpl [zero, negOne, one] x = v9 at *
  generalize hpl [zero, zero, negOne] x = v10 at *
  generalize hpl [zero, one, negOne] x = v11 at *
  generalize hpl [one, negOne, zero] x = v12 at *
  generalize hpl [one, zero, negOne] x = v13 at *
  generalize hpl [negOne, zero] x = v14 at *
  generalize hpl [negOne, one] x = v15 at *
  generalize hpl [zero, negOne] x = v16 at *
  generalize hpl [zero, one] x = v17 at *
  generalize hpl [one, negOne] x = v18 at *
  generalize hpl [negOne] x = v19 at *
  generalize hpl [zero] x = v20 at *
  generalize hpl [one] x = v21 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s74k2N0 (x : ℝ) : ℝ :=
    (2) * hpl [one, negOne, negOne] x +
    (4) * hpl [zero, one, negOne, negOne] x +
    (4) * hpl [one, negOne, negOne, zero] x +
    (4) * hpl [one, negOne, zero, negOne] x +
    (4) * hpl [one, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s74k2N0`. -/
noncomputable def i8Psi4s74k2dN0 (x : ℝ) : ℝ :=
    (2) * (one.kernel x * hpl [negOne, negOne] x) +
    (4) * (zero.kernel x * hpl [one, negOne, negOne] x) +
    (4) * (one.kernel x * hpl [negOne, negOne, zero] x) +
    (4) * (one.kernel x * hpl [negOne, zero, negOne] x) +
    (4) * (one.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s74k2N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k2N0 (i8Psi4s74k2dN0 x) x := by
  unfold i8Psi4s74k2N0 i8Psi4s74k2dN0
  exact ((((((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, negOne] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s74k2N1 (x : ℝ) : ℝ :=
    (6) * hpl [negOne, negOne] x +
    (4) * hpl [negOne, negOne, zero] x +
    (4) * hpl [negOne, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne] x +
    (16) * hpl [one, negOne, negOne] x +
    (16) * hpl [zero, one, negOne, negOne] x +
    (16) * hpl [one, negOne, negOne, zero] x +
    (16) * hpl [one, negOne, zero, negOne] x +
    (16) * hpl [one, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s74k2N1`. -/
noncomputable def i8Psi4s74k2dN1 (x : ℝ) : ℝ :=
    (6) * (negOne.kernel x * hpl [negOne] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne] x) +
    (16) * (one.kernel x * hpl [negOne, negOne] x) +
    (16) * (zero.kernel x * hpl [one, negOne, negOne] x) +
    (16) * (one.kernel x * hpl [negOne, negOne, zero] x) +
    (16) * (one.kernel x * hpl [negOne, zero, negOne] x) +
    (16) * (one.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s74k2N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k2N1 (i8Psi4s74k2dN1 x) x := by
  unfold i8Psi4s74k2N1 i8Psi4s74k2dN1
  exact ((((((((((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (6)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s74k2N2 (x : ℝ) : ℝ :=
    (105 / 2) * hpl [negOne] x +
    (-30) * hpl [negOne, negOne] x +
    (-17) * hpl [negOne, zero] x +
    (-6) * hpl [zero, negOne] x +
    (22) * hpl [negOne, negOne, zero] x +
    (22) * hpl [negOne, zero, negOne] x +
    (-18) * hpl [zero, negOne, negOne] x +
    (-40) * hpl [one, negOne, negOne, zero] x +
    (-40) * hpl [one, negOne, zero, negOne] x +
    (-40) * hpl [one, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s74k2N2`. -/
noncomputable def i8Psi4s74k2dN2 (x : ℝ) : ℝ :=
    (105 / 2) * (negOne.kernel x * hpl [] x) +
    (-30) * (negOne.kernel x * hpl [negOne] x) +
    (-17) * (negOne.kernel x * hpl [zero] x) +
    (-6) * (zero.kernel x * hpl [negOne] x) +
    (22) * (negOne.kernel x * hpl [negOne, zero] x) +
    (22) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-18) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-40) * (one.kernel x * hpl [negOne, negOne, zero] x) +
    (-40) * (one.kernel x * hpl [negOne, zero, negOne] x) +
    (-40) * (one.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s74k2N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k2N2 (i8Psi4s74k2dN2 x) x := by
  unfold i8Psi4s74k2N2 i8Psi4s74k2dN2
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (105 / 2)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-17))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (22))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (22))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, zero] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, negOne] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, negOne] hx).const_mul (-40)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s74k2N3 (x : ℝ) : ℝ :=
    (-139 / 2) +
    (54) * hpl [negOne] x +
    (17) * hpl [zero] x +
    (-38) * hpl [negOne, negOne] x +
    (-18) * hpl [negOne, zero] x +
    (-18) * hpl [zero, negOne] x +
    (20) * hpl [negOne, negOne, zero] x +
    (20) * hpl [negOne, zero, negOne] x +
    (20) * hpl [zero, negOne, negOne] x +
    (-16) * hpl [one, negOne, negOne] x +
    (16) * hpl [zero, one, negOne, negOne] x +
    (16) * hpl [one, negOne, negOne, zero] x +
    (16) * hpl [one, negOne, zero, negOne] x +
    (16) * hpl [one, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s74k2N3`. -/
noncomputable def i8Psi4s74k2dN3 (x : ℝ) : ℝ :=
    0 +
    (54) * (negOne.kernel x * hpl [] x) +
    (17) * (zero.kernel x * hpl [] x) +
    (-38) * (negOne.kernel x * hpl [negOne] x) +
    (-18) * (negOne.kernel x * hpl [zero] x) +
    (-18) * (zero.kernel x * hpl [negOne] x) +
    (20) * (negOne.kernel x * hpl [negOne, zero] x) +
    (20) * (negOne.kernel x * hpl [zero, negOne] x) +
    (20) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-16) * (one.kernel x * hpl [negOne, negOne] x) +
    (16) * (zero.kernel x * hpl [one, negOne, negOne] x) +
    (16) * (one.kernel x * hpl [negOne, negOne, zero] x) +
    (16) * (one.kernel x * hpl [negOne, zero, negOne] x) +
    (16) * (one.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s74k2N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k2N3 (i8Psi4s74k2dN3 x) x := by
  unfold i8Psi4s74k2N3 i8Psi4s74k2dN3
  exact ((((((((((((((hasDerivAt_const x (-139 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (54))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (17))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-38))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽74⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s74k2N4 (x : ℝ) : ℝ :=
    (-1) +
    (3 / 2) * hpl [negOne] x +
    (1 / 2) * hpl [zero] x +
    (-2) * hpl [negOne, negOne] x +
    (-1) * hpl [negOne, zero] x +
    (-1) * hpl [zero, negOne] x +
    (2) * hpl [negOne, negOne, zero] x +
    (2) * hpl [negOne, zero, negOne] x +
    (2) * hpl [zero, negOne, negOne] x +
    (-2) * hpl [one, negOne, negOne] x +
    (4) * hpl [zero, one, negOne, negOne] x +
    (4) * hpl [one, negOne, negOne, zero] x +
    (4) * hpl [one, negOne, zero, negOne] x +
    (4) * hpl [one, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s74k2N4`. -/
noncomputable def i8Psi4s74k2dN4 (x : ℝ) : ℝ :=
    0 +
    (3 / 2) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, negOne] x) +
    (4) * (zero.kernel x * hpl [one, negOne, negOne] x) +
    (4) * (one.kernel x * hpl [negOne, negOne, zero] x) +
    (4) * (one.kernel x * hpl [negOne, zero, negOne] x) +
    (4) * (one.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s74k2N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k2N4 (i8Psi4s74k2dN4 x) x := by
  unfold i8Psi4s74k2N4 i8Psi4s74k2dN4
  exact ((((((((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, negOne] hx).const_mul (4)))

/-- The part of `Ψ₄⁽74⁾` with constant coefficients. -/
noncomputable def i8Psi4s74k2W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne] x +
    (-20) * hpl [zero, negOne, negOne, zero] x +
    (-20) * hpl [zero, negOne, zero, negOne] x +
    (-20) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s74k2W`. -/
noncomputable def i8Psi4s74k2dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne] x) +
    (-20) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (-20) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-20) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s74k2W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k2W (i8Psi4s74k2dW x) x := by
  unfold i8Psi4s74k2W i8Psi4s74k2dW
  exact ((((((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (-20)))

/-- Chunk 2 of the piece `Ψ₄⁽74⁾`. -/
noncomputable def i8Psi4s74k2 (x : ℝ) : ℝ :=
  (i8Psi4s74k2N0 x + x * i8Psi4s74k2N1 x + x ^ 2 * i8Psi4s74k2N2 x + x ^ 3 * i8Psi4s74k2N3 x +
    x ^ 4 * i8Psi4s74k2N4 x) / x ^ 2 + i8Psi4s74k2W x

/-- The derivative of `i8Psi4s74k2`. -/
noncomputable def i8Psi4s74k2D (x : ℝ) : ℝ :=
  ((i8Psi4s74k2dN0 x + (i8Psi4s74k2N1 x + x * i8Psi4s74k2dN1 x) + (2 * x * i8Psi4s74k2N2 x +
    x ^ 2 * i8Psi4s74k2dN2 x) + (3 * x ^ 2 * i8Psi4s74k2N3 x + x ^ 3 * i8Psi4s74k2dN3 x) +
    (4 * x ^ 3 * i8Psi4s74k2N4 x + x ^ 4 * i8Psi4s74k2dN4 x)) * x ^ 2 - (i8Psi4s74k2N0 x +
    x * i8Psi4s74k2N1 x + x ^ 2 * i8Psi4s74k2N2 x + x ^ 3 * i8Psi4s74k2N3 x +
    x ^ 4 * i8Psi4s74k2N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s74k2dW x

theorem hasDerivAt_i8Psi4s74k2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74k2 (i8Psi4s74k2D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s74k2N0 hx).add (X.mul (hasDerivAt_i8Psi4s74k2N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s74k2N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s74k2N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s74k2N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s74k2W hx)
  unfold i8Psi4s74k2
  refine e.congr_deriv ?_
  unfold i8Psi4s74k2D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 2 of `p₄⁽74⁾` over words. -/
noncomputable def i8P4w74k2 (x : ℝ) : ℝ :=
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [zero, one, negOne, negOne] x +
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [one, negOne, negOne, zero] x +
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [one, negOne, zero, negOne] x +
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [one, zero, negOne, negOne] x

theorem i8Psi4s74k2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s74k2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w74k2 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s74k2D i8Psi4s74k2N0 i8Psi4s74k2N1 i8Psi4s74k2N2 i8Psi4s74k2N3 i8Psi4s74k2N4
    i8Psi4s74k2dN0 i8Psi4s74k2dN1 i8Psi4s74k2dN2 i8Psi4s74k2dN3 i8Psi4s74k2dN4 i8Psi4s74k2dW
    i8P4w74k2
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, negOne, zero] x = v0 at *
  generalize hpl [zero, negOne, zero, negOne] x = v1 at *
  generalize hpl [zero, zero, negOne, negOne] x = v2 at *
  generalize hpl [zero, one, negOne, negOne] x = v3 at *
  generalize hpl [one, negOne, negOne, zero] x = v4 at *
  generalize hpl [one, negOne, zero, negOne] x = v5 at *
  generalize hpl [one, zero, negOne, negOne] x = v6 at *
  generalize hpl [negOne, negOne, zero] x = v7 at *
  generalize hpl [negOne, zero, negOne] x = v8 at *
  generalize hpl [zero, negOne, negOne] x = v9 at *
  generalize hpl [zero, negOne, zero] x = v10 at *
  generalize hpl [zero, zero, negOne] x = v11 at *
  generalize hpl [one, negOne, negOne] x = v12 at *
  generalize hpl [negOne, negOne] x = v13 at *
  generalize hpl [negOne, zero] x = v14 at *
  generalize hpl [zero, negOne] x = v15 at *
  generalize hpl [negOne] x = v16 at *
  generalize hpl [zero] x = v17 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽74⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s74 (x : ℝ) : ℝ :=
  i8Psi4s74k0 x + i8Psi4s74k1 x + i8Psi4s74k2 x

/-- The derivative of `Ψ₄⁽74⁾`. -/
noncomputable def i8Psi4s74D (x : ℝ) : ℝ :=
  i8Psi4s74k0D x + i8Psi4s74k1D x + i8Psi4s74k2D x

theorem hasDerivAt_i8Psi4s74 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s74 (i8Psi4s74D x) x := by
  unfold i8Psi4s74 i8Psi4s74D
  exact (((hasDerivAt_i8Psi4s74k0 hx).add (hasDerivAt_i8Psi4s74k1 hx)).add (hasDerivAt_i8Psi4s74k2
    hx))

/-- The sub-piece 74 of `p₄` in `ξ`: from `t B1 A2 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s74 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 - x) * (1 * hpl [zero] x)) * ((1 +
    x) / (1 - x) * (2 * hpl [negOne, negOne] x)))

/-- `p₄⁽74⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w74 (x : ℝ) : ℝ :=
  i8P4w74k0 x + i8P4w74k1 x + i8P4w74k2 x

theorem i8P4s74_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s74 x = i8P4w74 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s74 i8P4w74 i8P4w74k0 i8P4w74k1 i8P4w74k2
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [zero] [one] hx
  have e1 := hpl_mul_hpl [negOne, negOne] [zero, one] hx
  have e2 := hpl_mul_hpl [negOne, negOne] [one, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0 e1 e2
  linear_combination (norm := skip) (((8 + 8 * x ^ 2 +
    16 * x) / (x)) * hpl [negOne, negOne] x) * e0 + (((8 + 8 * x ^ 2 + 16 * x) / (x))) * e1 +
    (((8 + 8 * x ^ 2 + 16 * x) / (x))) * e2
  field_simp
  generalize hpl [negOne, negOne, zero, one] x = v0 at *
  generalize hpl [negOne, negOne, one, zero] x = v1 at *
  generalize hpl [negOne, zero, negOne, one] x = v2 at *
  generalize hpl [negOne, zero, one, negOne] x = v3 at *
  generalize hpl [negOne, one, negOne, zero] x = v4 at *
  generalize hpl [negOne, one, zero, negOne] x = v5 at *
  generalize hpl [zero, negOne, negOne, one] x = v6 at *
  generalize hpl [zero, negOne, one, negOne] x = v7 at *
  generalize hpl [zero, one, negOne, negOne] x = v8 at *
  generalize hpl [one, negOne, negOne, zero] x = v9 at *
  generalize hpl [one, negOne, zero, negOne] x = v10 at *
  generalize hpl [one, zero, negOne, negOne] x = v11 at *
  generalize hpl [negOne, negOne] x = v12 at *
  generalize hpl [zero, one] x = v13 at *
  generalize hpl [one, zero] x = v14 at *
  generalize hpl [zero] x = v15 at *
  generalize hpl [one] x = v16 at *
  ring

/-- **`(Ψ₄⁽74⁾)'(ξ) ξ' = p₄⁽74⁾`**, in terms of `ξ`. -/
theorem i8Psi4s74D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s74D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s74 x := by
  rw [i8P4s74_eq_w hx]
  unfold i8Psi4s74D i8P4w74
  rw [← i8Psi4s74k0D_mul hx, ← i8Psi4s74k1D_mul hx, ← i8Psi4s74k2D_mul hx]
  ring

end QED.ThreeLoopD
