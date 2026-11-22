/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P21

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 87 to 87

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s87`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s87D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s87`, `QED.ThreeLoopD.i8Psi4s87D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s87k1N0 (x : ℝ) : ℝ :=
    (-2) * hpl [one, negOne, zero] x +
    (-2) * hpl [one, zero, negOne] x +
    (-2) * hpl [negOne, zero, zero, one] x +
    (-2) * hpl [negOne, zero, one, zero] x

/-- The derivative of `i8Psi4s87k1N0`. -/
noncomputable def i8Psi4s87k1dN0 (x : ℝ) : ℝ :=
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-2) * (negOne.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s87k1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k1N0 (i8Psi4s87k1dN0 x) x := by
  unfold i8Psi4s87k1N0 i8Psi4s87k1dN0
  exact (((((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s87k1N1 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne] x +
    (-2) * hpl [one] x +
    (-2) * hpl [negOne, zero] x +
    (-2) * hpl [zero, negOne] x +
    (-2) * hpl [zero, one] x +
    (-2) * hpl [one, zero] x +
    (-2) * hpl [zero, zero, one] x +
    (-2) * hpl [zero, one, zero] x +
    (-8) * hpl [one, negOne, zero] x +
    (-8) * hpl [one, zero, negOne] x +
    (-16) * hpl [negOne, zero, zero, one] x +
    (-16) * hpl [negOne, zero, one, zero] x

/-- The derivative of `i8Psi4s87k1N1`. -/
noncomputable def i8Psi4s87k1dN1 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [zero, one] x) +
    (-2) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne] x) +
    (-16) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-16) * (negOne.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s87k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k1N1 (i8Psi4s87k1dN1 x) x := by
  unfold i8Psi4s87k1N1 i8Psi4s87k1dN1
  exact (((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s87k1N2 (x : ℝ) : ℝ :=
    (15 / 2) * hpl [negOne] x +
    (4) * hpl [zero] x +
    (65 / 4) * hpl [one] x +
    (-11) * hpl [negOne, zero] x +
    (-25 / 2) * hpl [one, zero] x +
    (20) * hpl [one, negOne, zero] x +
    (20) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s87k1N2`. -/
noncomputable def i8Psi4s87k1dN2 (x : ℝ) : ℝ :=
    (15 / 2) * (negOne.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [] x) +
    (65 / 4) * (one.kernel x * hpl [] x) +
    (-11) * (negOne.kernel x * hpl [zero] x) +
    (-25 / 2) * (one.kernel x * hpl [zero] x) +
    (20) * (one.kernel x * hpl [negOne, zero] x) +
    (20) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s87k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k1N2 (i8Psi4s87k1dN2 x) x := by
  unfold i8Psi4s87k1N2 i8Psi4s87k1dN2
  exact ((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (15 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (65 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-25 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (20)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s87k1N3 (x : ℝ) : ℝ :=
    (-189 / 4) +
    (10) * hpl [negOne] x +
    (47 / 2) * hpl [zero] x +
    (-14) * hpl [one] x +
    (-10) * hpl [negOne, zero] x +
    (-10) * hpl [zero, negOne] x +
    (14) * hpl [zero, one] x +
    (14) * hpl [one, zero] x +
    (-14) * hpl [zero, zero, one] x +
    (-14) * hpl [zero, one, zero] x +
    (-8) * hpl [one, negOne, zero] x +
    (-8) * hpl [one, zero, negOne] x +
    (16) * hpl [negOne, zero, zero, one] x +
    (16) * hpl [negOne, zero, one, zero] x

/-- The derivative of `i8Psi4s87k1N3`. -/
noncomputable def i8Psi4s87k1dN3 (x : ℝ) : ℝ :=
    0 +
    (10) * (negOne.kernel x * hpl [] x) +
    (47 / 2) * (zero.kernel x * hpl [] x) +
    (-14) * (one.kernel x * hpl [] x) +
    (-10) * (negOne.kernel x * hpl [zero] x) +
    (-10) * (zero.kernel x * hpl [negOne] x) +
    (14) * (zero.kernel x * hpl [one] x) +
    (14) * (one.kernel x * hpl [zero] x) +
    (-14) * (zero.kernel x * hpl [zero, one] x) +
    (-14) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne] x) +
    (16) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (16) * (negOne.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s87k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k1N3 (i8Psi4s87k1dN3 x) x := by
  unfold i8Psi4s87k1N3 i8Psi4s87k1dN3
  exact ((((((((((((((hasDerivAt_const x (-189 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (47 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s87k1N4 (x : ℝ) : ℝ :=
    (-3 / 4) +
    (1 / 2) * hpl [negOne] x +
    (3 / 4) * hpl [zero] x +
    (-1 / 4) * hpl [one] x +
    (-1) * hpl [negOne, zero] x +
    (-1) * hpl [zero, negOne] x +
    (1 / 2) * hpl [zero, one] x +
    (1 / 2) * hpl [one, zero] x +
    (-1) * hpl [zero, zero, one] x +
    (-1) * hpl [zero, one, zero] x +
    (-2) * hpl [one, negOne, zero] x +
    (-2) * hpl [one, zero, negOne] x +
    (2) * hpl [negOne, zero, zero, one] x +
    (2) * hpl [negOne, zero, one, zero] x

/-- The derivative of `i8Psi4s87k1N4`. -/
noncomputable def i8Psi4s87k1dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (negOne.kernel x * hpl [] x) +
    (3 / 4) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [one] x) +
    (1 / 2) * (one.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [zero, one] x) +
    (-1) * (zero.kernel x * hpl [one, zero] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (2) * (negOne.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s87k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k1N4 (i8Psi4s87k1dN4 x) x := by
  unfold i8Psi4s87k1N4 i8Psi4s87k1dN4
  exact ((((((((((((((hasDerivAt_const x (-3 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (2)))

/-- The part of `Ψ₄⁽87⁾` with constant coefficients. -/
noncomputable def i8Psi4s87k1W (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero] x +
    (10) * hpl [zero, negOne, zero] x +
    (10) * hpl [zero, zero, negOne] x +
    (14) * hpl [zero, zero, zero, one] x +
    (14) * hpl [zero, zero, one, zero] x +
    (24) * hpl [zero, negOne, zero, zero, one] x +
    (24) * hpl [zero, negOne, zero, one, zero] x

/-- The derivative of `i8Psi4s87k1W`. -/
noncomputable def i8Psi4s87k1dW (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero] x) +
    (10) * (zero.kernel x * hpl [negOne, zero] x) +
    (10) * (zero.kernel x * hpl [zero, negOne] x) +
    (14) * (zero.kernel x * hpl [zero, zero, one] x) +
    (14) * (zero.kernel x * hpl [zero, one, zero] x) +
    (24) * (zero.kernel x * hpl [negOne, zero, zero, one] x) +
    (24) * (zero.kernel x * hpl [negOne, zero, one, zero] x)

theorem hasDerivAt_i8Psi4s87k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k1W (i8Psi4s87k1dW x) x := by
  unfold i8Psi4s87k1W i8Psi4s87k1dW
  exact ((((((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one, zero] hx).const_mul (24)))

/-- Chunk 1 of the piece `Ψ₄⁽87⁾`. -/
noncomputable def i8Psi4s87k1 (x : ℝ) : ℝ :=
  (i8Psi4s87k1N0 x + x * i8Psi4s87k1N1 x + x ^ 2 * i8Psi4s87k1N2 x + x ^ 3 * i8Psi4s87k1N3 x +
    x ^ 4 * i8Psi4s87k1N4 x) / x ^ 2 + i8Psi4s87k1W x

/-- The derivative of `i8Psi4s87k1`. -/
noncomputable def i8Psi4s87k1D (x : ℝ) : ℝ :=
  ((i8Psi4s87k1dN0 x + (i8Psi4s87k1N1 x + x * i8Psi4s87k1dN1 x) + (2 * x * i8Psi4s87k1N2 x +
    x ^ 2 * i8Psi4s87k1dN2 x) + (3 * x ^ 2 * i8Psi4s87k1N3 x + x ^ 3 * i8Psi4s87k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s87k1N4 x + x ^ 4 * i8Psi4s87k1dN4 x)) * x ^ 2 - (i8Psi4s87k1N0 x +
    x * i8Psi4s87k1N1 x + x ^ 2 * i8Psi4s87k1N2 x + x ^ 3 * i8Psi4s87k1N3 x +
    x ^ 4 * i8Psi4s87k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s87k1dW x

theorem hasDerivAt_i8Psi4s87k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k1 (i8Psi4s87k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s87k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s87k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s87k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s87k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s87k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s87k1W hx)
  unfold i8Psi4s87k1
  refine e.congr_deriv ?_
  unfold i8Psi4s87k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽87⁾` over words. -/
noncomputable def i8P4w87k1 (x : ℝ) : ℝ :=
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [one, negOne, zero] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [one, zero, negOne] x +
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [negOne, zero, zero, one] x +
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [negOne, zero, one, zero] x

theorem i8Psi4s87k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s87k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w87k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s87k1D i8Psi4s87k1N0 i8Psi4s87k1N1 i8Psi4s87k1N2 i8Psi4s87k1N3 i8Psi4s87k1N4
    i8Psi4s87k1dN0 i8Psi4s87k1dN1 i8Psi4s87k1dN2 i8Psi4s87k1dN3 i8Psi4s87k1dN4 i8Psi4s87k1dW
    i8P4w87k1
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, zero, zero, one] x = v0 at *
  generalize hpl [zero, negOne, zero, one, zero] x = v1 at *
  generalize hpl [negOne, zero, zero, one] x = v2 at *
  generalize hpl [negOne, zero, one, zero] x = v3 at *
  generalize hpl [zero, zero, zero, one] x = v4 at *
  generalize hpl [zero, zero, one, zero] x = v5 at *
  generalize hpl [zero, negOne, zero] x = v6 at *
  generalize hpl [zero, zero, negOne] x = v7 at *
  generalize hpl [zero, zero, one] x = v8 at *
  generalize hpl [zero, one, zero] x = v9 at *
  generalize hpl [one, negOne, zero] x = v10 at *
  generalize hpl [one, zero, negOne] x = v11 at *
  generalize hpl [negOne, zero] x = v12 at *
  generalize hpl [zero, negOne] x = v13 at *
  generalize hpl [zero, zero] x = v14 at *
  generalize hpl [zero, one] x = v15 at *
  generalize hpl [one, zero] x = v16 at *
  generalize hpl [negOne] x = v17 at *
  generalize hpl [zero] x = v18 at *
  generalize hpl [one] x = v19 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s87k2N0 (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [negOne, one] x +
    (-1) * hpl [negOne, zero, one] x +
    (-1) * hpl [negOne, one, zero] x +
    (-1) * hpl [zero, negOne, one] x +
    (-2) * hpl [negOne, one, zero, zero] x +
    (-2) * hpl [zero, negOne, zero, one] x +
    (-2) * hpl [zero, negOne, one, zero] x +
    (-2) * hpl [zero, zero, negOne, one] x

/-- The derivative of `i8Psi4s87k2N0`. -/
noncomputable def i8Psi4s87k2dN0 (x : ℝ) : ℝ :=
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1) * (negOne.kernel x * hpl [zero, one] x) +
    (-1) * (negOne.kernel x * hpl [one, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (-2) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, one] x)

theorem hasDerivAt_i8Psi4s87k2N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k2N0 (i8Psi4s87k2dN0 x) x := by
  unfold i8Psi4s87k2N0 i8Psi4s87k2dN0
  exact (((((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s87k2N1 (x : ℝ) : ℝ :=
    (-3 / 2) * hpl [one] x +
    (-16) * hpl [negOne, one] x +
    (-1) * hpl [zero, one] x +
    (-1) * hpl [one, zero] x +
    (-16) * hpl [negOne, zero, one] x +
    (-16) * hpl [negOne, one, zero] x +
    (-16) * hpl [zero, negOne, one] x +
    (-2) * hpl [one, zero, zero] x +
    (-16) * hpl [negOne, one, zero, zero] x +
    (-16) * hpl [zero, negOne, zero, one] x +
    (-16) * hpl [zero, negOne, one, zero] x +
    (-16) * hpl [zero, zero, negOne, one] x

/-- The derivative of `i8Psi4s87k2N1`. -/
noncomputable def i8Psi4s87k2dN1 (x : ℝ) : ℝ :=
    (-3 / 2) * (one.kernel x * hpl [] x) +
    (-16) * (negOne.kernel x * hpl [one] x) +
    (-1) * (zero.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, one] x) +
    (-16) * (negOne.kernel x * hpl [one, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (one.kernel x * hpl [zero, zero] x) +
    (-16) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (-16) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, negOne, one] x)

theorem hasDerivAt_i8Psi4s87k2N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k2N1 (i8Psi4s87k2dN1 x) x := by
  unfold i8Psi4s87k2N1 i8Psi4s87k2dN1
  exact (((((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 2)).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s87k2N2 (x : ℝ) : ℝ :=
    (3 / 2) * hpl [zero] x +
    (65 / 2) * hpl [one] x +
    (1) * hpl [zero, zero] x +
    (31 / 2) * hpl [zero, one] x +
    (-29 / 2) * hpl [one, zero] x +
    (-30) * hpl [negOne, zero, one] x +
    (-30) * hpl [negOne, one, zero] x +
    (17) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s87k2N2`. -/
noncomputable def i8Psi4s87k2dN2 (x : ℝ) : ℝ :=
    (3 / 2) * (zero.kernel x * hpl [] x) +
    (65 / 2) * (one.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (31 / 2) * (zero.kernel x * hpl [one] x) +
    (-29 / 2) * (one.kernel x * hpl [zero] x) +
    (-30) * (negOne.kernel x * hpl [zero, one] x) +
    (-30) * (negOne.kernel x * hpl [one, zero] x) +
    (17) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s87k2N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k2N2 (i8Psi4s87k2dN2 x) x := by
  unfold i8Psi4s87k2N2 i8Psi4s87k2dN2
  exact (((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (65 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (31 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-29 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (17)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s87k2N3 (x : ℝ) : ℝ :=
    (-123 / 2) +
    (61 / 2) * hpl [zero] x +
    (-61 / 2) * hpl [one] x +
    (16) * hpl [negOne, one] x +
    (-15) * hpl [zero, zero] x +
    (15) * hpl [zero, one] x +
    (15) * hpl [one, zero] x +
    (-16) * hpl [negOne, zero, one] x +
    (-16) * hpl [negOne, one, zero] x +
    (-16) * hpl [zero, negOne, one] x +
    (-14) * hpl [one, zero, zero] x +
    (16) * hpl [negOne, one, zero, zero] x +
    (16) * hpl [zero, negOne, zero, one] x +
    (16) * hpl [zero, negOne, one, zero] x +
    (16) * hpl [zero, zero, negOne, one] x

/-- The derivative of `i8Psi4s87k2N3`. -/
noncomputable def i8Psi4s87k2dN3 (x : ℝ) : ℝ :=
    0 +
    (61 / 2) * (zero.kernel x * hpl [] x) +
    (-61 / 2) * (one.kernel x * hpl [] x) +
    (16) * (negOne.kernel x * hpl [one] x) +
    (-15) * (zero.kernel x * hpl [zero] x) +
    (15) * (zero.kernel x * hpl [one] x) +
    (15) * (one.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, one] x) +
    (-16) * (negOne.kernel x * hpl [one, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, one] x) +
    (-14) * (one.kernel x * hpl [zero, zero] x) +
    (16) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (16) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (16) * (zero.kernel x * hpl [zero, negOne, one] x)

theorem hasDerivAt_i8Psi4s87k2N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k2N3 (i8Psi4s87k2dN3 x) x := by
  unfold i8Psi4s87k2N3 i8Psi4s87k2dN3
  exact (((((((((((((((hasDerivAt_const x (-123 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (61 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-61 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-15))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s87k2N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (1 / 2) * hpl [zero] x +
    (-1 / 2) * hpl [one] x +
    (1 / 2) * hpl [negOne, one] x +
    (-1 / 2) * hpl [zero, zero] x +
    (1 / 2) * hpl [zero, one] x +
    (1 / 2) * hpl [one, zero] x +
    (-1) * hpl [negOne, zero, one] x +
    (-1) * hpl [negOne, one, zero] x +
    (-1) * hpl [zero, negOne, one] x +
    (-1) * hpl [one, zero, zero] x +
    (2) * hpl [negOne, one, zero, zero] x +
    (2) * hpl [zero, negOne, zero, one] x +
    (2) * hpl [zero, negOne, one, zero] x +
    (2) * hpl [zero, zero, negOne, one] x

/-- The derivative of `i8Psi4s87k2N4`. -/
noncomputable def i8Psi4s87k2dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (one.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [one] x) +
    (1 / 2) * (one.kernel x * hpl [zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, one] x) +
    (-1) * (negOne.kernel x * hpl [one, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, one] x) +
    (-1) * (one.kernel x * hpl [zero, zero] x) +
    (2) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (2) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, one] x)

theorem hasDerivAt_i8Psi4s87k2N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k2N4 (i8Psi4s87k2dN4 x) x := by
  unfold i8Psi4s87k2N4 i8Psi4s87k2dN4
  exact (((((((((((((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (2)))

/-- The part of `Ψ₄⁽87⁾` with constant coefficients. -/
noncomputable def i8Psi4s87k2W (x : ℝ) : ℝ :=
    (2) * hpl [zero, zero, zero] x +
    (15) * hpl [zero, zero, one] x +
    (15) * hpl [zero, one, zero] x +
    (14) * hpl [zero, one, zero, zero] x +
    (24) * hpl [zero, negOne, one, zero, zero] x +
    (24) * hpl [zero, zero, negOne, zero, one] x +
    (24) * hpl [zero, zero, negOne, one, zero] x +
    (24) * hpl [zero, zero, zero, negOne, one] x

/-- The derivative of `i8Psi4s87k2W`. -/
noncomputable def i8Psi4s87k2dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [zero, zero] x) +
    (15) * (zero.kernel x * hpl [zero, one] x) +
    (15) * (zero.kernel x * hpl [one, zero] x) +
    (14) * (zero.kernel x * hpl [one, zero, zero] x) +
    (24) * (zero.kernel x * hpl [negOne, one, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, negOne, zero, one] x) +
    (24) * (zero.kernel x * hpl [zero, negOne, one, zero] x) +
    (24) * (zero.kernel x * hpl [zero, zero, negOne, one] x)

theorem hasDerivAt_i8Psi4s87k2W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k2W (i8Psi4s87k2dW x) x := by
  unfold i8Psi4s87k2W i8Psi4s87k2dW
  exact (((((((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, one] hx).const_mul (24)))

/-- Chunk 2 of the piece `Ψ₄⁽87⁾`. -/
noncomputable def i8Psi4s87k2 (x : ℝ) : ℝ :=
  (i8Psi4s87k2N0 x + x * i8Psi4s87k2N1 x + x ^ 2 * i8Psi4s87k2N2 x + x ^ 3 * i8Psi4s87k2N3 x +
    x ^ 4 * i8Psi4s87k2N4 x) / x ^ 2 + i8Psi4s87k2W x

/-- The derivative of `i8Psi4s87k2`. -/
noncomputable def i8Psi4s87k2D (x : ℝ) : ℝ :=
  ((i8Psi4s87k2dN0 x + (i8Psi4s87k2N1 x + x * i8Psi4s87k2dN1 x) + (2 * x * i8Psi4s87k2N2 x +
    x ^ 2 * i8Psi4s87k2dN2 x) + (3 * x ^ 2 * i8Psi4s87k2N3 x + x ^ 3 * i8Psi4s87k2dN3 x) +
    (4 * x ^ 3 * i8Psi4s87k2N4 x + x ^ 4 * i8Psi4s87k2dN4 x)) * x ^ 2 - (i8Psi4s87k2N0 x +
    x * i8Psi4s87k2N1 x + x ^ 2 * i8Psi4s87k2N2 x + x ^ 3 * i8Psi4s87k2N3 x +
    x ^ 4 * i8Psi4s87k2N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s87k2dW x

theorem hasDerivAt_i8Psi4s87k2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k2 (i8Psi4s87k2D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s87k2N0 hx).add (X.mul (hasDerivAt_i8Psi4s87k2N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s87k2N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s87k2N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s87k2N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s87k2W hx)
  unfold i8Psi4s87k2
  refine e.congr_deriv ?_
  unfold i8Psi4s87k2D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 2 of `p₄⁽87⁾` over words. -/
noncomputable def i8P4w87k2 (x : ℝ) : ℝ :=
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [negOne, one, zero, zero] x +
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [zero, negOne, zero, one] x +
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [zero, negOne, one, zero] x +
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [zero, zero, negOne, one] x

theorem i8Psi4s87k2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s87k2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w87k2 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s87k2D i8Psi4s87k2N0 i8Psi4s87k2N1 i8Psi4s87k2N2 i8Psi4s87k2N3 i8Psi4s87k2N4
    i8Psi4s87k2dN0 i8Psi4s87k2dN1 i8Psi4s87k2dN2 i8Psi4s87k2dN3 i8Psi4s87k2dN4 i8Psi4s87k2dW
    i8P4w87k2
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, one, zero, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, zero, one] x = v1 at *
  generalize hpl [zero, zero, negOne, one, zero] x = v2 at *
  generalize hpl [zero, zero, zero, negOne, one] x = v3 at *
  generalize hpl [negOne, one, zero, zero] x = v4 at *
  generalize hpl [zero, negOne, zero, one] x = v5 at *
  generalize hpl [zero, negOne, one, zero] x = v6 at *
  generalize hpl [zero, zero, negOne, one] x = v7 at *
  generalize hpl [zero, one, zero, zero] x = v8 at *
  generalize hpl [negOne, zero, one] x = v9 at *
  generalize hpl [negOne, one, zero] x = v10 at *
  generalize hpl [zero, negOne, one] x = v11 at *
  generalize hpl [zero, zero, zero] x = v12 at *
  generalize hpl [zero, zero, one] x = v13 at *
  generalize hpl [zero, one, zero] x = v14 at *
  generalize hpl [one, zero, zero] x = v15 at *
  generalize hpl [negOne, one] x = v16 at *
  generalize hpl [zero, zero] x = v17 at *
  generalize hpl [zero, one] x = v18 at *
  generalize hpl [one, zero] x = v19 at *
  generalize hpl [zero] x = v20 at *
  generalize hpl [one] x = v21 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s87k3N0 (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [one, negOne] x +
    (-1) * hpl [zero, one, negOne] x +
    (-1) * hpl [one, negOne, zero] x +
    (-1) * hpl [one, zero, negOne] x +
    (-2) * hpl [zero, zero, one, negOne] x +
    (-2) * hpl [zero, one, negOne, zero] x +
    (-2) * hpl [zero, one, zero, negOne] x +
    (-2) * hpl [one, negOne, zero, zero] x

/-- The derivative of `i8Psi4s87k3N0`. -/
noncomputable def i8Psi4s87k3dN0 (x : ℝ) : ℝ :=
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1) * (zero.kernel x * hpl [one, negOne] x) +
    (-1) * (one.kernel x * hpl [negOne, zero] x) +
    (-1) * (one.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (-2) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s87k3N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k3N0 (i8Psi4s87k3dN0 x) x := by
  unfold i8Psi4s87k3N0 i8Psi4s87k3dN0
  exact (((((((((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s87k3N1 (x : ℝ) : ℝ :=
    (-3 / 2) * hpl [negOne] x +
    (-1) * hpl [negOne, zero] x +
    (-1) * hpl [zero, negOne] x +
    (-16) * hpl [one, negOne] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-16) * hpl [zero, one, negOne] x +
    (-16) * hpl [one, negOne, zero] x +
    (-16) * hpl [one, zero, negOne] x +
    (-16) * hpl [zero, zero, one, negOne] x +
    (-16) * hpl [zero, one, negOne, zero] x +
    (-16) * hpl [zero, one, zero, negOne] x +
    (-16) * hpl [one, negOne, zero, zero] x

/-- The derivative of `i8Psi4s87k3N1`. -/
noncomputable def i8Psi4s87k3dN1 (x : ℝ) : ℝ :=
    (-3 / 2) * (negOne.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (-16) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-16) * (zero.kernel x * hpl [one, negOne] x) +
    (-16) * (one.kernel x * hpl [negOne, zero] x) +
    (-16) * (one.kernel x * hpl [zero, negOne] x) +
    (-16) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (-16) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (-16) * (one.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s87k3N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k3N1 (i8Psi4s87k3dN1 x) x := by
  unfold i8Psi4s87k3N1 i8Psi4s87k3dN1
  exact (((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s87k3N2 (x : ℝ) : ℝ :=
    (63 / 2) * hpl [negOne] x +
    (3 / 2) * hpl [zero] x +
    (-35 / 2) * hpl [negOne, zero] x +
    (33 / 2) * hpl [zero, negOne] x +
    (1) * hpl [zero, zero] x +
    (15) * hpl [negOne, zero, zero] x +
    (34) * hpl [one, negOne, zero] x +
    (34) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s87k3N2`. -/
noncomputable def i8Psi4s87k3dN2 (x : ℝ) : ℝ :=
    (63 / 2) * (negOne.kernel x * hpl [] x) +
    (3 / 2) * (zero.kernel x * hpl [] x) +
    (-35 / 2) * (negOne.kernel x * hpl [zero] x) +
    (33 / 2) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (15) * (negOne.kernel x * hpl [zero, zero] x) +
    (34) * (one.kernel x * hpl [negOne, zero] x) +
    (34) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s87k3N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k3N2 (i8Psi4s87k3dN2 x) x := by
  unfold i8Psi4s87k3N2 i8Psi4s87k3dN2
  exact (((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (63 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-35 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (33 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (34))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (34)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s87k3N3 (x : ℝ) : ℝ :=
    (-133 / 2) +
    (67 / 2) * hpl [negOne] x +
    (67 / 2) * hpl [zero] x +
    (-17) * hpl [negOne, zero] x +
    (-17) * hpl [zero, negOne] x +
    (-17) * hpl [zero, zero] x +
    (16) * hpl [one, negOne] x +
    (18) * hpl [negOne, zero, zero] x +
    (-16) * hpl [zero, one, negOne] x +
    (-16) * hpl [one, negOne, zero] x +
    (-16) * hpl [one, zero, negOne] x +
    (16) * hpl [zero, zero, one, negOne] x +
    (16) * hpl [zero, one, negOne, zero] x +
    (16) * hpl [zero, one, zero, negOne] x +
    (16) * hpl [one, negOne, zero, zero] x

/-- The derivative of `i8Psi4s87k3N3`. -/
noncomputable def i8Psi4s87k3dN3 (x : ℝ) : ℝ :=
    0 +
    (67 / 2) * (negOne.kernel x * hpl [] x) +
    (67 / 2) * (zero.kernel x * hpl [] x) +
    (-17) * (negOne.kernel x * hpl [zero] x) +
    (-17) * (zero.kernel x * hpl [negOne] x) +
    (-17) * (zero.kernel x * hpl [zero] x) +
    (16) * (one.kernel x * hpl [negOne] x) +
    (18) * (negOne.kernel x * hpl [zero, zero] x) +
    (-16) * (zero.kernel x * hpl [one, negOne] x) +
    (-16) * (one.kernel x * hpl [negOne, zero] x) +
    (-16) * (one.kernel x * hpl [zero, negOne] x) +
    (16) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (16) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (16) * (one.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s87k3N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k3N3 (i8Psi4s87k3dN3 x) x := by
  unfold i8Psi4s87k3N3 i8Psi4s87k3dN3
  exact (((((((((((((((hasDerivAt_const x (-133 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (67 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (67 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-17))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-17))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-17))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s87k3N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (1 / 2) * hpl [negOne] x +
    (1 / 2) * hpl [zero] x +
    (-1 / 2) * hpl [negOne, zero] x +
    (-1 / 2) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [zero, zero] x +
    (1 / 2) * hpl [one, negOne] x +
    (1) * hpl [negOne, zero, zero] x +
    (-1) * hpl [zero, one, negOne] x +
    (-1) * hpl [one, negOne, zero] x +
    (-1) * hpl [one, zero, negOne] x +
    (2) * hpl [zero, zero, one, negOne] x +
    (2) * hpl [zero, one, negOne, zero] x +
    (2) * hpl [zero, one, zero, negOne] x +
    (2) * hpl [one, negOne, zero, zero] x

/-- The derivative of `i8Psi4s87k3N4`. -/
noncomputable def i8Psi4s87k3dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (one.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1) * (zero.kernel x * hpl [one, negOne] x) +
    (-1) * (one.kernel x * hpl [negOne, zero] x) +
    (-1) * (one.kernel x * hpl [zero, negOne] x) +
    (2) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (2) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (2) * (one.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s87k3N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k3N4 (i8Psi4s87k3dN4 x) x := by
  unfold i8Psi4s87k3N4 i8Psi4s87k3dN4
  exact (((((((((((((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (2)))

/-- The part of `Ψ₄⁽87⁾` with constant coefficients. -/
noncomputable def i8Psi4s87k3W (x : ℝ) : ℝ :=
    (17) * hpl [zero, negOne, zero] x +
    (17) * hpl [zero, zero, negOne] x +
    (2) * hpl [zero, zero, zero] x +
    (18) * hpl [zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, zero, one, negOne] x +
    (24) * hpl [zero, zero, one, negOne, zero] x +
    (24) * hpl [zero, zero, one, zero, negOne] x +
    (24) * hpl [zero, one, negOne, zero, zero] x

/-- The derivative of `i8Psi4s87k3W`. -/
noncomputable def i8Psi4s87k3dW (x : ℝ) : ℝ :=
    (17) * (zero.kernel x * hpl [negOne, zero] x) +
    (17) * (zero.kernel x * hpl [zero, negOne] x) +
    (2) * (zero.kernel x * hpl [zero, zero] x) +
    (18) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, zero, one, negOne] x) +
    (24) * (zero.kernel x * hpl [zero, one, negOne, zero] x) +
    (24) * (zero.kernel x * hpl [zero, one, zero, negOne] x) +
    (24) * (zero.kernel x * hpl [one, negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s87k3W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k3W (i8Psi4s87k3dW x) x := by
  unfold i8Psi4s87k3W i8Psi4s87k3dW
  exact (((((((((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (17)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (17))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one, negOne] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero, negOne] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero, zero] hx).const_mul (24)))

/-- Chunk 3 of the piece `Ψ₄⁽87⁾`. -/
noncomputable def i8Psi4s87k3 (x : ℝ) : ℝ :=
  (i8Psi4s87k3N0 x + x * i8Psi4s87k3N1 x + x ^ 2 * i8Psi4s87k3N2 x + x ^ 3 * i8Psi4s87k3N3 x +
    x ^ 4 * i8Psi4s87k3N4 x) / x ^ 2 + i8Psi4s87k3W x

/-- The derivative of `i8Psi4s87k3`. -/
noncomputable def i8Psi4s87k3D (x : ℝ) : ℝ :=
  ((i8Psi4s87k3dN0 x + (i8Psi4s87k3N1 x + x * i8Psi4s87k3dN1 x) + (2 * x * i8Psi4s87k3N2 x +
    x ^ 2 * i8Psi4s87k3dN2 x) + (3 * x ^ 2 * i8Psi4s87k3N3 x + x ^ 3 * i8Psi4s87k3dN3 x) +
    (4 * x ^ 3 * i8Psi4s87k3N4 x + x ^ 4 * i8Psi4s87k3dN4 x)) * x ^ 2 - (i8Psi4s87k3N0 x +
    x * i8Psi4s87k3N1 x + x ^ 2 * i8Psi4s87k3N2 x + x ^ 3 * i8Psi4s87k3N3 x +
    x ^ 4 * i8Psi4s87k3N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s87k3dW x

theorem hasDerivAt_i8Psi4s87k3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k3 (i8Psi4s87k3D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s87k3N0 hx).add (X.mul (hasDerivAt_i8Psi4s87k3N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s87k3N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s87k3N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s87k3N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s87k3W hx)
  unfold i8Psi4s87k3
  refine e.congr_deriv ?_
  unfold i8Psi4s87k3D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 3 of `p₄⁽87⁾` over words. -/
noncomputable def i8P4w87k3 (x : ℝ) : ℝ :=
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [zero, zero, one, negOne] x +
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [zero, one, negOne, zero] x +
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [zero, one, zero, negOne] x +
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [one, negOne, zero, zero] x

theorem i8Psi4s87k3D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s87k3D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w87k3 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s87k3D i8Psi4s87k3N0 i8Psi4s87k3N1 i8Psi4s87k3N2 i8Psi4s87k3N3 i8Psi4s87k3N4
    i8Psi4s87k3dN0 i8Psi4s87k3dN1 i8Psi4s87k3dN2 i8Psi4s87k3dN3 i8Psi4s87k3dN4 i8Psi4s87k3dW
    i8P4w87k3
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, zero, zero, one, negOne] x = v0 at *
  generalize hpl [zero, zero, one, negOne, zero] x = v1 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v2 at *
  generalize hpl [zero, one, negOne, zero, zero] x = v3 at *
  generalize hpl [zero, negOne, zero, zero] x = v4 at *
  generalize hpl [zero, zero, one, negOne] x = v5 at *
  generalize hpl [zero, one, negOne, zero] x = v6 at *
  generalize hpl [zero, one, zero, negOne] x = v7 at *
  generalize hpl [one, negOne, zero, zero] x = v8 at *
  generalize hpl [negOne, zero, zero] x = v9 at *
  generalize hpl [zero, negOne, zero] x = v10 at *
  generalize hpl [zero, zero, negOne] x = v11 at *
  generalize hpl [zero, zero, zero] x = v12 at *
  generalize hpl [zero, one, negOne] x = v13 at *
  generalize hpl [one, negOne, zero] x = v14 at *
  generalize hpl [one, zero, negOne] x = v15 at *
  generalize hpl [negOne, zero] x = v16 at *
  generalize hpl [zero, negOne] x = v17 at *
  generalize hpl [zero, zero] x = v18 at *
  generalize hpl [one, negOne] x = v19 at *
  generalize hpl [negOne] x = v20 at *
  generalize hpl [zero] x = v21 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s87k4N0 (x : ℝ) : ℝ :=
    (-2) * hpl [one, zero, negOne, zero] x +
    (-2) * hpl [one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s87k4N0`. -/
noncomputable def i8Psi4s87k4dN0 (x : ℝ) : ℝ :=
    (-2) * (one.kernel x * hpl [zero, negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s87k4N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k4N0 (i8Psi4s87k4dN0 x) x := by
  unfold i8Psi4s87k4N0 i8Psi4s87k4dN0
  exact (((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [zero, zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s87k4N1 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne] x +
    (-2) * hpl [negOne, zero] x +
    (-2) * hpl [zero, negOne] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, zero, negOne] x +
    (-16) * hpl [one, zero, negOne, zero] x +
    (-16) * hpl [one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s87k4N1`. -/
noncomputable def i8Psi4s87k4dN1 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-16) * (one.kernel x * hpl [zero, negOne, zero] x) +
    (-16) * (one.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s87k4N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k4N1 (i8Psi4s87k4dN1 x) x := by
  unfold i8Psi4s87k4N1 i8Psi4s87k4dN1
  exact ((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, zero, negOne] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s87k4N2 (x : ℝ) : ℝ :=
    (63 / 4) * hpl [negOne] x +
    (2) * hpl [zero] x +
    (-39 / 2) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s87k4N2`. -/
noncomputable def i8Psi4s87k4dN2 (x : ℝ) : ℝ :=
    (63 / 4) * (negOne.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [] x) +
    (-39 / 2) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s87k4N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k4N2 (i8Psi4s87k4dN2 x) x := by
  unfold i8Psi4s87k4N2 i8Psi4s87k4dN2
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (63 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-39 / 2)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s87k4N3 (x : ℝ) : ℝ :=
    (-141 / 4) +
    (18) * hpl [negOne] x +
    (35 / 2) * hpl [zero] x +
    (-18) * hpl [negOne, zero] x +
    (-18) * hpl [zero, negOne] x +
    (18) * hpl [zero, negOne, zero] x +
    (18) * hpl [zero, zero, negOne] x +
    (16) * hpl [one, zero, negOne, zero] x +
    (16) * hpl [one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s87k4N3`. -/
noncomputable def i8Psi4s87k4dN3 (x : ℝ) : ℝ :=
    0 +
    (18) * (negOne.kernel x * hpl [] x) +
    (35 / 2) * (zero.kernel x * hpl [] x) +
    (-18) * (negOne.kernel x * hpl [zero] x) +
    (-18) * (zero.kernel x * hpl [negOne] x) +
    (18) * (zero.kernel x * hpl [negOne, zero] x) +
    (18) * (zero.kernel x * hpl [zero, negOne] x) +
    (16) * (one.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (one.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s87k4N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k4N3 (i8Psi4s87k4dN3 x) x := by
  unfold i8Psi4s87k4N3 i8Psi4s87k4dN3
  exact (((((((((hasDerivAt_const x (-141 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (35 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, zero, negOne] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s87k4N4 (x : ℝ) : ℝ :=
    (-1 / 4) +
    (1 / 4) * hpl [negOne] x +
    (1 / 4) * hpl [zero] x +
    (-1 / 2) * hpl [negOne, zero] x +
    (-1 / 2) * hpl [zero, negOne] x +
    (1) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, negOne] x +
    (2) * hpl [one, zero, negOne, zero] x +
    (2) * hpl [one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s87k4N4`. -/
noncomputable def i8Psi4s87k4dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 4) * (negOne.kernel x * hpl [] x) +
    (1 / 4) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x) +
    (2) * (one.kernel x * hpl [zero, negOne, zero] x) +
    (2) * (one.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s87k4N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k4N4 (i8Psi4s87k4dN4 x) x := by
  unfold i8Psi4s87k4N4 i8Psi4s87k4dN4
  exact (((((((((hasDerivAt_const x (-1 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero, negOne] hx).const_mul (2)))

/-- The part of `Ψ₄⁽87⁾` with constant coefficients. -/
noncomputable def i8Psi4s87k4W (x : ℝ) : ℝ :=
    (2) * hpl [zero, zero] x +
    (18) * hpl [zero, zero, negOne, zero] x +
    (18) * hpl [zero, zero, zero, negOne] x +
    (24) * hpl [zero, one, zero, negOne, zero] x +
    (24) * hpl [zero, one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s87k4W`. -/
noncomputable def i8Psi4s87k4dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [zero] x) +
    (18) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (18) * (zero.kernel x * hpl [zero, zero, negOne] x) +
    (24) * (zero.kernel x * hpl [one, zero, negOne, zero] x) +
    (24) * (zero.kernel x * hpl [one, zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s87k4W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k4W (i8Psi4s87k4dW x) x := by
  unfold i8Psi4s87k4W i8Psi4s87k4dW
  exact ((((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero, negOne] hx).const_mul (24)))

/-- Chunk 4 of the piece `Ψ₄⁽87⁾`. -/
noncomputable def i8Psi4s87k4 (x : ℝ) : ℝ :=
  (i8Psi4s87k4N0 x + x * i8Psi4s87k4N1 x + x ^ 2 * i8Psi4s87k4N2 x + x ^ 3 * i8Psi4s87k4N3 x +
    x ^ 4 * i8Psi4s87k4N4 x) / x ^ 2 + i8Psi4s87k4W x

/-- The derivative of `i8Psi4s87k4`. -/
noncomputable def i8Psi4s87k4D (x : ℝ) : ℝ :=
  ((i8Psi4s87k4dN0 x + (i8Psi4s87k4N1 x + x * i8Psi4s87k4dN1 x) + (2 * x * i8Psi4s87k4N2 x +
    x ^ 2 * i8Psi4s87k4dN2 x) + (3 * x ^ 2 * i8Psi4s87k4N3 x + x ^ 3 * i8Psi4s87k4dN3 x) +
    (4 * x ^ 3 * i8Psi4s87k4N4 x + x ^ 4 * i8Psi4s87k4dN4 x)) * x ^ 2 - (i8Psi4s87k4N0 x +
    x * i8Psi4s87k4N1 x + x ^ 2 * i8Psi4s87k4N2 x + x ^ 3 * i8Psi4s87k4N3 x +
    x ^ 4 * i8Psi4s87k4N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s87k4dW x

theorem hasDerivAt_i8Psi4s87k4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k4 (i8Psi4s87k4D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s87k4N0 hx).add (X.mul (hasDerivAt_i8Psi4s87k4N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s87k4N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s87k4N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s87k4N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s87k4W hx)
  unfold i8Psi4s87k4
  refine e.congr_deriv ?_
  unfold i8Psi4s87k4D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 4 of `p₄⁽87⁾` over words. -/
noncomputable def i8P4w87k4 (x : ℝ) : ℝ :=
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [one, zero, negOne, zero] x +
    ((-4 - 12 * x - 12 * x ^ 2 - 4 * x ^ 3) / (x * (1 - x))) * hpl [one, zero, zero, negOne] x

theorem i8Psi4s87k4D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s87k4D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w87k4 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s87k4D i8Psi4s87k4N0 i8Psi4s87k4N1 i8Psi4s87k4N2 i8Psi4s87k4N3 i8Psi4s87k4N4
    i8Psi4s87k4dN0 i8Psi4s87k4dN1 i8Psi4s87k4dN2 i8Psi4s87k4dN3 i8Psi4s87k4dN4 i8Psi4s87k4dW
    i8P4w87k4
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, one, zero, negOne, zero] x = v0 at *
  generalize hpl [zero, one, zero, zero, negOne] x = v1 at *
  generalize hpl [zero, zero, negOne, zero] x = v2 at *
  generalize hpl [zero, zero, zero, negOne] x = v3 at *
  generalize hpl [one, zero, negOne, zero] x = v4 at *
  generalize hpl [one, zero, zero, negOne] x = v5 at *
  generalize hpl [zero, negOne, zero] x = v6 at *
  generalize hpl [zero, zero, negOne] x = v7 at *
  generalize hpl [negOne, zero] x = v8 at *
  generalize hpl [zero, negOne] x = v9 at *
  generalize hpl [zero, zero] x = v10 at *
  generalize hpl [negOne] x = v11 at *
  generalize hpl [zero] x = v12 at *
  field_simp
  ring

end QED.ThreeLoopD
