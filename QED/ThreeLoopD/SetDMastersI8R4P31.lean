/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P30

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 115 to 115

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s115`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s115D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s115`, `QED.ThreeLoopD.i8Psi4s115D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s115k0N0 (x : ℝ) : ℝ :=
    (2) * hpl [negOne, negOne, zero, one] x +
    (2) * hpl [negOne, negOne, one, zero] x +
    (2) * hpl [negOne, zero, negOne, one] x +
    (2) * hpl [negOne, zero, one, negOne] x

/-- The derivative of `i8Psi4s115k0N0`. -/
noncomputable def i8Psi4s115k0dN0 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [negOne, zero, one] x) +
    (2) * (negOne.kernel x * hpl [negOne, one, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, one] x) +
    (2) * (negOne.kernel x * hpl [zero, one, negOne] x)

theorem hasDerivAt_i8Psi4s115k0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k0N0 (i8Psi4s115k0dN0 x) x := by
  unfold i8Psi4s115k0N0 i8Psi4s115k0dN0
  exact (((((hasDerivAt_hpl_cons negOne [negOne, zero, one] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s115k0N1 (x : ℝ) : ℝ :=
    (2) * hpl [negOne, one] x +
    (2) * hpl [one, negOne] x +
    (2) * hpl [negOne, zero, one] x +
    (2) * hpl [negOne, one, zero] x +
    (2) * hpl [zero, negOne, one] x +
    (2) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi4s115k0N1`. -/
noncomputable def i8Psi4s115k0dN1 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, one] x) +
    (2) * (negOne.kernel x * hpl [one, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, one] x) +
    (2) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s115k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k0N1 (i8Psi4s115k0dN1 x) x := by
  unfold i8Psi4s115k0N1 i8Psi4s115k0dN1
  exact (((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s115k0N2 (x : ℝ) : ℝ :=
    (7 / 4) * hpl [negOne] x +
    (5) * hpl [one] x +
    (9 / 2) * hpl [negOne, one] x +
    (-2) * hpl [zero, one] x +
    (-7 / 2) * hpl [one, negOne] x +
    (-5 / 2) * hpl [one, zero] x +
    (-1) * hpl [negOne, zero, one] x +
    (-1) * hpl [negOne, one, zero] x

/-- The derivative of `i8Psi4s115k0N2`. -/
noncomputable def i8Psi4s115k0dN2 (x : ℝ) : ℝ :=
    (7 / 4) * (negOne.kernel x * hpl [] x) +
    (5) * (one.kernel x * hpl [] x) +
    (9 / 2) * (negOne.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [one] x) +
    (-7 / 2) * (one.kernel x * hpl [negOne] x) +
    (-5 / 2) * (one.kernel x * hpl [zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, one] x) +
    (-1) * (negOne.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s115k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k0N2 (i8Psi4s115k0dN2 x) x := by
  unfold i8Psi4s115k0N2 i8Psi4s115k0dN2
  exact (((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (7 / 4)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (9 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s115k0N3 (x : ℝ) : ℝ :=
    (-37 / 4) +
    (3 / 2) * hpl [negOne] x +
    (5 / 2) * hpl [zero] x +
    (-11 / 2) * hpl [one] x +
    (2) * hpl [negOne, one] x +
    (3) * hpl [zero, one] x +
    (2) * hpl [one, negOne] x +
    (3) * hpl [one, zero] x +
    (-2) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, one, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi4s115k0N3`. -/
noncomputable def i8Psi4s115k0dN3 (x : ℝ) : ℝ :=
    0 +
    (3 / 2) * (negOne.kernel x * hpl [] x) +
    (5 / 2) * (zero.kernel x * hpl [] x) +
    (-11 / 2) * (one.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [one] x) +
    (3) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [negOne] x) +
    (3) * (one.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s115k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k0N3 (i8Psi4s115k0dN3 x) x := by
  unfold i8Psi4s115k0N3 i8Psi4s115k0dN3
  exact ((((((((((((hasDerivAt_const x (-37 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s115k0N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 4) * hpl [negOne] x +
    (-1 / 4) * hpl [zero] x +
    (1 / 2) * hpl [one] x +
    (-1 / 2) * hpl [negOne, one] x +
    (-1 / 2) * hpl [zero, one] x +
    (-1 / 2) * hpl [one, negOne] x +
    (-1 / 2) * hpl [one, zero] x +
    (1) * hpl [negOne, zero, one] x +
    (1) * hpl [negOne, one, zero] x +
    (1) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, negOne] x +
    (-2) * hpl [negOne, negOne, zero, one] x +
    (-2) * hpl [negOne, negOne, one, zero] x +
    (-2) * hpl [negOne, zero, negOne, one] x +
    (-2) * hpl [negOne, zero, one, negOne] x

/-- The derivative of `i8Psi4s115k0N4`. -/
noncomputable def i8Psi4s115k0dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 4) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (one.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1 / 2) * (zero.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1 / 2) * (one.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [zero, one] x) +
    (1) * (negOne.kernel x * hpl [one, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, zero, one] x) +
    (-2) * (negOne.kernel x * hpl [negOne, one, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, negOne, one] x) +
    (-2) * (negOne.kernel x * hpl [zero, one, negOne] x)

theorem hasDerivAt_i8Psi4s115k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k0N4 (i8Psi4s115k0dN4 x) x := by
  unfold i8Psi4s115k0N4 i8Psi4s115k0dN4
  exact ((((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽115⁾` with constant coefficients. -/
noncomputable def i8Psi4s115k0W (x : ℝ) : ℝ :=
    (-2) * hpl [zero, negOne] x +
    (-2) * hpl [zero, zero, one] x +
    (-2) * hpl [zero, one, zero] x +
    (2) * hpl [zero, negOne, zero, one] x +
    (2) * hpl [zero, negOne, one, zero] x +
    (2) * hpl [zero, zero, negOne, one] x +
    (2) * hpl [zero, zero, one, negOne] x +
    (8) * hpl [zero, negOne, negOne, zero, one] x +
    (8) * hpl [zero, negOne, negOne, one, zero] x +
    (8) * hpl [zero, negOne, zero, negOne, one] x +
    (8) * hpl [zero, negOne, zero, one, negOne] x

/-- The derivative of `i8Psi4s115k0W`. -/
noncomputable def i8Psi4s115k0dW (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [zero, one] x) +
    (-2) * (zero.kernel x * hpl [one, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (2) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (2) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, zero, one] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, one, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, negOne, one] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, one, negOne] x)

theorem hasDerivAt_i8Psi4s115k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k0W (i8Psi4s115k0dW x) x := by
  unfold i8Psi4s115k0W i8Psi4s115k0dW
  exact ((((((((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one, negOne] hx).const_mul (8)))

/-- Chunk 0 of the piece `Ψ₄⁽115⁾`. -/
noncomputable def i8Psi4s115k0 (x : ℝ) : ℝ :=
  (i8Psi4s115k0N0 x + x * i8Psi4s115k0N1 x + x ^ 2 * i8Psi4s115k0N2 x + x ^ 3 * i8Psi4s115k0N3 x +
    x ^ 4 * i8Psi4s115k0N4 x) / x ^ 2 + i8Psi4s115k0W x

/-- The derivative of `i8Psi4s115k0`. -/
noncomputable def i8Psi4s115k0D (x : ℝ) : ℝ :=
  ((i8Psi4s115k0dN0 x + (i8Psi4s115k0N1 x + x * i8Psi4s115k0dN1 x) + (2 * x * i8Psi4s115k0N2 x +
    x ^ 2 * i8Psi4s115k0dN2 x) + (3 * x ^ 2 * i8Psi4s115k0N3 x + x ^ 3 * i8Psi4s115k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s115k0N4 x + x ^ 4 * i8Psi4s115k0dN4 x)) * x ^ 2 - (i8Psi4s115k0N0 x +
    x * i8Psi4s115k0N1 x + x ^ 2 * i8Psi4s115k0N2 x + x ^ 3 * i8Psi4s115k0N3 x +
    x ^ 4 * i8Psi4s115k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s115k0dW x

theorem hasDerivAt_i8Psi4s115k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k0 (i8Psi4s115k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s115k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s115k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s115k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s115k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s115k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s115k0W hx)
  unfold i8Psi4s115k0
  refine e.congr_deriv ?_
  unfold i8Psi4s115k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽115⁾` over words. -/
noncomputable def i8P4w115k0 (x : ℝ) : ℝ :=
    ((4 - 4 * x ^ 2) / (x)) * hpl [negOne, negOne, zero, one] x +
    ((4 - 4 * x ^ 2) / (x)) * hpl [negOne, negOne, one, zero] x +
    ((4 - 4 * x ^ 2) / (x)) * hpl [negOne, zero, negOne, one] x +
    ((4 - 4 * x ^ 2) / (x)) * hpl [negOne, zero, one, negOne] x

theorem i8Psi4s115k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s115k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w115k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s115k0D i8Psi4s115k0N0 i8Psi4s115k0N1 i8Psi4s115k0N2 i8Psi4s115k0N3 i8Psi4s115k0N4
    i8Psi4s115k0dN0 i8Psi4s115k0dN1 i8Psi4s115k0dN2 i8Psi4s115k0dN3 i8Psi4s115k0dN4 i8Psi4s115k0dW
    i8P4w115k0
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, negOne, zero, one] x = v0 at *
  generalize hpl [zero, negOne, negOne, one, zero] x = v1 at *
  generalize hpl [zero, negOne, zero, negOne, one] x = v2 at *
  generalize hpl [zero, negOne, zero, one, negOne] x = v3 at *
  generalize hpl [negOne, negOne, zero, one] x = v4 at *
  generalize hpl [negOne, negOne, one, zero] x = v5 at *
  generalize hpl [negOne, zero, negOne, one] x = v6 at *
  generalize hpl [negOne, zero, one, negOne] x = v7 at *
  generalize hpl [zero, negOne, zero, one] x = v8 at *
  generalize hpl [zero, negOne, one, zero] x = v9 at *
  generalize hpl [zero, zero, negOne, one] x = v10 at *
  generalize hpl [zero, zero, one, negOne] x = v11 at *
  generalize hpl [negOne, zero, one] x = v12 at *
  generalize hpl [negOne, one, zero] x = v13 at *
  generalize hpl [zero, negOne, one] x = v14 at *
  generalize hpl [zero, zero, one] x = v15 at *
  generalize hpl [zero, one, negOne] x = v16 at *
  generalize hpl [zero, one, zero] x = v17 at *
  generalize hpl [negOne, one] x = v18 at *
  generalize hpl [zero, negOne] x = v19 at *
  generalize hpl [zero, one] x = v20 at *
  generalize hpl [one, negOne] x = v21 at *
  generalize hpl [one, zero] x = v22 at *
  generalize hpl [negOne] x = v23 at *
  generalize hpl [zero] x = v24 at *
  generalize hpl [one] x = v25 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s115k1N0 (x : ℝ) : ℝ :=
    (1) * hpl [negOne, negOne, one] x +
    (1) * hpl [negOne, one, negOne] x +
    (2) * hpl [negOne, one, negOne, zero] x +
    (2) * hpl [negOne, one, zero, negOne] x +
    (2) * hpl [zero, negOne, negOne, one] x +
    (2) * hpl [zero, negOne, one, negOne] x

/-- The derivative of `i8Psi4s115k1N0`. -/
noncomputable def i8Psi4s115k1dN0 (x : ℝ) : ℝ :=
    (1) * (negOne.kernel x * hpl [negOne, one] x) +
    (1) * (negOne.kernel x * hpl [one, negOne] x) +
    (2) * (negOne.kernel x * hpl [one, negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [one, zero, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (2) * (zero.kernel x * hpl [negOne, one, negOne] x)

theorem hasDerivAt_i8Psi4s115k1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k1N0 (i8Psi4s115k1dN0 x) x := by
  unfold i8Psi4s115k1N0 i8Psi4s115k1dN0
  exact (((((((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s115k1N1 (x : ℝ) : ℝ :=
    (1) * hpl [negOne, one] x +
    (1) * hpl [one, negOne] x +
    (2) * hpl [one, negOne, zero] x +
    (2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s115k1N1`. -/
noncomputable def i8Psi4s115k1dN1 (x : ℝ) : ℝ :=
    (1) * (negOne.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (2) * (one.kernel x * hpl [negOne, zero] x) +
    (2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s115k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k1N1 (i8Psi4s115k1dN1 x) x := by
  unfold i8Psi4s115k1N1 i8Psi4s115k1dN1
  exact (((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s115k1N2 (x : ℝ) : ℝ :=
    (2) * hpl [negOne] x +
    (5 / 4) * hpl [one] x +
    (-3 / 2) * hpl [negOne, zero] x +
    (5 / 2) * hpl [negOne, one] x +
    (-1) * hpl [zero, negOne] x +
    (-3 / 2) * hpl [one, negOne] x +
    (-2) * hpl [negOne, negOne, one] x +
    (-2) * hpl [negOne, one, negOne] x +
    (-1) * hpl [one, negOne, zero] x +
    (-1) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s115k1N2`. -/
noncomputable def i8Psi4s115k1dN2 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [] x) +
    (5 / 4) * (one.kernel x * hpl [] x) +
    (-3 / 2) * (negOne.kernel x * hpl [zero] x) +
    (5 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (-3 / 2) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, one] x) +
    (-2) * (negOne.kernel x * hpl [one, negOne] x) +
    (-1) * (one.kernel x * hpl [negOne, zero] x) +
    (-1) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s115k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k1N2 (i8Psi4s115k1dN2 x) x := by
  unfold i8Psi4s115k1N2 i8Psi4s115k1dN2
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (5 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s115k1N3 (x : ℝ) : ℝ :=
    (-19 / 4) +
    (3 / 2) * hpl [negOne] x +
    (3 / 2) * hpl [zero] x +
    (-3 / 2) * hpl [one] x +
    (-1) * hpl [negOne, zero] x +
    (1) * hpl [negOne, one] x +
    (-1) * hpl [zero, negOne] x +
    (1) * hpl [one, negOne] x +
    (-2) * hpl [one, negOne, zero] x +
    (-2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s115k1N3`. -/
noncomputable def i8Psi4s115k1dN3 (x : ℝ) : ℝ :=
    0 +
    (3 / 2) * (negOne.kernel x * hpl [] x) +
    (3 / 2) * (zero.kernel x * hpl [] x) +
    (-3 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s115k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k1N3 (i8Psi4s115k1dN3 x) x := by
  unfold i8Psi4s115k1N3 i8Psi4s115k1dN3
  exact ((((((((((hasDerivAt_const x (-19 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s115k1N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 2) * hpl [negOne] x +
    (-1 / 4) * hpl [zero] x +
    (1 / 4) * hpl [one] x +
    (1 / 2) * hpl [negOne, zero] x +
    (-1 / 2) * hpl [negOne, one] x +
    (1 / 2) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [one, negOne] x +
    (1) * hpl [negOne, negOne, one] x +
    (1) * hpl [negOne, one, negOne] x +
    (1) * hpl [one, negOne, zero] x +
    (1) * hpl [one, zero, negOne] x +
    (-2) * hpl [negOne, one, negOne, zero] x +
    (-2) * hpl [negOne, one, zero, negOne] x +
    (-2) * hpl [zero, negOne, negOne, one] x +
    (-2) * hpl [zero, negOne, one, negOne] x

/-- The derivative of `i8Psi4s115k1N4`. -/
noncomputable def i8Psi4s115k1dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 4) * (one.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [negOne, one] x) +
    (1) * (negOne.kernel x * hpl [one, negOne] x) +
    (1) * (one.kernel x * hpl [negOne, zero] x) +
    (1) * (one.kernel x * hpl [zero, negOne] x) +
    (-2) * (negOne.kernel x * hpl [one, negOne, zero] x) +
    (-2) * (negOne.kernel x * hpl [one, zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (-2) * (zero.kernel x * hpl [negOne, one, negOne] x)

theorem hasDerivAt_i8Psi4s115k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k1N4 (i8Psi4s115k1dN4 x) x := by
  unfold i8Psi4s115k1N4 i8Psi4s115k1dN4
  exact ((((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽115⁾` with constant coefficients. -/
noncomputable def i8Psi4s115k1W (x : ℝ) : ℝ :=
    (-1) * hpl [zero, one] x +
    (-2) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, zero, negOne] x +
    (1) * hpl [zero, one, negOne] x +
    (2) * hpl [zero, one, negOne, zero] x +
    (2) * hpl [zero, one, zero, negOne] x +
    (8) * hpl [zero, negOne, one, negOne, zero] x +
    (8) * hpl [zero, negOne, one, zero, negOne] x +
    (8) * hpl [zero, zero, negOne, negOne, one] x +
    (8) * hpl [zero, zero, negOne, one, negOne] x

/-- The derivative of `i8Psi4s115k1W`. -/
noncomputable def i8Psi4s115k1dW (x : ℝ) : ℝ :=
    (-1) * (zero.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (2) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, one, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, one, zero, negOne] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, negOne, one] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, one, negOne] x)

theorem hasDerivAt_i8Psi4s115k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k1W (i8Psi4s115k1dW x) x := by
  unfold i8Psi4s115k1W i8Psi4s115k1dW
  exact ((((((((((((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one, negOne] hx).const_mul (8)))

/-- Chunk 1 of the piece `Ψ₄⁽115⁾`. -/
noncomputable def i8Psi4s115k1 (x : ℝ) : ℝ :=
  (i8Psi4s115k1N0 x + x * i8Psi4s115k1N1 x + x ^ 2 * i8Psi4s115k1N2 x + x ^ 3 * i8Psi4s115k1N3 x +
    x ^ 4 * i8Psi4s115k1N4 x) / x ^ 2 + i8Psi4s115k1W x

/-- The derivative of `i8Psi4s115k1`. -/
noncomputable def i8Psi4s115k1D (x : ℝ) : ℝ :=
  ((i8Psi4s115k1dN0 x + (i8Psi4s115k1N1 x + x * i8Psi4s115k1dN1 x) + (2 * x * i8Psi4s115k1N2 x +
    x ^ 2 * i8Psi4s115k1dN2 x) + (3 * x ^ 2 * i8Psi4s115k1N3 x + x ^ 3 * i8Psi4s115k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s115k1N4 x + x ^ 4 * i8Psi4s115k1dN4 x)) * x ^ 2 - (i8Psi4s115k1N0 x +
    x * i8Psi4s115k1N1 x + x ^ 2 * i8Psi4s115k1N2 x + x ^ 3 * i8Psi4s115k1N3 x +
    x ^ 4 * i8Psi4s115k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s115k1dW x

theorem hasDerivAt_i8Psi4s115k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k1 (i8Psi4s115k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s115k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s115k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s115k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s115k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s115k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s115k1W hx)
  unfold i8Psi4s115k1
  refine e.congr_deriv ?_
  unfold i8Psi4s115k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽115⁾` over words. -/
noncomputable def i8P4w115k1 (x : ℝ) : ℝ :=
    ((4 - 4 * x ^ 2) / (x)) * hpl [negOne, one, negOne, zero] x +
    ((4 - 4 * x ^ 2) / (x)) * hpl [negOne, one, zero, negOne] x +
    ((4 - 4 * x ^ 2) / (x)) * hpl [zero, negOne, negOne, one] x +
    ((4 - 4 * x ^ 2) / (x)) * hpl [zero, negOne, one, negOne] x

theorem i8Psi4s115k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s115k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w115k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s115k1D i8Psi4s115k1N0 i8Psi4s115k1N1 i8Psi4s115k1N2 i8Psi4s115k1N3 i8Psi4s115k1N4
    i8Psi4s115k1dN0 i8Psi4s115k1dN1 i8Psi4s115k1dN2 i8Psi4s115k1dN3 i8Psi4s115k1dN4 i8Psi4s115k1dW
    i8P4w115k1
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, one, negOne, zero] x = v0 at *
  generalize hpl [zero, negOne, one, zero, negOne] x = v1 at *
  generalize hpl [zero, zero, negOne, negOne, one] x = v2 at *
  generalize hpl [zero, zero, negOne, one, negOne] x = v3 at *
  generalize hpl [negOne, one, negOne, zero] x = v4 at *
  generalize hpl [negOne, one, zero, negOne] x = v5 at *
  generalize hpl [zero, negOne, negOne, one] x = v6 at *
  generalize hpl [zero, negOne, one, negOne] x = v7 at *
  generalize hpl [zero, one, negOne, zero] x = v8 at *
  generalize hpl [zero, one, zero, negOne] x = v9 at *
  generalize hpl [negOne, negOne, one] x = v10 at *
  generalize hpl [negOne, one, negOne] x = v11 at *
  generalize hpl [zero, negOne, zero] x = v12 at *
  generalize hpl [zero, negOne, one] x = v13 at *
  generalize hpl [zero, zero, negOne] x = v14 at *
  generalize hpl [zero, one, negOne] x = v15 at *
  generalize hpl [one, negOne, zero] x = v16 at *
  generalize hpl [one, zero, negOne] x = v17 at *
  generalize hpl [negOne, zero] x = v18 at *
  generalize hpl [negOne, one] x = v19 at *
  generalize hpl [zero, negOne] x = v20 at *
  generalize hpl [zero, one] x = v21 at *
  generalize hpl [one, negOne] x = v22 at *
  generalize hpl [negOne] x = v23 at *
  generalize hpl [zero] x = v24 at *
  generalize hpl [one] x = v25 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s115k2N0 (x : ℝ) : ℝ :=
    (1) * hpl [one, negOne, negOne] x +
    (2) * hpl [zero, one, negOne, negOne] x +
    (2) * hpl [one, negOne, negOne, zero] x +
    (2) * hpl [one, negOne, zero, negOne] x +
    (2) * hpl [one, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s115k2N0`. -/
noncomputable def i8Psi4s115k2dN0 (x : ℝ) : ℝ :=
    (1) * (one.kernel x * hpl [negOne, negOne] x) +
    (2) * (zero.kernel x * hpl [one, negOne, negOne] x) +
    (2) * (one.kernel x * hpl [negOne, negOne, zero] x) +
    (2) * (one.kernel x * hpl [negOne, zero, negOne] x) +
    (2) * (one.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s115k2N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k2N0 (i8Psi4s115k2dN0 x) x := by
  unfold i8Psi4s115k2N0 i8Psi4s115k2dN0
  exact ((((((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s115k2N1 (x : ℝ) : ℝ :=
    (3) * hpl [negOne, negOne] x +
    (2) * hpl [negOne, negOne, zero] x +
    (2) * hpl [negOne, zero, negOne] x +
    (2) * hpl [zero, negOne, negOne] x

/-- The derivative of `i8Psi4s115k2N1`. -/
noncomputable def i8Psi4s115k2dN1 (x : ℝ) : ℝ :=
    (3) * (negOne.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s115k2N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k2N1 (i8Psi4s115k2dN1 x) x := by
  unfold i8Psi4s115k2N1 i8Psi4s115k2dN1
  exact (((((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (3)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s115k2N2 (x : ℝ) : ℝ :=
    (-9 / 4) * hpl [negOne] x +
    (5) * hpl [negOne, negOne] x +
    (1 / 2) * hpl [negOne, zero] x +
    (-3) * hpl [zero, negOne] x +
    (1) * hpl [negOne, negOne, zero] x +
    (1) * hpl [negOne, zero, negOne] x +
    (-1) * hpl [zero, negOne, negOne] x +
    (-2) * hpl [one, negOne, negOne] x

/-- The derivative of `i8Psi4s115k2N2`. -/
noncomputable def i8Psi4s115k2dN2 (x : ℝ) : ℝ :=
    (-9 / 4) * (negOne.kernel x * hpl [] x) +
    (5) * (negOne.kernel x * hpl [negOne] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-3) * (zero.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [negOne, zero] x) +
    (1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s115k2N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k2N2 (i8Psi4s115k2dN2 x) x := by
  unfold i8Psi4s115k2N2 i8Psi4s115k2dN2
  exact (((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-9 / 4)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s115k2N3 (x : ℝ) : ℝ :=
    (11 / 4) +
    (-3) * hpl [negOne] x +
    (-1 / 2) * hpl [zero] x +
    (3) * hpl [negOne, negOne] x +
    (1) * hpl [negOne, zero] x +
    (1) * hpl [zero, negOne] x +
    (-2) * hpl [negOne, negOne, zero] x +
    (-2) * hpl [negOne, zero, negOne] x +
    (-2) * hpl [zero, negOne, negOne] x

/-- The derivative of `i8Psi4s115k2N3`. -/
noncomputable def i8Psi4s115k2dN3 (x : ℝ) : ℝ :=
    0 +
    (-3) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (3) * (negOne.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s115k2N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k2N3 (i8Psi4s115k2dN3 x) x := by
  unfold i8Psi4s115k2N3 i8Psi4s115k2dN3
  exact (((((((((hasDerivAt_const x (11 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽115⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s115k2N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-3 / 4) * hpl [negOne] x +
    (-1 / 4) * hpl [zero] x +
    (1) * hpl [negOne, negOne] x +
    (1 / 2) * hpl [negOne, zero] x +
    (1 / 2) * hpl [zero, negOne] x +
    (-1) * hpl [negOne, negOne, zero] x +
    (-1) * hpl [negOne, zero, negOne] x +
    (-1) * hpl [zero, negOne, negOne] x +
    (1) * hpl [one, negOne, negOne] x +
    (-2) * hpl [zero, one, negOne, negOne] x +
    (-2) * hpl [one, negOne, negOne, zero] x +
    (-2) * hpl [one, negOne, zero, negOne] x +
    (-2) * hpl [one, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s115k2N4`. -/
noncomputable def i8Psi4s115k2dN4 (x : ℝ) : ℝ :=
    0 +
    (-3 / 4) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [negOne] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, negOne] x) +
    (1) * (one.kernel x * hpl [negOne, negOne] x) +
    (-2) * (zero.kernel x * hpl [one, negOne, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, negOne, zero] x) +
    (-2) * (one.kernel x * hpl [negOne, zero, negOne] x) +
    (-2) * (one.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s115k2N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k2N4 (i8Psi4s115k2dN4 x) x := by
  unfold i8Psi4s115k2N4 i8Psi4s115k2dN4
  exact ((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽115⁾` with constant coefficients. -/
noncomputable def i8Psi4s115k2W (x : ℝ) : ℝ :=
    (-2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, zero, negOne] x +
    (-2) * hpl [zero, negOne, negOne, zero] x +
    (-2) * hpl [zero, negOne, zero, negOne] x +
    (-2) * hpl [zero, zero, negOne, negOne] x +
    (8) * hpl [zero, zero, one, negOne, negOne] x +
    (8) * hpl [zero, one, negOne, negOne, zero] x +
    (8) * hpl [zero, one, negOne, zero, negOne] x +
    (8) * hpl [zero, one, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s115k2W`. -/
noncomputable def i8Psi4s115k2dW (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (8) * (zero.kernel x * hpl [zero, one, negOne, negOne] x) +
    (8) * (zero.kernel x * hpl [one, negOne, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [one, negOne, zero, negOne] x) +
    (8) * (zero.kernel x * hpl [one, zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s115k2W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k2W (i8Psi4s115k2dW x) x := by
  unfold i8Psi4s115k2W i8Psi4s115k2dW
  exact ((((((((((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne, negOne] hx).const_mul (8)))

/-- Chunk 2 of the piece `Ψ₄⁽115⁾`. -/
noncomputable def i8Psi4s115k2 (x : ℝ) : ℝ :=
  (i8Psi4s115k2N0 x + x * i8Psi4s115k2N1 x + x ^ 2 * i8Psi4s115k2N2 x + x ^ 3 * i8Psi4s115k2N3 x +
    x ^ 4 * i8Psi4s115k2N4 x) / x ^ 2 + i8Psi4s115k2W x

/-- The derivative of `i8Psi4s115k2`. -/
noncomputable def i8Psi4s115k2D (x : ℝ) : ℝ :=
  ((i8Psi4s115k2dN0 x + (i8Psi4s115k2N1 x + x * i8Psi4s115k2dN1 x) + (2 * x * i8Psi4s115k2N2 x +
    x ^ 2 * i8Psi4s115k2dN2 x) + (3 * x ^ 2 * i8Psi4s115k2N3 x + x ^ 3 * i8Psi4s115k2dN3 x) +
    (4 * x ^ 3 * i8Psi4s115k2N4 x + x ^ 4 * i8Psi4s115k2dN4 x)) * x ^ 2 - (i8Psi4s115k2N0 x +
    x * i8Psi4s115k2N1 x + x ^ 2 * i8Psi4s115k2N2 x + x ^ 3 * i8Psi4s115k2N3 x +
    x ^ 4 * i8Psi4s115k2N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s115k2dW x

theorem hasDerivAt_i8Psi4s115k2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115k2 (i8Psi4s115k2D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s115k2N0 hx).add (X.mul (hasDerivAt_i8Psi4s115k2N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s115k2N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s115k2N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s115k2N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s115k2W hx)
  unfold i8Psi4s115k2
  refine e.congr_deriv ?_
  unfold i8Psi4s115k2D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 2 of `p₄⁽115⁾` over words. -/
noncomputable def i8P4w115k2 (x : ℝ) : ℝ :=
    ((4 - 4 * x ^ 2) / (x)) * hpl [zero, one, negOne, negOne] x +
    ((4 - 4 * x ^ 2) / (x)) * hpl [one, negOne, negOne, zero] x +
    ((4 - 4 * x ^ 2) / (x)) * hpl [one, negOne, zero, negOne] x +
    ((4 - 4 * x ^ 2) / (x)) * hpl [one, zero, negOne, negOne] x

theorem i8Psi4s115k2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s115k2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w115k2 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s115k2D i8Psi4s115k2N0 i8Psi4s115k2N1 i8Psi4s115k2N2 i8Psi4s115k2N3 i8Psi4s115k2N4
    i8Psi4s115k2dN0 i8Psi4s115k2dN1 i8Psi4s115k2dN2 i8Psi4s115k2dN3 i8Psi4s115k2dN4 i8Psi4s115k2dW
    i8P4w115k2
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, zero, one, negOne, negOne] x = v0 at *
  generalize hpl [zero, one, negOne, negOne, zero] x = v1 at *
  generalize hpl [zero, one, negOne, zero, negOne] x = v2 at *
  generalize hpl [zero, one, zero, negOne, negOne] x = v3 at *
  generalize hpl [zero, negOne, negOne, zero] x = v4 at *
  generalize hpl [zero, negOne, zero, negOne] x = v5 at *
  generalize hpl [zero, zero, negOne, negOne] x = v6 at *
  generalize hpl [zero, one, negOne, negOne] x = v7 at *
  generalize hpl [one, negOne, negOne, zero] x = v8 at *
  generalize hpl [one, negOne, zero, negOne] x = v9 at *
  generalize hpl [one, zero, negOne, negOne] x = v10 at *
  generalize hpl [negOne, negOne, zero] x = v11 at *
  generalize hpl [negOne, zero, negOne] x = v12 at *
  generalize hpl [zero, negOne, negOne] x = v13 at *
  generalize hpl [zero, negOne, zero] x = v14 at *
  generalize hpl [zero, zero, negOne] x = v15 at *
  generalize hpl [one, negOne, negOne] x = v16 at *
  generalize hpl [negOne, negOne] x = v17 at *
  generalize hpl [negOne, zero] x = v18 at *
  generalize hpl [zero, negOne] x = v19 at *
  generalize hpl [negOne] x = v20 at *
  generalize hpl [zero] x = v21 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽115⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s115 (x : ℝ) : ℝ :=
  i8Psi4s115k0 x + i8Psi4s115k1 x + i8Psi4s115k2 x

/-- The derivative of `Ψ₄⁽115⁾`. -/
noncomputable def i8Psi4s115D (x : ℝ) : ℝ :=
  i8Psi4s115k0D x + i8Psi4s115k1D x + i8Psi4s115k2D x

theorem hasDerivAt_i8Psi4s115 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s115 (i8Psi4s115D x) x := by
  unfold i8Psi4s115 i8Psi4s115D
  exact (((hasDerivAt_i8Psi4s115k0 hx).add (hasDerivAt_i8Psi4s115k1 hx)).add
    (hasDerivAt_i8Psi4s115k2 hx))

/-- The sub-piece 115 of `p₄` in `ξ`: from `t B0 A2 (-λ)^2/2!`, the term with `log^1 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s115 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * Real.log x * ((1 + x) / (1 -
    x) * (2 * hpl [negOne, negOne] x)))

/-- `p₄⁽115⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w115 (x : ℝ) : ℝ :=
  i8P4w115k0 x + i8P4w115k1 x + i8P4w115k2 x

theorem i8P4s115_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s115 x = i8P4w115 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s115 i8P4w115 i8P4w115k0 i8P4w115k1 i8P4w115k2
  rw [i13_log_one_sub_eq hx]
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [one] hx
  have e1 := hpl_mul_hpl [negOne, negOne] [zero, one] hx
  have e2 := hpl_mul_hpl [negOne, negOne] [one, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  linear_combination (norm := skip) (((4 - 4 * x ^ 2) / (x)) * hpl [negOne, negOne] x) * e0 +
    (((4 - 4 * x ^ 2) / (x))) * e1 + (((4 - 4 * x ^ 2) / (x))) * e2
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

/-- **`(Ψ₄⁽115⁾)'(ξ) ξ' = p₄⁽115⁾`**, in terms of `ξ`. -/
theorem i8Psi4s115D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s115D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s115 x := by
  rw [i8P4s115_eq_w hx]
  unfold i8Psi4s115D i8P4w115
  rw [← i8Psi4s115k0D_mul hx, ← i8Psi4s115k1D_mul hx, ← i8Psi4s115k2D_mul hx]
  ring

end QED.ThreeLoopD
