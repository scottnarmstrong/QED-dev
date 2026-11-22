/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P44

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 146 to 147

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s146`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s146D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s146`, `QED.ThreeLoopD.i8Psi4s146D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s146k0N0 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne, one, one] x +
    (-2) * hpl [negOne, zero, one, one] x +
    (-2) * hpl [negOne, one, zero, one] x +
    (-2) * hpl [negOne, one, one, zero] x +
    (-2) * hpl [zero, negOne, one, one] x

/-- The derivative of `i8Psi4s146k0N0`. -/
noncomputable def i8Psi4s146k0dN0 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [one, one] x) +
    (-2) * (negOne.kernel x * hpl [zero, one, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one, one] x)

theorem hasDerivAt_i8Psi4s146k0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k0N0 (i8Psi4s146k0dN0 x) x := by
  unfold i8Psi4s146k0N0 i8Psi4s146k0dN0
  exact ((((((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons negOne [zero, one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s146k0N1 (x : ℝ) : ℝ :=
    (-3) * hpl [one, one] x +
    (-2) * hpl [zero, one, one] x +
    (-2) * hpl [one, zero, one] x +
    (-2) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s146k0N1`. -/
noncomputable def i8Psi4s146k0dN1 (x : ℝ) : ℝ :=
    (-3) * (one.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [one, one] x) +
    (-2) * (one.kernel x * hpl [zero, one] x) +
    (-2) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s146k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k0N1 (i8Psi4s146k0dN1 x) x := by
  unfold i8Psi4s146k0N1 i8Psi4s146k0dN1
  exact (((((hasDerivAt_hpl_cons one [one] hx).const_mul (-3)).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s146k0N2 (x : ℝ) : ℝ :=
    (9 / 4) * hpl [one] x +
    (3) * hpl [zero, one] x +
    (-1 / 2) * hpl [one, zero] x +
    (5) * hpl [one, one] x +
    (2) * hpl [negOne, one, one] x +
    (-1) * hpl [zero, one, one] x +
    (1) * hpl [one, zero, one] x +
    (1) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s146k0N2`. -/
noncomputable def i8Psi4s146k0dN2 (x : ℝ) : ℝ :=
    (9 / 4) * (one.kernel x * hpl [] x) +
    (3) * (zero.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [zero] x) +
    (5) * (one.kernel x * hpl [one] x) +
    (2) * (negOne.kernel x * hpl [one, one] x) +
    (-1) * (zero.kernel x * hpl [one, one] x) +
    (1) * (one.kernel x * hpl [zero, one] x) +
    (1) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s146k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k0N2 (i8Psi4s146k0dN2 x) x := by
  unfold i8Psi4s146k0N2 i8Psi4s146k0dN2
  exact (((((((((hasDerivAt_hpl_cons one [] hx).const_mul (9 / 4)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s146k0N3 (x : ℝ) : ℝ :=
    (-11 / 4) +
    (1 / 2) * hpl [zero] x +
    (-3) * hpl [one] x +
    (1) * hpl [zero, one] x +
    (1) * hpl [one, zero] x +
    (-3) * hpl [one, one] x +
    (2) * hpl [zero, one, one] x +
    (2) * hpl [one, zero, one] x +
    (2) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s146k0N3`. -/
noncomputable def i8Psi4s146k0dN3 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-3) * (one.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [zero] x) +
    (-3) * (one.kernel x * hpl [one] x) +
    (2) * (zero.kernel x * hpl [one, one] x) +
    (2) * (one.kernel x * hpl [zero, one] x) +
    (2) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s146k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k0N3 (i8Psi4s146k0dN3 x) x := by
  unfold i8Psi4s146k0N3 i8Psi4s146k0dN3
  exact (((((((((hasDerivAt_const x (-11 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s146k0N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 4) * hpl [zero] x +
    (3 / 4) * hpl [one] x +
    (-1 / 2) * hpl [zero, one] x +
    (-1 / 2) * hpl [one, zero] x +
    (1) * hpl [one, one] x +
    (-1) * hpl [negOne, one, one] x +
    (-1) * hpl [zero, one, one] x +
    (-1) * hpl [one, zero, one] x +
    (-1) * hpl [one, one, zero] x +
    (2) * hpl [negOne, zero, one, one] x +
    (2) * hpl [negOne, one, zero, one] x +
    (2) * hpl [negOne, one, one, zero] x +
    (2) * hpl [zero, negOne, one, one] x

/-- The derivative of `i8Psi4s146k0N4`. -/
noncomputable def i8Psi4s146k0dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 4) * (zero.kernel x * hpl [] x) +
    (3 / 4) * (one.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [zero] x) +
    (1) * (one.kernel x * hpl [one] x) +
    (-1) * (negOne.kernel x * hpl [one, one] x) +
    (-1) * (zero.kernel x * hpl [one, one] x) +
    (-1) * (one.kernel x * hpl [zero, one] x) +
    (-1) * (one.kernel x * hpl [one, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, one, one] x) +
    (2) * (negOne.kernel x * hpl [one, zero, one] x) +
    (2) * (negOne.kernel x * hpl [one, one, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, one, one] x)

theorem hasDerivAt_i8Psi4s146k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k0N4 (i8Psi4s146k0dN4 x) x := by
  unfold i8Psi4s146k0N4 i8Psi4s146k0dN4
  exact ((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (3 / 4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (2)))

/-- The part of `Ψ₄⁽146⁾` with constant coefficients. -/
noncomputable def i8Psi4s146k0W (x : ℝ) : ℝ :=
    (2) * hpl [zero, zero, one] x +
    (2) * hpl [zero, one, zero] x +
    (-2) * hpl [zero, zero, one, one] x +
    (-2) * hpl [zero, one, zero, one] x +
    (-2) * hpl [zero, one, one, zero] x +
    (-8) * hpl [zero, negOne, zero, one, one] x +
    (-8) * hpl [zero, negOne, one, zero, one] x +
    (-8) * hpl [zero, negOne, one, one, zero] x +
    (-8) * hpl [zero, zero, negOne, one, one] x

/-- The derivative of `i8Psi4s146k0W`. -/
noncomputable def i8Psi4s146k0dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (2) * (zero.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, one, one] x) +
    (-2) * (zero.kernel x * hpl [one, zero, one] x) +
    (-2) * (zero.kernel x * hpl [one, one, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, one, one] x) +
    (-8) * (zero.kernel x * hpl [negOne, one, zero, one] x) +
    (-8) * (zero.kernel x * hpl [negOne, one, one, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, one, one] x)

theorem hasDerivAt_i8Psi4s146k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k0W (i8Psi4s146k0dW x) x := by
  unfold i8Psi4s146k0W i8Psi4s146k0dW
  exact ((((((((((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one, one] hx).const_mul (-8)))

/-- Chunk 0 of the piece `Ψ₄⁽146⁾`. -/
noncomputable def i8Psi4s146k0 (x : ℝ) : ℝ :=
  (i8Psi4s146k0N0 x + x * i8Psi4s146k0N1 x + x ^ 2 * i8Psi4s146k0N2 x + x ^ 3 * i8Psi4s146k0N3 x +
    x ^ 4 * i8Psi4s146k0N4 x) / x ^ 2 + i8Psi4s146k0W x

/-- The derivative of `i8Psi4s146k0`. -/
noncomputable def i8Psi4s146k0D (x : ℝ) : ℝ :=
  ((i8Psi4s146k0dN0 x + (i8Psi4s146k0N1 x + x * i8Psi4s146k0dN1 x) + (2 * x * i8Psi4s146k0N2 x +
    x ^ 2 * i8Psi4s146k0dN2 x) + (3 * x ^ 2 * i8Psi4s146k0N3 x + x ^ 3 * i8Psi4s146k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s146k0N4 x + x ^ 4 * i8Psi4s146k0dN4 x)) * x ^ 2 - (i8Psi4s146k0N0 x +
    x * i8Psi4s146k0N1 x + x ^ 2 * i8Psi4s146k0N2 x + x ^ 3 * i8Psi4s146k0N3 x +
    x ^ 4 * i8Psi4s146k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s146k0dW x

theorem hasDerivAt_i8Psi4s146k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k0 (i8Psi4s146k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s146k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s146k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s146k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s146k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s146k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s146k0W hx)
  unfold i8Psi4s146k0
  refine e.congr_deriv ?_
  unfold i8Psi4s146k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽146⁾` over words. -/
noncomputable def i8P4w146k0 (x : ℝ) : ℝ :=
    ((-4 + 4 * x ^ 2) / (x)) * hpl [negOne, zero, one, one] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [negOne, one, zero, one] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [negOne, one, one, zero] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [zero, negOne, one, one] x

theorem i8Psi4s146k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s146k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w146k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s146k0D i8Psi4s146k0N0 i8Psi4s146k0N1 i8Psi4s146k0N2 i8Psi4s146k0N3 i8Psi4s146k0N4
    i8Psi4s146k0dN0 i8Psi4s146k0dN1 i8Psi4s146k0dN2 i8Psi4s146k0dN3 i8Psi4s146k0dN4 i8Psi4s146k0dW
    i8P4w146k0
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, zero, one, one] x = v0 at *
  generalize hpl [zero, negOne, one, zero, one] x = v1 at *
  generalize hpl [zero, negOne, one, one, zero] x = v2 at *
  generalize hpl [zero, zero, negOne, one, one] x = v3 at *
  generalize hpl [negOne, zero, one, one] x = v4 at *
  generalize hpl [negOne, one, zero, one] x = v5 at *
  generalize hpl [negOne, one, one, zero] x = v6 at *
  generalize hpl [zero, negOne, one, one] x = v7 at *
  generalize hpl [zero, zero, one, one] x = v8 at *
  generalize hpl [zero, one, zero, one] x = v9 at *
  generalize hpl [zero, one, one, zero] x = v10 at *
  generalize hpl [negOne, one, one] x = v11 at *
  generalize hpl [zero, zero, one] x = v12 at *
  generalize hpl [zero, one, zero] x = v13 at *
  generalize hpl [zero, one, one] x = v14 at *
  generalize hpl [one, zero, one] x = v15 at *
  generalize hpl [one, one, zero] x = v16 at *
  generalize hpl [zero, one] x = v17 at *
  generalize hpl [one, zero] x = v18 at *
  generalize hpl [one, one] x = v19 at *
  generalize hpl [zero] x = v20 at *
  generalize hpl [one] x = v21 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s146k1N0 (x : ℝ) : ℝ :=
    (-1) * hpl [one, negOne, one] x +
    (-1) * hpl [one, one, negOne] x +
    (-2) * hpl [zero, one, negOne, one] x +
    (-2) * hpl [zero, one, one, negOne] x +
    (-2) * hpl [one, negOne, zero, one] x +
    (-2) * hpl [one, negOne, one, zero] x

/-- The derivative of `i8Psi4s146k1N0`. -/
noncomputable def i8Psi4s146k1dN0 (x : ℝ) : ℝ :=
    (-1) * (one.kernel x * hpl [negOne, one] x) +
    (-1) * (one.kernel x * hpl [one, negOne] x) +
    (-2) * (zero.kernel x * hpl [one, negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero, one] x) +
    (-2) * (one.kernel x * hpl [negOne, one, zero] x)

theorem hasDerivAt_i8Psi4s146k1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k1N0 (i8Psi4s146k1dN0 x) x := by
  unfold i8Psi4s146k1N0 i8Psi4s146k1dN0
  exact (((((((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, one, zero] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s146k1N1 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne, one] x +
    (-1) * hpl [one, negOne] x +
    (-2) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, one, zero] x

/-- The derivative of `i8Psi4s146k1N1`. -/
noncomputable def i8Psi4s146k1dN1 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s146k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k1N1 (i8Psi4s146k1dN1 x) x := by
  unfold i8Psi4s146k1N1 i8Psi4s146k1dN1
  exact (((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s146k1N2 (x : ℝ) : ℝ :=
    (-5 / 4) * hpl [negOne] x +
    (-2) * hpl [one] x +
    (-3 / 2) * hpl [negOne, one] x +
    (1) * hpl [zero, one] x +
    (5 / 2) * hpl [one, negOne] x +
    (3 / 2) * hpl [one, zero] x +
    (-1) * hpl [negOne, zero, one] x +
    (-1) * hpl [negOne, one, zero] x +
    (2) * hpl [one, negOne, one] x +
    (2) * hpl [one, one, negOne] x

/-- The derivative of `i8Psi4s146k1N2`. -/
noncomputable def i8Psi4s146k1dN2 (x : ℝ) : ℝ :=
    (-5 / 4) * (negOne.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [] x) +
    (-3 / 2) * (negOne.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [one] x) +
    (5 / 2) * (one.kernel x * hpl [negOne] x) +
    (3 / 2) * (one.kernel x * hpl [zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, one] x) +
    (-1) * (negOne.kernel x * hpl [one, zero] x) +
    (2) * (one.kernel x * hpl [negOne, one] x) +
    (2) * (one.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s146k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k1N2 (i8Psi4s146k1dN2 x) x := by
  unfold i8Psi4s146k1N2 i8Psi4s146k1dN2
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-5 / 4)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s146k1N3 (x : ℝ) : ℝ :=
    (19 / 4) +
    (-3 / 2) * hpl [negOne] x +
    (-3 / 2) * hpl [zero] x +
    (3 / 2) * hpl [one] x +
    (-1) * hpl [negOne, one] x +
    (-1) * hpl [zero, one] x +
    (-1) * hpl [one, negOne] x +
    (-1) * hpl [one, zero] x +
    (2) * hpl [negOne, zero, one] x +
    (2) * hpl [negOne, one, zero] x

/-- The derivative of `i8Psi4s146k1N3`. -/
noncomputable def i8Psi4s146k1dN3 (x : ℝ) : ℝ :=
    0 +
    (-3 / 2) * (negOne.kernel x * hpl [] x) +
    (-3 / 2) * (zero.kernel x * hpl [] x) +
    (3 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [one] x) +
    (-1) * (zero.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [negOne] x) +
    (-1) * (one.kernel x * hpl [zero] x) +
    (2) * (negOne.kernel x * hpl [zero, one] x) +
    (2) * (negOne.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s146k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k1N3 (i8Psi4s146k1dN3 x) x := by
  unfold i8Psi4s146k1N3 i8Psi4s146k1dN3
  exact ((((((((((hasDerivAt_const x (19 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s146k1N4 (x : ℝ) : ℝ :=
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
    (-1) * hpl [one, negOne, one] x +
    (-1) * hpl [one, one, negOne] x +
    (2) * hpl [zero, one, negOne, one] x +
    (2) * hpl [zero, one, one, negOne] x +
    (2) * hpl [one, negOne, zero, one] x +
    (2) * hpl [one, negOne, one, zero] x

/-- The derivative of `i8Psi4s146k1N4`. -/
noncomputable def i8Psi4s146k1dN4 (x : ℝ) : ℝ :=
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
    (-1) * (one.kernel x * hpl [negOne, one] x) +
    (-1) * (one.kernel x * hpl [one, negOne] x) +
    (2) * (zero.kernel x * hpl [one, negOne, one] x) +
    (2) * (zero.kernel x * hpl [one, one, negOne] x) +
    (2) * (one.kernel x * hpl [negOne, zero, one] x) +
    (2) * (one.kernel x * hpl [negOne, one, zero] x)

theorem hasDerivAt_i8Psi4s146k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k1N4 (i8Psi4s146k1dN4 x) x := by
  unfold i8Psi4s146k1N4 i8Psi4s146k1dN4
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
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, one, zero] hx).const_mul (2)))

/-- The part of `Ψ₄⁽146⁾` with constant coefficients. -/
noncomputable def i8Psi4s146k1W (x : ℝ) : ℝ :=
    (1) * hpl [zero, negOne] x +
    (1) * hpl [zero, negOne, one] x +
    (2) * hpl [zero, zero, one] x +
    (1) * hpl [zero, one, negOne] x +
    (2) * hpl [zero, one, zero] x +
    (2) * hpl [zero, negOne, zero, one] x +
    (2) * hpl [zero, negOne, one, zero] x +
    (-8) * hpl [zero, zero, one, negOne, one] x +
    (-8) * hpl [zero, zero, one, one, negOne] x +
    (-8) * hpl [zero, one, negOne, zero, one] x +
    (-8) * hpl [zero, one, negOne, one, zero] x

/-- The derivative of `i8Psi4s146k1W`. -/
noncomputable def i8Psi4s146k1dW (x : ℝ) : ℝ :=
    (1) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (2) * (zero.kernel x * hpl [one, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (2) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, one, negOne, one] x) +
    (-8) * (zero.kernel x * hpl [zero, one, one, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, negOne, zero, one] x) +
    (-8) * (zero.kernel x * hpl [one, negOne, one, zero] x)

theorem hasDerivAt_i8Psi4s146k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k1W (i8Psi4s146k1dW x) x := by
  unfold i8Psi4s146k1W i8Psi4s146k1dW
  exact ((((((((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one, zero] hx).const_mul (-8)))

/-- Chunk 1 of the piece `Ψ₄⁽146⁾`. -/
noncomputable def i8Psi4s146k1 (x : ℝ) : ℝ :=
  (i8Psi4s146k1N0 x + x * i8Psi4s146k1N1 x + x ^ 2 * i8Psi4s146k1N2 x + x ^ 3 * i8Psi4s146k1N3 x +
    x ^ 4 * i8Psi4s146k1N4 x) / x ^ 2 + i8Psi4s146k1W x

/-- The derivative of `i8Psi4s146k1`. -/
noncomputable def i8Psi4s146k1D (x : ℝ) : ℝ :=
  ((i8Psi4s146k1dN0 x + (i8Psi4s146k1N1 x + x * i8Psi4s146k1dN1 x) + (2 * x * i8Psi4s146k1N2 x +
    x ^ 2 * i8Psi4s146k1dN2 x) + (3 * x ^ 2 * i8Psi4s146k1N3 x + x ^ 3 * i8Psi4s146k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s146k1N4 x + x ^ 4 * i8Psi4s146k1dN4 x)) * x ^ 2 - (i8Psi4s146k1N0 x +
    x * i8Psi4s146k1N1 x + x ^ 2 * i8Psi4s146k1N2 x + x ^ 3 * i8Psi4s146k1N3 x +
    x ^ 4 * i8Psi4s146k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s146k1dW x

theorem hasDerivAt_i8Psi4s146k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k1 (i8Psi4s146k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s146k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s146k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s146k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s146k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s146k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s146k1W hx)
  unfold i8Psi4s146k1
  refine e.congr_deriv ?_
  unfold i8Psi4s146k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽146⁾` over words. -/
noncomputable def i8P4w146k1 (x : ℝ) : ℝ :=
    ((-4 + 4 * x ^ 2) / (x)) * hpl [zero, one, negOne, one] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [zero, one, one, negOne] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [one, negOne, zero, one] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [one, negOne, one, zero] x

theorem i8Psi4s146k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s146k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w146k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s146k1D i8Psi4s146k1N0 i8Psi4s146k1N1 i8Psi4s146k1N2 i8Psi4s146k1N3 i8Psi4s146k1N4
    i8Psi4s146k1dN0 i8Psi4s146k1dN1 i8Psi4s146k1dN2 i8Psi4s146k1dN3 i8Psi4s146k1dN4 i8Psi4s146k1dW
    i8P4w146k1
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, zero, one, negOne, one] x = v0 at *
  generalize hpl [zero, zero, one, one, negOne] x = v1 at *
  generalize hpl [zero, one, negOne, zero, one] x = v2 at *
  generalize hpl [zero, one, negOne, one, zero] x = v3 at *
  generalize hpl [zero, negOne, zero, one] x = v4 at *
  generalize hpl [zero, negOne, one, zero] x = v5 at *
  generalize hpl [zero, one, negOne, one] x = v6 at *
  generalize hpl [zero, one, one, negOne] x = v7 at *
  generalize hpl [one, negOne, zero, one] x = v8 at *
  generalize hpl [one, negOne, one, zero] x = v9 at *
  generalize hpl [negOne, zero, one] x = v10 at *
  generalize hpl [negOne, one, zero] x = v11 at *
  generalize hpl [zero, negOne, one] x = v12 at *
  generalize hpl [zero, zero, one] x = v13 at *
  generalize hpl [zero, one, negOne] x = v14 at *
  generalize hpl [zero, one, zero] x = v15 at *
  generalize hpl [one, negOne, one] x = v16 at *
  generalize hpl [one, one, negOne] x = v17 at *
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

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s146k2N0 (x : ℝ) : ℝ :=
    (-2) * hpl [one, zero, negOne, one] x +
    (-2) * hpl [one, zero, one, negOne] x +
    (-2) * hpl [one, one, negOne, zero] x +
    (-2) * hpl [one, one, zero, negOne] x

/-- The derivative of `i8Psi4s146k2N0`. -/
noncomputable def i8Psi4s146k2dN0 (x : ℝ) : ℝ :=
    (-2) * (one.kernel x * hpl [zero, negOne, one] x) +
    (-2) * (one.kernel x * hpl [zero, one, negOne] x) +
    (-2) * (one.kernel x * hpl [one, negOne, zero] x) +
    (-2) * (one.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s146k2N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k2N0 (i8Psi4s146k2dN0 x) x := by
  unfold i8Psi4s146k2N0 i8Psi4s146k2dN0
  exact (((((hasDerivAt_hpl_cons one [zero, negOne, one] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [zero, one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s146k2N1 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne, one] x +
    (-2) * hpl [one, negOne] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, one, negOne] x +
    (-2) * hpl [one, negOne, zero] x +
    (-2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s146k2N1`. -/
noncomputable def i8Psi4s146k2dN1 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s146k2N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k2N1 (i8Psi4s146k2dN1 x) x := by
  unfold i8Psi4s146k2N1 i8Psi4s146k2dN1
  exact (((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s146k2N2 (x : ℝ) : ℝ :=
    (-5) * hpl [negOne] x +
    (-7 / 4) * hpl [one] x +
    (5 / 2) * hpl [negOne, zero] x +
    (-7 / 2) * hpl [negOne, one] x +
    (2) * hpl [zero, negOne] x +
    (9 / 2) * hpl [one, negOne] x +
    (-1) * hpl [one, negOne, zero] x +
    (-1) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s146k2N2`. -/
noncomputable def i8Psi4s146k2dN2 (x : ℝ) : ℝ :=
    (-5) * (negOne.kernel x * hpl [] x) +
    (-7 / 4) * (one.kernel x * hpl [] x) +
    (5 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-7 / 2) * (negOne.kernel x * hpl [one] x) +
    (2) * (zero.kernel x * hpl [negOne] x) +
    (9 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1) * (one.kernel x * hpl [negOne, zero] x) +
    (-1) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s146k2N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k2N2 (i8Psi4s146k2dN2 x) x := by
  unfold i8Psi4s146k2N2 i8Psi4s146k2dN2
  exact (((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-5)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-7 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (9 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s146k2N3 (x : ℝ) : ℝ :=
    (37 / 4) +
    (-11 / 2) * hpl [negOne] x +
    (-5 / 2) * hpl [zero] x +
    (3 / 2) * hpl [one] x +
    (3) * hpl [negOne, zero] x +
    (-2) * hpl [negOne, one] x +
    (3) * hpl [zero, negOne] x +
    (-2) * hpl [one, negOne] x +
    (2) * hpl [zero, negOne, one] x +
    (2) * hpl [zero, one, negOne] x +
    (2) * hpl [one, negOne, zero] x +
    (2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s146k2N3`. -/
noncomputable def i8Psi4s146k2dN3 (x : ℝ) : ℝ :=
    0 +
    (-11 / 2) * (negOne.kernel x * hpl [] x) +
    (-5 / 2) * (zero.kernel x * hpl [] x) +
    (3 / 2) * (one.kernel x * hpl [] x) +
    (3) * (negOne.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [one] x) +
    (3) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (one.kernel x * hpl [negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, one] x) +
    (2) * (zero.kernel x * hpl [one, negOne] x) +
    (2) * (one.kernel x * hpl [negOne, zero] x) +
    (2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s146k2N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k2N3 (i8Psi4s146k2dN3 x) x := by
  unfold i8Psi4s146k2N3 i8Psi4s146k2dN3
  exact ((((((((((((hasDerivAt_const x (37 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽146⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s146k2N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 2) * hpl [negOne] x +
    (-1 / 4) * hpl [zero] x +
    (1 / 4) * hpl [one] x +
    (1 / 2) * hpl [negOne, zero] x +
    (-1 / 2) * hpl [negOne, one] x +
    (1 / 2) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [one, negOne] x +
    (1) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, negOne] x +
    (1) * hpl [one, negOne, zero] x +
    (1) * hpl [one, zero, negOne] x +
    (2) * hpl [one, zero, negOne, one] x +
    (2) * hpl [one, zero, one, negOne] x +
    (2) * hpl [one, one, negOne, zero] x +
    (2) * hpl [one, one, zero, negOne] x

/-- The derivative of `i8Psi4s146k2N4`. -/
noncomputable def i8Psi4s146k2dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 4) * (one.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (1) * (one.kernel x * hpl [negOne, zero] x) +
    (1) * (one.kernel x * hpl [zero, negOne] x) +
    (2) * (one.kernel x * hpl [zero, negOne, one] x) +
    (2) * (one.kernel x * hpl [zero, one, negOne] x) +
    (2) * (one.kernel x * hpl [one, negOne, zero] x) +
    (2) * (one.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s146k2N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k2N4 (i8Psi4s146k2dN4 x) x := by
  unfold i8Psi4s146k2N4 i8Psi4s146k2dN4
  exact ((((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, zero, negOne] hx).const_mul (2)))

/-- The part of `Ψ₄⁽146⁾` with constant coefficients. -/
noncomputable def i8Psi4s146k2W (x : ℝ) : ℝ :=
    (2) * hpl [zero, one] x +
    (2) * hpl [zero, negOne, zero] x +
    (2) * hpl [zero, zero, negOne] x +
    (2) * hpl [zero, zero, negOne, one] x +
    (2) * hpl [zero, zero, one, negOne] x +
    (2) * hpl [zero, one, negOne, zero] x +
    (2) * hpl [zero, one, zero, negOne] x +
    (-8) * hpl [zero, one, zero, negOne, one] x +
    (-8) * hpl [zero, one, zero, one, negOne] x +
    (-8) * hpl [zero, one, one, negOne, zero] x +
    (-8) * hpl [zero, one, one, zero, negOne] x

/-- The derivative of `i8Psi4s146k2W`. -/
noncomputable def i8Psi4s146k2dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [one] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (zero.kernel x * hpl [zero, negOne] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (2) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (2) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, zero, negOne, one] x) +
    (-8) * (zero.kernel x * hpl [one, zero, one, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, one, negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [one, one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s146k2W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k2W (i8Psi4s146k2dW x) x := by
  unfold i8Psi4s146k2W i8Psi4s146k2dW
  exact ((((((((((((hasDerivAt_hpl_cons zero [one] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero, negOne] hx).const_mul (-8)))

/-- Chunk 2 of the piece `Ψ₄⁽146⁾`. -/
noncomputable def i8Psi4s146k2 (x : ℝ) : ℝ :=
  (i8Psi4s146k2N0 x + x * i8Psi4s146k2N1 x + x ^ 2 * i8Psi4s146k2N2 x + x ^ 3 * i8Psi4s146k2N3 x +
    x ^ 4 * i8Psi4s146k2N4 x) / x ^ 2 + i8Psi4s146k2W x

/-- The derivative of `i8Psi4s146k2`. -/
noncomputable def i8Psi4s146k2D (x : ℝ) : ℝ :=
  ((i8Psi4s146k2dN0 x + (i8Psi4s146k2N1 x + x * i8Psi4s146k2dN1 x) + (2 * x * i8Psi4s146k2N2 x +
    x ^ 2 * i8Psi4s146k2dN2 x) + (3 * x ^ 2 * i8Psi4s146k2N3 x + x ^ 3 * i8Psi4s146k2dN3 x) +
    (4 * x ^ 3 * i8Psi4s146k2N4 x + x ^ 4 * i8Psi4s146k2dN4 x)) * x ^ 2 - (i8Psi4s146k2N0 x +
    x * i8Psi4s146k2N1 x + x ^ 2 * i8Psi4s146k2N2 x + x ^ 3 * i8Psi4s146k2N3 x +
    x ^ 4 * i8Psi4s146k2N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s146k2dW x

theorem hasDerivAt_i8Psi4s146k2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146k2 (i8Psi4s146k2D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s146k2N0 hx).add (X.mul (hasDerivAt_i8Psi4s146k2N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s146k2N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s146k2N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s146k2N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s146k2W hx)
  unfold i8Psi4s146k2
  refine e.congr_deriv ?_
  unfold i8Psi4s146k2D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 2 of `p₄⁽146⁾` over words. -/
noncomputable def i8P4w146k2 (x : ℝ) : ℝ :=
    ((-4 + 4 * x ^ 2) / (x)) * hpl [one, zero, negOne, one] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [one, zero, one, negOne] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [one, one, negOne, zero] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [one, one, zero, negOne] x

theorem i8Psi4s146k2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s146k2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w146k2 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s146k2D i8Psi4s146k2N0 i8Psi4s146k2N1 i8Psi4s146k2N2 i8Psi4s146k2N3 i8Psi4s146k2N4
    i8Psi4s146k2dN0 i8Psi4s146k2dN1 i8Psi4s146k2dN2 i8Psi4s146k2dN3 i8Psi4s146k2dN4 i8Psi4s146k2dW
    i8P4w146k2
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, one, zero, negOne, one] x = v0 at *
  generalize hpl [zero, one, zero, one, negOne] x = v1 at *
  generalize hpl [zero, one, one, negOne, zero] x = v2 at *
  generalize hpl [zero, one, one, zero, negOne] x = v3 at *
  generalize hpl [zero, zero, negOne, one] x = v4 at *
  generalize hpl [zero, zero, one, negOne] x = v5 at *
  generalize hpl [zero, one, negOne, zero] x = v6 at *
  generalize hpl [zero, one, zero, negOne] x = v7 at *
  generalize hpl [one, zero, negOne, one] x = v8 at *
  generalize hpl [one, zero, one, negOne] x = v9 at *
  generalize hpl [one, one, negOne, zero] x = v10 at *
  generalize hpl [one, one, zero, negOne] x = v11 at *
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

/-- The piece `Ψ₄⁽146⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s146 (x : ℝ) : ℝ :=
  i8Psi4s146k0 x + i8Psi4s146k1 x + i8Psi4s146k2 x

/-- The derivative of `Ψ₄⁽146⁾`. -/
noncomputable def i8Psi4s146D (x : ℝ) : ℝ :=
  i8Psi4s146k0D x + i8Psi4s146k1D x + i8Psi4s146k2D x

theorem hasDerivAt_i8Psi4s146 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s146 (i8Psi4s146D x) x := by
  unfold i8Psi4s146 i8Psi4s146D
  exact (((hasDerivAt_i8Psi4s146k0 hx).add (hasDerivAt_i8Psi4s146k1 hx)).add
    (hasDerivAt_i8Psi4s146k2 hx))

/-- The sub-piece 146 of `p₄` in `ξ`: from `t B0 A1 (-λ)^3/3!`, the term with `log^2 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s146 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 2 * Real.log x * ((1 + x) / (1 - x) * (-hpl [negOne] x))

/-- `p₄⁽146⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w146 (x : ℝ) : ℝ :=
  i8P4w146k0 x + i8P4w146k1 x + i8P4w146k2 x

theorem i8P4s146_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s146 x = i8P4w146 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s146 i8P4w146 i8P4w146k0 i8P4w146k1 i8P4w146k2
  rw [i13_log_one_sub_eq hx]
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [one] [one] hx
  have e1 := hpl_mul_hpl [zero] [one, one] hx
  have e2 := hpl_mul_hpl [negOne] [zero, one, one] hx
  have e3 := hpl_mul_hpl [negOne] [one, zero, one] hx
  have e4 := hpl_mul_hpl [negOne] [one, one, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e3
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e4
  linear_combination (norm := skip) (((-2 +
    2 * x ^ 2) / (x)) * hpl [zero] x * hpl [negOne] x) * e0 + (((-4 +
    4 * x ^ 2) / (x)) * hpl [negOne] x) * e1 + (((-4 + 4 * x ^ 2) / (x))) * e2 + (((-4 +
    4 * x ^ 2) / (x))) * e3 + (((-4 + 4 * x ^ 2) / (x))) * e4
  field_simp
  generalize hpl [negOne, zero, one, one] x = v0 at *
  generalize hpl [negOne, one, zero, one] x = v1 at *
  generalize hpl [negOne, one, one, zero] x = v2 at *
  generalize hpl [zero, negOne, one, one] x = v3 at *
  generalize hpl [zero, one, negOne, one] x = v4 at *
  generalize hpl [zero, one, one, negOne] x = v5 at *
  generalize hpl [one, negOne, zero, one] x = v6 at *
  generalize hpl [one, negOne, one, zero] x = v7 at *
  generalize hpl [one, zero, negOne, one] x = v8 at *
  generalize hpl [one, zero, one, negOne] x = v9 at *
  generalize hpl [one, one, negOne, zero] x = v10 at *
  generalize hpl [one, one, zero, negOne] x = v11 at *
  generalize hpl [zero, one, one] x = v12 at *
  generalize hpl [one, zero, one] x = v13 at *
  generalize hpl [one, one, zero] x = v14 at *
  generalize hpl [one, one] x = v15 at *
  generalize hpl [negOne] x = v16 at *
  generalize hpl [zero] x = v17 at *
  generalize hpl [one] x = v18 at *
  ring

/-- **`(Ψ₄⁽146⁾)'(ξ) ξ' = p₄⁽146⁾`**, in terms of `ξ`. -/
theorem i8Psi4s146D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s146D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s146 x := by
  rw [i8P4s146_eq_w hx]
  unfold i8Psi4s146D i8P4w146
  rw [← i8Psi4s146k0D_mul hx, ← i8Psi4s146k1D_mul hx, ← i8Psi4s146k2D_mul hx]
  ring

/-- The part of `ξ² Ψ₄⁽147⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s147N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s147N0`. -/
noncomputable def i8Psi4s147dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s147N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s147N0 (i8Psi4s147dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽147⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s147N1 (x : ℝ) : ℝ :=
    (8) * hpl [one, one, one] x

/-- The derivative of `i8Psi4s147N1`. -/
noncomputable def i8Psi4s147dN1 (x : ℝ) : ℝ :=
    (8) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi4s147N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s147N1 (i8Psi4s147dN1 x) x := by
  unfold i8Psi4s147N1 i8Psi4s147dN1
  exact ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (8))

/-- The part of `ξ² Ψ₄⁽147⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s147N2 (x : ℝ) : ℝ :=
    (-1) * hpl [one] x +
    (-2) * hpl [one, one] x +
    (-12) * hpl [one, one, one] x

/-- The derivative of `i8Psi4s147N2`. -/
noncomputable def i8Psi4s147dN2 (x : ℝ) : ℝ :=
    (-1) * (one.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [one] x) +
    (-12) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi4s147N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s147N2 (i8Psi4s147dN2 x) x := by
  unfold i8Psi4s147N2 i8Psi4s147dN2
  exact ((((hasDerivAt_hpl_cons one [] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽147⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s147N3 (x : ℝ) : ℝ :=
    (1) +
    (2) * hpl [one] x +
    (4) * hpl [one, one] x +
    (8) * hpl [one, one, one] x

/-- The derivative of `i8Psi4s147N3`. -/
noncomputable def i8Psi4s147dN3 (x : ℝ) : ℝ :=
    0 +
    (2) * (one.kernel x * hpl [] x) +
    (4) * (one.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi4s147N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s147N3 (i8Psi4s147dN3 x) x := by
  unfold i8Psi4s147N3 i8Psi4s147dN3
  exact ((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽147⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s147N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (-1) * hpl [one] x +
    (-2) * hpl [one, one] x +
    (-4) * hpl [one, one, one] x

/-- The derivative of `i8Psi4s147N4`. -/
noncomputable def i8Psi4s147dN4 (x : ℝ) : ℝ :=
    0 +
    (-1) * (one.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [one] x) +
    (-4) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi4s147N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s147N4 (i8Psi4s147dN4 x) x := by
  unfold i8Psi4s147N4 i8Psi4s147dN4
  exact ((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽147⁾` with constant coefficients. -/
noncomputable def i8Psi4s147W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, one, one] x +
    (8) * hpl [zero, one, one, one] x

/-- The derivative of `i8Psi4s147W`. -/
noncomputable def i8Psi4s147dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [one, one] x) +
    (8) * (zero.kernel x * hpl [one, one, one] x)

theorem hasDerivAt_i8Psi4s147W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s147W (i8Psi4s147dW x) x := by
  unfold i8Psi4s147W i8Psi4s147dW
  exact (((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (8)))

/-- The piece `Ψ₄⁽147⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s147 (x : ℝ) : ℝ :=
  (i8Psi4s147N0 x + x * i8Psi4s147N1 x + x ^ 2 * i8Psi4s147N2 x + x ^ 3 * i8Psi4s147N3 x +
    x ^ 4 * i8Psi4s147N4 x) / x ^ 2 + i8Psi4s147W x

/-- The derivative of `Ψ₄⁽147⁾`. -/
noncomputable def i8Psi4s147D (x : ℝ) : ℝ :=
  ((i8Psi4s147dN0 x + (i8Psi4s147N1 x + x * i8Psi4s147dN1 x) + (2 * x * i8Psi4s147N2 x +
    x ^ 2 * i8Psi4s147dN2 x) + (3 * x ^ 2 * i8Psi4s147N3 x + x ^ 3 * i8Psi4s147dN3 x) +
    (4 * x ^ 3 * i8Psi4s147N4 x + x ^ 4 * i8Psi4s147dN4 x)) * x ^ 2 - (i8Psi4s147N0 x +
    x * i8Psi4s147N1 x + x ^ 2 * i8Psi4s147N2 x + x ^ 3 * i8Psi4s147N3 x +
    x ^ 4 * i8Psi4s147N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s147dW x

theorem hasDerivAt_i8Psi4s147 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s147 (i8Psi4s147D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s147N0 hx).add (X.mul (hasDerivAt_i8Psi4s147N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s147N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s147N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s147N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s147W hx)
  unfold i8Psi4s147
  refine e.congr_deriv ?_
  unfold i8Psi4s147D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 147 of `p₄` in `ξ`: from `t B0 A1 (-λ)^3/3!`, the term with `log^3 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s147 (x : ℝ) : ℝ :=
  -((4 / 3) * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 3 * ((1 + x) / (1 - x) * (x / (1 + x))))

/-- `p₄⁽147⁾` written over words. -/
noncomputable def i8P4w147 (x : ℝ) : ℝ :=
    (8 - 8 * x) * hpl [one, one, one] x

theorem i8P4s147_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s147 x = i8P4w147 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s147 i8P4w147
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [one] [one] hx
  have e1 := hpl_mul_hpl [one] [one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  linear_combination (norm := skip) ((4 / 3 - 4 / 3 * x) * hpl [one] x) * e0 + ((8 / 3 -
    8 / 3 * x)) * e1
  field_simp
  generalize hpl [one, one, one] x = v0 at *
  generalize hpl [one, one] x = v1 at *
  generalize hpl [one] x = v2 at *
  ring

/-- **`(Ψ₄⁽147⁾)'(ξ) ξ' = p₄⁽147⁾`**, in terms of `ξ`. -/
theorem i8Psi4s147D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s147D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s147 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s147_eq_w hx]
  unfold i8Psi4s147D i8Psi4s147N0 i8Psi4s147N1 i8Psi4s147N2 i8Psi4s147N3 i8Psi4s147N4 i8Psi4s147dN0
    i8Psi4s147dN1 i8Psi4s147dN2 i8Psi4s147dN3 i8Psi4s147dN4 i8Psi4s147dW i8P4w147
  simp only [kernel_zero, kernel_one, hpl_nil]
  field_simp
  generalize hpl [zero, one, one, one] x = v0 at *
  generalize hpl [zero, one, one] x = v1 at *
  generalize hpl [one, one, one] x = v2 at *
  generalize hpl [one, one] x = v3 at *
  generalize hpl [one] x = v4 at *
  ring

end QED.ThreeLoopD
