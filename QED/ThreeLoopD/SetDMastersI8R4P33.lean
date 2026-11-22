/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P32

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 119 to 120

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s119`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s119D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s119`, `QED.ThreeLoopD.i8Psi4s119D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽119⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s119k0N0 (x : ℝ) : ℝ :=
    (4) * hpl [negOne, negOne, one, one] x +
    (4) * hpl [negOne, one, negOne, one] x +
    (4) * hpl [negOne, one, one, negOne] x +
    (4) * hpl [one, negOne, negOne, one] x

/-- The derivative of `i8Psi4s119k0N0`. -/
noncomputable def i8Psi4s119k0dN0 (x : ℝ) : ℝ :=
    (4) * (negOne.kernel x * hpl [negOne, one, one] x) +
    (4) * (negOne.kernel x * hpl [one, negOne, one] x) +
    (4) * (negOne.kernel x * hpl [one, one, negOne] x) +
    (4) * (one.kernel x * hpl [negOne, negOne, one] x)

theorem hasDerivAt_i8Psi4s119k0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k0N0 (i8Psi4s119k0dN0 x) x := by
  unfold i8Psi4s119k0N0 i8Psi4s119k0dN0
  exact (((((hasDerivAt_hpl_cons negOne [negOne, one, one] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [one, one, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, one] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽119⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s119k0N1 (x : ℝ) : ℝ :=
    (4) * hpl [negOne, negOne, one] x +
    (4) * hpl [negOne, one, one] x +
    (4) * hpl [one, negOne, one] x +
    (4) * hpl [one, one, negOne] x

/-- The derivative of `i8Psi4s119k0N1`. -/
noncomputable def i8Psi4s119k0dN1 (x : ℝ) : ℝ :=
    (4) * (negOne.kernel x * hpl [negOne, one] x) +
    (4) * (negOne.kernel x * hpl [one, one] x) +
    (4) * (one.kernel x * hpl [negOne, one] x) +
    (4) * (one.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s119k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k0N1 (i8Psi4s119k0dN1 x) x := by
  unfold i8Psi4s119k0N1 i8Psi4s119k0dN1
  exact (((((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽119⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s119k0N2 (x : ℝ) : ℝ :=
    (-3 / 2) * hpl [negOne] x +
    (-11 / 2) * hpl [one] x +
    (-2) * hpl [negOne, one] x +
    (1) * hpl [one, negOne] x +
    (-5) * hpl [one, one] x +
    (2) * hpl [negOne, negOne, one] x +
    (-2) * hpl [negOne, one, one] x +
    (-2) * hpl [one, negOne, one] x +
    (-2) * hpl [one, one, negOne] x

/-- The derivative of `i8Psi4s119k0N2`. -/
noncomputable def i8Psi4s119k0dN2 (x : ℝ) : ℝ :=
    (-3 / 2) * (negOne.kernel x * hpl [] x) +
    (-11 / 2) * (one.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (-5) * (one.kernel x * hpl [one] x) +
    (2) * (negOne.kernel x * hpl [negOne, one] x) +
    (-2) * (negOne.kernel x * hpl [one, one] x) +
    (-2) * (one.kernel x * hpl [negOne, one] x) +
    (-2) * (one.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s119k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k0N2 (i8Psi4s119k0dN2 x) x := by
  unfold i8Psi4s119k0N2 i8Psi4s119k0dN2
  exact ((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽119⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s119k0N3 (x : ℝ) : ℝ :=
    (7) +
    (-1) * hpl [negOne] x +
    (7) * hpl [one] x +
    (-2) * hpl [one, negOne] x +
    (6) * hpl [one, one] x +
    (-4) * hpl [negOne, negOne, one] x +
    (-4) * hpl [negOne, one, one] x +
    (-4) * hpl [one, negOne, one] x +
    (-4) * hpl [one, one, negOne] x

/-- The derivative of `i8Psi4s119k0N3`. -/
noncomputable def i8Psi4s119k0dN3 (x : ℝ) : ℝ :=
    0 +
    (-1) * (negOne.kernel x * hpl [] x) +
    (7) * (one.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [negOne] x) +
    (6) * (one.kernel x * hpl [one] x) +
    (-4) * (negOne.kernel x * hpl [negOne, one] x) +
    (-4) * (negOne.kernel x * hpl [one, one] x) +
    (-4) * (one.kernel x * hpl [negOne, one] x) +
    (-4) * (one.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s119k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k0N3 (i8Psi4s119k0dN3 x) x := by
  unfold i8Psi4s119k0N3 i8Psi4s119k0dN3
  exact (((((((((hasDerivAt_const x (7)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽119⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s119k0N4 (x : ℝ) : ℝ :=
    (-1) +
    (1 / 2) * hpl [negOne] x +
    (-3 / 2) * hpl [one] x +
    (2) * hpl [negOne, one] x +
    (1) * hpl [one, negOne] x +
    (-1) * hpl [one, one] x +
    (-2) * hpl [negOne, negOne, one] x +
    (2) * hpl [negOne, one, one] x +
    (2) * hpl [one, negOne, one] x +
    (2) * hpl [one, one, negOne] x +
    (-4) * hpl [negOne, negOne, one, one] x +
    (-4) * hpl [negOne, one, negOne, one] x +
    (-4) * hpl [negOne, one, one, negOne] x +
    (-4) * hpl [one, negOne, negOne, one] x

/-- The derivative of `i8Psi4s119k0N4`. -/
noncomputable def i8Psi4s119k0dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (negOne.kernel x * hpl [] x) +
    (-3 / 2) * (one.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (-1) * (one.kernel x * hpl [one] x) +
    (-2) * (negOne.kernel x * hpl [negOne, one] x) +
    (2) * (negOne.kernel x * hpl [one, one] x) +
    (2) * (one.kernel x * hpl [negOne, one] x) +
    (2) * (one.kernel x * hpl [one, negOne] x) +
    (-4) * (negOne.kernel x * hpl [negOne, one, one] x) +
    (-4) * (negOne.kernel x * hpl [one, negOne, one] x) +
    (-4) * (negOne.kernel x * hpl [one, one, negOne] x) +
    (-4) * (one.kernel x * hpl [negOne, negOne, one] x)

theorem hasDerivAt_i8Psi4s119k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k0N4 (i8Psi4s119k0dN4 x) x := by
  unfold i8Psi4s119k0N4 i8Psi4s119k0dN4
  exact ((((((((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, one] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽119⁾` with constant coefficients. -/
noncomputable def i8Psi4s119k0W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, one, negOne] x +
    (-4) * hpl [zero, one, one] x +
    (-4) * hpl [zero, negOne, negOne, one] x +
    (4) * hpl [zero, negOne, one, one] x +
    (4) * hpl [zero, one, negOne, one] x +
    (4) * hpl [zero, one, one, negOne] x +
    (16) * hpl [zero, negOne, negOne, one, one] x +
    (16) * hpl [zero, negOne, one, negOne, one] x +
    (16) * hpl [zero, negOne, one, one, negOne] x +
    (16) * hpl [zero, one, negOne, negOne, one] x

/-- The derivative of `i8Psi4s119k0W`. -/
noncomputable def i8Psi4s119k0dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [negOne, one] x) +
    (-4) * (zero.kernel x * hpl [one, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, one] x) +
    (-4) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (4) * (zero.kernel x * hpl [negOne, one, one] x) +
    (4) * (zero.kernel x * hpl [one, negOne, one] x) +
    (4) * (zero.kernel x * hpl [one, one, negOne] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, one, one] x) +
    (16) * (zero.kernel x * hpl [negOne, one, negOne, one] x) +
    (16) * (zero.kernel x * hpl [negOne, one, one, negOne] x) +
    (16) * (zero.kernel x * hpl [one, negOne, negOne, one] x)

theorem hasDerivAt_i8Psi4s119k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k0W (i8Psi4s119k0dW x) x := by
  unfold i8Psi4s119k0W i8Psi4s119k0dW
  exact ((((((((((((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne, one] hx).const_mul (16)))

/-- Chunk 0 of the piece `Ψ₄⁽119⁾`. -/
noncomputable def i8Psi4s119k0 (x : ℝ) : ℝ :=
  (i8Psi4s119k0N0 x + x * i8Psi4s119k0N1 x + x ^ 2 * i8Psi4s119k0N2 x + x ^ 3 * i8Psi4s119k0N3 x +
    x ^ 4 * i8Psi4s119k0N4 x) / x ^ 2 + i8Psi4s119k0W x

/-- The derivative of `i8Psi4s119k0`. -/
noncomputable def i8Psi4s119k0D (x : ℝ) : ℝ :=
  ((i8Psi4s119k0dN0 x + (i8Psi4s119k0N1 x + x * i8Psi4s119k0dN1 x) + (2 * x * i8Psi4s119k0N2 x +
    x ^ 2 * i8Psi4s119k0dN2 x) + (3 * x ^ 2 * i8Psi4s119k0N3 x + x ^ 3 * i8Psi4s119k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s119k0N4 x + x ^ 4 * i8Psi4s119k0dN4 x)) * x ^ 2 - (i8Psi4s119k0N0 x +
    x * i8Psi4s119k0N1 x + x ^ 2 * i8Psi4s119k0N2 x + x ^ 3 * i8Psi4s119k0N3 x +
    x ^ 4 * i8Psi4s119k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s119k0dW x

theorem hasDerivAt_i8Psi4s119k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k0 (i8Psi4s119k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s119k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s119k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s119k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s119k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s119k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s119k0W hx)
  unfold i8Psi4s119k0
  refine e.congr_deriv ?_
  unfold i8Psi4s119k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽119⁾` over words. -/
noncomputable def i8P4w119k0 (x : ℝ) : ℝ :=
    ((8 - 8 * x ^ 2) / (x)) * hpl [negOne, negOne, one, one] x +
    ((8 - 8 * x ^ 2) / (x)) * hpl [negOne, one, negOne, one] x +
    ((8 - 8 * x ^ 2) / (x)) * hpl [negOne, one, one, negOne] x +
    ((8 - 8 * x ^ 2) / (x)) * hpl [one, negOne, negOne, one] x

theorem i8Psi4s119k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s119k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w119k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s119k0D i8Psi4s119k0N0 i8Psi4s119k0N1 i8Psi4s119k0N2 i8Psi4s119k0N3 i8Psi4s119k0N4
    i8Psi4s119k0dN0 i8Psi4s119k0dN1 i8Psi4s119k0dN2 i8Psi4s119k0dN3 i8Psi4s119k0dN4 i8Psi4s119k0dW
    i8P4w119k0
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, negOne, one, one] x = v0 at *
  generalize hpl [zero, negOne, one, negOne, one] x = v1 at *
  generalize hpl [zero, negOne, one, one, negOne] x = v2 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v3 at *
  generalize hpl [negOne, negOne, one, one] x = v4 at *
  generalize hpl [negOne, one, negOne, one] x = v5 at *
  generalize hpl [negOne, one, one, negOne] x = v6 at *
  generalize hpl [zero, negOne, negOne, one] x = v7 at *
  generalize hpl [zero, negOne, one, one] x = v8 at *
  generalize hpl [zero, one, negOne, one] x = v9 at *
  generalize hpl [zero, one, one, negOne] x = v10 at *
  generalize hpl [one, negOne, negOne, one] x = v11 at *
  generalize hpl [negOne, negOne, one] x = v12 at *
  generalize hpl [negOne, one, one] x = v13 at *
  generalize hpl [zero, negOne, one] x = v14 at *
  generalize hpl [zero, one, negOne] x = v15 at *
  generalize hpl [zero, one, one] x = v16 at *
  generalize hpl [one, negOne, one] x = v17 at *
  generalize hpl [one, one, negOne] x = v18 at *
  generalize hpl [negOne, one] x = v19 at *
  generalize hpl [one, negOne] x = v20 at *
  generalize hpl [one, one] x = v21 at *
  generalize hpl [negOne] x = v22 at *
  generalize hpl [one] x = v23 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽119⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s119k1N0 (x : ℝ) : ℝ :=
    (4) * hpl [one, negOne, one, negOne] x +
    (4) * hpl [one, one, negOne, negOne] x

/-- The derivative of `i8Psi4s119k1N0`. -/
noncomputable def i8Psi4s119k1dN0 (x : ℝ) : ℝ :=
    (4) * (one.kernel x * hpl [negOne, one, negOne] x) +
    (4) * (one.kernel x * hpl [one, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s119k1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k1N0 (i8Psi4s119k1dN0 x) x := by
  unfold i8Psi4s119k1N0 i8Psi4s119k1dN0
  exact (((hasDerivAt_hpl_cons one [negOne, one, negOne] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons one [one, negOne, negOne] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽119⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s119k1N1 (x : ℝ) : ℝ :=
    (4) * hpl [negOne, one, negOne] x +
    (4) * hpl [one, negOne, negOne] x

/-- The derivative of `i8Psi4s119k1N1`. -/
noncomputable def i8Psi4s119k1dN1 (x : ℝ) : ℝ :=
    (4) * (negOne.kernel x * hpl [one, negOne] x) +
    (4) * (one.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s119k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k1N1 (i8Psi4s119k1dN1 x) x := by
  unfold i8Psi4s119k1N1 i8Psi4s119k1dN1
  exact (((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽119⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s119k1N2 (x : ℝ) : ℝ :=
    (7) * hpl [negOne] x +
    (-5) * hpl [negOne, negOne] x +
    (-3) * hpl [one, negOne] x +
    (2) * hpl [negOne, one, negOne] x +
    (2) * hpl [one, negOne, negOne] x

/-- The derivative of `i8Psi4s119k1N2`. -/
noncomputable def i8Psi4s119k1dN2 (x : ℝ) : ℝ :=
    (7) * (negOne.kernel x * hpl [] x) +
    (-5) * (negOne.kernel x * hpl [negOne] x) +
    (-3) * (one.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [one, negOne] x) +
    (2) * (one.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s119k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k1N2 (i8Psi4s119k1dN2 x) x := by
  unfold i8Psi4s119k1N2 i8Psi4s119k1dN2
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (7)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽119⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s119k1N3 (x : ℝ) : ℝ :=
    (-7) +
    (8) * hpl [negOne] x +
    (-6) * hpl [negOne, negOne] x +
    (2) * hpl [one, negOne] x +
    (-4) * hpl [negOne, one, negOne] x +
    (-4) * hpl [one, negOne, negOne] x

/-- The derivative of `i8Psi4s119k1N3`. -/
noncomputable def i8Psi4s119k1dN3 (x : ℝ) : ℝ :=
    0 +
    (8) * (negOne.kernel x * hpl [] x) +
    (-6) * (negOne.kernel x * hpl [negOne] x) +
    (2) * (one.kernel x * hpl [negOne] x) +
    (-4) * (negOne.kernel x * hpl [one, negOne] x) +
    (-4) * (one.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s119k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k1N3 (i8Psi4s119k1dN3 x) x := by
  unfold i8Psi4s119k1N3 i8Psi4s119k1dN3
  exact ((((((hasDerivAt_const x (-7)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽119⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s119k1N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (1) * hpl [negOne] x +
    (-1) * hpl [negOne, negOne] x +
    (1) * hpl [one, negOne] x +
    (-2) * hpl [negOne, one, negOne] x +
    (-2) * hpl [one, negOne, negOne] x +
    (-4) * hpl [one, negOne, one, negOne] x +
    (-4) * hpl [one, one, negOne, negOne] x

/-- The derivative of `i8Psi4s119k1N4`. -/
noncomputable def i8Psi4s119k1dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (negOne.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [negOne] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, negOne] x) +
    (-4) * (one.kernel x * hpl [negOne, one, negOne] x) +
    (-4) * (one.kernel x * hpl [one, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s119k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k1N4 (i8Psi4s119k1dN4 x) x := by
  unfold i8Psi4s119k1N4 i8Psi4s119k1dN4
  exact ((((((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, negOne, negOne] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽119⁾` with constant coefficients. -/
noncomputable def i8Psi4s119k1W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, negOne, negOne] x +
    (-4) * hpl [zero, one, negOne] x +
    (-4) * hpl [zero, negOne, one, negOne] x +
    (-4) * hpl [zero, one, negOne, negOne] x +
    (16) * hpl [zero, one, negOne, one, negOne] x +
    (16) * hpl [zero, one, one, negOne, negOne] x

/-- The derivative of `i8Psi4s119k1W`. -/
noncomputable def i8Psi4s119k1dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, negOne] x) +
    (-4) * (zero.kernel x * hpl [negOne, one, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, negOne, negOne] x) +
    (16) * (zero.kernel x * hpl [one, negOne, one, negOne] x) +
    (16) * (zero.kernel x * hpl [one, one, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s119k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k1W (i8Psi4s119k1dW x) x := by
  unfold i8Psi4s119k1W i8Psi4s119k1dW
  exact (((((((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne, negOne] hx).const_mul (16)))

/-- Chunk 1 of the piece `Ψ₄⁽119⁾`. -/
noncomputable def i8Psi4s119k1 (x : ℝ) : ℝ :=
  (i8Psi4s119k1N0 x + x * i8Psi4s119k1N1 x + x ^ 2 * i8Psi4s119k1N2 x + x ^ 3 * i8Psi4s119k1N3 x +
    x ^ 4 * i8Psi4s119k1N4 x) / x ^ 2 + i8Psi4s119k1W x

/-- The derivative of `i8Psi4s119k1`. -/
noncomputable def i8Psi4s119k1D (x : ℝ) : ℝ :=
  ((i8Psi4s119k1dN0 x + (i8Psi4s119k1N1 x + x * i8Psi4s119k1dN1 x) + (2 * x * i8Psi4s119k1N2 x +
    x ^ 2 * i8Psi4s119k1dN2 x) + (3 * x ^ 2 * i8Psi4s119k1N3 x + x ^ 3 * i8Psi4s119k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s119k1N4 x + x ^ 4 * i8Psi4s119k1dN4 x)) * x ^ 2 - (i8Psi4s119k1N0 x +
    x * i8Psi4s119k1N1 x + x ^ 2 * i8Psi4s119k1N2 x + x ^ 3 * i8Psi4s119k1N3 x +
    x ^ 4 * i8Psi4s119k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s119k1dW x

theorem hasDerivAt_i8Psi4s119k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119k1 (i8Psi4s119k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s119k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s119k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s119k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s119k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s119k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s119k1W hx)
  unfold i8Psi4s119k1
  refine e.congr_deriv ?_
  unfold i8Psi4s119k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽119⁾` over words. -/
noncomputable def i8P4w119k1 (x : ℝ) : ℝ :=
    ((8 - 8 * x ^ 2) / (x)) * hpl [one, negOne, one, negOne] x +
    ((8 - 8 * x ^ 2) / (x)) * hpl [one, one, negOne, negOne] x

theorem i8Psi4s119k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s119k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w119k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s119k1D i8Psi4s119k1N0 i8Psi4s119k1N1 i8Psi4s119k1N2 i8Psi4s119k1N3 i8Psi4s119k1N4
    i8Psi4s119k1dN0 i8Psi4s119k1dN1 i8Psi4s119k1dN2 i8Psi4s119k1dN3 i8Psi4s119k1dN4 i8Psi4s119k1dW
    i8P4w119k1
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, one, negOne, one, negOne] x = v0 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v1 at *
  generalize hpl [zero, negOne, one, negOne] x = v2 at *
  generalize hpl [zero, one, negOne, negOne] x = v3 at *
  generalize hpl [one, negOne, one, negOne] x = v4 at *
  generalize hpl [one, one, negOne, negOne] x = v5 at *
  generalize hpl [negOne, one, negOne] x = v6 at *
  generalize hpl [zero, negOne, negOne] x = v7 at *
  generalize hpl [zero, one, negOne] x = v8 at *
  generalize hpl [one, negOne, negOne] x = v9 at *
  generalize hpl [negOne, negOne] x = v10 at *
  generalize hpl [one, negOne] x = v11 at *
  generalize hpl [negOne] x = v12 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽119⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s119 (x : ℝ) : ℝ :=
  i8Psi4s119k0 x + i8Psi4s119k1 x

/-- The derivative of `Ψ₄⁽119⁾`. -/
noncomputable def i8Psi4s119D (x : ℝ) : ℝ :=
  i8Psi4s119k0D x + i8Psi4s119k1D x

theorem hasDerivAt_i8Psi4s119 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s119 (i8Psi4s119D x) x := by
  unfold i8Psi4s119 i8Psi4s119D
  exact ((hasDerivAt_i8Psi4s119k0 hx).add (hasDerivAt_i8Psi4s119k1 hx))

/-- The sub-piece 119 of `p₄` in `ξ`: from `t B0 A2 (-λ)^2/2!`, the term with `log^2 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s119 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 2 * ((1 + x) / (1 - x) * (2 * hpl [negOne, negOne] x))

/-- `p₄⁽119⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w119 (x : ℝ) : ℝ :=
  i8P4w119k0 x + i8P4w119k1 x

theorem i8P4s119_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s119 x = i8P4w119 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s119 i8P4w119 i8P4w119k0 i8P4w119k1
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [one] [one] hx
  have e1 := hpl_mul_hpl [negOne, negOne] [one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  linear_combination (norm := skip) (((4 - 4 * x ^ 2) / (x)) * hpl [negOne, negOne] x) * e0 +
    (((8 - 8 * x ^ 2) / (x))) * e1
  field_simp
  generalize hpl [negOne, negOne, one, one] x = v0 at *
  generalize hpl [negOne, one, negOne, one] x = v1 at *
  generalize hpl [negOne, one, one, negOne] x = v2 at *
  generalize hpl [one, negOne, negOne, one] x = v3 at *
  generalize hpl [one, negOne, one, negOne] x = v4 at *
  generalize hpl [one, one, negOne, negOne] x = v5 at *
  generalize hpl [negOne, negOne] x = v6 at *
  generalize hpl [one, one] x = v7 at *
  generalize hpl [one] x = v8 at *
  ring

/-- **`(Ψ₄⁽119⁾)'(ξ) ξ' = p₄⁽119⁾`**, in terms of `ξ`. -/
theorem i8Psi4s119D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s119D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s119 x := by
  rw [i8P4s119_eq_w hx]
  unfold i8Psi4s119D i8P4w119
  rw [← i8Psi4s119k0D_mul hx, ← i8Psi4s119k1D_mul hx]
  ring

/-- The part of `ξ² Ψ₄⁽120⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s120k0N0 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne, one, one] x +
    (-1) * hpl [one, negOne, one] x +
    (-1) * hpl [one, one, negOne] x +
    (-2) * hpl [zero, negOne, one, one] x +
    (-2) * hpl [zero, one, negOne, one] x +
    (-2) * hpl [zero, one, one, negOne] x +
    (-2) * hpl [one, zero, negOne, one] x

/-- The derivative of `i8Psi4s120k0N0`. -/
noncomputable def i8Psi4s120k0dN0 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [one, one] x) +
    (-1) * (one.kernel x * hpl [negOne, one] x) +
    (-1) * (one.kernel x * hpl [one, negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, one, one] x) +
    (-2) * (zero.kernel x * hpl [one, negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, one, negOne] x) +
    (-2) * (one.kernel x * hpl [zero, negOne, one] x)

theorem hasDerivAt_i8Psi4s120k0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k0N0 (i8Psi4s120k0dN0 x) x := by
  unfold i8Psi4s120k0N0 i8Psi4s120k0dN0
  exact ((((((((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, one] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽120⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s120k0N1 (x : ℝ) : ℝ :=
    (-3) * hpl [negOne, one] x +
    (-1) * hpl [one, negOne] x +
    (-1) * hpl [one, one] x +
    (-2) * hpl [zero, negOne, one] x

/-- The derivative of `i8Psi4s120k0N1`. -/
noncomputable def i8Psi4s120k0dN1 (x : ℝ) : ℝ :=
    (-3) * (negOne.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [negOne] x) +
    (-1) * (one.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x)

theorem hasDerivAt_i8Psi4s120k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k0N1 (i8Psi4s120k0dN1 x) x := by
  unfold i8Psi4s120k0N1 i8Psi4s120k0dN1
  exact (((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-3)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽120⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s120k0N2 (x : ℝ) : ℝ :=
    (-5 / 4) * hpl [negOne] x +
    (-9 / 4) * hpl [one] x +
    (-5) * hpl [negOne, one] x +
    (5 / 2) * hpl [one, negOne] x +
    (3 / 2) * hpl [one, one] x +
    (2) * hpl [negOne, one, one] x +
    (1) * hpl [zero, negOne, one] x +
    (2) * hpl [one, negOne, one] x +
    (2) * hpl [one, one, negOne] x

/-- The derivative of `i8Psi4s120k0N2`. -/
noncomputable def i8Psi4s120k0dN2 (x : ℝ) : ℝ :=
    (-5 / 4) * (negOne.kernel x * hpl [] x) +
    (-9 / 4) * (one.kernel x * hpl [] x) +
    (-5) * (negOne.kernel x * hpl [one] x) +
    (5 / 2) * (one.kernel x * hpl [negOne] x) +
    (3 / 2) * (one.kernel x * hpl [one] x) +
    (2) * (negOne.kernel x * hpl [one, one] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (2) * (one.kernel x * hpl [negOne, one] x) +
    (2) * (one.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s120k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k0N2 (i8Psi4s120k0dN2 x) x := by
  unfold i8Psi4s120k0N2 i8Psi4s120k0dN2
  exact ((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-5 / 4)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-9 / 4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽120⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s120k0N3 (x : ℝ) : ℝ :=
    (7 / 2) +
    (-3 / 2) * hpl [negOne] x +
    (3 / 2) * hpl [one] x +
    (-3) * hpl [negOne, one] x +
    (-1) * hpl [one, negOne] x +
    (-1) * hpl [one, one] x +
    (2) * hpl [zero, negOne, one] x

/-- The derivative of `i8Psi4s120k0N3`. -/
noncomputable def i8Psi4s120k0dN3 (x : ℝ) : ℝ :=
    0 +
    (-3 / 2) * (negOne.kernel x * hpl [] x) +
    (3 / 2) * (one.kernel x * hpl [] x) +
    (-3) * (negOne.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [negOne] x) +
    (-1) * (one.kernel x * hpl [one] x) +
    (2) * (zero.kernel x * hpl [negOne, one] x)

theorem hasDerivAt_i8Psi4s120k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k0N3 (i8Psi4s120k0dN3 x) x := by
  unfold i8Psi4s120k0N3 i8Psi4s120k0dN3
  exact (((((((hasDerivAt_const x (7 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽120⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s120k0N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 4) * hpl [negOne] x +
    (3 / 4) * hpl [one] x +
    (-1) * hpl [negOne, one] x +
    (-1 / 2) * hpl [one, negOne] x +
    (1 / 2) * hpl [one, one] x +
    (-1) * hpl [negOne, one, one] x +
    (1) * hpl [zero, negOne, one] x +
    (-1) * hpl [one, negOne, one] x +
    (-1) * hpl [one, one, negOne] x +
    (2) * hpl [zero, negOne, one, one] x +
    (2) * hpl [zero, one, negOne, one] x +
    (2) * hpl [zero, one, one, negOne] x +
    (2) * hpl [one, zero, negOne, one] x

/-- The derivative of `i8Psi4s120k0N4`. -/
noncomputable def i8Psi4s120k0dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 4) * (negOne.kernel x * hpl [] x) +
    (3 / 4) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (1 / 2) * (one.kernel x * hpl [one] x) +
    (-1) * (negOne.kernel x * hpl [one, one] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (-1) * (one.kernel x * hpl [negOne, one] x) +
    (-1) * (one.kernel x * hpl [one, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, one, one] x) +
    (2) * (zero.kernel x * hpl [one, negOne, one] x) +
    (2) * (zero.kernel x * hpl [one, one, negOne] x) +
    (2) * (one.kernel x * hpl [zero, negOne, one] x)

theorem hasDerivAt_i8Psi4s120k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k0N4 (i8Psi4s120k0dN4 x) x := by
  unfold i8Psi4s120k0N4 i8Psi4s120k0dN4
  exact ((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (3 / 4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, one] hx).const_mul (2)))

/-- The part of `Ψ₄⁽120⁾` with constant coefficients. -/
noncomputable def i8Psi4s120k0W (x : ℝ) : ℝ :=
    (1) * hpl [zero, negOne] x +
    (4) * hpl [zero, one] x +
    (1) * hpl [zero, one, negOne] x +
    (-1) * hpl [zero, one, one] x +
    (2) * hpl [zero, zero, negOne, one] x +
    (-8) * hpl [zero, zero, negOne, one, one] x +
    (-8) * hpl [zero, zero, one, negOne, one] x +
    (-8) * hpl [zero, zero, one, one, negOne] x +
    (-8) * hpl [zero, one, zero, negOne, one] x

/-- The derivative of `i8Psi4s120k0W`. -/
noncomputable def i8Psi4s120k0dW (x : ℝ) : ℝ :=
    (1) * (zero.kernel x * hpl [negOne] x) +
    (4) * (zero.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (-1) * (zero.kernel x * hpl [one, one] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, one, one] x) +
    (-8) * (zero.kernel x * hpl [zero, one, negOne, one] x) +
    (-8) * (zero.kernel x * hpl [zero, one, one, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, zero, negOne, one] x)

theorem hasDerivAt_i8Psi4s120k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k0W (i8Psi4s120k0dW x) x := by
  unfold i8Psi4s120k0W i8Psi4s120k0dW
  exact ((((((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne, one] hx).const_mul (-8)))

/-- Chunk 0 of the piece `Ψ₄⁽120⁾`. -/
noncomputable def i8Psi4s120k0 (x : ℝ) : ℝ :=
  (i8Psi4s120k0N0 x + x * i8Psi4s120k0N1 x + x ^ 2 * i8Psi4s120k0N2 x + x ^ 3 * i8Psi4s120k0N3 x +
    x ^ 4 * i8Psi4s120k0N4 x) / x ^ 2 + i8Psi4s120k0W x

/-- The derivative of `i8Psi4s120k0`. -/
noncomputable def i8Psi4s120k0D (x : ℝ) : ℝ :=
  ((i8Psi4s120k0dN0 x + (i8Psi4s120k0N1 x + x * i8Psi4s120k0dN1 x) + (2 * x * i8Psi4s120k0N2 x +
    x ^ 2 * i8Psi4s120k0dN2 x) + (3 * x ^ 2 * i8Psi4s120k0N3 x + x ^ 3 * i8Psi4s120k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s120k0N4 x + x ^ 4 * i8Psi4s120k0dN4 x)) * x ^ 2 - (i8Psi4s120k0N0 x +
    x * i8Psi4s120k0N1 x + x ^ 2 * i8Psi4s120k0N2 x + x ^ 3 * i8Psi4s120k0N3 x +
    x ^ 4 * i8Psi4s120k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s120k0dW x

theorem hasDerivAt_i8Psi4s120k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k0 (i8Psi4s120k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s120k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s120k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s120k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s120k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s120k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s120k0W hx)
  unfold i8Psi4s120k0
  refine e.congr_deriv ?_
  unfold i8Psi4s120k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽120⁾` over words. -/
noncomputable def i8P4w120k0 (x : ℝ) : ℝ :=
    ((-4 + 4 * x ^ 2) / (x)) * hpl [zero, negOne, one, one] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [zero, one, negOne, one] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [zero, one, one, negOne] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [one, zero, negOne, one] x

theorem i8Psi4s120k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s120k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w120k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s120k0D i8Psi4s120k0N0 i8Psi4s120k0N1 i8Psi4s120k0N2 i8Psi4s120k0N3 i8Psi4s120k0N4
    i8Psi4s120k0dN0 i8Psi4s120k0dN1 i8Psi4s120k0dN2 i8Psi4s120k0dN3 i8Psi4s120k0dN4 i8Psi4s120k0dW
    i8P4w120k0
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, zero, negOne, one, one] x = v0 at *
  generalize hpl [zero, zero, one, negOne, one] x = v1 at *
  generalize hpl [zero, zero, one, one, negOne] x = v2 at *
  generalize hpl [zero, one, zero, negOne, one] x = v3 at *
  generalize hpl [zero, negOne, one, one] x = v4 at *
  generalize hpl [zero, zero, negOne, one] x = v5 at *
  generalize hpl [zero, one, negOne, one] x = v6 at *
  generalize hpl [zero, one, one, negOne] x = v7 at *
  generalize hpl [one, zero, negOne, one] x = v8 at *
  generalize hpl [negOne, one, one] x = v9 at *
  generalize hpl [zero, negOne, one] x = v10 at *
  generalize hpl [zero, one, negOne] x = v11 at *
  generalize hpl [zero, one, one] x = v12 at *
  generalize hpl [one, negOne, one] x = v13 at *
  generalize hpl [one, one, negOne] x = v14 at *
  generalize hpl [negOne, one] x = v15 at *
  generalize hpl [zero, negOne] x = v16 at *
  generalize hpl [zero, one] x = v17 at *
  generalize hpl [one, negOne] x = v18 at *
  generalize hpl [one, one] x = v19 at *
  generalize hpl [negOne] x = v20 at *
  generalize hpl [one] x = v21 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽120⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s120k1N0 (x : ℝ) : ℝ :=
    (-2) * hpl [one, zero, one, negOne] x +
    (-2) * hpl [one, one, zero, negOne] x

/-- The derivative of `i8Psi4s120k1N0`. -/
noncomputable def i8Psi4s120k1dN0 (x : ℝ) : ℝ :=
    (-2) * (one.kernel x * hpl [zero, one, negOne] x) +
    (-2) * (one.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s120k1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k1N0 (i8Psi4s120k1dN0 x) x := by
  unfold i8Psi4s120k1N0 i8Psi4s120k1dN0
  exact (((hasDerivAt_hpl_cons one [zero, one, negOne] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [one, zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽120⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s120k1N1 (x : ℝ) : ℝ :=
    (-2) * hpl [one, negOne] x +
    (-2) * hpl [zero, one, negOne] x +
    (-2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s120k1N1`. -/
noncomputable def i8Psi4s120k1dN1 (x : ℝ) : ℝ :=
    (-2) * (one.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s120k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k1N1 (i8Psi4s120k1dN1 x) x := by
  unfold i8Psi4s120k1N1 i8Psi4s120k1dN1
  exact ((((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽120⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s120k1N2 (x : ℝ) : ℝ :=
    (-5) * hpl [negOne] x +
    (2) * hpl [zero, negOne] x +
    (9 / 2) * hpl [one, negOne] x +
    (-1) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s120k1N2`. -/
noncomputable def i8Psi4s120k1dN2 (x : ℝ) : ℝ :=
    (-5) * (negOne.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [negOne] x) +
    (9 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s120k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k1N2 (i8Psi4s120k1dN2 x) x := by
  unfold i8Psi4s120k1N2 i8Psi4s120k1dN2
  exact (((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-5)).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (9 / 2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽120⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s120k1N3 (x : ℝ) : ℝ :=
    (5) +
    (-11 / 2) * hpl [negOne] x +
    (3) * hpl [zero, negOne] x +
    (-2) * hpl [one, negOne] x +
    (2) * hpl [zero, one, negOne] x +
    (2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s120k1N3`. -/
noncomputable def i8Psi4s120k1dN3 (x : ℝ) : ℝ :=
    0 +
    (-11 / 2) * (negOne.kernel x * hpl [] x) +
    (3) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (one.kernel x * hpl [negOne] x) +
    (2) * (zero.kernel x * hpl [one, negOne] x) +
    (2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s120k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k1N3 (i8Psi4s120k1dN3 x) x := by
  unfold i8Psi4s120k1N3 i8Psi4s120k1dN3
  exact ((((((hasDerivAt_const x (5)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽120⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s120k1N4 (x : ℝ) : ℝ :=
    (1 / 4) +
    (-1 / 2) * hpl [negOne] x +
    (1 / 2) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [one, negOne] x +
    (1) * hpl [zero, one, negOne] x +
    (1) * hpl [one, zero, negOne] x +
    (2) * hpl [one, zero, one, negOne] x +
    (2) * hpl [one, one, zero, negOne] x

/-- The derivative of `i8Psi4s120k1N4`. -/
noncomputable def i8Psi4s120k1dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (1) * (one.kernel x * hpl [zero, negOne] x) +
    (2) * (one.kernel x * hpl [zero, one, negOne] x) +
    (2) * (one.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s120k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k1N4 (i8Psi4s120k1dN4 x) x := by
  unfold i8Psi4s120k1N4 i8Psi4s120k1dN4
  exact ((((((((hasDerivAt_const x (1 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, zero, negOne] hx).const_mul (2)))

/-- The part of `Ψ₄⁽120⁾` with constant coefficients. -/
noncomputable def i8Psi4s120k1W (x : ℝ) : ℝ :=
    (2) * hpl [zero, zero, negOne] x +
    (2) * hpl [zero, zero, one, negOne] x +
    (2) * hpl [zero, one, zero, negOne] x +
    (-8) * hpl [zero, one, zero, one, negOne] x +
    (-8) * hpl [zero, one, one, zero, negOne] x

/-- The derivative of `i8Psi4s120k1W`. -/
noncomputable def i8Psi4s120k1dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [zero, negOne] x) +
    (2) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (2) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, zero, one, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s120k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k1W (i8Psi4s120k1dW x) x := by
  unfold i8Psi4s120k1W i8Psi4s120k1dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero, negOne] hx).const_mul (-8)))

/-- Chunk 1 of the piece `Ψ₄⁽120⁾`. -/
noncomputable def i8Psi4s120k1 (x : ℝ) : ℝ :=
  (i8Psi4s120k1N0 x + x * i8Psi4s120k1N1 x + x ^ 2 * i8Psi4s120k1N2 x + x ^ 3 * i8Psi4s120k1N3 x +
    x ^ 4 * i8Psi4s120k1N4 x) / x ^ 2 + i8Psi4s120k1W x

/-- The derivative of `i8Psi4s120k1`. -/
noncomputable def i8Psi4s120k1D (x : ℝ) : ℝ :=
  ((i8Psi4s120k1dN0 x + (i8Psi4s120k1N1 x + x * i8Psi4s120k1dN1 x) + (2 * x * i8Psi4s120k1N2 x +
    x ^ 2 * i8Psi4s120k1dN2 x) + (3 * x ^ 2 * i8Psi4s120k1N3 x + x ^ 3 * i8Psi4s120k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s120k1N4 x + x ^ 4 * i8Psi4s120k1dN4 x)) * x ^ 2 - (i8Psi4s120k1N0 x +
    x * i8Psi4s120k1N1 x + x ^ 2 * i8Psi4s120k1N2 x + x ^ 3 * i8Psi4s120k1N3 x +
    x ^ 4 * i8Psi4s120k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s120k1dW x

theorem hasDerivAt_i8Psi4s120k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120k1 (i8Psi4s120k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s120k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s120k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s120k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s120k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s120k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s120k1W hx)
  unfold i8Psi4s120k1
  refine e.congr_deriv ?_
  unfold i8Psi4s120k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽120⁾` over words. -/
noncomputable def i8P4w120k1 (x : ℝ) : ℝ :=
    ((-4 + 4 * x ^ 2) / (x)) * hpl [one, zero, one, negOne] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [one, one, zero, negOne] x

theorem i8Psi4s120k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s120k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w120k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s120k1D i8Psi4s120k1N0 i8Psi4s120k1N1 i8Psi4s120k1N2 i8Psi4s120k1N3 i8Psi4s120k1N4
    i8Psi4s120k1dN0 i8Psi4s120k1dN1 i8Psi4s120k1dN2 i8Psi4s120k1dN3 i8Psi4s120k1dN4 i8Psi4s120k1dW
    i8P4w120k1
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, one, zero, one, negOne] x = v0 at *
  generalize hpl [zero, one, one, zero, negOne] x = v1 at *
  generalize hpl [zero, zero, one, negOne] x = v2 at *
  generalize hpl [zero, one, zero, negOne] x = v3 at *
  generalize hpl [one, zero, one, negOne] x = v4 at *
  generalize hpl [one, one, zero, negOne] x = v5 at *
  generalize hpl [zero, zero, negOne] x = v6 at *
  generalize hpl [zero, one, negOne] x = v7 at *
  generalize hpl [one, zero, negOne] x = v8 at *
  generalize hpl [zero, negOne] x = v9 at *
  generalize hpl [one, negOne] x = v10 at *
  generalize hpl [negOne] x = v11 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽120⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s120 (x : ℝ) : ℝ :=
  i8Psi4s120k0 x + i8Psi4s120k1 x

/-- The derivative of `Ψ₄⁽120⁾`. -/
noncomputable def i8Psi4s120D (x : ℝ) : ℝ :=
  i8Psi4s120k0D x + i8Psi4s120k1D x

theorem hasDerivAt_i8Psi4s120 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s120 (i8Psi4s120D x) x := by
  unfold i8Psi4s120 i8Psi4s120D
  exact ((hasDerivAt_i8Psi4s120k0 hx).add (hasDerivAt_i8Psi4s120k1 hx))

/-- The sub-piece 120 of `p₄` in `ξ`: from `t B0 A2 (-λ)^2/2!`, the term with `log^2 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s120 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 2 * ((1 + x) / (1 - x) * (-hpl [zero, negOne] x))

/-- `p₄⁽120⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w120 (x : ℝ) : ℝ :=
  i8P4w120k0 x + i8P4w120k1 x

theorem i8P4s120_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s120 x = i8P4w120 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s120 i8P4w120 i8P4w120k0 i8P4w120k1
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [one] [one] hx
  have e1 := hpl_mul_hpl [zero, negOne] [one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  linear_combination (norm := skip) (((-2 + 2 * x ^ 2) / (x)) * hpl [zero, negOne] x) * e0 +
    (((-4 + 4 * x ^ 2) / (x))) * e1
  field_simp
  generalize hpl [zero, negOne, one, one] x = v0 at *
  generalize hpl [zero, one, negOne, one] x = v1 at *
  generalize hpl [zero, one, one, negOne] x = v2 at *
  generalize hpl [one, zero, negOne, one] x = v3 at *
  generalize hpl [one, zero, one, negOne] x = v4 at *
  generalize hpl [one, one, zero, negOne] x = v5 at *
  generalize hpl [zero, negOne] x = v6 at *
  generalize hpl [one, one] x = v7 at *
  generalize hpl [one] x = v8 at *
  ring

/-- **`(Ψ₄⁽120⁾)'(ξ) ξ' = p₄⁽120⁾`**, in terms of `ξ`. -/
theorem i8Psi4s120D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s120D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s120 x := by
  rw [i8P4s120_eq_w hx]
  unfold i8Psi4s120D i8P4w120
  rw [← i8Psi4s120k0D_mul hx, ← i8Psi4s120k1D_mul hx]
  ring

end QED.ThreeLoopD
