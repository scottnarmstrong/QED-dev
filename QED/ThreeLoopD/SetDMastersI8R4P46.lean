/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P45

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 148 to 150

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s148`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s148D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s148`, `QED.ThreeLoopD.i8Psi4s148D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽148⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s148k0N0 (x : ℝ) : ℝ :=
    (-4) * hpl [negOne, one, one, one] x +
    (-4) * hpl [one, negOne, one, one] x +
    (-4) * hpl [one, one, negOne, one] x +
    (-4) * hpl [one, one, one, negOne] x

/-- The derivative of `i8Psi4s148k0N0`. -/
noncomputable def i8Psi4s148k0dN0 (x : ℝ) : ℝ :=
    (-4) * (negOne.kernel x * hpl [one, one, one] x) +
    (-4) * (one.kernel x * hpl [negOne, one, one] x) +
    (-4) * (one.kernel x * hpl [one, negOne, one] x) +
    (-4) * (one.kernel x * hpl [one, one, negOne] x)

theorem hasDerivAt_i8Psi4s148k0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s148k0N0 (i8Psi4s148k0dN0 x) x := by
  unfold i8Psi4s148k0N0 i8Psi4s148k0dN0
  exact (((((hasDerivAt_hpl_cons negOne [one, one, one] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons one [negOne, one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, one, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽148⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s148k0N1 (x : ℝ) : ℝ :=
    (-4) * hpl [negOne, one, one] x +
    (-4) * hpl [one, negOne, one] x +
    (-4) * hpl [one, one, negOne] x +
    (-4) * hpl [one, one, one] x

/-- The derivative of `i8Psi4s148k0N1`. -/
noncomputable def i8Psi4s148k0dN1 (x : ℝ) : ℝ :=
    (-4) * (negOne.kernel x * hpl [one, one] x) +
    (-4) * (one.kernel x * hpl [negOne, one] x) +
    (-4) * (one.kernel x * hpl [one, negOne] x) +
    (-4) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi4s148k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s148k0N1 (i8Psi4s148k0dN1 x) x := by
  unfold i8Psi4s148k0N1 i8Psi4s148k0dN1
  exact (((((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽148⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s148k0N2 (x : ℝ) : ℝ :=
    (13 / 2) * hpl [negOne] x +
    (17 / 2) * hpl [one] x +
    (5) * hpl [negOne, one] x +
    (-7) * hpl [one, negOne] x +
    (2) * hpl [one, one] x +
    (-2) * hpl [negOne, one, one] x +
    (-2) * hpl [one, negOne, one] x +
    (-2) * hpl [one, one, negOne] x +
    (2) * hpl [one, one, one] x

/-- The derivative of `i8Psi4s148k0N2`. -/
noncomputable def i8Psi4s148k0dN2 (x : ℝ) : ℝ :=
    (13 / 2) * (negOne.kernel x * hpl [] x) +
    (17 / 2) * (one.kernel x * hpl [] x) +
    (5) * (negOne.kernel x * hpl [one] x) +
    (-7) * (one.kernel x * hpl [negOne] x) +
    (2) * (one.kernel x * hpl [one] x) +
    (-2) * (negOne.kernel x * hpl [one, one] x) +
    (-2) * (one.kernel x * hpl [negOne, one] x) +
    (-2) * (one.kernel x * hpl [one, negOne] x) +
    (2) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi4s148k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s148k0N2 (i8Psi4s148k0dN2 x) x := by
  unfold i8Psi4s148k0N2 i8Psi4s148k0dN2
  exact ((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (13 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (17 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽148⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s148k0N3 (x : ℝ) : ℝ :=
    (-15) +
    (7) * hpl [negOne] x +
    (-7) * hpl [one] x +
    (6) * hpl [negOne, one] x +
    (6) * hpl [one, negOne] x +
    (4) * hpl [negOne, one, one] x +
    (4) * hpl [one, negOne, one] x +
    (4) * hpl [one, one, negOne] x +
    (4) * hpl [one, one, one] x

/-- The derivative of `i8Psi4s148k0N3`. -/
noncomputable def i8Psi4s148k0dN3 (x : ℝ) : ℝ :=
    0 +
    (7) * (negOne.kernel x * hpl [] x) +
    (-7) * (one.kernel x * hpl [] x) +
    (6) * (negOne.kernel x * hpl [one] x) +
    (6) * (one.kernel x * hpl [negOne] x) +
    (4) * (negOne.kernel x * hpl [one, one] x) +
    (4) * (one.kernel x * hpl [negOne, one] x) +
    (4) * (one.kernel x * hpl [one, negOne] x) +
    (4) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi4s148k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s148k0N3 (i8Psi4s148k0dN3 x) x := by
  unfold i8Psi4s148k0N3 i8Psi4s148k0dN3
  exact (((((((((hasDerivAt_const x (-15)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽148⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s148k0N4 (x : ℝ) : ℝ :=
    (-1) +
    (1 / 2) * hpl [negOne] x +
    (-3 / 2) * hpl [one] x +
    (1) * hpl [negOne, one] x +
    (1) * hpl [one, negOne] x +
    (-2) * hpl [one, one] x +
    (2) * hpl [negOne, one, one] x +
    (2) * hpl [one, negOne, one] x +
    (2) * hpl [one, one, negOne] x +
    (-2) * hpl [one, one, one] x +
    (4) * hpl [negOne, one, one, one] x +
    (4) * hpl [one, negOne, one, one] x +
    (4) * hpl [one, one, negOne, one] x +
    (4) * hpl [one, one, one, negOne] x

/-- The derivative of `i8Psi4s148k0N4`. -/
noncomputable def i8Psi4s148k0dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (negOne.kernel x * hpl [] x) +
    (-3 / 2) * (one.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (-2) * (one.kernel x * hpl [one] x) +
    (2) * (negOne.kernel x * hpl [one, one] x) +
    (2) * (one.kernel x * hpl [negOne, one] x) +
    (2) * (one.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [one, one] x) +
    (4) * (negOne.kernel x * hpl [one, one, one] x) +
    (4) * (one.kernel x * hpl [negOne, one, one] x) +
    (4) * (one.kernel x * hpl [one, negOne, one] x) +
    (4) * (one.kernel x * hpl [one, one, negOne] x)

theorem hasDerivAt_i8Psi4s148k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s148k0N4 (i8Psi4s148k0dN4 x) x := by
  unfold i8Psi4s148k0N4 i8Psi4s148k0dN4
  exact ((((((((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, one, negOne] hx).const_mul (4)))

/-- The part of `Ψ₄⁽148⁾` with constant coefficients. -/
noncomputable def i8Psi4s148k0W (x : ℝ) : ℝ :=
    (4) * hpl [zero, negOne, one] x +
    (4) * hpl [zero, one, negOne] x +
    (8) * hpl [zero, one, one] x +
    (4) * hpl [zero, negOne, one, one] x +
    (4) * hpl [zero, one, negOne, one] x +
    (4) * hpl [zero, one, one, negOne] x +
    (-4) * hpl [zero, one, one, one] x +
    (-16) * hpl [zero, negOne, one, one, one] x +
    (-16) * hpl [zero, one, negOne, one, one] x +
    (-16) * hpl [zero, one, one, negOne, one] x +
    (-16) * hpl [zero, one, one, one, negOne] x

/-- The derivative of `i8Psi4s148k0W`. -/
noncomputable def i8Psi4s148k0dW (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [negOne, one] x) +
    (4) * (zero.kernel x * hpl [one, negOne] x) +
    (8) * (zero.kernel x * hpl [one, one] x) +
    (4) * (zero.kernel x * hpl [negOne, one, one] x) +
    (4) * (zero.kernel x * hpl [one, negOne, one] x) +
    (4) * (zero.kernel x * hpl [one, one, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, one, one] x) +
    (-16) * (zero.kernel x * hpl [negOne, one, one, one] x) +
    (-16) * (zero.kernel x * hpl [one, negOne, one, one] x) +
    (-16) * (zero.kernel x * hpl [one, one, negOne, one] x) +
    (-16) * (zero.kernel x * hpl [one, one, one, negOne] x)

theorem hasDerivAt_i8Psi4s148k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s148k0W (i8Psi4s148k0dW x) x := by
  unfold i8Psi4s148k0W i8Psi4s148k0dW
  exact ((((((((((((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, one, one, negOne] hx).const_mul (-16)))

/-- Chunk 0 of the piece `Ψ₄⁽148⁾`. -/
noncomputable def i8Psi4s148k0 (x : ℝ) : ℝ :=
  (i8Psi4s148k0N0 x + x * i8Psi4s148k0N1 x + x ^ 2 * i8Psi4s148k0N2 x + x ^ 3 * i8Psi4s148k0N3 x +
    x ^ 4 * i8Psi4s148k0N4 x) / x ^ 2 + i8Psi4s148k0W x

/-- The derivative of `i8Psi4s148k0`. -/
noncomputable def i8Psi4s148k0D (x : ℝ) : ℝ :=
  ((i8Psi4s148k0dN0 x + (i8Psi4s148k0N1 x + x * i8Psi4s148k0dN1 x) + (2 * x * i8Psi4s148k0N2 x +
    x ^ 2 * i8Psi4s148k0dN2 x) + (3 * x ^ 2 * i8Psi4s148k0N3 x + x ^ 3 * i8Psi4s148k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s148k0N4 x + x ^ 4 * i8Psi4s148k0dN4 x)) * x ^ 2 - (i8Psi4s148k0N0 x +
    x * i8Psi4s148k0N1 x + x ^ 2 * i8Psi4s148k0N2 x + x ^ 3 * i8Psi4s148k0N3 x +
    x ^ 4 * i8Psi4s148k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s148k0dW x

theorem hasDerivAt_i8Psi4s148k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s148k0 (i8Psi4s148k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s148k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s148k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s148k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s148k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s148k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s148k0W hx)
  unfold i8Psi4s148k0
  refine e.congr_deriv ?_
  unfold i8Psi4s148k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽148⁾` over words. -/
noncomputable def i8P4w148k0 (x : ℝ) : ℝ :=
    ((-8 + 8 * x ^ 2) / (x)) * hpl [negOne, one, one, one] x +
    ((-8 + 8 * x ^ 2) / (x)) * hpl [one, negOne, one, one] x +
    ((-8 + 8 * x ^ 2) / (x)) * hpl [one, one, negOne, one] x +
    ((-8 + 8 * x ^ 2) / (x)) * hpl [one, one, one, negOne] x

theorem i8Psi4s148k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s148k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w148k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s148k0D i8Psi4s148k0N0 i8Psi4s148k0N1 i8Psi4s148k0N2 i8Psi4s148k0N3 i8Psi4s148k0N4
    i8Psi4s148k0dN0 i8Psi4s148k0dN1 i8Psi4s148k0dN2 i8Psi4s148k0dN3 i8Psi4s148k0dN4 i8Psi4s148k0dW
    i8P4w148k0
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, one, one, one] x = v0 at *
  generalize hpl [zero, one, negOne, one, one] x = v1 at *
  generalize hpl [zero, one, one, negOne, one] x = v2 at *
  generalize hpl [zero, one, one, one, negOne] x = v3 at *
  generalize hpl [negOne, one, one, one] x = v4 at *
  generalize hpl [zero, negOne, one, one] x = v5 at *
  generalize hpl [zero, one, negOne, one] x = v6 at *
  generalize hpl [zero, one, one, negOne] x = v7 at *
  generalize hpl [zero, one, one, one] x = v8 at *
  generalize hpl [one, negOne, one, one] x = v9 at *
  generalize hpl [one, one, negOne, one] x = v10 at *
  generalize hpl [one, one, one, negOne] x = v11 at *
  generalize hpl [negOne, one, one] x = v12 at *
  generalize hpl [zero, negOne, one] x = v13 at *
  generalize hpl [zero, one, negOne] x = v14 at *
  generalize hpl [zero, one, one] x = v15 at *
  generalize hpl [one, negOne, one] x = v16 at *
  generalize hpl [one, one, negOne] x = v17 at *
  generalize hpl [one, one, one] x = v18 at *
  generalize hpl [negOne, one] x = v19 at *
  generalize hpl [one, negOne] x = v20 at *
  generalize hpl [one, one] x = v21 at *
  generalize hpl [negOne] x = v22 at *
  generalize hpl [one] x = v23 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽148⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s148 (x : ℝ) : ℝ :=
  i8Psi4s148k0 x

/-- The derivative of `Ψ₄⁽148⁾`. -/
noncomputable def i8Psi4s148D (x : ℝ) : ℝ :=
  i8Psi4s148k0D x

theorem hasDerivAt_i8Psi4s148 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s148 (i8Psi4s148D x) x := by
  unfold i8Psi4s148 i8Psi4s148D
  exact (hasDerivAt_i8Psi4s148k0 hx)

/-- The sub-piece 148 of `p₄` in `ξ`: from `t B0 A1 (-λ)^3/3!`, the term with `log^3 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s148 (x : ℝ) : ℝ :=
  -((4 / 3) * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 3 * ((1 + x) / (1 - x) * (-hpl [negOne] x)))

/-- `p₄⁽148⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w148 (x : ℝ) : ℝ :=
  i8P4w148k0 x

theorem i8P4s148_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s148 x = i8P4w148 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s148 i8P4w148 i8P4w148k0
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [one] [one] hx
  have e1 := hpl_mul_hpl [one] [one, one] hx
  have e2 := hpl_mul_hpl [negOne] [one, one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  linear_combination (norm := skip) (((-4 / 3 +
    4 / 3 * x ^ 2) / (x)) * hpl [one] x * hpl [negOne] x) * e0 + (((-8 / 3 +
    8 / 3 * x ^ 2) / (x)) * hpl [negOne] x) * e1 + (((-8 + 8 * x ^ 2) / (x))) * e2
  field_simp
  generalize hpl [negOne, one, one, one] x = v0 at *
  generalize hpl [one, negOne, one, one] x = v1 at *
  generalize hpl [one, one, negOne, one] x = v2 at *
  generalize hpl [one, one, one, negOne] x = v3 at *
  generalize hpl [one, one, one] x = v4 at *
  generalize hpl [one, one] x = v5 at *
  generalize hpl [negOne] x = v6 at *
  generalize hpl [one] x = v7 at *
  ring

/-- **`(Ψ₄⁽148⁾)'(ξ) ξ' = p₄⁽148⁾`**, in terms of `ξ`. -/
theorem i8Psi4s148D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s148D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s148 x := by
  rw [i8P4s148_eq_w hx]
  unfold i8Psi4s148D i8P4w148
  rw [← i8Psi4s148k0D_mul hx]

/-- The part of `ξ² Ψ₄⁽149⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s149N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s149N0`. -/
noncomputable def i8Psi4s149dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s149N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s149N0 (i8Psi4s149dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽149⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s149N1 (x : ℝ) : ℝ :=
    (12) +
    (12) * hpl [zero] x +
    (12) * hpl [zero, zero] x +
    (12) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s149N1`. -/
noncomputable def i8Psi4s149dN1 (x : ℝ) : ℝ :=
    0 +
    (12) * (zero.kernel x * hpl [] x) +
    (12) * (zero.kernel x * hpl [zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s149N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s149N1 (i8Psi4s149dN1 x) x := by
  unfold i8Psi4s149N1 i8Psi4s149dN1
  exact (((((hasDerivAt_const x (12)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽149⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s149N2 (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s149N2`. -/
noncomputable def i8Psi4s149dN2 (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s149N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s149N2 (i8Psi4s149dN2 x) x := by
  unfold i8Psi4s149N2 i8Psi4s149dN2
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (4))

/-- The part of `ξ² Ψ₄⁽149⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s149N3 (x : ℝ) : ℝ :=
    (4) +
    (-4) * hpl [zero] x +
    (4) * hpl [zero, zero] x +
    (-4) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s149N3`. -/
noncomputable def i8Psi4s149dN3 (x : ℝ) : ℝ :=
    0 +
    (-4) * (zero.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s149N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s149N3 (i8Psi4s149dN3 x) x := by
  unfold i8Psi4s149N3 i8Psi4s149dN3
  exact (((((hasDerivAt_const x (4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽149⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s149N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1) * hpl [zero] x +
    (2) * hpl [zero, zero] x +
    (-4) * hpl [zero, zero, zero] x +
    (4) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s149N4`. -/
noncomputable def i8Psi4s149dN4 (x : ℝ) : ℝ :=
    0 +
    (-1) * (zero.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s149N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s149N4 (i8Psi4s149dN4 x) x := by
  unfold i8Psi4s149N4 i8Psi4s149dN4
  exact (((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽149⁾` with constant coefficients. -/
noncomputable def i8Psi4s149W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s149W`. -/
noncomputable def i8Psi4s149dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s149W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s149W (i8Psi4s149dW x) x := by
  unfold i8Psi4s149W i8Psi4s149dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero, zero] hx).const_mul (-8))

/-- The piece `Ψ₄⁽149⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s149 (x : ℝ) : ℝ :=
  (i8Psi4s149N0 x + x * i8Psi4s149N1 x + x ^ 2 * i8Psi4s149N2 x + x ^ 3 * i8Psi4s149N3 x +
    x ^ 4 * i8Psi4s149N4 x) / x ^ 2 + i8Psi4s149W x

/-- The derivative of `Ψ₄⁽149⁾`. -/
noncomputable def i8Psi4s149D (x : ℝ) : ℝ :=
  ((i8Psi4s149dN0 x + (i8Psi4s149N1 x + x * i8Psi4s149dN1 x) + (2 * x * i8Psi4s149N2 x +
    x ^ 2 * i8Psi4s149dN2 x) + (3 * x ^ 2 * i8Psi4s149N3 x + x ^ 3 * i8Psi4s149dN3 x) +
    (4 * x ^ 3 * i8Psi4s149N4 x + x ^ 4 * i8Psi4s149dN4 x)) * x ^ 2 - (i8Psi4s149N0 x +
    x * i8Psi4s149N1 x + x ^ 2 * i8Psi4s149N2 x + x ^ 3 * i8Psi4s149N3 x +
    x ^ 4 * i8Psi4s149N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s149dW x

theorem hasDerivAt_i8Psi4s149 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s149 (i8Psi4s149D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s149N0 hx).add (X.mul (hasDerivAt_i8Psi4s149N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s149N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s149N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s149N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s149W hx)
  unfold i8Psi4s149
  refine e.congr_deriv ?_
  unfold i8Psi4s149D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 149 of `p₄` in `ξ`: from `t B1 A0 (-λ)^3/3!`, the term with `log^0 (1 -
  ξ) log^3 ξ`. -/
noncomputable def i8P4s149 (x : ℝ) : ℝ :=
  (1 / 3) * (1 - x) ^ 2 / x * Real.log x ^ 3 * (2 + Real.log x * (1 + x) / (1 - x)) * (x / (1 - x))

/-- `p₄⁽149⁾` written over words. -/
noncomputable def i8P4w149 (x : ℝ) : ℝ :=
    (4 - 4 * x) * hpl [zero, zero, zero] x +
    (8 + 8 * x) * hpl [zero, zero, zero, zero] x

theorem i8P4s149_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s149 x = i8P4w149 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s149 i8P4w149
  simp only [i13hw_000, i13hw_0000]
  field_simp
  generalize hpl [zero, negOne, negOne, negOne, negOne] x = v0 at *
  generalize hpl [zero, negOne, negOne, negOne, one] x = v1 at *
  generalize hpl [zero, negOne, negOne, zero, one] x = v2 at *
  generalize hpl [zero, negOne, negOne, one, negOne] x = v3 at *
  generalize hpl [zero, negOne, negOne, one, one] x = v4 at *
  generalize hpl [zero, negOne, zero, negOne, negOne] x = v5 at *
  generalize hpl [zero, negOne, zero, negOne, one] x = v6 at *
  generalize hpl [zero, negOne, zero, one, negOne] x = v7 at *
  generalize hpl [zero, negOne, zero, one, one] x = v8 at *
  generalize hpl [zero, negOne, one, negOne, negOne] x = v9 at *
  generalize hpl [zero, negOne, one, negOne, one] x = v10 at *
  generalize hpl [zero, negOne, one, zero, one] x = v11 at *
  generalize hpl [zero, negOne, one, one, negOne] x = v12 at *
  generalize hpl [zero, negOne, one, one, one] x = v13 at *
  generalize hpl [zero, zero, negOne, negOne, negOne] x = v14 at *
  generalize hpl [zero, zero, negOne, negOne, one] x = v15 at *
  generalize hpl [zero, zero, negOne, zero, negOne] x = v16 at *
  generalize hpl [zero, zero, negOne, zero, one] x = v17 at *
  generalize hpl [zero, zero, negOne, one, negOne] x = v18 at *
  generalize hpl [zero, zero, negOne, one, one] x = v19 at *
  generalize hpl [zero, zero, zero, negOne, negOne] x = v20 at *
  generalize hpl [zero, zero, zero, negOne, one] x = v21 at *
  generalize hpl [zero, zero, zero, zero, negOne] x = v22 at *
  generalize hpl [zero, zero, zero, zero, zero] x = v23 at *
  generalize hpl [zero, zero, zero, zero, one] x = v24 at *
  generalize hpl [zero, zero, zero, one, negOne] x = v25 at *
  generalize hpl [zero, zero, zero, one, one] x = v26 at *
  generalize hpl [zero, zero, one, negOne, negOne] x = v27 at *
  generalize hpl [zero, zero, one, negOne, one] x = v28 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v29 at *
  generalize hpl [zero, zero, one, zero, one] x = v30 at *
  generalize hpl [zero, zero, one, one, negOne] x = v31 at *
  generalize hpl [zero, zero, one, one, one] x = v32 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v33 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v34 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v35 at *
  generalize hpl [zero, one, negOne, one, one] x = v36 at *
  generalize hpl [zero, one, zero, one, negOne] x = v37 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v38 at *
  generalize hpl [zero, one, one, negOne, one] x = v39 at *
  generalize hpl [zero, one, one, one, negOne] x = v40 at *
  generalize hpl [zero, one, one, one, one] x = v41 at *
  generalize hpl [negOne, negOne, one, one] x = v42 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v43 at *
  generalize hpl [zero, negOne, negOne, one] x = v44 at *
  generalize hpl [zero, negOne, zero, one] x = v45 at *
  generalize hpl [zero, negOne, one, negOne] x = v46 at *
  generalize hpl [zero, negOne, one, one] x = v47 at *
  generalize hpl [zero, zero, negOne, negOne] x = v48 at *
  generalize hpl [zero, zero, negOne, one] x = v49 at *
  generalize hpl [zero, zero, zero, negOne] x = v50 at *
  generalize hpl [zero, zero, zero, zero] x = v51 at *
  generalize hpl [zero, zero, zero, one] x = v52 at *
  generalize hpl [zero, zero, one, negOne] x = v53 at *
  generalize hpl [zero, zero, one, one] x = v54 at *
  generalize hpl [zero, one, negOne, negOne] x = v55 at *
  generalize hpl [zero, one, negOne, one] x = v56 at *
  generalize hpl [zero, one, one, negOne] x = v57 at *
  generalize hpl [zero, one, one, one] x = v58 at *
  generalize hpl [negOne, negOne, one] x = v59 at *
  generalize hpl [negOne, one, one] x = v60 at *
  generalize hpl [zero, negOne, negOne] x = v61 at *
  generalize hpl [zero, negOne, one] x = v62 at *
  generalize hpl [zero, zero, negOne] x = v63 at *
  generalize hpl [zero, zero, zero] x = v64 at *
  generalize hpl [zero, zero, one] x = v65 at *
  generalize hpl [zero, one, negOne] x = v66 at *
  generalize hpl [zero, one, one] x = v67 at *
  generalize hpl [negOne, one] x = v68 at *
  generalize hpl [zero, negOne] x = v69 at *
  generalize hpl [zero, zero] x = v70 at *
  generalize hpl [zero, one] x = v71 at *
  generalize hpl [negOne] x = v72 at *
  generalize hpl [zero] x = v73 at *
  generalize hpl [one] x = v74 at *
  ring

/-- **`(Ψ₄⁽149⁾)'(ξ) ξ' = p₄⁽149⁾`**, in terms of `ξ`. -/
theorem i8Psi4s149D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s149D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s149 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s149_eq_w hx]
  unfold i8Psi4s149D i8Psi4s149N0 i8Psi4s149N1 i8Psi4s149N2 i8Psi4s149N3 i8Psi4s149N4 i8Psi4s149dN0
    i8Psi4s149dN1 i8Psi4s149dN2 i8Psi4s149dN3 i8Psi4s149dN4 i8Psi4s149dW i8P4w149
  simp only [kernel_zero, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero, zero] x = v1 at *
  generalize hpl [zero, zero, zero] x = v2 at *
  generalize hpl [zero, zero] x = v3 at *
  generalize hpl [zero] x = v4 at *
  ring

/-- The part of `ξ² Ψ₄⁽150⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s150N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s150N0`. -/
noncomputable def i8Psi4s150dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s150N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s150N0 (i8Psi4s150dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽150⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s150N1 (x : ℝ) : ℝ :=
    (20) * hpl [one] x +
    (20) * hpl [zero, one] x +
    (20) * hpl [one, zero] x +
    (20) * hpl [zero, zero, one] x +
    (20) * hpl [zero, one, zero] x +
    (20) * hpl [one, zero, zero] x +
    (12) * hpl [zero, zero, zero, one] x +
    (12) * hpl [zero, zero, one, zero] x +
    (12) * hpl [zero, one, zero, zero] x +
    (12) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s150N1`. -/
noncomputable def i8Psi4s150dN1 (x : ℝ) : ℝ :=
    (20) * (one.kernel x * hpl [] x) +
    (20) * (zero.kernel x * hpl [one] x) +
    (20) * (one.kernel x * hpl [zero] x) +
    (20) * (zero.kernel x * hpl [zero, one] x) +
    (20) * (zero.kernel x * hpl [one, zero] x) +
    (20) * (one.kernel x * hpl [zero, zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero, one] x) +
    (12) * (zero.kernel x * hpl [zero, one, zero] x) +
    (12) * (zero.kernel x * hpl [one, zero, zero] x) +
    (12) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s150N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s150N1 (i8Psi4s150dN1 x) x := by
  unfold i8Psi4s150N1 i8Psi4s150dN1
  exact (((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (20)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽150⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s150N2 (x : ℝ) : ℝ :=
    (-20) * hpl [zero] x +
    (-57 / 4) * hpl [one] x +
    (-20) * hpl [zero, zero] x +
    (-55 / 2) * hpl [one, zero] x +
    (-20) * hpl [zero, zero, zero] x +
    (-9) * hpl [one, zero, zero] x +
    (8) * hpl [zero, zero, zero, one] x +
    (8) * hpl [zero, zero, one, zero] x +
    (8) * hpl [zero, one, zero, zero] x +
    (-30) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s150N2`. -/
noncomputable def i8Psi4s150dN2 (x : ℝ) : ℝ :=
    (-20) * (zero.kernel x * hpl [] x) +
    (-57 / 4) * (one.kernel x * hpl [] x) +
    (-20) * (zero.kernel x * hpl [zero] x) +
    (-55 / 2) * (one.kernel x * hpl [zero] x) +
    (-20) * (zero.kernel x * hpl [zero, zero] x) +
    (-9) * (one.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, zero, one] x) +
    (8) * (zero.kernel x * hpl [zero, one, zero] x) +
    (8) * (zero.kernel x * hpl [one, zero, zero] x) +
    (-30) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s150N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s150N2 (i8Psi4s150dN2 x) x := by
  unfold i8Psi4s150N2 i8Psi4s150dN2
  exact (((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-20)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-57 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-55 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-9))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (-30)))

/-- The part of `ξ² Ψ₄⁽150⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s150N3 (x : ℝ) : ℝ :=
    (-169 / 4) +
    (73 / 2) * hpl [zero] x +
    (-4) * hpl [one] x +
    (-29) * hpl [zero, zero] x +
    (4) * hpl [zero, one] x +
    (4) * hpl [one, zero] x +
    (18) * hpl [zero, zero, zero] x +
    (-4) * hpl [zero, zero, one] x +
    (-4) * hpl [zero, one, zero] x +
    (-4) * hpl [one, zero, zero] x +
    (12) * hpl [zero, zero, zero, one] x +
    (12) * hpl [zero, zero, one, zero] x +
    (12) * hpl [zero, one, zero, zero] x +
    (12) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s150N3`. -/
noncomputable def i8Psi4s150dN3 (x : ℝ) : ℝ :=
    0 +
    (73 / 2) * (zero.kernel x * hpl [] x) +
    (-4) * (one.kernel x * hpl [] x) +
    (-29) * (zero.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [zero] x) +
    (18) * (zero.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, one] x) +
    (-4) * (zero.kernel x * hpl [one, zero] x) +
    (-4) * (one.kernel x * hpl [zero, zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero, one] x) +
    (12) * (zero.kernel x * hpl [zero, one, zero] x) +
    (12) * (zero.kernel x * hpl [one, zero, zero] x) +
    (12) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s150N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s150N3 (i8Psi4s150dN3 x) x := by
  unfold i8Psi4s150N3 i8Psi4s150dN3
  exact ((((((((((((((hasDerivAt_const x (-169 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (73 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-29))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽150⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s150N4 (x : ℝ) : ℝ :=
    (-3) +
    (17 / 4) * hpl [zero] x +
    (-7 / 4) * hpl [one] x +
    (-5) * hpl [zero, zero] x +
    (7 / 2) * hpl [zero, one] x +
    (7 / 2) * hpl [one, zero] x +
    (3) * hpl [zero, zero, zero] x +
    (-7) * hpl [zero, zero, one] x +
    (-7) * hpl [zero, one, zero] x +
    (-7) * hpl [one, zero, zero] x +
    (6) * hpl [zero, zero, zero, one] x +
    (6) * hpl [zero, zero, one, zero] x +
    (6) * hpl [zero, one, zero, zero] x +
    (6) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s150N4`. -/
noncomputable def i8Psi4s150dN4 (x : ℝ) : ℝ :=
    0 +
    (17 / 4) * (zero.kernel x * hpl [] x) +
    (-7 / 4) * (one.kernel x * hpl [] x) +
    (-5) * (zero.kernel x * hpl [zero] x) +
    (7 / 2) * (zero.kernel x * hpl [one] x) +
    (7 / 2) * (one.kernel x * hpl [zero] x) +
    (3) * (zero.kernel x * hpl [zero, zero] x) +
    (-7) * (zero.kernel x * hpl [zero, one] x) +
    (-7) * (zero.kernel x * hpl [one, zero] x) +
    (-7) * (one.kernel x * hpl [zero, zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero, one] x) +
    (6) * (zero.kernel x * hpl [zero, one, zero] x) +
    (6) * (zero.kernel x * hpl [one, zero, zero] x) +
    (6) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s150N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s150N4 (i8Psi4s150dN4 x) x := by
  unfold i8Psi4s150N4 i8Psi4s150dN4
  exact ((((((((((((((hasDerivAt_const x (-3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (17 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-7 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (6)))

/-- The part of `Ψ₄⁽150⁾` with constant coefficients. -/
noncomputable def i8Psi4s150W (x : ℝ) : ℝ :=
    (-12) * hpl [zero, zero, zero, zero] x +
    (-12) * hpl [zero, zero, zero, zero, one] x +
    (-12) * hpl [zero, zero, zero, one, zero] x +
    (-12) * hpl [zero, zero, one, zero, zero] x +
    (-12) * hpl [zero, one, zero, zero, zero] x

/-- The derivative of `i8Psi4s150W`. -/
noncomputable def i8Psi4s150dW (x : ℝ) : ℝ :=
    (-12) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, zero, one] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, one, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, one, zero, zero] x) +
    (-12) * (zero.kernel x * hpl [one, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s150W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s150W (i8Psi4s150dW x) x := by
  unfold i8Psi4s150W i8Psi4s150dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-12)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero, zero] hx).const_mul (-12)))

/-- The piece `Ψ₄⁽150⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s150 (x : ℝ) : ℝ :=
  (i8Psi4s150N0 x + x * i8Psi4s150N1 x + x ^ 2 * i8Psi4s150N2 x + x ^ 3 * i8Psi4s150N3 x +
    x ^ 4 * i8Psi4s150N4 x) / x ^ 2 + i8Psi4s150W x

/-- The derivative of `Ψ₄⁽150⁾`. -/
noncomputable def i8Psi4s150D (x : ℝ) : ℝ :=
  ((i8Psi4s150dN0 x + (i8Psi4s150N1 x + x * i8Psi4s150dN1 x) + (2 * x * i8Psi4s150N2 x +
    x ^ 2 * i8Psi4s150dN2 x) + (3 * x ^ 2 * i8Psi4s150N3 x + x ^ 3 * i8Psi4s150dN3 x) +
    (4 * x ^ 3 * i8Psi4s150N4 x + x ^ 4 * i8Psi4s150dN4 x)) * x ^ 2 - (i8Psi4s150N0 x +
    x * i8Psi4s150N1 x + x ^ 2 * i8Psi4s150N2 x + x ^ 3 * i8Psi4s150N3 x +
    x ^ 4 * i8Psi4s150N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s150dW x

theorem hasDerivAt_i8Psi4s150 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s150 (i8Psi4s150D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s150N0 hx).add (X.mul (hasDerivAt_i8Psi4s150N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s150N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s150N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s150N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s150W hx)
  unfold i8Psi4s150
  refine e.congr_deriv ?_
  unfold i8Psi4s150D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 150 of `p₄` in `ξ`: from `t B1 A0 (-λ)^3/3!`, the term with `log^1 (1 -
  ξ) log^2 ξ`. -/
noncomputable def i8P4s150 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * Real.log x ^ 2 * (2 + Real.log x * (1 + x) / (1 -
    x)) * (x / (1 - x)))

/-- `p₄⁽150⁾` written over words. -/
noncomputable def i8P4w150 (x : ℝ) : ℝ :=
    (8 - 8 * x) * hpl [zero, zero, one] x +
    (8 - 8 * x) * hpl [zero, one, zero] x +
    (8 - 8 * x) * hpl [one, zero, zero] x +
    (12 + 12 * x) * hpl [zero, zero, zero, one] x +
    (12 + 12 * x) * hpl [zero, zero, one, zero] x +
    (12 + 12 * x) * hpl [zero, one, zero, zero] x +
    (12 + 12 * x) * hpl [one, zero, zero, zero] x

theorem i8P4s150_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s150 x = i8P4w150 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s150 i8P4w150
  simp only [i13hw_010 hx, i13hw_100 hx, i13hw_0010 hx, i13hw_0100 hx, i13hw_1000 hx,
    i13_log_one_sub_eq hx]
  field_simp
  generalize hpl [zero, negOne, negOne, negOne, negOne] x = v0 at *
  generalize hpl [zero, negOne, negOne, negOne, one] x = v1 at *
  generalize hpl [zero, negOne, negOne, zero, one] x = v2 at *
  generalize hpl [zero, negOne, negOne, one, negOne] x = v3 at *
  generalize hpl [zero, negOne, negOne, one, one] x = v4 at *
  generalize hpl [zero, negOne, zero, negOne, negOne] x = v5 at *
  generalize hpl [zero, negOne, zero, negOne, one] x = v6 at *
  generalize hpl [zero, negOne, zero, one, negOne] x = v7 at *
  generalize hpl [zero, negOne, zero, one, one] x = v8 at *
  generalize hpl [zero, negOne, one, negOne, negOne] x = v9 at *
  generalize hpl [zero, negOne, one, negOne, one] x = v10 at *
  generalize hpl [zero, negOne, one, zero, one] x = v11 at *
  generalize hpl [zero, negOne, one, one, negOne] x = v12 at *
  generalize hpl [zero, negOne, one, one, one] x = v13 at *
  generalize hpl [zero, zero, negOne, negOne, negOne] x = v14 at *
  generalize hpl [zero, zero, negOne, negOne, one] x = v15 at *
  generalize hpl [zero, zero, negOne, zero, negOne] x = v16 at *
  generalize hpl [zero, zero, negOne, zero, one] x = v17 at *
  generalize hpl [zero, zero, negOne, one, negOne] x = v18 at *
  generalize hpl [zero, zero, negOne, one, one] x = v19 at *
  generalize hpl [zero, zero, zero, negOne, negOne] x = v20 at *
  generalize hpl [zero, zero, zero, negOne, one] x = v21 at *
  generalize hpl [zero, zero, zero, zero, negOne] x = v22 at *
  generalize hpl [zero, zero, zero, zero, one] x = v23 at *
  generalize hpl [zero, zero, zero, one, negOne] x = v24 at *
  generalize hpl [zero, zero, zero, one, zero] x = v25 at *
  generalize hpl [zero, zero, zero, one, one] x = v26 at *
  generalize hpl [zero, zero, one, negOne, negOne] x = v27 at *
  generalize hpl [zero, zero, one, negOne, one] x = v28 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v29 at *
  generalize hpl [zero, zero, one, zero, zero] x = v30 at *
  generalize hpl [zero, zero, one, zero, one] x = v31 at *
  generalize hpl [zero, zero, one, one, negOne] x = v32 at *
  generalize hpl [zero, zero, one, one, one] x = v33 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v34 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v35 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v36 at *
  generalize hpl [zero, one, negOne, one, one] x = v37 at *
  generalize hpl [zero, one, zero, zero, zero] x = v38 at *
  generalize hpl [zero, one, zero, one, negOne] x = v39 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v40 at *
  generalize hpl [zero, one, one, negOne, one] x = v41 at *
  generalize hpl [zero, one, one, one, negOne] x = v42 at *
  generalize hpl [zero, one, one, one, one] x = v43 at *
  generalize hpl [negOne, negOne, one, one] x = v44 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v45 at *
  generalize hpl [zero, negOne, negOne, one] x = v46 at *
  generalize hpl [zero, negOne, zero, one] x = v47 at *
  generalize hpl [zero, negOne, one, negOne] x = v48 at *
  generalize hpl [zero, negOne, one, one] x = v49 at *
  generalize hpl [zero, zero, negOne, negOne] x = v50 at *
  generalize hpl [zero, zero, negOne, one] x = v51 at *
  generalize hpl [zero, zero, zero, negOne] x = v52 at *
  generalize hpl [zero, zero, zero, zero] x = v53 at *
  generalize hpl [zero, zero, zero, one] x = v54 at *
  generalize hpl [zero, zero, one, negOne] x = v55 at *
  generalize hpl [zero, zero, one, zero] x = v56 at *
  generalize hpl [zero, zero, one, one] x = v57 at *
  generalize hpl [zero, one, negOne, negOne] x = v58 at *
  generalize hpl [zero, one, negOne, one] x = v59 at *
  generalize hpl [zero, one, zero, zero] x = v60 at *
  generalize hpl [zero, one, one, negOne] x = v61 at *
  generalize hpl [zero, one, one, one] x = v62 at *
  generalize hpl [one, zero, zero, zero] x = v63 at *
  generalize hpl [negOne, negOne, one] x = v64 at *
  generalize hpl [negOne, one, one] x = v65 at *
  generalize hpl [zero, negOne, negOne] x = v66 at *
  generalize hpl [zero, negOne, one] x = v67 at *
  generalize hpl [zero, zero, negOne] x = v68 at *
  generalize hpl [zero, zero, zero] x = v69 at *
  generalize hpl [zero, zero, one] x = v70 at *
  generalize hpl [zero, one, negOne] x = v71 at *
  generalize hpl [zero, one, zero] x = v72 at *
  generalize hpl [zero, one, one] x = v73 at *
  generalize hpl [one, zero, zero] x = v74 at *
  generalize hpl [negOne, one] x = v75 at *
  generalize hpl [zero, negOne] x = v76 at *
  generalize hpl [zero, zero] x = v77 at *
  generalize hpl [zero, one] x = v78 at *
  generalize hpl [one, zero] x = v79 at *
  generalize hpl [negOne] x = v80 at *
  generalize hpl [zero] x = v81 at *
  generalize hpl [one] x = v82 at *
  ring

/-- **`(Ψ₄⁽150⁾)'(ξ) ξ' = p₄⁽150⁾`**, in terms of `ξ`. -/
theorem i8Psi4s150D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s150D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s150 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s150_eq_w hx]
  unfold i8Psi4s150D i8Psi4s150N0 i8Psi4s150N1 i8Psi4s150N2 i8Psi4s150N3 i8Psi4s150N4 i8Psi4s150dN0
    i8Psi4s150dN1 i8Psi4s150dN2 i8Psi4s150dN3 i8Psi4s150dN4 i8Psi4s150dW i8P4w150
  simp only [kernel_zero, kernel_one, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero, zero, one] x = v0 at *
  generalize hpl [zero, zero, zero, one, zero] x = v1 at *
  generalize hpl [zero, zero, one, zero, zero] x = v2 at *
  generalize hpl [zero, one, zero, zero, zero] x = v3 at *
  generalize hpl [zero, zero, zero, zero] x = v4 at *
  generalize hpl [zero, zero, zero, one] x = v5 at *
  generalize hpl [zero, zero, one, zero] x = v6 at *
  generalize hpl [zero, one, zero, zero] x = v7 at *
  generalize hpl [one, zero, zero, zero] x = v8 at *
  generalize hpl [zero, zero, zero] x = v9 at *
  generalize hpl [zero, zero, one] x = v10 at *
  generalize hpl [zero, one, zero] x = v11 at *
  generalize hpl [one, zero, zero] x = v12 at *
  generalize hpl [zero, zero] x = v13 at *
  generalize hpl [zero, one] x = v14 at *
  generalize hpl [one, zero] x = v15 at *
  generalize hpl [zero] x = v16 at *
  generalize hpl [one] x = v17 at *
  ring

end QED.ThreeLoopD
