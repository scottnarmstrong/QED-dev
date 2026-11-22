/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P37

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 128 to 128

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s128`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s128D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s128`, `QED.ThreeLoopD.i8Psi4s128D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s128k0N0 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne, one, one] x +
    (-4) * hpl [negOne, zero, one, one] x +
    (-4) * hpl [negOne, one, zero, one] x +
    (-4) * hpl [negOne, one, one, zero] x +
    (-4) * hpl [zero, negOne, one, one] x

/-- The derivative of `i8Psi4s128k0N0`. -/
noncomputable def i8Psi4s128k0dN0 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [one, one] x) +
    (-4) * (negOne.kernel x * hpl [zero, one, one] x) +
    (-4) * (negOne.kernel x * hpl [one, zero, one] x) +
    (-4) * (negOne.kernel x * hpl [one, one, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, one, one] x)

theorem hasDerivAt_i8Psi4s128k0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k0N0 (i8Psi4s128k0dN0 x) x := by
  unfold i8Psi4s128k0N0 i8Psi4s128k0dN0
  exact ((((((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons negOne [zero, one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s128k0N1 (x : ℝ) : ℝ :=
    (-6) * hpl [one, one] x +
    (-16) * hpl [negOne, one, one] x +
    (-4) * hpl [zero, one, one] x +
    (-4) * hpl [one, zero, one] x +
    (-4) * hpl [one, one, zero] x +
    (-16) * hpl [negOne, zero, one, one] x +
    (-16) * hpl [negOne, one, zero, one] x +
    (-16) * hpl [negOne, one, one, zero] x +
    (-16) * hpl [zero, negOne, one, one] x

/-- The derivative of `i8Psi4s128k0N1`. -/
noncomputable def i8Psi4s128k0dN1 (x : ℝ) : ℝ :=
    (-6) * (one.kernel x * hpl [one] x) +
    (-16) * (negOne.kernel x * hpl [one, one] x) +
    (-4) * (zero.kernel x * hpl [one, one] x) +
    (-4) * (one.kernel x * hpl [zero, one] x) +
    (-4) * (one.kernel x * hpl [one, zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, one, one] x) +
    (-16) * (negOne.kernel x * hpl [one, zero, one] x) +
    (-16) * (negOne.kernel x * hpl [one, one, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, one, one] x)

theorem hasDerivAt_i8Psi4s128k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k0N1 (i8Psi4s128k0dN1 x) x := by
  unfold i8Psi4s128k0N1 i8Psi4s128k0dN1
  exact ((((((((((hasDerivAt_hpl_cons one [one] hx).const_mul (-6)).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s128k0N2 (x : ℝ) : ℝ :=
    (87 / 2) * hpl [one] x +
    (6) * hpl [zero, one] x +
    (-15) * hpl [one, zero] x +
    (34) * hpl [one, one] x +
    (14) * hpl [zero, one, one] x +
    (-10) * hpl [one, zero, one] x +
    (-10) * hpl [one, one, zero] x +
    (-24) * hpl [negOne, zero, one, one] x +
    (-24) * hpl [negOne, one, zero, one] x +
    (-24) * hpl [negOne, one, one, zero] x

/-- The derivative of `i8Psi4s128k0N2`. -/
noncomputable def i8Psi4s128k0dN2 (x : ℝ) : ℝ :=
    (87 / 2) * (one.kernel x * hpl [] x) +
    (6) * (zero.kernel x * hpl [one] x) +
    (-15) * (one.kernel x * hpl [zero] x) +
    (34) * (one.kernel x * hpl [one] x) +
    (14) * (zero.kernel x * hpl [one, one] x) +
    (-10) * (one.kernel x * hpl [zero, one] x) +
    (-10) * (one.kernel x * hpl [one, zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, one, one] x) +
    (-24) * (negOne.kernel x * hpl [one, zero, one] x) +
    (-24) * (negOne.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s128k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k0N2 (i8Psi4s128k0dN2 x) x := by
  unfold i8Psi4s128k0N2 i8Psi4s128k0dN2
  exact (((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (87 / 2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-15))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (34))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [one, one, zero] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s128k0N3 (x : ℝ) : ℝ :=
    (-117 / 2) +
    (15) * hpl [zero] x +
    (-42) * hpl [one] x +
    (14) * hpl [zero, one] x +
    (14) * hpl [one, zero] x +
    (-26) * hpl [one, one] x +
    (16) * hpl [negOne, one, one] x +
    (12) * hpl [zero, one, one] x +
    (12) * hpl [one, zero, one] x +
    (12) * hpl [one, one, zero] x +
    (-16) * hpl [negOne, zero, one, one] x +
    (-16) * hpl [negOne, one, zero, one] x +
    (-16) * hpl [negOne, one, one, zero] x +
    (-16) * hpl [zero, negOne, one, one] x

/-- The derivative of `i8Psi4s128k0N3`. -/
noncomputable def i8Psi4s128k0dN3 (x : ℝ) : ℝ :=
    0 +
    (15) * (zero.kernel x * hpl [] x) +
    (-42) * (one.kernel x * hpl [] x) +
    (14) * (zero.kernel x * hpl [one] x) +
    (14) * (one.kernel x * hpl [zero] x) +
    (-26) * (one.kernel x * hpl [one] x) +
    (16) * (negOne.kernel x * hpl [one, one] x) +
    (12) * (zero.kernel x * hpl [one, one] x) +
    (12) * (one.kernel x * hpl [zero, one] x) +
    (12) * (one.kernel x * hpl [one, zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, one, one] x) +
    (-16) * (negOne.kernel x * hpl [one, zero, one] x) +
    (-16) * (negOne.kernel x * hpl [one, one, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, one, one] x)

theorem hasDerivAt_i8Psi4s128k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k0N3 (i8Psi4s128k0dN3 x) x := by
  unfold i8Psi4s128k0N3 i8Psi4s128k0dN3
  exact ((((((((((((((hasDerivAt_const x (-117 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-42))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-26))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s128k0N4 (x : ℝ) : ℝ :=
    (-1) +
    (1 / 2) * hpl [zero] x +
    (-3 / 2) * hpl [one] x +
    (1) * hpl [zero, one] x +
    (1) * hpl [one, zero] x +
    (-2) * hpl [one, one] x +
    (2) * hpl [negOne, one, one] x +
    (2) * hpl [zero, one, one] x +
    (2) * hpl [one, zero, one] x +
    (2) * hpl [one, one, zero] x +
    (-4) * hpl [negOne, zero, one, one] x +
    (-4) * hpl [negOne, one, zero, one] x +
    (-4) * hpl [negOne, one, one, zero] x +
    (-4) * hpl [zero, negOne, one, one] x

/-- The derivative of `i8Psi4s128k0N4`. -/
noncomputable def i8Psi4s128k0dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-3 / 2) * (one.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [zero] x) +
    (-2) * (one.kernel x * hpl [one] x) +
    (2) * (negOne.kernel x * hpl [one, one] x) +
    (2) * (zero.kernel x * hpl [one, one] x) +
    (2) * (one.kernel x * hpl [zero, one] x) +
    (2) * (one.kernel x * hpl [one, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, one, one] x) +
    (-4) * (negOne.kernel x * hpl [one, zero, one] x) +
    (-4) * (negOne.kernel x * hpl [one, one, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, one, one] x)

theorem hasDerivAt_i8Psi4s128k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k0N4 (i8Psi4s128k0dN4 x) x := by
  unfold i8Psi4s128k0N4 i8Psi4s128k0dN4
  exact ((((((((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽128⁾` with constant coefficients. -/
noncomputable def i8Psi4s128k0W (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (12) * hpl [zero, zero, one, one] x +
    (12) * hpl [zero, one, zero, one] x +
    (12) * hpl [zero, one, one, zero] x

/-- The derivative of `i8Psi4s128k0W`. -/
noncomputable def i8Psi4s128k0dW (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (12) * (zero.kernel x * hpl [zero, one, one] x) +
    (12) * (zero.kernel x * hpl [one, zero, one] x) +
    (12) * (zero.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s128k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k0W (i8Psi4s128k0dW x) x := by
  unfold i8Psi4s128k0W i8Psi4s128k0dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (12)))

/-- Chunk 0 of the piece `Ψ₄⁽128⁾`. -/
noncomputable def i8Psi4s128k0 (x : ℝ) : ℝ :=
  (i8Psi4s128k0N0 x + x * i8Psi4s128k0N1 x + x ^ 2 * i8Psi4s128k0N2 x + x ^ 3 * i8Psi4s128k0N3 x +
    x ^ 4 * i8Psi4s128k0N4 x) / x ^ 2 + i8Psi4s128k0W x

/-- The derivative of `i8Psi4s128k0`. -/
noncomputable def i8Psi4s128k0D (x : ℝ) : ℝ :=
  ((i8Psi4s128k0dN0 x + (i8Psi4s128k0N1 x + x * i8Psi4s128k0dN1 x) + (2 * x * i8Psi4s128k0N2 x +
    x ^ 2 * i8Psi4s128k0dN2 x) + (3 * x ^ 2 * i8Psi4s128k0N3 x + x ^ 3 * i8Psi4s128k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s128k0N4 x + x ^ 4 * i8Psi4s128k0dN4 x)) * x ^ 2 - (i8Psi4s128k0N0 x +
    x * i8Psi4s128k0N1 x + x ^ 2 * i8Psi4s128k0N2 x + x ^ 3 * i8Psi4s128k0N3 x +
    x ^ 4 * i8Psi4s128k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s128k0dW x

theorem hasDerivAt_i8Psi4s128k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k0 (i8Psi4s128k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s128k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s128k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s128k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s128k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s128k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s128k0W hx)
  unfold i8Psi4s128k0
  refine e.congr_deriv ?_
  unfold i8Psi4s128k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽128⁾` over words. -/
noncomputable def i8P4w128k0 (x : ℝ) : ℝ :=
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [negOne, zero, one, one] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [negOne, one, zero, one] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [negOne, one, one, zero] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [zero, negOne, one, one] x

theorem i8Psi4s128k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s128k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w128k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s128k0D i8Psi4s128k0N0 i8Psi4s128k0N1 i8Psi4s128k0N2 i8Psi4s128k0N3 i8Psi4s128k0N4
    i8Psi4s128k0dN0 i8Psi4s128k0dN1 i8Psi4s128k0dN2 i8Psi4s128k0dN3 i8Psi4s128k0dN4 i8Psi4s128k0dW
    i8P4w128k0
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [negOne, zero, one, one] x = v0 at *
  generalize hpl [negOne, one, zero, one] x = v1 at *
  generalize hpl [negOne, one, one, zero] x = v2 at *
  generalize hpl [zero, negOne, one, one] x = v3 at *
  generalize hpl [zero, zero, one, one] x = v4 at *
  generalize hpl [zero, one, zero, one] x = v5 at *
  generalize hpl [zero, one, one, zero] x = v6 at *
  generalize hpl [negOne, one, one] x = v7 at *
  generalize hpl [zero, zero, one] x = v8 at *
  generalize hpl [zero, one, zero] x = v9 at *
  generalize hpl [zero, one, one] x = v10 at *
  generalize hpl [one, zero, one] x = v11 at *
  generalize hpl [one, one, zero] x = v12 at *
  generalize hpl [zero, one] x = v13 at *
  generalize hpl [one, zero] x = v14 at *
  generalize hpl [one, one] x = v15 at *
  generalize hpl [zero] x = v16 at *
  generalize hpl [one] x = v17 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s128k1N0 (x : ℝ) : ℝ :=
    (-2) * hpl [one, negOne, one] x +
    (-2) * hpl [one, one, negOne] x +
    (-4) * hpl [zero, one, negOne, one] x +
    (-4) * hpl [zero, one, one, negOne] x +
    (-4) * hpl [one, negOne, zero, one] x +
    (-4) * hpl [one, negOne, one, zero] x

/-- The derivative of `i8Psi4s128k1N0`. -/
noncomputable def i8Psi4s128k1dN0 (x : ℝ) : ℝ :=
    (-2) * (one.kernel x * hpl [negOne, one] x) +
    (-2) * (one.kernel x * hpl [one, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, negOne, one] x) +
    (-4) * (zero.kernel x * hpl [one, one, negOne] x) +
    (-4) * (one.kernel x * hpl [negOne, zero, one] x) +
    (-4) * (one.kernel x * hpl [negOne, one, zero] x)

theorem hasDerivAt_i8Psi4s128k1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k1N0 (i8Psi4s128k1dN0 x) x := by
  unfold i8Psi4s128k1N0 i8Psi4s128k1dN0
  exact (((((((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, one, zero] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s128k1N1 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne, one] x +
    (-2) * hpl [one, negOne] x +
    (-4) * hpl [negOne, zero, one] x +
    (-4) * hpl [negOne, one, zero] x +
    (-16) * hpl [one, negOne, one] x +
    (-16) * hpl [one, one, negOne] x +
    (-16) * hpl [zero, one, negOne, one] x +
    (-16) * hpl [zero, one, one, negOne] x +
    (-16) * hpl [one, negOne, zero, one] x +
    (-16) * hpl [one, negOne, one, zero] x

/-- The derivative of `i8Psi4s128k1N1`. -/
noncomputable def i8Psi4s128k1dN1 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [negOne] x) +
    (-4) * (negOne.kernel x * hpl [zero, one] x) +
    (-4) * (negOne.kernel x * hpl [one, zero] x) +
    (-16) * (one.kernel x * hpl [negOne, one] x) +
    (-16) * (one.kernel x * hpl [one, negOne] x) +
    (-16) * (zero.kernel x * hpl [one, negOne, one] x) +
    (-16) * (zero.kernel x * hpl [one, one, negOne] x) +
    (-16) * (one.kernel x * hpl [negOne, zero, one] x) +
    (-16) * (one.kernel x * hpl [negOne, one, zero] x)

theorem hasDerivAt_i8Psi4s128k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k1N1 (i8Psi4s128k1dN1 x) x := by
  unfold i8Psi4s128k1N1 i8Psi4s128k1dN1
  exact (((((((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, one, zero] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s128k1N2 (x : ℝ) : ℝ :=
    (37 / 2) * hpl [negOne] x +
    (36) * hpl [one] x +
    (15) * hpl [negOne, one] x +
    (2) * hpl [zero, one] x +
    (-17) * hpl [one, negOne] x +
    (-19) * hpl [one, zero] x +
    (-22) * hpl [negOne, zero, one] x +
    (-22) * hpl [negOne, one, zero] x +
    (40) * hpl [one, negOne, zero, one] x +
    (40) * hpl [one, negOne, one, zero] x

/-- The derivative of `i8Psi4s128k1N2`. -/
noncomputable def i8Psi4s128k1dN2 (x : ℝ) : ℝ :=
    (37 / 2) * (negOne.kernel x * hpl [] x) +
    (36) * (one.kernel x * hpl [] x) +
    (15) * (negOne.kernel x * hpl [one] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (-17) * (one.kernel x * hpl [negOne] x) +
    (-19) * (one.kernel x * hpl [zero] x) +
    (-22) * (negOne.kernel x * hpl [zero, one] x) +
    (-22) * (negOne.kernel x * hpl [one, zero] x) +
    (40) * (one.kernel x * hpl [negOne, zero, one] x) +
    (40) * (one.kernel x * hpl [negOne, one, zero] x)

theorem hasDerivAt_i8Psi4s128k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k1N2 (i8Psi4s128k1dN2 x) x := by
  unfold i8Psi4s128k1N2 i8Psi4s128k1dN2
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (37 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-17))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-19))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, one] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons one [negOne, one, zero] hx).const_mul (40)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s128k1N3 (x : ℝ) : ℝ :=
    (-147 / 2) +
    (19) * hpl [negOne] x +
    (19) * hpl [zero] x +
    (-35) * hpl [one] x +
    (18) * hpl [negOne, one] x +
    (18) * hpl [zero, one] x +
    (18) * hpl [one, negOne] x +
    (18) * hpl [one, zero] x +
    (-20) * hpl [negOne, zero, one] x +
    (-20) * hpl [negOne, one, zero] x +
    (16) * hpl [one, negOne, one] x +
    (16) * hpl [one, one, negOne] x +
    (-16) * hpl [zero, one, negOne, one] x +
    (-16) * hpl [zero, one, one, negOne] x +
    (-16) * hpl [one, negOne, zero, one] x +
    (-16) * hpl [one, negOne, one, zero] x

/-- The derivative of `i8Psi4s128k1N3`. -/
noncomputable def i8Psi4s128k1dN3 (x : ℝ) : ℝ :=
    0 +
    (19) * (negOne.kernel x * hpl [] x) +
    (19) * (zero.kernel x * hpl [] x) +
    (-35) * (one.kernel x * hpl [] x) +
    (18) * (negOne.kernel x * hpl [one] x) +
    (18) * (zero.kernel x * hpl [one] x) +
    (18) * (one.kernel x * hpl [negOne] x) +
    (18) * (one.kernel x * hpl [zero] x) +
    (-20) * (negOne.kernel x * hpl [zero, one] x) +
    (-20) * (negOne.kernel x * hpl [one, zero] x) +
    (16) * (one.kernel x * hpl [negOne, one] x) +
    (16) * (one.kernel x * hpl [one, negOne] x) +
    (-16) * (zero.kernel x * hpl [one, negOne, one] x) +
    (-16) * (zero.kernel x * hpl [one, one, negOne] x) +
    (-16) * (one.kernel x * hpl [negOne, zero, one] x) +
    (-16) * (one.kernel x * hpl [negOne, one, zero] x)

theorem hasDerivAt_i8Psi4s128k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k1N3 (i8Psi4s128k1dN3 x) x := by
  unfold i8Psi4s128k1N3 i8Psi4s128k1dN3
  exact ((((((((((((((((hasDerivAt_const x (-147 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (19))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (19))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-35))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, one, zero] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s128k1N4 (x : ℝ) : ℝ :=
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
    (2) * hpl [one, negOne, one] x +
    (2) * hpl [one, one, negOne] x +
    (-4) * hpl [zero, one, negOne, one] x +
    (-4) * hpl [zero, one, one, negOne] x +
    (-4) * hpl [one, negOne, zero, one] x +
    (-4) * hpl [one, negOne, one, zero] x

/-- The derivative of `i8Psi4s128k1N4`. -/
noncomputable def i8Psi4s128k1dN4 (x : ℝ) : ℝ :=
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
    (2) * (one.kernel x * hpl [negOne, one] x) +
    (2) * (one.kernel x * hpl [one, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, negOne, one] x) +
    (-4) * (zero.kernel x * hpl [one, one, negOne] x) +
    (-4) * (one.kernel x * hpl [negOne, zero, one] x) +
    (-4) * (one.kernel x * hpl [negOne, one, zero] x)

theorem hasDerivAt_i8Psi4s128k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k1N4 (i8Psi4s128k1dN4 x) x := by
  unfold i8Psi4s128k1N4 i8Psi4s128k1dN4
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
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, one, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽128⁾` with constant coefficients. -/
noncomputable def i8Psi4s128k1W (x : ℝ) : ℝ :=
    (2) * hpl [zero, negOne] x +
    (18) * hpl [zero, negOne, one] x +
    (4) * hpl [zero, zero, one] x +
    (18) * hpl [zero, one, negOne] x +
    (4) * hpl [zero, one, zero] x +
    (20) * hpl [zero, negOne, zero, one] x +
    (20) * hpl [zero, negOne, one, zero] x

/-- The derivative of `i8Psi4s128k1W`. -/
noncomputable def i8Psi4s128k1dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [negOne] x) +
    (18) * (zero.kernel x * hpl [negOne, one] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (18) * (zero.kernel x * hpl [one, negOne] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (20) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (20) * (zero.kernel x * hpl [negOne, one, zero] x)

theorem hasDerivAt_i8Psi4s128k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k1W (i8Psi4s128k1dW x) x := by
  unfold i8Psi4s128k1W i8Psi4s128k1dW
  exact ((((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (20)))

/-- Chunk 1 of the piece `Ψ₄⁽128⁾`. -/
noncomputable def i8Psi4s128k1 (x : ℝ) : ℝ :=
  (i8Psi4s128k1N0 x + x * i8Psi4s128k1N1 x + x ^ 2 * i8Psi4s128k1N2 x + x ^ 3 * i8Psi4s128k1N3 x +
    x ^ 4 * i8Psi4s128k1N4 x) / x ^ 2 + i8Psi4s128k1W x

/-- The derivative of `i8Psi4s128k1`. -/
noncomputable def i8Psi4s128k1D (x : ℝ) : ℝ :=
  ((i8Psi4s128k1dN0 x + (i8Psi4s128k1N1 x + x * i8Psi4s128k1dN1 x) + (2 * x * i8Psi4s128k1N2 x +
    x ^ 2 * i8Psi4s128k1dN2 x) + (3 * x ^ 2 * i8Psi4s128k1N3 x + x ^ 3 * i8Psi4s128k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s128k1N4 x + x ^ 4 * i8Psi4s128k1dN4 x)) * x ^ 2 - (i8Psi4s128k1N0 x +
    x * i8Psi4s128k1N1 x + x ^ 2 * i8Psi4s128k1N2 x + x ^ 3 * i8Psi4s128k1N3 x +
    x ^ 4 * i8Psi4s128k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s128k1dW x

theorem hasDerivAt_i8Psi4s128k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k1 (i8Psi4s128k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s128k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s128k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s128k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s128k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s128k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s128k1W hx)
  unfold i8Psi4s128k1
  refine e.congr_deriv ?_
  unfold i8Psi4s128k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽128⁾` over words. -/
noncomputable def i8P4w128k1 (x : ℝ) : ℝ :=
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [zero, one, negOne, one] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [zero, one, one, negOne] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [one, negOne, zero, one] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [one, negOne, one, zero] x

theorem i8Psi4s128k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s128k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w128k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s128k1D i8Psi4s128k1N0 i8Psi4s128k1N1 i8Psi4s128k1N2 i8Psi4s128k1N3 i8Psi4s128k1N4
    i8Psi4s128k1dN0 i8Psi4s128k1dN1 i8Psi4s128k1dN2 i8Psi4s128k1dN3 i8Psi4s128k1dN4 i8Psi4s128k1dW
    i8P4w128k1
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, zero, one] x = v0 at *
  generalize hpl [zero, negOne, one, zero] x = v1 at *
  generalize hpl [zero, one, negOne, one] x = v2 at *
  generalize hpl [zero, one, one, negOne] x = v3 at *
  generalize hpl [one, negOne, zero, one] x = v4 at *
  generalize hpl [one, negOne, one, zero] x = v5 at *
  generalize hpl [negOne, zero, one] x = v6 at *
  generalize hpl [negOne, one, zero] x = v7 at *
  generalize hpl [zero, negOne, one] x = v8 at *
  generalize hpl [zero, zero, one] x = v9 at *
  generalize hpl [zero, one, negOne] x = v10 at *
  generalize hpl [zero, one, zero] x = v11 at *
  generalize hpl [one, negOne, one] x = v12 at *
  generalize hpl [one, one, negOne] x = v13 at *
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

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s128k2N0 (x : ℝ) : ℝ :=
    (-4) * hpl [one, zero, negOne, one] x +
    (-4) * hpl [one, zero, one, negOne] x +
    (-4) * hpl [one, one, negOne, zero] x +
    (-4) * hpl [one, one, zero, negOne] x

/-- The derivative of `i8Psi4s128k2N0`. -/
noncomputable def i8Psi4s128k2dN0 (x : ℝ) : ℝ :=
    (-4) * (one.kernel x * hpl [zero, negOne, one] x) +
    (-4) * (one.kernel x * hpl [zero, one, negOne] x) +
    (-4) * (one.kernel x * hpl [one, negOne, zero] x) +
    (-4) * (one.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s128k2N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k2N0 (i8Psi4s128k2dN0 x) x := by
  unfold i8Psi4s128k2N0 i8Psi4s128k2dN0
  exact (((((hasDerivAt_hpl_cons one [zero, negOne, one] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons one [zero, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, zero, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s128k2N1 (x : ℝ) : ℝ :=
    (-4) * hpl [negOne, one] x +
    (-4) * hpl [one, negOne] x +
    (-4) * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, one, negOne] x +
    (-4) * hpl [one, negOne, zero] x +
    (-4) * hpl [one, zero, negOne] x +
    (-16) * hpl [one, zero, negOne, one] x +
    (-16) * hpl [one, zero, one, negOne] x +
    (-16) * hpl [one, one, negOne, zero] x +
    (-16) * hpl [one, one, zero, negOne] x

/-- The derivative of `i8Psi4s128k2N1`. -/
noncomputable def i8Psi4s128k2dN1 (x : ℝ) : ℝ :=
    (-4) * (negOne.kernel x * hpl [one] x) +
    (-4) * (one.kernel x * hpl [negOne] x) +
    (-4) * (zero.kernel x * hpl [negOne, one] x) +
    (-4) * (zero.kernel x * hpl [one, negOne] x) +
    (-4) * (one.kernel x * hpl [negOne, zero] x) +
    (-4) * (one.kernel x * hpl [zero, negOne] x) +
    (-16) * (one.kernel x * hpl [zero, negOne, one] x) +
    (-16) * (one.kernel x * hpl [zero, one, negOne] x) +
    (-16) * (one.kernel x * hpl [one, negOne, zero] x) +
    (-16) * (one.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s128k2N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k2N1 (i8Psi4s128k2dN1 x) x := by
  unfold i8Psi4s128k2N1 i8Psi4s128k2dN1
  exact (((((((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [one, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [one, zero, negOne] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s128k2N2 (x : ℝ) : ℝ :=
    (42) * hpl [negOne] x +
    (39 / 2) * hpl [one] x +
    (-21) * hpl [negOne, zero] x +
    (15) * hpl [negOne, one] x +
    (4) * hpl [zero, negOne] x +
    (-17) * hpl [one, negOne] x +
    (26) * hpl [one, negOne, zero] x +
    (26) * hpl [one, zero, negOne] x +
    (40) * hpl [one, zero, negOne, one] x +
    (40) * hpl [one, zero, one, negOne] x +
    (40) * hpl [one, one, negOne, zero] x +
    (40) * hpl [one, one, zero, negOne] x

/-- The derivative of `i8Psi4s128k2N2`. -/
noncomputable def i8Psi4s128k2dN2 (x : ℝ) : ℝ :=
    (42) * (negOne.kernel x * hpl [] x) +
    (39 / 2) * (one.kernel x * hpl [] x) +
    (-21) * (negOne.kernel x * hpl [zero] x) +
    (15) * (negOne.kernel x * hpl [one] x) +
    (4) * (zero.kernel x * hpl [negOne] x) +
    (-17) * (one.kernel x * hpl [negOne] x) +
    (26) * (one.kernel x * hpl [negOne, zero] x) +
    (26) * (one.kernel x * hpl [zero, negOne] x) +
    (40) * (one.kernel x * hpl [zero, negOne, one] x) +
    (40) * (one.kernel x * hpl [zero, one, negOne] x) +
    (40) * (one.kernel x * hpl [one, negOne, zero] x) +
    (40) * (one.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s128k2N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k2N2 (i8Psi4s128k2dN2 x) x := by
  unfold i8Psi4s128k2N2 i8Psi4s128k2dN2
  exact (((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (42)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (39 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-21))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-17))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (26))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (26))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, one] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons one [zero, one, negOne] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons one [one, negOne, zero] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons one [one, zero, negOne] hx).const_mul (40)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s128k2N3 (x : ℝ) : ℝ :=
    (-165 / 2) +
    (43) * hpl [negOne] x +
    (21) * hpl [zero] x +
    (-19) * hpl [one] x +
    (-22) * hpl [negOne, zero] x +
    (20) * hpl [negOne, one] x +
    (-22) * hpl [zero, negOne] x +
    (20) * hpl [one, negOne] x +
    (-20) * hpl [zero, negOne, one] x +
    (-20) * hpl [zero, one, negOne] x +
    (-20) * hpl [one, negOne, zero] x +
    (-20) * hpl [one, zero, negOne] x +
    (-16) * hpl [one, zero, negOne, one] x +
    (-16) * hpl [one, zero, one, negOne] x +
    (-16) * hpl [one, one, negOne, zero] x +
    (-16) * hpl [one, one, zero, negOne] x

/-- The derivative of `i8Psi4s128k2N3`. -/
noncomputable def i8Psi4s128k2dN3 (x : ℝ) : ℝ :=
    0 +
    (43) * (negOne.kernel x * hpl [] x) +
    (21) * (zero.kernel x * hpl [] x) +
    (-19) * (one.kernel x * hpl [] x) +
    (-22) * (negOne.kernel x * hpl [zero] x) +
    (20) * (negOne.kernel x * hpl [one] x) +
    (-22) * (zero.kernel x * hpl [negOne] x) +
    (20) * (one.kernel x * hpl [negOne] x) +
    (-20) * (zero.kernel x * hpl [negOne, one] x) +
    (-20) * (zero.kernel x * hpl [one, negOne] x) +
    (-20) * (one.kernel x * hpl [negOne, zero] x) +
    (-20) * (one.kernel x * hpl [zero, negOne] x) +
    (-16) * (one.kernel x * hpl [zero, negOne, one] x) +
    (-16) * (one.kernel x * hpl [zero, one, negOne] x) +
    (-16) * (one.kernel x * hpl [one, negOne, zero] x) +
    (-16) * (one.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s128k2N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k2N3 (i8Psi4s128k2dN3 x) x := by
  unfold i8Psi4s128k2N3 i8Psi4s128k2dN3
  exact ((((((((((((((((hasDerivAt_const x (-165 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (43))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (21))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-19))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [one, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [one, zero, negOne] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽128⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s128k2N4 (x : ℝ) : ℝ :=
    (-1) +
    (1) * hpl [negOne] x +
    (1 / 2) * hpl [zero] x +
    (-1 / 2) * hpl [one] x +
    (-1) * hpl [negOne, zero] x +
    (1) * hpl [negOne, one] x +
    (-1) * hpl [zero, negOne] x +
    (1) * hpl [one, negOne] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, one, negOne] x +
    (-2) * hpl [one, negOne, zero] x +
    (-2) * hpl [one, zero, negOne] x +
    (-4) * hpl [one, zero, negOne, one] x +
    (-4) * hpl [one, zero, one, negOne] x +
    (-4) * hpl [one, one, negOne, zero] x +
    (-4) * hpl [one, one, zero, negOne] x

/-- The derivative of `i8Psi4s128k2N4`. -/
noncomputable def i8Psi4s128k2dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x) +
    (-4) * (one.kernel x * hpl [zero, negOne, one] x) +
    (-4) * (one.kernel x * hpl [zero, one, negOne] x) +
    (-4) * (one.kernel x * hpl [one, negOne, zero] x) +
    (-4) * (one.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s128k2N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k2N4 (i8Psi4s128k2dN4 x) x := by
  unfold i8Psi4s128k2N4 i8Psi4s128k2dN4
  exact ((((((((((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, zero, negOne] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽128⁾` with constant coefficients. -/
noncomputable def i8Psi4s128k2W (x : ℝ) : ℝ :=
    (4) * hpl [zero, one] x +
    (4) * hpl [zero, negOne, zero] x +
    (4) * hpl [zero, zero, negOne] x +
    (20) * hpl [zero, zero, negOne, one] x +
    (20) * hpl [zero, zero, one, negOne] x +
    (20) * hpl [zero, one, negOne, zero] x +
    (20) * hpl [zero, one, zero, negOne] x

/-- The derivative of `i8Psi4s128k2W`. -/
noncomputable def i8Psi4s128k2dW (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [one] x) +
    (4) * (zero.kernel x * hpl [negOne, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne] x) +
    (20) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (20) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (20) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (20) * (zero.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s128k2W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k2W (i8Psi4s128k2dW x) x := by
  unfold i8Psi4s128k2W i8Psi4s128k2dW
  exact ((((((((hasDerivAt_hpl_cons zero [one] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (20)))

/-- Chunk 2 of the piece `Ψ₄⁽128⁾`. -/
noncomputable def i8Psi4s128k2 (x : ℝ) : ℝ :=
  (i8Psi4s128k2N0 x + x * i8Psi4s128k2N1 x + x ^ 2 * i8Psi4s128k2N2 x + x ^ 3 * i8Psi4s128k2N3 x +
    x ^ 4 * i8Psi4s128k2N4 x) / x ^ 2 + i8Psi4s128k2W x

/-- The derivative of `i8Psi4s128k2`. -/
noncomputable def i8Psi4s128k2D (x : ℝ) : ℝ :=
  ((i8Psi4s128k2dN0 x + (i8Psi4s128k2N1 x + x * i8Psi4s128k2dN1 x) + (2 * x * i8Psi4s128k2N2 x +
    x ^ 2 * i8Psi4s128k2dN2 x) + (3 * x ^ 2 * i8Psi4s128k2N3 x + x ^ 3 * i8Psi4s128k2dN3 x) +
    (4 * x ^ 3 * i8Psi4s128k2N4 x + x ^ 4 * i8Psi4s128k2dN4 x)) * x ^ 2 - (i8Psi4s128k2N0 x +
    x * i8Psi4s128k2N1 x + x ^ 2 * i8Psi4s128k2N2 x + x ^ 3 * i8Psi4s128k2N3 x +
    x ^ 4 * i8Psi4s128k2N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s128k2dW x

theorem hasDerivAt_i8Psi4s128k2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128k2 (i8Psi4s128k2D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s128k2N0 hx).add (X.mul (hasDerivAt_i8Psi4s128k2N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s128k2N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s128k2N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s128k2N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s128k2W hx)
  unfold i8Psi4s128k2
  refine e.congr_deriv ?_
  unfold i8Psi4s128k2D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 2 of `p₄⁽128⁾` over words. -/
noncomputable def i8P4w128k2 (x : ℝ) : ℝ :=
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [one, zero, negOne, one] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [one, zero, one, negOne] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [one, one, negOne, zero] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [one, one, zero, negOne] x

theorem i8Psi4s128k2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s128k2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w128k2 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s128k2D i8Psi4s128k2N0 i8Psi4s128k2N1 i8Psi4s128k2N2 i8Psi4s128k2N3 i8Psi4s128k2N4
    i8Psi4s128k2dN0 i8Psi4s128k2dN1 i8Psi4s128k2dN2 i8Psi4s128k2dN3 i8Psi4s128k2dN4 i8Psi4s128k2dW
    i8P4w128k2
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, zero, negOne, one] x = v0 at *
  generalize hpl [zero, zero, one, negOne] x = v1 at *
  generalize hpl [zero, one, negOne, zero] x = v2 at *
  generalize hpl [zero, one, zero, negOne] x = v3 at *
  generalize hpl [one, zero, negOne, one] x = v4 at *
  generalize hpl [one, zero, one, negOne] x = v5 at *
  generalize hpl [one, one, negOne, zero] x = v6 at *
  generalize hpl [one, one, zero, negOne] x = v7 at *
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

/-- The piece `Ψ₄⁽128⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s128 (x : ℝ) : ℝ :=
  i8Psi4s128k0 x + i8Psi4s128k1 x + i8Psi4s128k2 x

/-- The derivative of `Ψ₄⁽128⁾`. -/
noncomputable def i8Psi4s128D (x : ℝ) : ℝ :=
  i8Psi4s128k0D x + i8Psi4s128k1D x + i8Psi4s128k2D x

theorem hasDerivAt_i8Psi4s128 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s128 (i8Psi4s128D x) x := by
  unfold i8Psi4s128 i8Psi4s128D
  exact (((hasDerivAt_i8Psi4s128k0 hx).add (hasDerivAt_i8Psi4s128k1 hx)).add
    (hasDerivAt_i8Psi4s128k2 hx))

/-- The sub-piece 128 of `p₄` in `ξ`: from `t B1 A1 (-λ)^2/2!`, the term with `log^2 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s128 (x : ℝ) : ℝ :=
  4 * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 2 * ((1 + x) / (1 - x) * (1 * hpl [zero] x)) * ((1 +
    x) / (1 - x) * (-hpl [negOne] x))

/-- `p₄⁽128⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w128 (x : ℝ) : ℝ :=
  i8P4w128k0 x + i8P4w128k1 x + i8P4w128k2 x

theorem i8P4s128_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s128 x = i8P4w128 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s128 i8P4w128 i8P4w128k0 i8P4w128k1 i8P4w128k2
  rw [i13_log_one_sub_eq hx]
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
  linear_combination (norm := skip) (((-4 - 8 * x -
    4 * x ^ 2) / (x)) * hpl [zero] x * hpl [negOne] x) * e0 + (((-8 - 16 * x -
    8 * x ^ 2) / (x)) * hpl [negOne] x) * e1 + (((-8 - 16 * x - 8 * x ^ 2) / (x))) * e2 + (((-8 -
    16 * x - 8 * x ^ 2) / (x))) * e3 + (((-8 - 16 * x - 8 * x ^ 2) / (x))) * e4
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

/-- **`(Ψ₄⁽128⁾)'(ξ) ξ' = p₄⁽128⁾`**, in terms of `ξ`. -/
theorem i8Psi4s128D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s128D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s128 x := by
  rw [i8P4s128_eq_w hx]
  unfold i8Psi4s128D i8P4w128
  rw [← i8Psi4s128k0D_mul hx, ← i8Psi4s128k1D_mul hx, ← i8Psi4s128k2D_mul hx]
  ring

end QED.ThreeLoopD
