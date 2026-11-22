/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P18

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 81 to 81

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s81`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s81D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s81`, `QED.ThreeLoopD.i8Psi4s81D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s81k0N0 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, zero, zero, one] x +
    (-2) * hpl [negOne, zero, one, zero] x +
    (-2) * hpl [negOne, one, zero, zero] x +
    (-2) * hpl [zero, negOne, zero, one] x

/-- The derivative of `i8Psi4s81k0N0`. -/
noncomputable def i8Psi4s81k0dN0 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-2) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-2) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, one] x)

theorem hasDerivAt_i8Psi4s81k0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k0N0 (i8Psi4s81k0dN0 x) x := by
  unfold i8Psi4s81k0N0 i8Psi4s81k0dN0
  exact ((((((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s81k0N1 (x : ℝ) : ℝ :=
    (-3) * hpl [one] x +
    (-3) * hpl [zero, one] x +
    (-2) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-2) * hpl [zero, zero, one] x +
    (-2) * hpl [zero, one, zero] x +
    (-2) * hpl [one, zero, zero] x +
    (-8) * hpl [negOne, zero, zero, one] x +
    (-8) * hpl [negOne, zero, one, zero] x +
    (-8) * hpl [negOne, one, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, one] x

/-- The derivative of `i8Psi4s81k0N1`. -/
noncomputable def i8Psi4s81k0dN1 (x : ℝ) : ℝ :=
    (-3) * (one.kernel x * hpl [] x) +
    (-3) * (zero.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (zero.kernel x * hpl [zero, one] x) +
    (-2) * (zero.kernel x * hpl [one, zero] x) +
    (-2) * (one.kernel x * hpl [zero, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-8) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-8) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, one] x)

theorem hasDerivAt_i8Psi4s81k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k0N1 (i8Psi4s81k0dN1 x) x := by
  unfold i8Psi4s81k0N1 i8Psi4s81k0dN1
  exact ((((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (-3)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s81k0N2 (x : ℝ) : ℝ :=
    (3) * hpl [zero] x +
    (-21 / 2) * hpl [one] x +
    (2) * hpl [zero, zero] x +
    (17 / 2) * hpl [one, zero] x +
    (7) * hpl [zero, zero, one] x +
    (-5) * hpl [one, zero, zero] x +
    (-12) * hpl [negOne, zero, zero, one] x +
    (-12) * hpl [negOne, zero, one, zero] x +
    (-12) * hpl [negOne, one, zero, zero] x

/-- The derivative of `i8Psi4s81k0N2`. -/
noncomputable def i8Psi4s81k0dN2 (x : ℝ) : ℝ :=
    (3) * (zero.kernel x * hpl [] x) +
    (-21 / 2) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (17 / 2) * (one.kernel x * hpl [zero] x) +
    (7) * (zero.kernel x * hpl [zero, one] x) +
    (-5) * (one.kernel x * hpl [zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-12) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-12) * (negOne.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s81k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k0N2 (i8Psi4s81k0dN2 x) x := by
  unfold i8Psi4s81k0N2 i8Psi4s81k0dN2
  exact ((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (3)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-21 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (17 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s81k0N3 (x : ℝ) : ℝ :=
    (27) +
    (-27 / 2) * hpl [zero] x +
    (13) * hpl [one] x +
    (7) * hpl [zero, zero] x +
    (-13) * hpl [zero, one] x +
    (-6) * hpl [one, zero] x +
    (8) * hpl [negOne, zero, one] x +
    (6) * hpl [zero, zero, one] x +
    (6) * hpl [zero, one, zero] x +
    (6) * hpl [one, zero, zero] x +
    (-8) * hpl [negOne, zero, zero, one] x +
    (-8) * hpl [negOne, zero, one, zero] x +
    (-8) * hpl [negOne, one, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, one] x

/-- The derivative of `i8Psi4s81k0N3`. -/
noncomputable def i8Psi4s81k0dN3 (x : ℝ) : ℝ :=
    0 +
    (-27 / 2) * (zero.kernel x * hpl [] x) +
    (13) * (one.kernel x * hpl [] x) +
    (7) * (zero.kernel x * hpl [zero] x) +
    (-13) * (zero.kernel x * hpl [one] x) +
    (-6) * (one.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [zero, one] x) +
    (6) * (zero.kernel x * hpl [zero, one] x) +
    (6) * (zero.kernel x * hpl [one, zero] x) +
    (6) * (one.kernel x * hpl [zero, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-8) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-8) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, one] x)

theorem hasDerivAt_i8Psi4s81k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k0N3 (i8Psi4s81k0dN3 x) x := by
  unfold i8Psi4s81k0N3 i8Psi4s81k0dN3
  exact ((((((((((((((hasDerivAt_const x (27)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-27 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (13))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-13))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s81k0N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 2) * hpl [zero] x +
    (1 / 2) * hpl [one] x +
    (1 / 2) * hpl [zero, zero] x +
    (-1) * hpl [zero, one] x +
    (-1 / 2) * hpl [one, zero] x +
    (1) * hpl [negOne, zero, one] x +
    (1) * hpl [zero, zero, one] x +
    (1) * hpl [zero, one, zero] x +
    (1) * hpl [one, zero, zero] x +
    (-2) * hpl [negOne, zero, zero, one] x +
    (-2) * hpl [negOne, zero, one, zero] x +
    (-2) * hpl [negOne, one, zero, zero] x +
    (-2) * hpl [zero, negOne, zero, one] x

/-- The derivative of `i8Psi4s81k0N4`. -/
noncomputable def i8Psi4s81k0dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (one.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [zero, one] x) +
    (1) * (zero.kernel x * hpl [zero, one] x) +
    (1) * (zero.kernel x * hpl [one, zero] x) +
    (1) * (one.kernel x * hpl [zero, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-2) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-2) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, one] x)

theorem hasDerivAt_i8Psi4s81k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k0N4 (i8Psi4s81k0dN4 x) x := by
  unfold i8Psi4s81k0N4 i8Psi4s81k0dN4
  exact ((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽81⁾` with constant coefficients. -/
noncomputable def i8Psi4s81k0W (x : ℝ) : ℝ :=
    (2) * hpl [zero, zero, zero] x +
    (6) * hpl [zero, zero, zero, one] x +
    (6) * hpl [zero, zero, one, zero] x +
    (6) * hpl [zero, one, zero, zero] x

/-- The derivative of `i8Psi4s81k0W`. -/
noncomputable def i8Psi4s81k0dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [zero, zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero, one] x) +
    (6) * (zero.kernel x * hpl [zero, one, zero] x) +
    (6) * (zero.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s81k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k0W (i8Psi4s81k0dW x) x := by
  unfold i8Psi4s81k0W i8Psi4s81k0dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (6)))

/-- Chunk 0 of the piece `Ψ₄⁽81⁾`. -/
noncomputable def i8Psi4s81k0 (x : ℝ) : ℝ :=
  (i8Psi4s81k0N0 x + x * i8Psi4s81k0N1 x + x ^ 2 * i8Psi4s81k0N2 x + x ^ 3 * i8Psi4s81k0N3 x +
    x ^ 4 * i8Psi4s81k0N4 x) / x ^ 2 + i8Psi4s81k0W x

/-- The derivative of `i8Psi4s81k0`. -/
noncomputable def i8Psi4s81k0D (x : ℝ) : ℝ :=
  ((i8Psi4s81k0dN0 x + (i8Psi4s81k0N1 x + x * i8Psi4s81k0dN1 x) + (2 * x * i8Psi4s81k0N2 x +
    x ^ 2 * i8Psi4s81k0dN2 x) + (3 * x ^ 2 * i8Psi4s81k0N3 x + x ^ 3 * i8Psi4s81k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s81k0N4 x + x ^ 4 * i8Psi4s81k0dN4 x)) * x ^ 2 - (i8Psi4s81k0N0 x +
    x * i8Psi4s81k0N1 x + x ^ 2 * i8Psi4s81k0N2 x + x ^ 3 * i8Psi4s81k0N3 x +
    x ^ 4 * i8Psi4s81k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s81k0dW x

theorem hasDerivAt_i8Psi4s81k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k0 (i8Psi4s81k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s81k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s81k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s81k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s81k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s81k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s81k0W hx)
  unfold i8Psi4s81k0
  refine e.congr_deriv ?_
  unfold i8Psi4s81k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽81⁾` over words. -/
noncomputable def i8P4w81k0 (x : ℝ) : ℝ :=
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [negOne, zero, zero, one] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [negOne, zero, one, zero] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [negOne, one, zero, zero] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [zero, negOne, zero, one] x

theorem i8Psi4s81k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s81k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w81k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s81k0D i8Psi4s81k0N0 i8Psi4s81k0N1 i8Psi4s81k0N2 i8Psi4s81k0N3 i8Psi4s81k0N4
    i8Psi4s81k0dN0 i8Psi4s81k0dN1 i8Psi4s81k0dN2 i8Psi4s81k0dN3 i8Psi4s81k0dN4 i8Psi4s81k0dW
    i8P4w81k0
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [negOne, zero, zero, one] x = v0 at *
  generalize hpl [negOne, zero, one, zero] x = v1 at *
  generalize hpl [negOne, one, zero, zero] x = v2 at *
  generalize hpl [zero, negOne, zero, one] x = v3 at *
  generalize hpl [zero, zero, zero, one] x = v4 at *
  generalize hpl [zero, zero, one, zero] x = v5 at *
  generalize hpl [zero, one, zero, zero] x = v6 at *
  generalize hpl [negOne, zero, one] x = v7 at *
  generalize hpl [zero, zero, zero] x = v8 at *
  generalize hpl [zero, zero, one] x = v9 at *
  generalize hpl [zero, one, zero] x = v10 at *
  generalize hpl [one, zero, zero] x = v11 at *
  generalize hpl [zero, zero] x = v12 at *
  generalize hpl [zero, one] x = v13 at *
  generalize hpl [one, zero] x = v14 at *
  generalize hpl [zero] x = v15 at *
  generalize hpl [one] x = v16 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s81k1N0 (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [negOne, one] x +
    (-1 / 2) * hpl [one, negOne] x +
    (-1) * hpl [negOne, one, zero] x +
    (-1) * hpl [zero, negOne, one] x +
    (-1) * hpl [zero, one, negOne] x +
    (-1) * hpl [one, negOne, zero] x +
    (-2) * hpl [zero, negOne, one, zero] x +
    (-2) * hpl [zero, zero, negOne, one] x +
    (-2) * hpl [zero, zero, one, negOne] x +
    (-2) * hpl [zero, one, negOne, zero] x

/-- The derivative of `i8Psi4s81k1N0`. -/
noncomputable def i8Psi4s81k1dN0 (x : ℝ) : ℝ :=
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [one, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, one] x) +
    (-1) * (zero.kernel x * hpl [one, negOne] x) +
    (-1) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (-2) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (-2) * (zero.kernel x * hpl [one, negOne, zero] x)

theorem hasDerivAt_i8Psi4s81k1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k1N0 (i8Psi4s81k1dN0 x) x := by
  unfold i8Psi4s81k1N0 i8Psi4s81k1dN0
  exact (((((((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s81k1N1 (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [negOne] x +
    (-1 / 2) * hpl [one] x +
    (-1) * hpl [negOne, zero] x +
    (-8) * hpl [negOne, one] x +
    (-8) * hpl [one, negOne] x +
    (-1) * hpl [one, zero] x +
    (-8) * hpl [negOne, one, zero] x +
    (-8) * hpl [zero, negOne, one] x +
    (-8) * hpl [zero, one, negOne] x +
    (-8) * hpl [one, negOne, zero] x +
    (-8) * hpl [zero, negOne, one, zero] x +
    (-8) * hpl [zero, zero, negOne, one] x +
    (-8) * hpl [zero, zero, one, negOne] x +
    (-8) * hpl [zero, one, negOne, zero] x

/-- The derivative of `i8Psi4s81k1N1`. -/
noncomputable def i8Psi4s81k1dN1 (x : ℝ) : ℝ :=
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [one] x) +
    (-8) * (one.kernel x * hpl [negOne] x) +
    (-1) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one] x) +
    (-8) * (zero.kernel x * hpl [one, negOne] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (-8) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, negOne, zero] x)

theorem hasDerivAt_i8Psi4s81k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k1N1 (i8Psi4s81k1dN1 x) x := by
  unfold i8Psi4s81k1N1 i8Psi4s81k1dN1
  exact (((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s81k1N2 (x : ℝ) : ℝ :=
    (-35 / 4) * hpl [negOne] x +
    (1) * hpl [zero] x +
    (-29 / 4) * hpl [one] x +
    (15 / 2) * hpl [negOne, zero] x +
    (-15) * hpl [negOne, one] x +
    (17) * hpl [one, negOne] x +
    (17 / 2) * hpl [one, zero] x

/-- The derivative of `i8Psi4s81k1N2`. -/
noncomputable def i8Psi4s81k1dN2 (x : ℝ) : ℝ :=
    (-35 / 4) * (negOne.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [] x) +
    (-29 / 4) * (one.kernel x * hpl [] x) +
    (15 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-15) * (negOne.kernel x * hpl [one] x) +
    (17) * (one.kernel x * hpl [negOne] x) +
    (17 / 2) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s81k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k1N2 (i8Psi4s81k1dN2 x) x := by
  unfold i8Psi4s81k1N2 i8Psi4s81k1dN2
  exact ((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-35 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-29 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (15 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-15))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (17))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (17 / 2)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s81k1N3 (x : ℝ) : ℝ :=
    (32) +
    (-17 / 2) * hpl [negOne] x +
    (-16) * hpl [zero] x +
    (15 / 2) * hpl [one] x +
    (9) * hpl [negOne, zero] x +
    (-8) * hpl [negOne, one] x +
    (-8) * hpl [one, negOne] x +
    (-7) * hpl [one, zero] x +
    (8) * hpl [negOne, one, zero] x +
    (8) * hpl [zero, negOne, one] x +
    (8) * hpl [zero, one, negOne] x +
    (8) * hpl [one, negOne, zero] x +
    (-8) * hpl [zero, negOne, one, zero] x +
    (-8) * hpl [zero, zero, negOne, one] x +
    (-8) * hpl [zero, zero, one, negOne] x +
    (-8) * hpl [zero, one, negOne, zero] x

/-- The derivative of `i8Psi4s81k1N3`. -/
noncomputable def i8Psi4s81k1dN3 (x : ℝ) : ℝ :=
    0 +
    (-17 / 2) * (negOne.kernel x * hpl [] x) +
    (-16) * (zero.kernel x * hpl [] x) +
    (15 / 2) * (one.kernel x * hpl [] x) +
    (9) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [one] x) +
    (-8) * (one.kernel x * hpl [negOne] x) +
    (-7) * (one.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, one] x) +
    (8) * (zero.kernel x * hpl [one, negOne] x) +
    (8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (-8) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, negOne, zero] x)

theorem hasDerivAt_i8Psi4s81k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k1N3 (i8Psi4s81k1dN3 x) x := by
  unfold i8Psi4s81k1N3 i8Psi4s81k1dN3
  exact ((((((((((((((((hasDerivAt_const x (32)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-17 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (15 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s81k1N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 4) * hpl [negOne] x +
    (-1 / 2) * hpl [zero] x +
    (1 / 4) * hpl [one] x +
    (1 / 2) * hpl [negOne, zero] x +
    (-1 / 2) * hpl [negOne, one] x +
    (-1 / 2) * hpl [one, negOne] x +
    (-1 / 2) * hpl [one, zero] x +
    (1) * hpl [negOne, one, zero] x +
    (1) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, negOne] x +
    (1) * hpl [one, negOne, zero] x +
    (-2) * hpl [zero, negOne, one, zero] x +
    (-2) * hpl [zero, zero, negOne, one] x +
    (-2) * hpl [zero, zero, one, negOne] x +
    (-2) * hpl [zero, one, negOne, zero] x

/-- The derivative of `i8Psi4s81k1N4`. -/
noncomputable def i8Psi4s81k1dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 4) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (1 / 4) * (one.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1 / 2) * (one.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [one, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (1) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (-2) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (-2) * (zero.kernel x * hpl [one, negOne, zero] x)

theorem hasDerivAt_i8Psi4s81k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k1N4 (i8Psi4s81k1dN4 x) x := by
  unfold i8Psi4s81k1N4 i8Psi4s81k1dN4
  exact ((((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽81⁾` with constant coefficients. -/
noncomputable def i8Psi4s81k1W (x : ℝ) : ℝ :=
    (17 / 2) * hpl [zero, negOne] x +
    (2) * hpl [zero, zero] x +
    (15 / 2) * hpl [zero, one] x +
    (9) * hpl [zero, negOne, zero] x +
    (7) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s81k1W`. -/
noncomputable def i8Psi4s81k1dW (x : ℝ) : ℝ :=
    (17 / 2) * (zero.kernel x * hpl [negOne] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (15 / 2) * (zero.kernel x * hpl [one] x) +
    (9) * (zero.kernel x * hpl [negOne, zero] x) +
    (7) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s81k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k1W (i8Psi4s81k1dW x) x := by
  unfold i8Psi4s81k1W i8Psi4s81k1dW
  exact ((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (17 / 2)).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (15 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (7)))

/-- Chunk 1 of the piece `Ψ₄⁽81⁾`. -/
noncomputable def i8Psi4s81k1 (x : ℝ) : ℝ :=
  (i8Psi4s81k1N0 x + x * i8Psi4s81k1N1 x + x ^ 2 * i8Psi4s81k1N2 x + x ^ 3 * i8Psi4s81k1N3 x +
    x ^ 4 * i8Psi4s81k1N4 x) / x ^ 2 + i8Psi4s81k1W x

/-- The derivative of `i8Psi4s81k1`. -/
noncomputable def i8Psi4s81k1D (x : ℝ) : ℝ :=
  ((i8Psi4s81k1dN0 x + (i8Psi4s81k1N1 x + x * i8Psi4s81k1dN1 x) + (2 * x * i8Psi4s81k1N2 x +
    x ^ 2 * i8Psi4s81k1dN2 x) + (3 * x ^ 2 * i8Psi4s81k1N3 x + x ^ 3 * i8Psi4s81k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s81k1N4 x + x ^ 4 * i8Psi4s81k1dN4 x)) * x ^ 2 - (i8Psi4s81k1N0 x +
    x * i8Psi4s81k1N1 x + x ^ 2 * i8Psi4s81k1N2 x + x ^ 3 * i8Psi4s81k1N3 x +
    x ^ 4 * i8Psi4s81k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s81k1dW x

theorem hasDerivAt_i8Psi4s81k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k1 (i8Psi4s81k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s81k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s81k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s81k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s81k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s81k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s81k1W hx)
  unfold i8Psi4s81k1
  refine e.congr_deriv ?_
  unfold i8Psi4s81k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽81⁾` over words. -/
noncomputable def i8P4w81k1 (x : ℝ) : ℝ :=
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [zero, negOne, one, zero] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [zero, zero, negOne, one] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [zero, zero, one, negOne] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [zero, one, negOne, zero] x

theorem i8Psi4s81k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s81k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w81k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s81k1D i8Psi4s81k1N0 i8Psi4s81k1N1 i8Psi4s81k1N2 i8Psi4s81k1N3 i8Psi4s81k1N4
    i8Psi4s81k1dN0 i8Psi4s81k1dN1 i8Psi4s81k1dN2 i8Psi4s81k1dN3 i8Psi4s81k1dN4 i8Psi4s81k1dW
    i8P4w81k1
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, one, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, one] x = v1 at *
  generalize hpl [zero, zero, one, negOne] x = v2 at *
  generalize hpl [zero, one, negOne, zero] x = v3 at *
  generalize hpl [negOne, one, zero] x = v4 at *
  generalize hpl [zero, negOne, zero] x = v5 at *
  generalize hpl [zero, negOne, one] x = v6 at *
  generalize hpl [zero, one, negOne] x = v7 at *
  generalize hpl [zero, one, zero] x = v8 at *
  generalize hpl [one, negOne, zero] x = v9 at *
  generalize hpl [negOne, zero] x = v10 at *
  generalize hpl [negOne, one] x = v11 at *
  generalize hpl [zero, negOne] x = v12 at *
  generalize hpl [zero, zero] x = v13 at *
  generalize hpl [zero, one] x = v14 at *
  generalize hpl [one, negOne] x = v15 at *
  generalize hpl [one, zero] x = v16 at *
  generalize hpl [negOne] x = v17 at *
  generalize hpl [zero] x = v18 at *
  generalize hpl [one] x = v19 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s81k2N0 (x : ℝ) : ℝ :=
    (-1) * hpl [one, zero, negOne] x +
    (-2) * hpl [zero, one, zero, negOne] x +
    (-2) * hpl [one, negOne, zero, zero] x +
    (-2) * hpl [one, zero, negOne, zero] x +
    (-2) * hpl [one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s81k2N0`. -/
noncomputable def i8Psi4s81k2dN0 (x : ℝ) : ℝ :=
    (-1) * (one.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s81k2N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k2N0 (i8Psi4s81k2dN0 x) x := by
  unfold i8Psi4s81k2N0 i8Psi4s81k2dN0
  exact ((((((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s81k2N1 (x : ℝ) : ℝ :=
    (-3) * hpl [negOne] x +
    (-2) * hpl [negOne, zero] x +
    (-3) * hpl [zero, negOne] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, zero, negOne] x +
    (-8) * hpl [one, zero, negOne] x +
    (-8) * hpl [zero, one, zero, negOne] x +
    (-8) * hpl [one, negOne, zero, zero] x +
    (-8) * hpl [one, zero, negOne, zero] x +
    (-8) * hpl [one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s81k2N1`. -/
noncomputable def i8Psi4s81k2dN1 (x : ℝ) : ℝ :=
    (-3) * (negOne.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (-3) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-8) * (one.kernel x * hpl [zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (-8) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne, zero] x) +
    (-8) * (one.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s81k2N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k2N1 (i8Psi4s81k2dN1 x) x := by
  unfold i8Psi4s81k2N1 i8Psi4s81k2dN1
  exact ((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s81k2N2 (x : ℝ) : ℝ :=
    (-43 / 2) * hpl [negOne] x +
    (3) * hpl [zero] x +
    (15 / 2) * hpl [negOne, zero] x +
    (2) * hpl [zero, zero] x +
    (-11) * hpl [negOne, zero, zero] x +
    (9) * hpl [zero, zero, negOne] x +
    (20) * hpl [one, negOne, zero, zero] x +
    (20) * hpl [one, zero, negOne, zero] x +
    (20) * hpl [one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s81k2N2`. -/
noncomputable def i8Psi4s81k2dN2 (x : ℝ) : ℝ :=
    (-43 / 2) * (negOne.kernel x * hpl [] x) +
    (3) * (zero.kernel x * hpl [] x) +
    (15 / 2) * (negOne.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (-11) * (negOne.kernel x * hpl [zero, zero] x) +
    (9) * (zero.kernel x * hpl [zero, negOne] x) +
    (20) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (20) * (one.kernel x * hpl [zero, negOne, zero] x) +
    (20) * (one.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s81k2N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k2N2 (i8Psi4s81k2dN2 x) x := by
  unfold i8Psi4s81k2N2 i8Psi4s81k2dN2
  exact ((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-43 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (15 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [zero, zero, negOne] hx).const_mul (20)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s81k2N3 (x : ℝ) : ℝ :=
    (37) +
    (-19) * hpl [negOne] x +
    (-37 / 2) * hpl [zero] x +
    (10) * hpl [negOne, zero] x +
    (19) * hpl [zero, negOne] x +
    (9) * hpl [zero, zero] x +
    (-10) * hpl [negOne, zero, zero] x +
    (-10) * hpl [zero, negOne, zero] x +
    (-10) * hpl [zero, zero, negOne] x +
    (8) * hpl [one, zero, negOne] x +
    (-8) * hpl [zero, one, zero, negOne] x +
    (-8) * hpl [one, negOne, zero, zero] x +
    (-8) * hpl [one, zero, negOne, zero] x +
    (-8) * hpl [one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s81k2N3`. -/
noncomputable def i8Psi4s81k2dN3 (x : ℝ) : ℝ :=
    0 +
    (-19) * (negOne.kernel x * hpl [] x) +
    (-37 / 2) * (zero.kernel x * hpl [] x) +
    (10) * (negOne.kernel x * hpl [zero] x) +
    (19) * (zero.kernel x * hpl [negOne] x) +
    (9) * (zero.kernel x * hpl [zero] x) +
    (-10) * (negOne.kernel x * hpl [zero, zero] x) +
    (-10) * (zero.kernel x * hpl [negOne, zero] x) +
    (-10) * (zero.kernel x * hpl [zero, negOne] x) +
    (8) * (one.kernel x * hpl [zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (-8) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne, zero] x) +
    (-8) * (one.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s81k2N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k2N3 (i8Psi4s81k2dN3 x) x := by
  unfold i8Psi4s81k2N3 i8Psi4s81k2dN3
  exact ((((((((((((((hasDerivAt_const x (37)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-19))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-37 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (19))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽81⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s81k2N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 2) * hpl [negOne] x +
    (-1 / 2) * hpl [zero] x +
    (1 / 2) * hpl [negOne, zero] x +
    (1) * hpl [zero, negOne] x +
    (1 / 2) * hpl [zero, zero] x +
    (-1) * hpl [negOne, zero, zero] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-1) * hpl [zero, zero, negOne] x +
    (1) * hpl [one, zero, negOne] x +
    (-2) * hpl [zero, one, zero, negOne] x +
    (-2) * hpl [one, negOne, zero, zero] x +
    (-2) * hpl [one, zero, negOne, zero] x +
    (-2) * hpl [one, zero, zero, negOne] x

/-- The derivative of `i8Psi4s81k2N4`. -/
noncomputable def i8Psi4s81k2dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne] x) +
    (1) * (one.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s81k2N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k2N4 (i8Psi4s81k2dN4 x) x := by
  unfold i8Psi4s81k2N4 i8Psi4s81k2dN4
  exact ((((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, zero, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽81⁾` with constant coefficients. -/
noncomputable def i8Psi4s81k2W (x : ℝ) : ℝ :=
    (2) * hpl [zero, zero, zero] x +
    (10) * hpl [zero, negOne, zero, zero] x +
    (10) * hpl [zero, zero, negOne, zero] x +
    (10) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s81k2W`. -/
noncomputable def i8Psi4s81k2dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [zero, zero] x) +
    (10) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (10) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (10) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s81k2W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k2W (i8Psi4s81k2dW x) x := by
  unfold i8Psi4s81k2W i8Psi4s81k2dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (10)))

/-- Chunk 2 of the piece `Ψ₄⁽81⁾`. -/
noncomputable def i8Psi4s81k2 (x : ℝ) : ℝ :=
  (i8Psi4s81k2N0 x + x * i8Psi4s81k2N1 x + x ^ 2 * i8Psi4s81k2N2 x + x ^ 3 * i8Psi4s81k2N3 x +
    x ^ 4 * i8Psi4s81k2N4 x) / x ^ 2 + i8Psi4s81k2W x

/-- The derivative of `i8Psi4s81k2`. -/
noncomputable def i8Psi4s81k2D (x : ℝ) : ℝ :=
  ((i8Psi4s81k2dN0 x + (i8Psi4s81k2N1 x + x * i8Psi4s81k2dN1 x) + (2 * x * i8Psi4s81k2N2 x +
    x ^ 2 * i8Psi4s81k2dN2 x) + (3 * x ^ 2 * i8Psi4s81k2N3 x + x ^ 3 * i8Psi4s81k2dN3 x) +
    (4 * x ^ 3 * i8Psi4s81k2N4 x + x ^ 4 * i8Psi4s81k2dN4 x)) * x ^ 2 - (i8Psi4s81k2N0 x +
    x * i8Psi4s81k2N1 x + x ^ 2 * i8Psi4s81k2N2 x + x ^ 3 * i8Psi4s81k2N3 x +
    x ^ 4 * i8Psi4s81k2N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s81k2dW x

theorem hasDerivAt_i8Psi4s81k2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81k2 (i8Psi4s81k2D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s81k2N0 hx).add (X.mul (hasDerivAt_i8Psi4s81k2N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s81k2N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s81k2N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s81k2N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s81k2W hx)
  unfold i8Psi4s81k2
  refine e.congr_deriv ?_
  unfold i8Psi4s81k2D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 2 of `p₄⁽81⁾` over words. -/
noncomputable def i8P4w81k2 (x : ℝ) : ℝ :=
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [zero, one, zero, negOne] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [one, negOne, zero, zero] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [one, zero, negOne, zero] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [one, zero, zero, negOne] x

theorem i8Psi4s81k2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s81k2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w81k2 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s81k2D i8Psi4s81k2N0 i8Psi4s81k2N1 i8Psi4s81k2N2 i8Psi4s81k2N3 i8Psi4s81k2N4
    i8Psi4s81k2dN0 i8Psi4s81k2dN1 i8Psi4s81k2dN2 i8Psi4s81k2dN3 i8Psi4s81k2dN4 i8Psi4s81k2dW
    i8P4w81k2
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, zero, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, zero] x = v1 at *
  generalize hpl [zero, zero, zero, negOne] x = v2 at *
  generalize hpl [zero, one, zero, negOne] x = v3 at *
  generalize hpl [one, negOne, zero, zero] x = v4 at *
  generalize hpl [one, zero, negOne, zero] x = v5 at *
  generalize hpl [one, zero, zero, negOne] x = v6 at *
  generalize hpl [negOne, zero, zero] x = v7 at *
  generalize hpl [zero, negOne, zero] x = v8 at *
  generalize hpl [zero, zero, negOne] x = v9 at *
  generalize hpl [zero, zero, zero] x = v10 at *
  generalize hpl [one, zero, negOne] x = v11 at *
  generalize hpl [negOne, zero] x = v12 at *
  generalize hpl [zero, negOne] x = v13 at *
  generalize hpl [zero, zero] x = v14 at *
  generalize hpl [negOne] x = v15 at *
  generalize hpl [zero] x = v16 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽81⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s81 (x : ℝ) : ℝ :=
  i8Psi4s81k0 x + i8Psi4s81k1 x + i8Psi4s81k2 x

/-- The derivative of `Ψ₄⁽81⁾`. -/
noncomputable def i8Psi4s81D (x : ℝ) : ℝ :=
  i8Psi4s81k0D x + i8Psi4s81k1D x + i8Psi4s81k2D x

theorem hasDerivAt_i8Psi4s81 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s81 (i8Psi4s81D x) x := by
  unfold i8Psi4s81 i8Psi4s81D
  exact (((hasDerivAt_i8Psi4s81k0 hx).add (hasDerivAt_i8Psi4s81k1 hx)).add (hasDerivAt_i8Psi4s81k2
    hx))

/-- The sub-piece 81 of `p₄` in `ξ`: from `t B2 A1 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s81 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 -
    x) * (1 * hpl [zero, zero] x)) * ((1 + x) / (1 - x) * (-hpl [negOne] x)))

/-- `p₄⁽81⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w81 (x : ℝ) : ℝ :=
  i8P4w81k0 x + i8P4w81k1 x + i8P4w81k2 x

theorem i8P4s81_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s81 x = i8P4w81 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s81 i8P4w81 i8P4w81k0 i8P4w81k1 i8P4w81k2
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [zero, zero] [one] hx
  have e1 := hpl_mul_hpl [negOne] [zero, zero, one] hx
  have e2 := hpl_mul_hpl [negOne] [zero, one, zero] hx
  have e3 := hpl_mul_hpl [negOne] [one, zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e3
  linear_combination (norm := skip) (((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [negOne] x) * e0 +
    (((-4 - 8 * x - 4 * x ^ 2) / (x))) * e1 + (((-4 - 8 * x - 4 * x ^ 2) / (x))) * e2 + (((-4 -
    8 * x - 4 * x ^ 2) / (x))) * e3
  field_simp
  generalize hpl [negOne, zero, zero, one] x = v0 at *
  generalize hpl [negOne, zero, one, zero] x = v1 at *
  generalize hpl [negOne, one, zero, zero] x = v2 at *
  generalize hpl [zero, negOne, zero, one] x = v3 at *
  generalize hpl [zero, negOne, one, zero] x = v4 at *
  generalize hpl [zero, zero, negOne, one] x = v5 at *
  generalize hpl [zero, zero, one, negOne] x = v6 at *
  generalize hpl [zero, one, negOne, zero] x = v7 at *
  generalize hpl [zero, one, zero, negOne] x = v8 at *
  generalize hpl [one, negOne, zero, zero] x = v9 at *
  generalize hpl [one, zero, negOne, zero] x = v10 at *
  generalize hpl [one, zero, zero, negOne] x = v11 at *
  generalize hpl [zero, zero, one] x = v12 at *
  generalize hpl [zero, one, zero] x = v13 at *
  generalize hpl [one, zero, zero] x = v14 at *
  generalize hpl [zero, zero] x = v15 at *
  generalize hpl [negOne] x = v16 at *
  generalize hpl [one] x = v17 at *
  ring

/-- **`(Ψ₄⁽81⁾)'(ξ) ξ' = p₄⁽81⁾`**, in terms of `ξ`. -/
theorem i8Psi4s81D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s81D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s81 x := by
  rw [i8P4s81_eq_w hx]
  unfold i8Psi4s81D i8P4w81
  rw [← i8Psi4s81k0D_mul hx, ← i8Psi4s81k1D_mul hx, ← i8Psi4s81k2D_mul hx]
  ring

end QED.ThreeLoopD
