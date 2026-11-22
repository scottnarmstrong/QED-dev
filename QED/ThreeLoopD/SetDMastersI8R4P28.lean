/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P27

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 108 to 108

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s108`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s108D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s108`, `QED.ThreeLoopD.i8Psi4s108D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s108k0N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s108k0N0`. -/
noncomputable def i8Psi4s108k0dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s108k0N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k0N0 (i8Psi4s108k0dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s108k0N1 (x : ℝ) : ℝ :=
    (32 - 2 / 3 * π ^ 2) * hpl [one] x +
    (32 - 2 / 3 * π ^ 2) * hpl [zero, one] x +
    (32 - 2 / 3 * π ^ 2) * hpl [one, zero] x +
    (16) * hpl [zero, zero, one] x +
    (16) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s108k0N1`. -/
noncomputable def i8Psi4s108k0dN1 (x : ℝ) : ℝ :=
    (32 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (32 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [one] x) +
    (32 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [zero] x) +
    (16) * (zero.kernel x * hpl [zero, one] x) +
    (16) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s108k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k0N1 (i8Psi4s108k0dN1 x) x := by
  unfold i8Psi4s108k0N1 i8Psi4s108k0dN1
  exact ((((((hasDerivAt_hpl_cons one [] hx).const_mul (32 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (32 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (32 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s108k0N2 (x : ℝ) : ℝ :=
    (-32 + 2 / 3 * π ^ 2) * hpl [zero] x +
    (38 + 17 / 6 * π ^ 2) * hpl [one] x +
    (-108 - 5 / 3 * π ^ 2) * hpl [one, zero] x +
    (-16 + 2 * π ^ 2) * hpl [zero, zero, one] x +
    (-16 + 2 * π ^ 2) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s108k0N2`. -/
noncomputable def i8Psi4s108k0dN2 (x : ℝ) : ℝ :=
    (-32 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (38 + 17 / 6 * π ^ 2) * (one.kernel x * hpl [] x) +
    (-108 - 5 / 3 * π ^ 2) * (one.kernel x * hpl [zero] x) +
    (-16 + 2 * π ^ 2) * (zero.kernel x * hpl [zero, one] x) +
    (-16 + 2 * π ^ 2) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s108k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k0N2 (i8Psi4s108k0dN2 x) x := by
  unfold i8Psi4s108k0N2 i8Psi4s108k0dN2
  exact ((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-32 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (38 + 17 / 6 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-108 - 5 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-16 + 2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-16 + 2 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s108k0N3 (x : ℝ) : ℝ :=
    (-146 - 9 / 2 * π ^ 2) +
    (76 + 7 / 3 * π ^ 2) * hpl [zero] x +
    (-64 - 2 * π ^ 2) * hpl [one] x +
    (64 + 2 * π ^ 2) * hpl [zero, one] x +
    (64 + 2 * π ^ 2) * hpl [one, zero] x +
    (-48) * hpl [zero, zero, one] x +
    (-48) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s108k0N3`. -/
noncomputable def i8Psi4s108k0dN3 (x : ℝ) : ℝ :=
    0 +
    (76 + 7 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-64 - 2 * π ^ 2) * (one.kernel x * hpl [] x) +
    (64 + 2 * π ^ 2) * (zero.kernel x * hpl [one] x) +
    (64 + 2 * π ^ 2) * (one.kernel x * hpl [zero] x) +
    (-48) * (zero.kernel x * hpl [zero, one] x) +
    (-48) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s108k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k0N3 (i8Psi4s108k0dN3 x) x := by
  unfold i8Psi4s108k0N3 i8Psi4s108k0dN3
  exact (((((((hasDerivAt_const x (-146 - 9 / 2 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (76 + 7 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-64 - 2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (64 + 2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (64 + 2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-48)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s108k0N4 (x : ℝ) : ℝ :=
    (-6 - π ^ 2 / 6) +
    (6 + π ^ 2 / 6) * hpl [zero] x +
    (-6 - π ^ 2 / 6) * hpl [one] x +
    (12 + π ^ 2 / 3) * hpl [zero, one] x +
    (12 + π ^ 2 / 3) * hpl [one, zero] x +
    (-8) * hpl [zero, zero, one] x +
    (-8) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s108k0N4`. -/
noncomputable def i8Psi4s108k0dN4 (x : ℝ) : ℝ :=
    0 +
    (6 + π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (-6 - π ^ 2 / 6) * (one.kernel x * hpl [] x) +
    (12 + π ^ 2 / 3) * (zero.kernel x * hpl [one] x) +
    (12 + π ^ 2 / 3) * (one.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [zero, one] x) +
    (-8) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s108k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k0N4 (i8Psi4s108k0dN4 x) x := by
  unfold i8Psi4s108k0N4 i8Psi4s108k0dN4
  exact (((((((hasDerivAt_const x (-6 - π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (6 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-6 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (12 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (12 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-8)))

/-- The part of `Ψ₄⁽108⁾` with constant coefficients. -/
noncomputable def i8Psi4s108k0W (x : ℝ) : ℝ :=
    (-32 + 2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (-48) * hpl [zero, zero, zero, one] x +
    (-48) * hpl [zero, zero, one, zero] x

/-- The derivative of `i8Psi4s108k0W`. -/
noncomputable def i8Psi4s108k0dW (x : ℝ) : ℝ :=
    (-32 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (-48) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-48) * (zero.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s108k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k0W (i8Psi4s108k0dW x) x := by
  unfold i8Psi4s108k0W i8Psi4s108k0dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-32 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-48)))

/-- Chunk 0 of the piece `Ψ₄⁽108⁾`. -/
noncomputable def i8Psi4s108k0 (x : ℝ) : ℝ :=
  (i8Psi4s108k0N0 x + x * i8Psi4s108k0N1 x + x ^ 2 * i8Psi4s108k0N2 x + x ^ 3 * i8Psi4s108k0N3 x +
    x ^ 4 * i8Psi4s108k0N4 x) / x ^ 2 + i8Psi4s108k0W x

/-- The derivative of `i8Psi4s108k0`. -/
noncomputable def i8Psi4s108k0D (x : ℝ) : ℝ :=
  ((i8Psi4s108k0dN0 x + (i8Psi4s108k0N1 x + x * i8Psi4s108k0dN1 x) + (2 * x * i8Psi4s108k0N2 x +
    x ^ 2 * i8Psi4s108k0dN2 x) + (3 * x ^ 2 * i8Psi4s108k0N3 x + x ^ 3 * i8Psi4s108k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s108k0N4 x + x ^ 4 * i8Psi4s108k0dN4 x)) * x ^ 2 - (i8Psi4s108k0N0 x +
    x * i8Psi4s108k0N1 x + x ^ 2 * i8Psi4s108k0N2 x + x ^ 3 * i8Psi4s108k0N3 x +
    x ^ 4 * i8Psi4s108k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s108k0dW x

theorem hasDerivAt_i8Psi4s108k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k0 (i8Psi4s108k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s108k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s108k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s108k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s108k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s108k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s108k0W hx)
  unfold i8Psi4s108k0
  refine e.congr_deriv ?_
  unfold i8Psi4s108k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽108⁾` over words. -/
noncomputable def i8P4w108k0 (x : ℝ) : ℝ :=
    ((16 - 16 * x ^ 2 - 2 / 3 * π ^ 2 - 4 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 2) / ((1 -
      x))) * hpl [zero, one] x +
    ((16 - 16 * x ^ 2 - 2 / 3 * π ^ 2 - 4 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 2) / ((1 -
      x))) * hpl [one, zero] x +
    ((16 + 16 * x ^ 2 + 32 * x) / ((1 - x))) * hpl [zero, zero, one] x +
    ((16 + 16 * x ^ 2 + 32 * x) / ((1 - x))) * hpl [zero, one, zero] x

theorem i8Psi4s108k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s108k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w108k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s108k0D i8Psi4s108k0N0 i8Psi4s108k0N1 i8Psi4s108k0N2 i8Psi4s108k0N3 i8Psi4s108k0N4
    i8Psi4s108k0dN0 i8Psi4s108k0dN1 i8Psi4s108k0dN2 i8Psi4s108k0dN3 i8Psi4s108k0dN4 i8Psi4s108k0dW
    i8P4w108k0
  simp only [kernel_zero, kernel_one, hpl_nil]
  generalize hpl [zero, zero, zero, one] x = v0 at *
  generalize hpl [zero, zero, one, zero] x = v1 at *
  generalize hpl [zero, zero, one] x = v2 at *
  generalize hpl [zero, one, zero] x = v3 at *
  generalize hpl [zero, zero] x = v4 at *
  generalize hpl [zero, one] x = v5 at *
  generalize hpl [one, zero] x = v6 at *
  generalize hpl [zero] x = v7 at *
  generalize hpl [one] x = v8 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s108k1N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s108k1N0`. -/
noncomputable def i8Psi4s108k1dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s108k1N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k1N0 (i8Psi4s108k1dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s108k1N1 (x : ℝ) : ℝ :=
    (16) * hpl [one, zero, zero] x +
    (-16) * hpl [negOne, zero, zero, one] x +
    (-16) * hpl [negOne, zero, one, zero] x +
    (-16) * hpl [negOne, one, zero, zero] x

/-- The derivative of `i8Psi4s108k1N1`. -/
noncomputable def i8Psi4s108k1dN1 (x : ℝ) : ℝ :=
    (16) * (one.kernel x * hpl [zero, zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-16) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-16) * (negOne.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s108k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k1N1 (i8Psi4s108k1dN1 x) x := by
  unfold i8Psi4s108k1N1 i8Psi4s108k1dN1
  exact (((((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s108k1N2 (x : ℝ) : ℝ :=
    (41) * hpl [one] x +
    (-42) * hpl [one, zero] x +
    (84) * hpl [one, zero, zero] x +
    (24) * hpl [negOne, zero, zero, one] x +
    (24) * hpl [negOne, zero, one, zero] x +
    (24) * hpl [negOne, one, zero, zero] x

/-- The derivative of `i8Psi4s108k1N2`. -/
noncomputable def i8Psi4s108k1dN2 (x : ℝ) : ℝ :=
    (41) * (one.kernel x * hpl [] x) +
    (-42) * (one.kernel x * hpl [zero] x) +
    (84) * (one.kernel x * hpl [zero, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (24) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (24) * (negOne.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s108k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k1N2 (i8Psi4s108k1dN2 x) x := by
  unfold i8Psi4s108k1N2 i8Psi4s108k1dN2
  exact (((((((hasDerivAt_hpl_cons one [] hx).const_mul (41)).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-42))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (84))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (24)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s108k1N3 (x : ℝ) : ℝ :=
    (-183) +
    (142) * hpl [zero] x +
    (-40) * hpl [one] x +
    (-100) * hpl [zero, zero] x +
    (40) * hpl [zero, one] x +
    (40) * hpl [one, zero] x +
    (-40) * hpl [zero, zero, one] x +
    (-40) * hpl [zero, one, zero] x +
    (-88) * hpl [one, zero, zero] x +
    (48) * hpl [negOne, zero, zero, one] x +
    (48) * hpl [negOne, zero, one, zero] x +
    (48) * hpl [negOne, one, zero, zero] x

/-- The derivative of `i8Psi4s108k1N3`. -/
noncomputable def i8Psi4s108k1dN3 (x : ℝ) : ℝ :=
    0 +
    (142) * (zero.kernel x * hpl [] x) +
    (-40) * (one.kernel x * hpl [] x) +
    (-100) * (zero.kernel x * hpl [zero] x) +
    (40) * (zero.kernel x * hpl [one] x) +
    (40) * (one.kernel x * hpl [zero] x) +
    (-40) * (zero.kernel x * hpl [zero, one] x) +
    (-40) * (zero.kernel x * hpl [one, zero] x) +
    (-88) * (one.kernel x * hpl [zero, zero] x) +
    (48) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (48) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (48) * (negOne.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s108k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k1N3 (i8Psi4s108k1dN3 x) x := by
  unfold i8Psi4s108k1N3 i8Psi4s108k1dN3
  exact ((((((((((((hasDerivAt_const x (-183)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (142))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-100))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-88))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (48)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s108k1N4 (x : ℝ) : ℝ :=
    (-5 / 2) +
    (4) * hpl [zero] x +
    (-1) * hpl [one] x +
    (-6) * hpl [zero, zero] x +
    (2) * hpl [zero, one] x +
    (2) * hpl [one, zero] x +
    (-4) * hpl [zero, zero, one] x +
    (-4) * hpl [zero, one, zero] x +
    (-12) * hpl [one, zero, zero] x +
    (8) * hpl [negOne, zero, zero, one] x +
    (8) * hpl [negOne, zero, one, zero] x +
    (8) * hpl [negOne, one, zero, zero] x

/-- The derivative of `i8Psi4s108k1N4`. -/
noncomputable def i8Psi4s108k1dN4 (x : ℝ) : ℝ :=
    0 +
    (4) * (zero.kernel x * hpl [] x) +
    (-1) * (one.kernel x * hpl [] x) +
    (-6) * (zero.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [zero, one] x) +
    (-4) * (zero.kernel x * hpl [one, zero] x) +
    (-12) * (one.kernel x * hpl [zero, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (8) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (8) * (negOne.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s108k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k1N4 (i8Psi4s108k1dN4 x) x := by
  unfold i8Psi4s108k1N4 i8Psi4s108k1dN4
  exact ((((((((((((hasDerivAt_const x (-5 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (8)))

/-- The part of `Ψ₄⁽108⁾` with constant coefficients. -/
noncomputable def i8Psi4s108k1W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, zero, zero] x +
    (16) * hpl [zero, zero, zero, one] x +
    (16) * hpl [zero, zero, one, zero] x +
    (-32) * hpl [zero, one, zero, zero] x +
    (48) * hpl [zero, negOne, zero, zero, one] x +
    (48) * hpl [zero, negOne, zero, one, zero] x +
    (48) * hpl [zero, negOne, one, zero, zero] x

/-- The derivative of `i8Psi4s108k1W`. -/
noncomputable def i8Psi4s108k1dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [zero, zero] x) +
    (16) * (zero.kernel x * hpl [zero, zero, one] x) +
    (16) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-32) * (zero.kernel x * hpl [one, zero, zero] x) +
    (48) * (zero.kernel x * hpl [negOne, zero, zero, one] x) +
    (48) * (zero.kernel x * hpl [negOne, zero, one, zero] x) +
    (48) * (zero.kernel x * hpl [negOne, one, zero, zero] x)

theorem hasDerivAt_i8Psi4s108k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k1W (i8Psi4s108k1dW x) x := by
  unfold i8Psi4s108k1W i8Psi4s108k1dW
  exact ((((((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, one] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero, zero] hx).const_mul (48)))

/-- Chunk 1 of the piece `Ψ₄⁽108⁾`. -/
noncomputable def i8Psi4s108k1 (x : ℝ) : ℝ :=
  (i8Psi4s108k1N0 x + x * i8Psi4s108k1N1 x + x ^ 2 * i8Psi4s108k1N2 x + x ^ 3 * i8Psi4s108k1N3 x +
    x ^ 4 * i8Psi4s108k1N4 x) / x ^ 2 + i8Psi4s108k1W x

/-- The derivative of `i8Psi4s108k1`. -/
noncomputable def i8Psi4s108k1D (x : ℝ) : ℝ :=
  ((i8Psi4s108k1dN0 x + (i8Psi4s108k1N1 x + x * i8Psi4s108k1dN1 x) + (2 * x * i8Psi4s108k1N2 x +
    x ^ 2 * i8Psi4s108k1dN2 x) + (3 * x ^ 2 * i8Psi4s108k1N3 x + x ^ 3 * i8Psi4s108k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s108k1N4 x + x ^ 4 * i8Psi4s108k1dN4 x)) * x ^ 2 - (i8Psi4s108k1N0 x +
    x * i8Psi4s108k1N1 x + x ^ 2 * i8Psi4s108k1N2 x + x ^ 3 * i8Psi4s108k1N3 x +
    x ^ 4 * i8Psi4s108k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s108k1dW x

theorem hasDerivAt_i8Psi4s108k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k1 (i8Psi4s108k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s108k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s108k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s108k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s108k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s108k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s108k1W hx)
  unfold i8Psi4s108k1
  refine e.congr_deriv ?_
  unfold i8Psi4s108k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽108⁾` over words. -/
noncomputable def i8P4w108k1 (x : ℝ) : ℝ :=
    ((16 + 16 * x ^ 2 + 32 * x) / ((1 - x))) * hpl [one, zero, zero] x +
    ((-16 - 32 * x - 16 * x ^ 2) / ((1 - x))) * hpl [negOne, zero, zero, one] x +
    ((-16 - 32 * x - 16 * x ^ 2) / ((1 - x))) * hpl [negOne, zero, one, zero] x +
    ((-16 - 32 * x - 16 * x ^ 2) / ((1 - x))) * hpl [negOne, one, zero, zero] x

theorem i8Psi4s108k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s108k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w108k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s108k1D i8Psi4s108k1N0 i8Psi4s108k1N1 i8Psi4s108k1N2 i8Psi4s108k1N3 i8Psi4s108k1N4
    i8Psi4s108k1dN0 i8Psi4s108k1dN1 i8Psi4s108k1dN2 i8Psi4s108k1dN3 i8Psi4s108k1dN4 i8Psi4s108k1dW
    i8P4w108k1
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, zero, zero, one] x = v0 at *
  generalize hpl [zero, negOne, zero, one, zero] x = v1 at *
  generalize hpl [zero, negOne, one, zero, zero] x = v2 at *
  generalize hpl [negOne, zero, zero, one] x = v3 at *
  generalize hpl [negOne, zero, one, zero] x = v4 at *
  generalize hpl [negOne, one, zero, zero] x = v5 at *
  generalize hpl [zero, zero, zero, one] x = v6 at *
  generalize hpl [zero, zero, one, zero] x = v7 at *
  generalize hpl [zero, one, zero, zero] x = v8 at *
  generalize hpl [zero, zero, zero] x = v9 at *
  generalize hpl [zero, zero, one] x = v10 at *
  generalize hpl [zero, one, zero] x = v11 at *
  generalize hpl [one, zero, zero] x = v12 at *
  generalize hpl [zero, zero] x = v13 at *
  generalize hpl [zero, one] x = v14 at *
  generalize hpl [one, zero] x = v15 at *
  generalize hpl [zero] x = v16 at *
  generalize hpl [one] x = v17 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s108k2N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s108k2N0`. -/
noncomputable def i8Psi4s108k2dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s108k2N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k2N0 (i8Psi4s108k2dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s108k2N1 (x : ℝ) : ℝ :=
    (12) * hpl [one] x +
    (12) * hpl [zero, one] x +
    (12) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (12) * hpl [zero, zero, one] x +
    (12) * hpl [zero, one, zero] x +
    (-8) * hpl [zero, negOne, zero, one] x +
    (-8) * hpl [zero, negOne, one, zero] x +
    (12) * hpl [zero, zero, zero, one] x +
    (12) * hpl [zero, zero, one, zero] x

/-- The derivative of `i8Psi4s108k2N1`. -/
noncomputable def i8Psi4s108k2dN1 (x : ℝ) : ℝ :=
    (12) * (one.kernel x * hpl [] x) +
    (12) * (zero.kernel x * hpl [one] x) +
    (12) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (12) * (zero.kernel x * hpl [zero, one] x) +
    (12) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (-8) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero, one] x) +
    (12) * (zero.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s108k2N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k2N1 (i8Psi4s108k2dN1 x) x := by
  unfold i8Psi4s108k2N1 i8Psi4s108k2dN1
  exact ((((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (12)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s108k2N2 (x : ℝ) : ℝ :=
    (-12) * hpl [zero] x +
    (-105 / 4) * hpl [one] x +
    (5 / 2) * hpl [one, zero] x +
    (-30) * hpl [negOne, zero, one] x +
    (-30) * hpl [negOne, one, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s108k2N2`. -/
noncomputable def i8Psi4s108k2dN2 (x : ℝ) : ℝ :=
    (-12) * (zero.kernel x * hpl [] x) +
    (-105 / 4) * (one.kernel x * hpl [] x) +
    (5 / 2) * (one.kernel x * hpl [zero] x) +
    (-30) * (negOne.kernel x * hpl [zero, one] x) +
    (-30) * (negOne.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s108k2N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k2N2 (i8Psi4s108k2dN2 x) x := by
  unfold i8Psi4s108k2N2 i8Psi4s108k2dN2
  exact ((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-12)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-105 / 4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s108k2N3 (x : ℝ) : ℝ :=
    (115 / 4) +
    (-29 / 2) * hpl [zero] x +
    (14) * hpl [one] x +
    (-14) * hpl [zero, one] x +
    (-14) * hpl [one, zero] x +
    (-24) * hpl [negOne, zero, one] x +
    (-24) * hpl [negOne, one, zero] x +
    (36) * hpl [zero, zero, one] x +
    (36) * hpl [zero, one, zero] x +
    (24) * hpl [zero, negOne, zero, one] x +
    (24) * hpl [zero, negOne, one, zero] x +
    (-36) * hpl [zero, zero, zero, one] x +
    (-36) * hpl [zero, zero, one, zero] x

/-- The derivative of `i8Psi4s108k2N3`. -/
noncomputable def i8Psi4s108k2dN3 (x : ℝ) : ℝ :=
    0 +
    (-29 / 2) * (zero.kernel x * hpl [] x) +
    (14) * (one.kernel x * hpl [] x) +
    (-14) * (zero.kernel x * hpl [one] x) +
    (-14) * (one.kernel x * hpl [zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, one] x) +
    (-24) * (negOne.kernel x * hpl [one, zero] x) +
    (36) * (zero.kernel x * hpl [zero, one] x) +
    (36) * (zero.kernel x * hpl [one, zero] x) +
    (24) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (24) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-36) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-36) * (zero.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s108k2N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k2N3 (i8Psi4s108k2dN3 x) x := by
  unfold i8Psi4s108k2N3 i8Psi4s108k2dN3
  exact (((((((((((((hasDerivAt_const x (115 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-29 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-36)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s108k2N4 (x : ℝ) : ℝ :=
    (1 / 4) +
    (-1 / 4) * hpl [zero] x +
    (1 / 4) * hpl [one] x +
    (-1 / 2) * hpl [zero, one] x +
    (-1 / 2) * hpl [one, zero] x +
    (-2) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, one, zero] x +
    (3) * hpl [zero, zero, one] x +
    (3) * hpl [zero, one, zero] x +
    (4) * hpl [zero, negOne, zero, one] x +
    (4) * hpl [zero, negOne, one, zero] x +
    (-6) * hpl [zero, zero, zero, one] x +
    (-6) * hpl [zero, zero, one, zero] x

/-- The derivative of `i8Psi4s108k2N4`. -/
noncomputable def i8Psi4s108k2dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 4) * (one.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x) +
    (3) * (zero.kernel x * hpl [zero, one] x) +
    (3) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (4) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-6) * (zero.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s108k2N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k2N4 (i8Psi4s108k2dN4 x) x := by
  unfold i8Psi4s108k2N4 i8Psi4s108k2dN4
  exact (((((((((((((hasDerivAt_const x (1 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-6)))

/-- The part of `Ψ₄⁽108⁾` with constant coefficients. -/
noncomputable def i8Psi4s108k2W (x : ℝ) : ℝ :=
    (-12) * hpl [zero, zero] x +
    (24) * hpl [zero, zero, negOne, zero, one] x +
    (24) * hpl [zero, zero, negOne, one, zero] x +
    (-36) * hpl [zero, zero, zero, zero, one] x +
    (-36) * hpl [zero, zero, zero, one, zero] x

/-- The derivative of `i8Psi4s108k2W`. -/
noncomputable def i8Psi4s108k2dW (x : ℝ) : ℝ :=
    (-12) * (zero.kernel x * hpl [zero] x) +
    (24) * (zero.kernel x * hpl [zero, negOne, zero, one] x) +
    (24) * (zero.kernel x * hpl [zero, negOne, one, zero] x) +
    (-36) * (zero.kernel x * hpl [zero, zero, zero, one] x) +
    (-36) * (zero.kernel x * hpl [zero, zero, one, zero] x)

theorem hasDerivAt_i8Psi4s108k2W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k2W (i8Psi4s108k2dW x) x := by
  unfold i8Psi4s108k2W i8Psi4s108k2dW
  exact ((((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-12)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, one] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one, zero] hx).const_mul (-36)))

/-- Chunk 2 of the piece `Ψ₄⁽108⁾`. -/
noncomputable def i8Psi4s108k2 (x : ℝ) : ℝ :=
  (i8Psi4s108k2N0 x + x * i8Psi4s108k2N1 x + x ^ 2 * i8Psi4s108k2N2 x + x ^ 3 * i8Psi4s108k2N3 x +
    x ^ 4 * i8Psi4s108k2N4 x) / x ^ 2 + i8Psi4s108k2W x

/-- The derivative of `i8Psi4s108k2`. -/
noncomputable def i8Psi4s108k2D (x : ℝ) : ℝ :=
  ((i8Psi4s108k2dN0 x + (i8Psi4s108k2N1 x + x * i8Psi4s108k2dN1 x) + (2 * x * i8Psi4s108k2N2 x +
    x ^ 2 * i8Psi4s108k2dN2 x) + (3 * x ^ 2 * i8Psi4s108k2N3 x + x ^ 3 * i8Psi4s108k2dN3 x) +
    (4 * x ^ 3 * i8Psi4s108k2N4 x + x ^ 4 * i8Psi4s108k2dN4 x)) * x ^ 2 - (i8Psi4s108k2N0 x +
    x * i8Psi4s108k2N1 x + x ^ 2 * i8Psi4s108k2N2 x + x ^ 3 * i8Psi4s108k2N3 x +
    x ^ 4 * i8Psi4s108k2N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s108k2dW x

theorem hasDerivAt_i8Psi4s108k2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k2 (i8Psi4s108k2D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s108k2N0 hx).add (X.mul (hasDerivAt_i8Psi4s108k2N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s108k2N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s108k2N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s108k2N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s108k2W hx)
  unfold i8Psi4s108k2
  refine e.congr_deriv ?_
  unfold i8Psi4s108k2D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 2 of `p₄⁽108⁾` over words. -/
noncomputable def i8P4w108k2 (x : ℝ) : ℝ :=
    ((-8 - 16 * x - 8 * x ^ 2) / ((1 - x))) * hpl [zero, negOne, zero, one] x +
    ((-8 - 16 * x - 8 * x ^ 2) / ((1 - x))) * hpl [zero, negOne, one, zero] x +
    ((12 + 12 * x ^ 2 + 24 * x) / ((1 - x))) * hpl [zero, zero, zero, one] x +
    ((12 + 12 * x ^ 2 + 24 * x) / ((1 - x))) * hpl [zero, zero, one, zero] x

theorem i8Psi4s108k2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s108k2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w108k2 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s108k2D i8Psi4s108k2N0 i8Psi4s108k2N1 i8Psi4s108k2N2 i8Psi4s108k2N3 i8Psi4s108k2N4
    i8Psi4s108k2dN0 i8Psi4s108k2dN1 i8Psi4s108k2dN2 i8Psi4s108k2dN3 i8Psi4s108k2dN4 i8Psi4s108k2dW
    i8P4w108k2
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, zero, negOne, zero, one] x = v0 at *
  generalize hpl [zero, zero, negOne, one, zero] x = v1 at *
  generalize hpl [zero, zero, zero, zero, one] x = v2 at *
  generalize hpl [zero, zero, zero, one, zero] x = v3 at *
  generalize hpl [zero, negOne, zero, one] x = v4 at *
  generalize hpl [zero, negOne, one, zero] x = v5 at *
  generalize hpl [zero, zero, zero, one] x = v6 at *
  generalize hpl [zero, zero, one, zero] x = v7 at *
  generalize hpl [negOne, zero, one] x = v8 at *
  generalize hpl [negOne, one, zero] x = v9 at *
  generalize hpl [zero, zero, one] x = v10 at *
  generalize hpl [zero, one, zero] x = v11 at *
  generalize hpl [zero, zero] x = v12 at *
  generalize hpl [zero, one] x = v13 at *
  generalize hpl [one, zero] x = v14 at *
  generalize hpl [zero] x = v15 at *
  generalize hpl [one] x = v16 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s108k3N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s108k3N0`. -/
noncomputable def i8Psi4s108k3dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s108k3N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k3N0 (i8Psi4s108k3dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s108k3N1 (x : ℝ) : ℝ :=
    (-8) * hpl [one, negOne, zero] x +
    (12) * hpl [one, zero, zero] x +
    (-8) * hpl [zero, one, negOne, zero] x +
    (12) * hpl [zero, one, zero, zero] x +
    (-16) * hpl [one, negOne, zero, zero] x +
    (-8) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s108k3N1`. -/
noncomputable def i8Psi4s108k3dN1 (x : ℝ) : ℝ :=
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (12) * (one.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (12) * (zero.kernel x * hpl [one, zero, zero] x) +
    (-16) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s108k3N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k3N1 (i8Psi4s108k3dN1 x) x := by
  unfold i8Psi4s108k3N1 i8Psi4s108k3dN1
  exact (((((((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s108k3N2 (x : ℝ) : ℝ :=
    (-52) * hpl [negOne, zero] x +
    (52) * hpl [negOne, zero, zero] x +
    (8) * hpl [zero, negOne, zero] x +
    (34) * hpl [one, negOne, zero] x +
    (-51) * hpl [one, zero, zero] x +
    (-40) * hpl [one, negOne, zero, zero] x +
    (-20) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s108k3N2`. -/
noncomputable def i8Psi4s108k3dN2 (x : ℝ) : ℝ :=
    (-52) * (negOne.kernel x * hpl [zero] x) +
    (52) * (negOne.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero] x) +
    (34) * (one.kernel x * hpl [negOne, zero] x) +
    (-51) * (one.kernel x * hpl [zero, zero] x) +
    (-40) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (-20) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s108k3N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k3N2 (i8Psi4s108k3dN2 x) x := by
  unfold i8Psi4s108k3N2 i8Psi4s108k3dN2
  exact ((((((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-52)).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (52))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (34))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-51))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-20)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s108k3N3 (x : ℝ) : ℝ :=
    (-65) +
    (65) * hpl [zero] x +
    (-54) * hpl [negOne, zero] x +
    (-13) * hpl [zero, zero] x +
    (56) * hpl [negOne, zero, zero] x +
    (28) * hpl [zero, negOne, zero] x +
    (-24) * hpl [one, negOne, zero] x +
    (36) * hpl [one, zero, zero] x +
    (24) * hpl [zero, one, negOne, zero] x +
    (-36) * hpl [zero, one, zero, zero] x +
    (48) * hpl [one, negOne, zero, zero] x +
    (24) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s108k3N3`. -/
noncomputable def i8Psi4s108k3dN3 (x : ℝ) : ℝ :=
    0 +
    (65) * (zero.kernel x * hpl [] x) +
    (-54) * (negOne.kernel x * hpl [zero] x) +
    (-13) * (zero.kernel x * hpl [zero] x) +
    (56) * (negOne.kernel x * hpl [zero, zero] x) +
    (28) * (zero.kernel x * hpl [negOne, zero] x) +
    (-24) * (one.kernel x * hpl [negOne, zero] x) +
    (36) * (one.kernel x * hpl [zero, zero] x) +
    (24) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-36) * (zero.kernel x * hpl [one, zero, zero] x) +
    (48) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (24) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s108k3N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k3N3 (i8Psi4s108k3dN3 x) x := by
  unfold i8Psi4s108k3N3 i8Psi4s108k3dN3
  exact ((((((((((((hasDerivAt_const x (-65)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (65))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-54))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-13))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (56))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (24)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s108k3N4 (x : ℝ) : ℝ :=
    (-5 / 8) +
    (5 / 4) * hpl [zero] x +
    (-2) * hpl [negOne, zero] x +
    (-1 / 2) * hpl [zero, zero] x +
    (4) * hpl [negOne, zero, zero] x +
    (2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [one, negOne, zero] x +
    (3) * hpl [one, zero, zero] x +
    (4) * hpl [zero, one, negOne, zero] x +
    (-6) * hpl [zero, one, zero, zero] x +
    (8) * hpl [one, negOne, zero, zero] x +
    (4) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s108k3N4`. -/
noncomputable def i8Psi4s108k3dN4 (x : ℝ) : ℝ :=
    0 +
    (5 / 4) * (zero.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (3) * (one.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [one, zero, zero] x) +
    (8) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (4) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s108k3N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k3N4 (i8Psi4s108k3dN4 x) x := by
  unfold i8Psi4s108k3N4 i8Psi4s108k3dN4
  exact ((((((((((((hasDerivAt_const x (-5 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (5 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽108⁾` with constant coefficients. -/
noncomputable def i8Psi4s108k3W (x : ℝ) : ℝ :=
    (-12) * hpl [zero, zero, zero] x +
    (16) * hpl [zero, negOne, zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x +
    (24) * hpl [zero, zero, one, negOne, zero] x +
    (-36) * hpl [zero, zero, one, zero, zero] x +
    (48) * hpl [zero, one, negOne, zero, zero] x +
    (24) * hpl [zero, one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s108k3W`. -/
noncomputable def i8Psi4s108k3dW (x : ℝ) : ℝ :=
    (-12) * (zero.kernel x * hpl [zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (24) * (zero.kernel x * hpl [zero, one, negOne, zero] x) +
    (-36) * (zero.kernel x * hpl [zero, one, zero, zero] x) +
    (48) * (zero.kernel x * hpl [one, negOne, zero, zero] x) +
    (24) * (zero.kernel x * hpl [one, zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s108k3W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k3W (i8Psi4s108k3dW x) x := by
  unfold i8Psi4s108k3W i8Psi4s108k3dW
  exact ((((((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-12)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero, zero] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne, zero] hx).const_mul (24)))

/-- Chunk 3 of the piece `Ψ₄⁽108⁾`. -/
noncomputable def i8Psi4s108k3 (x : ℝ) : ℝ :=
  (i8Psi4s108k3N0 x + x * i8Psi4s108k3N1 x + x ^ 2 * i8Psi4s108k3N2 x + x ^ 3 * i8Psi4s108k3N3 x +
    x ^ 4 * i8Psi4s108k3N4 x) / x ^ 2 + i8Psi4s108k3W x

/-- The derivative of `i8Psi4s108k3`. -/
noncomputable def i8Psi4s108k3D (x : ℝ) : ℝ :=
  ((i8Psi4s108k3dN0 x + (i8Psi4s108k3N1 x + x * i8Psi4s108k3dN1 x) + (2 * x * i8Psi4s108k3N2 x +
    x ^ 2 * i8Psi4s108k3dN2 x) + (3 * x ^ 2 * i8Psi4s108k3N3 x + x ^ 3 * i8Psi4s108k3dN3 x) +
    (4 * x ^ 3 * i8Psi4s108k3N4 x + x ^ 4 * i8Psi4s108k3dN4 x)) * x ^ 2 - (i8Psi4s108k3N0 x +
    x * i8Psi4s108k3N1 x + x ^ 2 * i8Psi4s108k3N2 x + x ^ 3 * i8Psi4s108k3N3 x +
    x ^ 4 * i8Psi4s108k3N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s108k3dW x

theorem hasDerivAt_i8Psi4s108k3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k3 (i8Psi4s108k3D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s108k3N0 hx).add (X.mul (hasDerivAt_i8Psi4s108k3N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s108k3N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s108k3N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s108k3N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s108k3W hx)
  unfold i8Psi4s108k3
  refine e.congr_deriv ?_
  unfold i8Psi4s108k3D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 3 of `p₄⁽108⁾` over words. -/
noncomputable def i8P4w108k3 (x : ℝ) : ℝ :=
    ((-8 - 16 * x - 8 * x ^ 2) / ((1 - x))) * hpl [zero, one, negOne, zero] x +
    ((12 + 12 * x ^ 2 + 24 * x) / ((1 - x))) * hpl [zero, one, zero, zero] x +
    ((-16 - 32 * x - 16 * x ^ 2) / ((1 - x))) * hpl [one, negOne, zero, zero] x +
    ((-8 - 16 * x - 8 * x ^ 2) / ((1 - x))) * hpl [one, zero, negOne, zero] x

theorem i8Psi4s108k3D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s108k3D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w108k3 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s108k3D i8Psi4s108k3N0 i8Psi4s108k3N1 i8Psi4s108k3N2 i8Psi4s108k3N3 i8Psi4s108k3N4
    i8Psi4s108k3dN0 i8Psi4s108k3dN1 i8Psi4s108k3dN2 i8Psi4s108k3dN3 i8Psi4s108k3dN4 i8Psi4s108k3dW
    i8P4w108k3
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, zero, one, negOne, zero] x = v0 at *
  generalize hpl [zero, zero, one, zero, zero] x = v1 at *
  generalize hpl [zero, one, negOne, zero, zero] x = v2 at *
  generalize hpl [zero, one, zero, negOne, zero] x = v3 at *
  generalize hpl [zero, negOne, zero, zero] x = v4 at *
  generalize hpl [zero, zero, negOne, zero] x = v5 at *
  generalize hpl [zero, one, negOne, zero] x = v6 at *
  generalize hpl [zero, one, zero, zero] x = v7 at *
  generalize hpl [one, negOne, zero, zero] x = v8 at *
  generalize hpl [one, zero, negOne, zero] x = v9 at *
  generalize hpl [negOne, zero, zero] x = v10 at *
  generalize hpl [zero, negOne, zero] x = v11 at *
  generalize hpl [zero, zero, zero] x = v12 at *
  generalize hpl [one, negOne, zero] x = v13 at *
  generalize hpl [one, zero, zero] x = v14 at *
  generalize hpl [negOne, zero] x = v15 at *
  generalize hpl [zero, zero] x = v16 at *
  generalize hpl [zero] x = v17 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s108k4N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s108k4N0`. -/
noncomputable def i8Psi4s108k4dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s108k4N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k4N0 (i8Psi4s108k4dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s108k4N1 (x : ℝ) : ℝ :=
    (12) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s108k4N1`. -/
noncomputable def i8Psi4s108k4dN1 (x : ℝ) : ℝ :=
    (12) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s108k4N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k4N1 (i8Psi4s108k4dN1 x) x := by
  unfold i8Psi4s108k4N1 i8Psi4s108k4dN1
  exact ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (12))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s108k4N2 (x : ℝ) : ℝ :=
    (30) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s108k4N2`. -/
noncomputable def i8Psi4s108k4dN2 (x : ℝ) : ℝ :=
    (30) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s108k4N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k4N2 (i8Psi4s108k4dN2 x) x := by
  unfold i8Psi4s108k4N2 i8Psi4s108k4dN2
  exact ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (30))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s108k4N3 (x : ℝ) : ℝ :=
    (42) +
    (-42) * hpl [zero] x +
    (42) * hpl [zero, zero] x +
    (-42) * hpl [zero, zero, zero] x +
    (-36) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s108k4N3`. -/
noncomputable def i8Psi4s108k4dN3 (x : ℝ) : ℝ :=
    0 +
    (-42) * (zero.kernel x * hpl [] x) +
    (42) * (zero.kernel x * hpl [zero] x) +
    (-42) * (zero.kernel x * hpl [zero, zero] x) +
    (-36) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s108k4N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k4N3 (i8Psi4s108k4dN3 x) x := by
  unfold i8Psi4s108k4N3 i8Psi4s108k4dN3
  exact (((((hasDerivAt_const x (42)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-42))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (42))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-42))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (-36)))

/-- The part of `ξ² Ψ₄⁽108⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s108k4N4 (x : ℝ) : ℝ :=
    (3 / 8) +
    (-3 / 4) * hpl [zero] x +
    (3 / 2) * hpl [zero, zero] x +
    (-3) * hpl [zero, zero, zero] x +
    (-6) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s108k4N4`. -/
noncomputable def i8Psi4s108k4dN4 (x : ℝ) : ℝ :=
    0 +
    (-3 / 4) * (zero.kernel x * hpl [] x) +
    (3 / 2) * (zero.kernel x * hpl [zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero] x) +
    (-6) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s108k4N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k4N4 (i8Psi4s108k4dN4 x) x := by
  unfold i8Psi4s108k4N4 i8Psi4s108k4dN4
  exact (((((hasDerivAt_const x (3 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (-6)))

/-- The part of `Ψ₄⁽108⁾` with constant coefficients. -/
noncomputable def i8Psi4s108k4W (x : ℝ) : ℝ :=
    (-12) * hpl [zero, zero, zero, zero] x +
    (-36) * hpl [zero, one, zero, zero, zero] x

/-- The derivative of `i8Psi4s108k4W`. -/
noncomputable def i8Psi4s108k4dW (x : ℝ) : ℝ :=
    (-12) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (-36) * (zero.kernel x * hpl [one, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s108k4W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k4W (i8Psi4s108k4dW x) x := by
  unfold i8Psi4s108k4W i8Psi4s108k4dW
  exact (((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-12)).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero, zero] hx).const_mul (-36)))

/-- Chunk 4 of the piece `Ψ₄⁽108⁾`. -/
noncomputable def i8Psi4s108k4 (x : ℝ) : ℝ :=
  (i8Psi4s108k4N0 x + x * i8Psi4s108k4N1 x + x ^ 2 * i8Psi4s108k4N2 x + x ^ 3 * i8Psi4s108k4N3 x +
    x ^ 4 * i8Psi4s108k4N4 x) / x ^ 2 + i8Psi4s108k4W x

/-- The derivative of `i8Psi4s108k4`. -/
noncomputable def i8Psi4s108k4D (x : ℝ) : ℝ :=
  ((i8Psi4s108k4dN0 x + (i8Psi4s108k4N1 x + x * i8Psi4s108k4dN1 x) + (2 * x * i8Psi4s108k4N2 x +
    x ^ 2 * i8Psi4s108k4dN2 x) + (3 * x ^ 2 * i8Psi4s108k4N3 x + x ^ 3 * i8Psi4s108k4dN3 x) +
    (4 * x ^ 3 * i8Psi4s108k4N4 x + x ^ 4 * i8Psi4s108k4dN4 x)) * x ^ 2 - (i8Psi4s108k4N0 x +
    x * i8Psi4s108k4N1 x + x ^ 2 * i8Psi4s108k4N2 x + x ^ 3 * i8Psi4s108k4N3 x +
    x ^ 4 * i8Psi4s108k4N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s108k4dW x

theorem hasDerivAt_i8Psi4s108k4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108k4 (i8Psi4s108k4D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s108k4N0 hx).add (X.mul (hasDerivAt_i8Psi4s108k4N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s108k4N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s108k4N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s108k4N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s108k4W hx)
  unfold i8Psi4s108k4
  refine e.congr_deriv ?_
  unfold i8Psi4s108k4D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 4 of `p₄⁽108⁾` over words. -/
noncomputable def i8P4w108k4 (x : ℝ) : ℝ :=
    ((12 + 12 * x ^ 2 + 24 * x) / ((1 - x))) * hpl [one, zero, zero, zero] x

theorem i8Psi4s108k4D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s108k4D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w108k4 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s108k4D i8Psi4s108k4N0 i8Psi4s108k4N1 i8Psi4s108k4N2 i8Psi4s108k4N3 i8Psi4s108k4N4
    i8Psi4s108k4dN0 i8Psi4s108k4dN1 i8Psi4s108k4dN2 i8Psi4s108k4dN3 i8Psi4s108k4dN4 i8Psi4s108k4dW
    i8P4w108k4
  simp only [kernel_zero, kernel_one, hpl_nil]
  generalize hpl [zero, one, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero, zero] x = v1 at *
  generalize hpl [one, zero, zero, zero] x = v2 at *
  generalize hpl [zero, zero, zero] x = v3 at *
  generalize hpl [zero, zero] x = v4 at *
  generalize hpl [zero] x = v5 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽108⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s108 (x : ℝ) : ℝ :=
  i8Psi4s108k0 x + i8Psi4s108k1 x + i8Psi4s108k2 x + i8Psi4s108k3 x + i8Psi4s108k4 x

/-- The derivative of `Ψ₄⁽108⁾`. -/
noncomputable def i8Psi4s108D (x : ℝ) : ℝ :=
  i8Psi4s108k0D x + i8Psi4s108k1D x + i8Psi4s108k2D x + i8Psi4s108k3D x + i8Psi4s108k4D x

theorem hasDerivAt_i8Psi4s108 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s108 (i8Psi4s108D x) x := by
  unfold i8Psi4s108 i8Psi4s108D
  exact (((((hasDerivAt_i8Psi4s108k0 hx).add (hasDerivAt_i8Psi4s108k1 hx)).add
    (hasDerivAt_i8Psi4s108k2 hx)).add (hasDerivAt_i8Psi4s108k3 hx)).add (hasDerivAt_i8Psi4s108k4
    hx))

/-- The sub-piece 108 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s108 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * i13Be2x x * ((1 + x) / (1 -
    x) * (1 * hpl [zero] x)) * (x / (1 - x)))

/-- `p₄⁽108⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w108 (x : ℝ) : ℝ :=
  i8P4w108k0 x + i8P4w108k1 x + i8P4w108k2 x + i8P4w108k3 x + i8P4w108k4 x

theorem i8P4s108_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s108 x = i8P4w108 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s108 i8P4w108 i8P4w108k0 i8P4w108k1 i8P4w108k2 i8P4w108k3 i8P4w108k4 i13Be2x
  simp only [hpl_zero, i13hw_10 hx, i13hw_010 hx, i13hw_100 hx, i13hw_0010 hx, i13hw_0100 hx,
    i13hw_01m0 hx, i13hw_0m10 hx, i13hw_1000 hx, i13hw_10m0 hx, i13hw_1m00 hx, i13hw_m001 hx,
    i13hw_m010 hx, i13hw_m100 hx, i13_Li₂_neg_eq hx, i13_log_one_add_eq hx, i13_log_one_sub_eq hx]
  field_simp
  generalize hpl [zero, negOne, negOne, negOne, negOne] x = v0 at *
  generalize hpl [zero, negOne, negOne, negOne, one] x = v1 at *
  generalize hpl [zero, negOne, negOne, zero, one] x = v2 at *
  generalize hpl [zero, negOne, negOne, one, negOne] x = v3 at *
  generalize hpl [zero, negOne, negOne, one, one] x = v4 at *
  generalize hpl [zero, negOne, zero, negOne, negOne] x = v5 at *
  generalize hpl [zero, negOne, zero, negOne, one] x = v6 at *
  generalize hpl [zero, negOne, zero, zero, one] x = v7 at *
  generalize hpl [zero, negOne, zero, one, negOne] x = v8 at *
  generalize hpl [zero, negOne, zero, one, zero] x = v9 at *
  generalize hpl [zero, negOne, zero, one, one] x = v10 at *
  generalize hpl [zero, negOne, one, negOne, negOne] x = v11 at *
  generalize hpl [zero, negOne, one, negOne, one] x = v12 at *
  generalize hpl [zero, negOne, one, zero, zero] x = v13 at *
  generalize hpl [zero, negOne, one, zero, one] x = v14 at *
  generalize hpl [zero, negOne, one, one, negOne] x = v15 at *
  generalize hpl [zero, negOne, one, one, one] x = v16 at *
  generalize hpl [zero, zero, negOne, negOne, negOne] x = v17 at *
  generalize hpl [zero, zero, negOne, negOne, one] x = v18 at *
  generalize hpl [zero, zero, negOne, zero, negOne] x = v19 at *
  generalize hpl [zero, zero, negOne, zero, one] x = v20 at *
  generalize hpl [zero, zero, negOne, one, negOne] x = v21 at *
  generalize hpl [zero, zero, negOne, one, zero] x = v22 at *
  generalize hpl [zero, zero, negOne, one, one] x = v23 at *
  generalize hpl [zero, zero, zero, negOne, negOne] x = v24 at *
  generalize hpl [zero, zero, zero, negOne, one] x = v25 at *
  generalize hpl [zero, zero, zero, zero, negOne] x = v26 at *
  generalize hpl [zero, zero, zero, zero, one] x = v27 at *
  generalize hpl [zero, zero, zero, one, negOne] x = v28 at *
  generalize hpl [zero, zero, zero, one, zero] x = v29 at *
  generalize hpl [zero, zero, zero, one, one] x = v30 at *
  generalize hpl [zero, zero, one, negOne, negOne] x = v31 at *
  generalize hpl [zero, zero, one, negOne, zero] x = v32 at *
  generalize hpl [zero, zero, one, negOne, one] x = v33 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v34 at *
  generalize hpl [zero, zero, one, zero, zero] x = v35 at *
  generalize hpl [zero, zero, one, zero, one] x = v36 at *
  generalize hpl [zero, zero, one, one, negOne] x = v37 at *
  generalize hpl [zero, zero, one, one, one] x = v38 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v39 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v40 at *
  generalize hpl [zero, one, negOne, zero, zero] x = v41 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v42 at *
  generalize hpl [zero, one, negOne, one, one] x = v43 at *
  generalize hpl [zero, one, zero, negOne, zero] x = v44 at *
  generalize hpl [zero, one, zero, zero, zero] x = v45 at *
  generalize hpl [zero, one, zero, one, negOne] x = v46 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v47 at *
  generalize hpl [zero, one, one, negOne, one] x = v48 at *
  generalize hpl [zero, one, one, one, negOne] x = v49 at *
  generalize hpl [zero, one, one, one, one] x = v50 at *
  generalize hpl [negOne, negOne, one, one] x = v51 at *
  generalize hpl [negOne, zero, zero, one] x = v52 at *
  generalize hpl [negOne, zero, one, zero] x = v53 at *
  generalize hpl [negOne, one, zero, zero] x = v54 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v55 at *
  generalize hpl [zero, negOne, negOne, one] x = v56 at *
  generalize hpl [zero, negOne, zero, zero] x = v57 at *
  generalize hpl [zero, negOne, zero, one] x = v58 at *
  generalize hpl [zero, negOne, one, negOne] x = v59 at *
  generalize hpl [zero, negOne, one, zero] x = v60 at *
  generalize hpl [zero, negOne, one, one] x = v61 at *
  generalize hpl [zero, zero, negOne, negOne] x = v62 at *
  generalize hpl [zero, zero, negOne, zero] x = v63 at *
  generalize hpl [zero, zero, negOne, one] x = v64 at *
  generalize hpl [zero, zero, zero, negOne] x = v65 at *
  generalize hpl [zero, zero, zero, zero] x = v66 at *
  generalize hpl [zero, zero, zero, one] x = v67 at *
  generalize hpl [zero, zero, one, negOne] x = v68 at *
  generalize hpl [zero, zero, one, zero] x = v69 at *
  generalize hpl [zero, zero, one, one] x = v70 at *
  generalize hpl [zero, one, negOne, negOne] x = v71 at *
  generalize hpl [zero, one, negOne, zero] x = v72 at *
  generalize hpl [zero, one, negOne, one] x = v73 at *
  generalize hpl [zero, one, zero, zero] x = v74 at *
  generalize hpl [zero, one, one, negOne] x = v75 at *
  generalize hpl [zero, one, one, one] x = v76 at *
  generalize hpl [one, negOne, zero, zero] x = v77 at *
  generalize hpl [one, zero, negOne, zero] x = v78 at *
  generalize hpl [one, zero, zero, zero] x = v79 at *
  generalize hpl [negOne, negOne, one] x = v80 at *
  generalize hpl [negOne, zero, zero] x = v81 at *
  generalize hpl [negOne, zero, one] x = v82 at *
  generalize hpl [negOne, one, zero] x = v83 at *
  generalize hpl [negOne, one, one] x = v84 at *
  generalize hpl [zero, negOne, negOne] x = v85 at *
  generalize hpl [zero, negOne, zero] x = v86 at *
  generalize hpl [zero, negOne, one] x = v87 at *
  generalize hpl [zero, zero, negOne] x = v88 at *
  generalize hpl [zero, zero, zero] x = v89 at *
  generalize hpl [zero, zero, one] x = v90 at *
  generalize hpl [zero, one, negOne] x = v91 at *
  generalize hpl [zero, one, zero] x = v92 at *
  generalize hpl [zero, one, one] x = v93 at *
  generalize hpl [one, negOne, zero] x = v94 at *
  generalize hpl [one, zero, zero] x = v95 at *
  generalize hpl [negOne, zero] x = v96 at *
  generalize hpl [negOne, one] x = v97 at *
  generalize hpl [zero, negOne] x = v98 at *
  generalize hpl [zero, zero] x = v99 at *
  generalize hpl [zero, one] x = v100 at *
  generalize hpl [one, zero] x = v101 at *
  generalize hpl [negOne] x = v102 at *
  generalize hpl [zero] x = v103 at *
  generalize hpl [one] x = v104 at *
  ring

/-- **`(Ψ₄⁽108⁾)'(ξ) ξ' = p₄⁽108⁾`**, in terms of `ξ`. -/
theorem i8Psi4s108D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s108D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s108 x := by
  rw [i8P4s108_eq_w hx]
  unfold i8Psi4s108D i8P4w108
  rw [← i8Psi4s108k0D_mul hx, ← i8Psi4s108k1D_mul hx, ← i8Psi4s108k2D_mul hx, ← i8Psi4s108k3D_mul
    hx, ← i8Psi4s108k4D_mul hx]
  ring

end QED.ThreeLoopD
