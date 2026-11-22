/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P4

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 21 to 26

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s21`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s21D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s21`, `QED.ThreeLoopD.i8Psi4s21D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽21⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s21N0 (x : ℝ) : ℝ :=
    (-111 / 8 + 5 / 12 * π ^ 2) * hpl [negOne] x +
    (-47 / 4 + π ^ 2 / 6) * hpl [negOne, zero] x +
    (-47 / 4 + π ^ 2 / 6) * hpl [zero, negOne] x +
    (10) * hpl [negOne, negOne, zero] x +
    (5) * hpl [negOne, zero, negOne] x +
    (-15 / 2) * hpl [negOne, zero, zero] x +
    (-15 / 2) * hpl [zero, negOne, zero] x +
    (-15 / 2) * hpl [zero, zero, negOne] x +
    (8) * hpl [negOne, negOne, zero, zero] x +
    (6) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [negOne, zero, zero, negOne] x +
    (-3) * hpl [negOne, zero, zero, zero] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (2) * hpl [zero, negOne, zero, negOne] x +
    (-3) * hpl [zero, negOne, zero, zero] x +
    (-3) * hpl [zero, zero, negOne, zero] x +
    (-3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s21N0`. -/
noncomputable def i8Psi4s21dN0 (x : ℝ) : ℝ :=
    (-111 / 8 + 5 / 12 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-47 / 4 + π ^ 2 / 6) * (negOne.kernel x * hpl [zero] x) +
    (-47 / 4 + π ^ 2 / 6) * (zero.kernel x * hpl [negOne] x) +
    (10) * (negOne.kernel x * hpl [negOne, zero] x) +
    (5) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-15 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-15 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-15 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (6) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-3) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-3) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s21N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21N0 (i8Psi4s21dN0 x) x := by
  unfold i8Psi4s21N0 i8Psi4s21dN0
  exact ((((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-111 / 8 +
    5 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-47 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-47 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-15 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-15 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-15 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3)))

/-- Chunk 0 of `i8Psi4s21N1`. -/
noncomputable def i8Psi4s21N1c0 (x : ℝ) : ℝ :=
    (-289 / 8 + 7 / 12 * π ^ 2) +
    (-87 + 8 / 3 * π ^ 2) * hpl [negOne] x +
    (-89 / 4 + π ^ 2 / 6) * hpl [zero] x +
    (-80 + 4 / 3 * π ^ 2) * hpl [negOne, zero] x +
    (-87 + 4 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (-21 / 2) * hpl [zero, zero] x +
    (64) * hpl [negOne, negOne, zero] x +
    (32) * hpl [negOne, zero, negOne] x +
    (-56) * hpl [negOne, zero, zero] x +
    (-58) * hpl [zero, negOne, zero] x +
    (-60) * hpl [zero, zero, negOne] x +
    (-3) * hpl [zero, zero, zero] x +
    (64) * hpl [negOne, negOne, zero, zero] x +
    (48) * hpl [negOne, zero, negOne, zero] x +
    (32) * hpl [negOne, zero, zero, negOne] x +
    (-24) * hpl [negOne, zero, zero, zero] x +
    (32) * hpl [zero, negOne, negOne, zero] x +
    (16) * hpl [zero, negOne, zero, negOne] x +
    (-24) * hpl [zero, negOne, zero, zero] x +
    (-24) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s21N1c0`. -/
noncomputable def i8Psi4s21dN1c0 (x : ℝ) : ℝ :=
    0 +
    (-87 + 8 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-89 / 4 + π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (-80 + 4 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (-87 + 4 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (-21 / 2) * (zero.kernel x * hpl [zero] x) +
    (64) * (negOne.kernel x * hpl [negOne, zero] x) +
    (32) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-56) * (negOne.kernel x * hpl [zero, zero] x) +
    (-58) * (zero.kernel x * hpl [negOne, zero] x) +
    (-60) * (zero.kernel x * hpl [zero, negOne] x) +
    (-3) * (zero.kernel x * hpl [zero, zero] x) +
    (64) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (48) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (32) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-24) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (32) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s21N1c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21N1c0 (i8Psi4s21dN1c0 x) x := by
  unfold i8Psi4s21N1c0 i8Psi4s21dN1c0
  exact ((((((((((((((((((((hasDerivAt_const x (-289 / 8 + 7 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-87 + 8 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-89 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-80 + 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-87 + 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-21 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (64))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-56))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-58))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-60))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (64))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-24)))

/-- Chunk 1 of `i8Psi4s21N1`. -/
noncomputable def i8Psi4s21N1c1 (x : ℝ) : ℝ :=
    (-24) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s21N1c1`. -/
noncomputable def i8Psi4s21dN1c1 (x : ℝ) : ℝ :=
    (-24) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s21N1c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21N1c1 (i8Psi4s21dN1c1 x) x := by
  unfold i8Psi4s21N1c1 i8Psi4s21dN1c1
  exact ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-24))

/-- The part of `ξ² Ψ₄⁽21⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s21N1 (x : ℝ) : ℝ :=
    i8Psi4s21N1c0 x + i8Psi4s21N1c1 x

/-- The derivative of `i8Psi4s21N1`. -/
noncomputable def i8Psi4s21dN1 (x : ℝ) : ℝ :=
    i8Psi4s21dN1c0 x + i8Psi4s21dN1c1 x

theorem hasDerivAt_i8Psi4s21N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21N1 (i8Psi4s21dN1 x) x := by
  unfold i8Psi4s21N1 i8Psi4s21dN1
  exact ((hasDerivAt_i8Psi4s21N1c0 hx).add (hasDerivAt_i8Psi4s21N1c1 hx))

/-- The part of `ξ² Ψ₄⁽21⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s21N2 (x : ℝ) : ℝ :=
    (9 / 2 * π ^ 2) * hpl [negOne] x +
    (585 / 8 - 9 / 4 * π ^ 2) * hpl [zero] x +
    (-363 / 2) * hpl [negOne, zero] x +
    (-32) * hpl [zero, negOne] x +
    (273 / 4 - 7 / 6 * π ^ 2) * hpl [zero, zero] x +
    (108) * hpl [negOne, negOne, zero] x +
    (54) * hpl [negOne, zero, negOne] x +
    (3) * hpl [negOne, zero, zero] x +
    (-54 - 2 * π ^ 2) * hpl [zero, negOne, zero] x +
    (-27 - 2 * π ^ 2) * hpl [zero, zero, negOne] x +
    (97 / 2) * hpl [zero, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (6) * hpl [zero, zero, negOne, zero] x +
    (20) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s21N2`. -/
noncomputable def i8Psi4s21dN2 (x : ℝ) : ℝ :=
    (9 / 2 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (585 / 8 - 9 / 4 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-363 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-32) * (zero.kernel x * hpl [negOne] x) +
    (273 / 4 - 7 / 6 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (108) * (negOne.kernel x * hpl [negOne, zero] x) +
    (54) * (negOne.kernel x * hpl [zero, negOne] x) +
    (3) * (negOne.kernel x * hpl [zero, zero] x) +
    (-54 - 2 * π ^ 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-27 - 2 * π ^ 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (97 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (6) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (20) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s21N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21N2 (i8Psi4s21dN2 x) x := by
  unfold i8Psi4s21N2 i8Psi4s21dN2
  exact (((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (9 / 2 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (585 / 8 - 9 / 4 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-363 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (273 / 4 - 7 / 6 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (108))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (54))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-54 - 2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-27 - 2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (97 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (20)))

/-- Chunk 0 of `i8Psi4s21N3`. -/
noncomputable def i8Psi4s21N3c0 (x : ℝ) : ℝ :=
    (-1735 / 8 - 41 / 12 * π ^ 2) +
    (87 + 8 / 3 * π ^ 2) * hpl [negOne] x +
    (575 / 4 + 7 / 6 * π ^ 2) * hpl [zero] x +
    (-128 - 4 / 3 * π ^ 2) * hpl [negOne, zero] x +
    (-87 - 4 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (-61 / 2) * hpl [zero, zero] x +
    (64) * hpl [negOne, negOne, zero] x +
    (32) * hpl [negOne, zero, negOne] x +
    (56) * hpl [negOne, zero, zero] x +
    (42) * hpl [zero, negOne, zero] x +
    (28) * hpl [zero, zero, negOne] x +
    (-21) * hpl [zero, zero, zero] x +
    (-64) * hpl [negOne, negOne, zero, zero] x +
    (-48) * hpl [negOne, zero, negOne, zero] x +
    (-32) * hpl [negOne, zero, zero, negOne] x +
    (24) * hpl [negOne, zero, zero, zero] x +
    (-32) * hpl [zero, negOne, negOne, zero] x +
    (-16) * hpl [zero, negOne, zero, negOne] x +
    (24) * hpl [zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s21N3c0`. -/
noncomputable def i8Psi4s21dN3c0 (x : ℝ) : ℝ :=
    0 +
    (87 + 8 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (575 / 4 + 7 / 6 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-128 - 4 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (-87 - 4 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (-61 / 2) * (zero.kernel x * hpl [zero] x) +
    (64) * (negOne.kernel x * hpl [negOne, zero] x) +
    (32) * (negOne.kernel x * hpl [zero, negOne] x) +
    (56) * (negOne.kernel x * hpl [zero, zero] x) +
    (42) * (zero.kernel x * hpl [negOne, zero] x) +
    (28) * (zero.kernel x * hpl [zero, negOne] x) +
    (-21) * (zero.kernel x * hpl [zero, zero] x) +
    (-64) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-48) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (-32) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (24) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-32) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (24) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s21N3c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21N3c0 (i8Psi4s21dN3c0 x) x := by
  unfold i8Psi4s21N3c0 i8Psi4s21dN3c0
  exact ((((((((((((((((((((hasDerivAt_const x (-1735 / 8 - 41 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (87 + 8 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (575 / 4 + 7 / 6 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-128 - 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-87 - 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-61 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (64))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (56))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (42))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-21))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (-64))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (24)))

/-- Chunk 1 of `i8Psi4s21N3`. -/
noncomputable def i8Psi4s21N3c1 (x : ℝ) : ℝ :=
    (24) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s21N3c1`. -/
noncomputable def i8Psi4s21dN3c1 (x : ℝ) : ℝ :=
    (24) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s21N3c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21N3c1 (i8Psi4s21dN3c1 x) x := by
  unfold i8Psi4s21N3c1 i8Psi4s21dN3c1
  exact ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (24))

/-- The part of `ξ² Ψ₄⁽21⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s21N3 (x : ℝ) : ℝ :=
    i8Psi4s21N3c0 x + i8Psi4s21N3c1 x

/-- The derivative of `i8Psi4s21N3`. -/
noncomputable def i8Psi4s21dN3 (x : ℝ) : ℝ :=
    i8Psi4s21dN3c0 x + i8Psi4s21dN3c1 x

theorem hasDerivAt_i8Psi4s21N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21N3 (i8Psi4s21dN3 x) x := by
  unfold i8Psi4s21N3 i8Psi4s21dN3
  exact ((hasDerivAt_i8Psi4s21N3c0 hx).add (hasDerivAt_i8Psi4s21N3c1 hx))

/-- Chunk 0 of `i8Psi4s21N4`. -/
noncomputable def i8Psi4s21N4c0 (x : ℝ) : ℝ :=
    (-11 - π ^ 2 / 4) +
    (111 / 8 + 5 / 12 * π ^ 2) * hpl [negOne] x +
    (65 / 8 + π ^ 2 / 12) * hpl [zero] x +
    (-59 / 4 - π ^ 2 / 6) * hpl [negOne, zero] x +
    (-47 / 4 - π ^ 2 / 6) * hpl [zero, negOne] x +
    (-3 / 2) * hpl [zero, zero] x +
    (10) * hpl [negOne, negOne, zero] x +
    (5) * hpl [negOne, zero, negOne] x +
    (9 / 2) * hpl [negOne, zero, zero] x +
    (7 / 2) * hpl [zero, negOne, zero] x +
    (5 / 2) * hpl [zero, zero, negOne] x +
    (-3 / 2) * hpl [zero, zero, zero] x +
    (-8) * hpl [negOne, negOne, zero, zero] x +
    (-6) * hpl [negOne, zero, negOne, zero] x +
    (-4) * hpl [negOne, zero, zero, negOne] x +
    (3) * hpl [negOne, zero, zero, zero] x +
    (-4) * hpl [zero, negOne, negOne, zero] x +
    (-2) * hpl [zero, negOne, zero, negOne] x +
    (3) * hpl [zero, negOne, zero, zero] x +
    (3) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s21N4c0`. -/
noncomputable def i8Psi4s21dN4c0 (x : ℝ) : ℝ :=
    0 +
    (111 / 8 + 5 / 12 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (65 / 8 + π ^ 2 / 12) * (zero.kernel x * hpl [] x) +
    (-59 / 4 - π ^ 2 / 6) * (negOne.kernel x * hpl [zero] x) +
    (-47 / 4 - π ^ 2 / 6) * (zero.kernel x * hpl [negOne] x) +
    (-3 / 2) * (zero.kernel x * hpl [zero] x) +
    (10) * (negOne.kernel x * hpl [negOne, zero] x) +
    (5) * (negOne.kernel x * hpl [zero, negOne] x) +
    (9 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (7 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (5 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-3 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (-8) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-6) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (3) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (3) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (3) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s21N4c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21N4c0 (i8Psi4s21dN4c0 x) x := by
  unfold i8Psi4s21N4c0 i8Psi4s21dN4c0
  exact ((((((((((((((((((((hasDerivAt_const x (-11 - π ^ 2 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (111 / 8 + 5 / 12 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (65 / 8 + π ^ 2 / 12))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-59 / 4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-47 / 4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (9 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (3)))

/-- Chunk 1 of `i8Psi4s21N4`. -/
noncomputable def i8Psi4s21N4c1 (x : ℝ) : ℝ :=
    (3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s21N4c1`. -/
noncomputable def i8Psi4s21dN4c1 (x : ℝ) : ℝ :=
    (3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s21N4c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21N4c1 (i8Psi4s21dN4c1 x) x := by
  unfold i8Psi4s21N4c1 i8Psi4s21dN4c1
  exact ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (3))

/-- The part of `ξ² Ψ₄⁽21⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s21N4 (x : ℝ) : ℝ :=
    i8Psi4s21N4c0 x + i8Psi4s21N4c1 x

/-- The derivative of `i8Psi4s21N4`. -/
noncomputable def i8Psi4s21dN4 (x : ℝ) : ℝ :=
    i8Psi4s21dN4c0 x + i8Psi4s21dN4c1 x

theorem hasDerivAt_i8Psi4s21N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21N4 (i8Psi4s21dN4 x) x := by
  unfold i8Psi4s21N4 i8Psi4s21dN4
  exact ((hasDerivAt_i8Psi4s21N4c0 hx).add (hasDerivAt_i8Psi4s21N4c1 hx))

/-- The part of `Ψ₄⁽21⁾` with constant coefficients. -/
noncomputable def i8Psi4s21W (x : ℝ) : ℝ :=
    (21) * hpl [zero, zero, zero, zero] x +
    (-96) * hpl [zero, negOne, negOne, zero, zero] x +
    (-72) * hpl [zero, negOne, zero, negOne, zero] x +
    (-48) * hpl [zero, negOne, zero, zero, negOne] x +
    (36) * hpl [zero, negOne, zero, zero, zero] x +
    (-48) * hpl [zero, zero, negOne, negOne, zero] x +
    (-24) * hpl [zero, zero, negOne, zero, negOne] x +
    (36) * hpl [zero, zero, negOne, zero, zero] x +
    (36) * hpl [zero, zero, zero, negOne, zero] x +
    (36) * hpl [zero, zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s21W`. -/
noncomputable def i8Psi4s21dW (x : ℝ) : ℝ :=
    (21) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (-96) * (zero.kernel x * hpl [negOne, negOne, zero, zero] x) +
    (-72) * (zero.kernel x * hpl [negOne, zero, negOne, zero] x) +
    (-48) * (zero.kernel x * hpl [negOne, zero, zero, negOne] x) +
    (36) * (zero.kernel x * hpl [negOne, zero, zero, zero] x) +
    (-48) * (zero.kernel x * hpl [zero, negOne, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, negOne, zero, negOne] x) +
    (36) * (zero.kernel x * hpl [zero, negOne, zero, zero] x) +
    (36) * (zero.kernel x * hpl [zero, zero, negOne, zero] x) +
    (36) * (zero.kernel x * hpl [zero, zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s21W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21W (i8Psi4s21dW x) x := by
  unfold i8Psi4s21W i8Psi4s21dW
  exact (((((((((((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (21)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero, zero] hx).const_mul (-96))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, zero] hx).const_mul (-72))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, negOne] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne, zero] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, negOne] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, negOne] hx).const_mul (36)))

/-- The piece `Ψ₄⁽21⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s21 (x : ℝ) : ℝ :=
  (i8Psi4s21N0 x + x * i8Psi4s21N1 x + x ^ 2 * i8Psi4s21N2 x + x ^ 3 * i8Psi4s21N3 x +
    x ^ 4 * i8Psi4s21N4 x) / x ^ 2 + i8Psi4s21W x

/-- The derivative of `Ψ₄⁽21⁾`. -/
noncomputable def i8Psi4s21D (x : ℝ) : ℝ :=
  ((i8Psi4s21dN0 x + (i8Psi4s21N1 x + x * i8Psi4s21dN1 x) + (2 * x * i8Psi4s21N2 x +
    x ^ 2 * i8Psi4s21dN2 x) + (3 * x ^ 2 * i8Psi4s21N3 x + x ^ 3 * i8Psi4s21dN3 x) +
    (4 * x ^ 3 * i8Psi4s21N4 x + x ^ 4 * i8Psi4s21dN4 x)) * x ^ 2 - (i8Psi4s21N0 x +
    x * i8Psi4s21N1 x + x ^ 2 * i8Psi4s21N2 x + x ^ 3 * i8Psi4s21N3 x +
    x ^ 4 * i8Psi4s21N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s21dW x

theorem hasDerivAt_i8Psi4s21 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s21 (i8Psi4s21D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s21N0 hx).add (X.mul (hasDerivAt_i8Psi4s21N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s21N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s21N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s21N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s21W hx)
  unfold i8Psi4s21
  refine e.congr_deriv ?_
  unfold i8Psi4s21D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 21 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s21 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * (2 + Real.log x * (1 + x) / (1 - x)) * i13Be2x x * ((1 + x) / (1 -
    x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽21⁾)'(ξ) ξ' = p₄⁽21⁾`**, in terms of `ξ`. -/
theorem i8Psi4s21D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s21D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s21 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s21D i8Psi4s21N0 i8Psi4s21N1 i8Psi4s21N2 i8Psi4s21N3 i8Psi4s21N4 i8Psi4s21dN0
    i8Psi4s21dN1 i8Psi4s21dN2 i8Psi4s21dN3 i8Psi4s21dN4 i8Psi4s21dW i8Psi4s21N1c0 i8Psi4s21dN1c0
    i8Psi4s21N1c1 i8Psi4s21dN1c1 i8Psi4s21N3c0 i8Psi4s21dN3c0 i8Psi4s21N3c1 i8Psi4s21dN3c1
    i8Psi4s21N4c0 i8Psi4s21dN4c0 i8Psi4s21N4c1 i8Psi4s21dN4c1 i8P4s21 i13Be2x
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_000,
    i13hw_0m0 hx, i13hw_m00 hx, i13hw_m0m hx, i13hw_mm0 hx, i13hw_00m0 hx, i13hw_0m00 hx, i13hw_0m0m
    hx, i13hw_0mm0 hx, i13hw_m000 hx, i13hw_m00m hx, i13hw_m0m0 hx, i13hw_mm00 hx, i13_Li₂_neg_eq
    hx, i13_log_one_add_eq hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽22⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s22N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s22N0`. -/
noncomputable def i8Psi4s22dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s22N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s22N0 (i8Psi4s22dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽22⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s22N1 (_x : ℝ) : ℝ :=
    (32 - 8 * zeta3 - 4 / 3 * π ^ 2 - π ^ 2 ^ 2 / 20)

/-- The derivative of `i8Psi4s22N1`. -/
noncomputable def i8Psi4s22dN1 (_x : ℝ) : ℝ :=
    0

theorem hasDerivAt_i8Psi4s22N1 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s22N1 (i8Psi4s22dN1 x) x := by
  unfold i8Psi4s22N1 i8Psi4s22dN1
  exact (hasDerivAt_const x (32 - 8 * zeta3 - 4 / 3 * π ^ 2 - π ^ 2 ^ 2 / 20))

/-- The part of `ξ² Ψ₄⁽22⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s22N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s22N2`. -/
noncomputable def i8Psi4s22dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s22N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s22N2 (i8Psi4s22dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽22⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s22N3 (_x : ℝ) : ℝ :=
    (32 - 8 * zeta3 - 4 / 3 * π ^ 2 - π ^ 2 ^ 2 / 20)

/-- The derivative of `i8Psi4s22N3`. -/
noncomputable def i8Psi4s22dN3 (_x : ℝ) : ℝ :=
    0

theorem hasDerivAt_i8Psi4s22N3 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s22N3 (i8Psi4s22dN3 x) x := by
  unfold i8Psi4s22N3 i8Psi4s22dN3
  exact (hasDerivAt_const x (32 - 8 * zeta3 - 4 / 3 * π ^ 2 - π ^ 2 ^ 2 / 20))

/-- The part of `ξ² Ψ₄⁽22⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s22N4 (_x : ℝ) : ℝ :=
    (-16 - 4 * zeta3 - 2 / 3 * π ^ 2 - π ^ 2 ^ 2 / 40)

/-- The derivative of `i8Psi4s22N4`. -/
noncomputable def i8Psi4s22dN4 (_x : ℝ) : ℝ :=
    0

theorem hasDerivAt_i8Psi4s22N4 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s22N4 (i8Psi4s22dN4 x) x := by
  unfold i8Psi4s22N4 i8Psi4s22dN4
  exact (hasDerivAt_const x (-16 - 4 * zeta3 - 2 / 3 * π ^ 2 - π ^ 2 ^ 2 / 40))

/-- The part of `Ψ₄⁽22⁾` with constant coefficients. -/
noncomputable def i8Psi4s22W (x : ℝ) : ℝ :=
    (32 + 8 * zeta3 + π ^ 2 ^ 2 / 20 + 4 / 3 * π ^ 2) * hpl [zero] x

/-- The derivative of `i8Psi4s22W`. -/
noncomputable def i8Psi4s22dW (x : ℝ) : ℝ :=
    (32 + 8 * zeta3 + π ^ 2 ^ 2 / 20 + 4 / 3 * π ^ 2) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s22W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s22W (i8Psi4s22dW x) x := by
  unfold i8Psi4s22W i8Psi4s22dW
  exact ((hasDerivAt_hpl_cons zero [] hx).const_mul (32 + 8 * zeta3 + π ^ 2 ^ 2 / 20 +
    4 / 3 * π ^ 2))

/-- The piece `Ψ₄⁽22⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s22 (x : ℝ) : ℝ :=
  (i8Psi4s22N0 x + x * i8Psi4s22N1 x + x ^ 2 * i8Psi4s22N2 x + x ^ 3 * i8Psi4s22N3 x +
    x ^ 4 * i8Psi4s22N4 x) / x ^ 2 + i8Psi4s22W x

/-- The derivative of `Ψ₄⁽22⁾`. -/
noncomputable def i8Psi4s22D (x : ℝ) : ℝ :=
  ((i8Psi4s22dN0 x + (i8Psi4s22N1 x + x * i8Psi4s22dN1 x) + (2 * x * i8Psi4s22N2 x +
    x ^ 2 * i8Psi4s22dN2 x) + (3 * x ^ 2 * i8Psi4s22N3 x + x ^ 3 * i8Psi4s22dN3 x) +
    (4 * x ^ 3 * i8Psi4s22N4 x + x ^ 4 * i8Psi4s22dN4 x)) * x ^ 2 - (i8Psi4s22N0 x +
    x * i8Psi4s22N1 x + x ^ 2 * i8Psi4s22N2 x + x ^ 3 * i8Psi4s22N3 x +
    x ^ 4 * i8Psi4s22N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s22dW x

theorem hasDerivAt_i8Psi4s22 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s22 (i8Psi4s22D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s22N0 hx).add (X.mul (hasDerivAt_i8Psi4s22N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s22N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s22N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s22N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s22W hx)
  unfold i8Psi4s22
  refine e.congr_deriv ?_
  unfold i8Psi4s22D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 22 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s22 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((1920 + ((-1920) * x) + ((-480) * zeta3) +
    ((-80) * π ^ 2) + ((-3) * (π ^ 2 ^ 2)) + ((-480) * x * zeta3) + ((-80) * π ^ 2 * x) +
    ((-3) * x * (π ^ 2 ^ 2))) / (120 + (120 * x)))) * (x / (1 - x))

/-- **`(Ψ₄⁽22⁾)'(ξ) ξ' = p₄⁽22⁾`**, in terms of `ξ`. -/
theorem i8Psi4s22D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s22D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s22 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s22D i8Psi4s22N0 i8Psi4s22N1 i8Psi4s22N2 i8Psi4s22N3 i8Psi4s22N4 i8Psi4s22dN0
    i8Psi4s22dN1 i8Psi4s22dN2 i8Psi4s22dN3 i8Psi4s22dN4 i8Psi4s22dW i8P4s22
  simp only [kernel_zero, hpl_nil]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽23⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s23N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s23N0`. -/
noncomputable def i8Psi4s23dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s23N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s23N0 (i8Psi4s23dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽23⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s23N1 (x : ℝ) : ℝ :=
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) +
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) * hpl [zero] x

/-- The derivative of `i8Psi4s23N1`. -/
noncomputable def i8Psi4s23dN1 (x : ℝ) : ℝ :=
    0 +
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s23N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s23N1 (i8Psi4s23dN1 x) x := by
  unfold i8Psi4s23N1 i8Psi4s23dN1
  exact ((hasDerivAt_const x (16 - 4 * zeta3 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (16 - 4 * zeta3 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽23⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s23N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s23N2`. -/
noncomputable def i8Psi4s23dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s23N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s23N2 (i8Psi4s23dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽23⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s23N3 (x : ℝ) : ℝ :=
    (-16 + 4 * zeta3 + 2 / 3 * π ^ 2) +
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) * hpl [zero] x

/-- The derivative of `i8Psi4s23N3`. -/
noncomputable def i8Psi4s23dN3 (x : ℝ) : ℝ :=
    0 +
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s23N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s23N3 (i8Psi4s23dN3 x) x := by
  unfold i8Psi4s23N3 i8Psi4s23dN3
  exact ((hasDerivAt_const x (-16 + 4 * zeta3 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (16 - 4 * zeta3 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽23⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s23N4 (x : ℝ) : ℝ :=
    (-4 + zeta3 + π ^ 2 / 6) +
    (8 - 2 * zeta3 - π ^ 2 / 3) * hpl [zero] x

/-- The derivative of `i8Psi4s23N4`. -/
noncomputable def i8Psi4s23dN4 (x : ℝ) : ℝ :=
    0 +
    (8 - 2 * zeta3 - π ^ 2 / 3) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s23N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s23N4 (i8Psi4s23dN4 x) x := by
  unfold i8Psi4s23N4 i8Psi4s23dN4
  exact ((hasDerivAt_const x (-4 + zeta3 + π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (8 - 2 * zeta3 - π ^ 2 / 3)))

/-- The part of `Ψ₄⁽23⁾` with constant coefficients. -/
noncomputable def i8Psi4s23W (x : ℝ) : ℝ :=
    (-16 + 4 * zeta3 + 2 / 3 * π ^ 2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s23W`. -/
noncomputable def i8Psi4s23dW (x : ℝ) : ℝ :=
    (-16 + 4 * zeta3 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s23W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s23W (i8Psi4s23dW x) x := by
  unfold i8Psi4s23W i8Psi4s23dW
  exact ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-16 + 4 * zeta3 + 2 / 3 * π ^ 2))

/-- The piece `Ψ₄⁽23⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s23 (x : ℝ) : ℝ :=
  (i8Psi4s23N0 x + x * i8Psi4s23N1 x + x ^ 2 * i8Psi4s23N2 x + x ^ 3 * i8Psi4s23N3 x +
    x ^ 4 * i8Psi4s23N4 x) / x ^ 2 + i8Psi4s23W x

/-- The derivative of `Ψ₄⁽23⁾`. -/
noncomputable def i8Psi4s23D (x : ℝ) : ℝ :=
  ((i8Psi4s23dN0 x + (i8Psi4s23N1 x + x * i8Psi4s23dN1 x) + (2 * x * i8Psi4s23N2 x +
    x ^ 2 * i8Psi4s23dN2 x) + (3 * x ^ 2 * i8Psi4s23N3 x + x ^ 3 * i8Psi4s23dN3 x) +
    (4 * x ^ 3 * i8Psi4s23N4 x + x ^ 4 * i8Psi4s23dN4 x)) * x ^ 2 - (i8Psi4s23N0 x +
    x * i8Psi4s23N1 x + x ^ 2 * i8Psi4s23N2 x + x ^ 3 * i8Psi4s23N3 x +
    x ^ 4 * i8Psi4s23N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s23dW x

theorem hasDerivAt_i8Psi4s23 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s23 (i8Psi4s23D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s23N0 hx).add (X.mul (hasDerivAt_i8Psi4s23N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s23N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s23N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s23N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s23W hx)
  unfold i8Psi4s23
  refine e.congr_deriv ?_
  unfold i8Psi4s23D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 23 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s23 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * (((24 + ((-1) * π ^ 2) +
    ((-6) * zeta3)) / 3) * hpl [zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽23⁾)'(ξ) ξ' = p₄⁽23⁾`**, in terms of `ξ`. -/
theorem i8Psi4s23D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s23D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s23 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s23D i8Psi4s23N0 i8Psi4s23N1 i8Psi4s23N2 i8Psi4s23N3 i8Psi4s23N4 i8Psi4s23dN0
    i8Psi4s23dN1 i8Psi4s23dN2 i8Psi4s23dN3 i8Psi4s23dN4 i8Psi4s23dW i8P4s23
  simp only [kernel_zero, hpl_nil, hpl_zero]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽24⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s24N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s24N0`. -/
noncomputable def i8Psi4s24dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s24N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s24N0 (i8Psi4s24dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽24⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s24N1 (x : ℝ) : ℝ :=
    (8 * zeta3 + 4 / 3 * π ^ 2) * hpl [negOne] x

/-- The derivative of `i8Psi4s24N1`. -/
noncomputable def i8Psi4s24dN1 (x : ℝ) : ℝ :=
    (8 * zeta3 + 4 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s24N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s24N1 (i8Psi4s24dN1 x) x := by
  unfold i8Psi4s24N1 i8Psi4s24dN1
  exact ((hasDerivAt_hpl_cons negOne [] hx).const_mul (8 * zeta3 + 4 / 3 * π ^ 2))

/-- The part of `ξ² Ψ₄⁽24⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s24N2 (x : ℝ) : ℝ :=
    (2 * π ^ 2 + 12 * zeta3) * hpl [negOne] x

/-- The derivative of `i8Psi4s24N2`. -/
noncomputable def i8Psi4s24dN2 (x : ℝ) : ℝ :=
    (2 * π ^ 2 + 12 * zeta3) * (negOne.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s24N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s24N2 (i8Psi4s24dN2 x) x := by
  unfold i8Psi4s24N2 i8Psi4s24dN2
  exact ((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 * π ^ 2 + 12 * zeta3))

/-- The part of `ξ² Ψ₄⁽24⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s24N3 (x : ℝ) : ℝ :=
    (-4 * zeta3 - 2 / 3 * π ^ 2) +
    (8 * zeta3 + 4 / 3 * π ^ 2) * hpl [negOne] x

/-- The derivative of `i8Psi4s24N3`. -/
noncomputable def i8Psi4s24dN3 (x : ℝ) : ℝ :=
    0 +
    (8 * zeta3 + 4 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s24N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s24N3 (i8Psi4s24dN3 x) x := by
  unfold i8Psi4s24N3 i8Psi4s24dN3
  exact ((hasDerivAt_const x (-4 * zeta3 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (8 * zeta3 + 4 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽24⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s24N4 (x : ℝ) : ℝ :=
    (-2 * zeta3 - π ^ 2 / 3) +
    (4 * zeta3 + 2 / 3 * π ^ 2) * hpl [negOne] x

/-- The derivative of `i8Psi4s24N4`. -/
noncomputable def i8Psi4s24dN4 (x : ℝ) : ℝ :=
    0 +
    (4 * zeta3 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s24N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s24N4 (i8Psi4s24dN4 x) x := by
  unfold i8Psi4s24N4 i8Psi4s24dN4
  exact ((hasDerivAt_const x (-2 * zeta3 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (4 * zeta3 + 2 / 3 * π ^ 2)))

/-- The part of `Ψ₄⁽24⁾` with constant coefficients. -/
noncomputable def i8Psi4s24W (x : ℝ) : ℝ :=
    (-8 * zeta3 - 4 / 3 * π ^ 2) * hpl [zero] x +
    (-8 * zeta3 - 4 / 3 * π ^ 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s24W`. -/
noncomputable def i8Psi4s24dW (x : ℝ) : ℝ :=
    (-8 * zeta3 - 4 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-8 * zeta3 - 4 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s24W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s24W (i8Psi4s24dW x) x := by
  unfold i8Psi4s24W i8Psi4s24dW
  exact (((hasDerivAt_hpl_cons zero [] hx).const_mul (-8 * zeta3 - 4 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-8 * zeta3 - 4 / 3 * π ^ 2)))

/-- The piece `Ψ₄⁽24⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s24 (x : ℝ) : ℝ :=
  (i8Psi4s24N0 x + x * i8Psi4s24N1 x + x ^ 2 * i8Psi4s24N2 x + x ^ 3 * i8Psi4s24N3 x +
    x ^ 4 * i8Psi4s24N4 x) / x ^ 2 + i8Psi4s24W x

/-- The derivative of `Ψ₄⁽24⁾`. -/
noncomputable def i8Psi4s24D (x : ℝ) : ℝ :=
  ((i8Psi4s24dN0 x + (i8Psi4s24N1 x + x * i8Psi4s24dN1 x) + (2 * x * i8Psi4s24N2 x +
    x ^ 2 * i8Psi4s24dN2 x) + (3 * x ^ 2 * i8Psi4s24N3 x + x ^ 3 * i8Psi4s24dN3 x) +
    (4 * x ^ 3 * i8Psi4s24N4 x + x ^ 4 * i8Psi4s24dN4 x)) * x ^ 2 - (i8Psi4s24N0 x +
    x * i8Psi4s24N1 x + x ^ 2 * i8Psi4s24N2 x + x ^ 3 * i8Psi4s24N3 x +
    x ^ 4 * i8Psi4s24N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s24dW x

theorem hasDerivAt_i8Psi4s24 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s24 (i8Psi4s24D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s24N0 hx).add (X.mul (hasDerivAt_i8Psi4s24N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s24N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s24N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s24N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s24W hx)
  unfold i8Psi4s24
  refine e.congr_deriv ?_
  unfold i8Psi4s24D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 24 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s24 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((((2 * π ^ 2) +
    (12 * zeta3)) / 3) * hpl [negOne] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽24⁾)'(ξ) ξ' = p₄⁽24⁾`**, in terms of `ξ`. -/
theorem i8Psi4s24D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s24D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s24 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s24D i8Psi4s24N0 i8Psi4s24N1 i8Psi4s24N2 i8Psi4s24N3 i8Psi4s24N4 i8Psi4s24dN0
    i8Psi4s24dN1 i8Psi4s24dN2 i8Psi4s24dN3 i8Psi4s24dN4 i8Psi4s24dW i8P4s24
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽25⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s25N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s25N0`. -/
noncomputable def i8Psi4s25dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s25N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s25N0 (i8Psi4s25dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽25⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s25N1 (x : ℝ) : ℝ :=
    (8 - π ^ 2 / 3) +
    (8 - π ^ 2 / 3) * hpl [zero] x +
    (8 - π ^ 2 / 3) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s25N1`. -/
noncomputable def i8Psi4s25dN1 (x : ℝ) : ℝ :=
    0 +
    (8 - π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (8 - π ^ 2 / 3) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s25N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s25N1 (i8Psi4s25dN1 x) x := by
  unfold i8Psi4s25N1 i8Psi4s25dN1
  exact (((hasDerivAt_const x (8 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (8 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8 - π ^ 2 / 3)))

/-- The part of `ξ² Ψ₄⁽25⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s25N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s25N2`. -/
noncomputable def i8Psi4s25dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s25N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s25N2 (i8Psi4s25dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽25⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s25N3 (x : ℝ) : ℝ :=
    (8 - π ^ 2 / 3) +
    (-8 + π ^ 2 / 3) * hpl [zero] x +
    (8 - π ^ 2 / 3) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s25N3`. -/
noncomputable def i8Psi4s25dN3 (x : ℝ) : ℝ :=
    0 +
    (-8 + π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (8 - π ^ 2 / 3) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s25N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s25N3 (i8Psi4s25dN3 x) x := by
  unfold i8Psi4s25N3 i8Psi4s25dN3
  exact (((hasDerivAt_const x (8 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-8 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8 - π ^ 2 / 3)))

/-- The part of `ξ² Ψ₄⁽25⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s25N4 (x : ℝ) : ℝ :=
    (1 - π ^ 2 / 24) +
    (-2 + π ^ 2 / 12) * hpl [zero] x +
    (4 - π ^ 2 / 6) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s25N4`. -/
noncomputable def i8Psi4s25dN4 (x : ℝ) : ℝ :=
    0 +
    (-2 + π ^ 2 / 12) * (zero.kernel x * hpl [] x) +
    (4 - π ^ 2 / 6) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s25N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s25N4 (i8Psi4s25dN4 x) x := by
  unfold i8Psi4s25N4 i8Psi4s25dN4
  exact (((hasDerivAt_const x (1 - π ^ 2 / 24)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2 + π ^ 2 / 12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4 - π ^ 2 / 6)))

/-- The part of `Ψ₄⁽25⁾` with constant coefficients. -/
noncomputable def i8Psi4s25W (x : ℝ) : ℝ :=
    (-8 + π ^ 2 / 3) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s25W`. -/
noncomputable def i8Psi4s25dW (x : ℝ) : ℝ :=
    (-8 + π ^ 2 / 3) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s25W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s25W (i8Psi4s25dW x) x := by
  unfold i8Psi4s25W i8Psi4s25dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-8 + π ^ 2 / 3))

/-- The piece `Ψ₄⁽25⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s25 (x : ℝ) : ℝ :=
  (i8Psi4s25N0 x + x * i8Psi4s25N1 x + x ^ 2 * i8Psi4s25N2 x + x ^ 3 * i8Psi4s25N3 x +
    x ^ 4 * i8Psi4s25N4 x) / x ^ 2 + i8Psi4s25W x

/-- The derivative of `Ψ₄⁽25⁾`. -/
noncomputable def i8Psi4s25D (x : ℝ) : ℝ :=
  ((i8Psi4s25dN0 x + (i8Psi4s25N1 x + x * i8Psi4s25dN1 x) + (2 * x * i8Psi4s25N2 x +
    x ^ 2 * i8Psi4s25dN2 x) + (3 * x ^ 2 * i8Psi4s25N3 x + x ^ 3 * i8Psi4s25dN3 x) +
    (4 * x ^ 3 * i8Psi4s25N4 x + x ^ 4 * i8Psi4s25dN4 x)) * x ^ 2 - (i8Psi4s25N0 x +
    x * i8Psi4s25N1 x + x ^ 2 * i8Psi4s25N2 x + x ^ 3 * i8Psi4s25N3 x +
    x ^ 4 * i8Psi4s25N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s25dW x

theorem hasDerivAt_i8Psi4s25 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s25 (i8Psi4s25D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s25N0 hx).add (X.mul (hasDerivAt_i8Psi4s25N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s25N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s25N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s25N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s25W hx)
  unfold i8Psi4s25
  refine e.congr_deriv ?_
  unfold i8Psi4s25D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 25 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s25 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * (((24 +
    ((-1) * π ^ 2)) / 6) * hpl [zero, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽25⁾)'(ξ) ξ' = p₄⁽25⁾`**, in terms of `ξ`. -/
theorem i8Psi4s25D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s25D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s25 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s25D i8Psi4s25N0 i8Psi4s25N1 i8Psi4s25N2 i8Psi4s25N3 i8Psi4s25N4 i8Psi4s25dN0
    i8Psi4s25dN1 i8Psi4s25dN2 i8Psi4s25dN3 i8Psi4s25dN4 i8Psi4s25dW i8P4s25
  simp only [kernel_zero, hpl_nil, hpl_zero, i13hw_00]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽26⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s26N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s26N0`. -/
noncomputable def i8Psi4s26dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s26N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s26N0 (i8Psi4s26dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽26⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s26N1 (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s26N1`. -/
noncomputable def i8Psi4s26dN1 (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s26N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s26N1 (i8Psi4s26dN1 x) x := by
  unfold i8Psi4s26N1 i8Psi4s26dN1
  exact ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-16 + 2 / 3 * π ^ 2))

/-- The part of `ξ² Ψ₄⁽26⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s26N2 (x : ℝ) : ℝ :=
    (-24 + π ^ 2) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s26N2`. -/
noncomputable def i8Psi4s26dN2 (x : ℝ) : ℝ :=
    (-24 + π ^ 2) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s26N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s26N2 (i8Psi4s26dN2 x) x := by
  unfold i8Psi4s26N2 i8Psi4s26dN2
  exact ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-24 + π ^ 2))

/-- The part of `ξ² Ψ₄⁽26⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s26N3 (x : ℝ) : ℝ :=
    (-8 + π ^ 2 / 3) +
    (8 - π ^ 2 / 3) * hpl [zero] x +
    (-16 + 2 / 3 * π ^ 2) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s26N3`. -/
noncomputable def i8Psi4s26dN3 (x : ℝ) : ℝ :=
    0 +
    (8 - π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (-16 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s26N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s26N3 (i8Psi4s26dN3 x) x := by
  unfold i8Psi4s26N3 i8Psi4s26dN3
  exact (((hasDerivAt_const x (-8 + π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (8 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-16 + 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽26⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s26N4 (x : ℝ) : ℝ :=
    (-2 + π ^ 2 / 12) +
    (4 - π ^ 2 / 6) * hpl [zero] x +
    (-8 + π ^ 2 / 3) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s26N4`. -/
noncomputable def i8Psi4s26dN4 (x : ℝ) : ℝ :=
    0 +
    (4 - π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (-8 + π ^ 2 / 3) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s26N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s26N4 (i8Psi4s26dN4 x) x := by
  unfold i8Psi4s26N4 i8Psi4s26dN4
  exact (((hasDerivAt_const x (-2 + π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8 + π ^ 2 / 3)))

/-- The part of `Ψ₄⁽26⁾` with constant coefficients. -/
noncomputable def i8Psi4s26W (x : ℝ) : ℝ :=
    (16 - 2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (16 - 2 / 3 * π ^ 2) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s26W`. -/
noncomputable def i8Psi4s26dW (x : ℝ) : ℝ :=
    (16 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (16 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s26W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s26W (i8Psi4s26dW x) x := by
  unfold i8Psi4s26W i8Psi4s26dW
  exact (((hasDerivAt_hpl_cons zero [zero] hx).const_mul (16 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (16 - 2 / 3 * π ^ 2)))

/-- The piece `Ψ₄⁽26⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s26 (x : ℝ) : ℝ :=
  (i8Psi4s26N0 x + x * i8Psi4s26N1 x + x ^ 2 * i8Psi4s26N2 x + x ^ 3 * i8Psi4s26N3 x +
    x ^ 4 * i8Psi4s26N4 x) / x ^ 2 + i8Psi4s26W x

/-- The derivative of `Ψ₄⁽26⁾`. -/
noncomputable def i8Psi4s26D (x : ℝ) : ℝ :=
  ((i8Psi4s26dN0 x + (i8Psi4s26N1 x + x * i8Psi4s26dN1 x) + (2 * x * i8Psi4s26N2 x +
    x ^ 2 * i8Psi4s26dN2 x) + (3 * x ^ 2 * i8Psi4s26N3 x + x ^ 3 * i8Psi4s26dN3 x) +
    (4 * x ^ 3 * i8Psi4s26N4 x + x ^ 4 * i8Psi4s26dN4 x)) * x ^ 2 - (i8Psi4s26N0 x +
    x * i8Psi4s26N1 x + x ^ 2 * i8Psi4s26N2 x + x ^ 3 * i8Psi4s26N3 x +
    x ^ 4 * i8Psi4s26N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s26dW x

theorem hasDerivAt_i8Psi4s26 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s26 (i8Psi4s26D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s26N0 hx).add (X.mul (hasDerivAt_i8Psi4s26N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s26N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s26N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s26N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s26W hx)
  unfold i8Psi4s26
  refine e.congr_deriv ?_
  unfold i8Psi4s26D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 26 of `p₄` in `ξ`: from `t B4 A0 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s26 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((((-24) +
    π ^ 2) / 3) * hpl [negOne, zero] x)) * (x / (1 - x))

/-- **`(Ψ₄⁽26⁾)'(ξ) ξ' = p₄⁽26⁾`**, in terms of `ξ`. -/
theorem i8Psi4s26D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s26D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s26 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s26D i8Psi4s26N0 i8Psi4s26N1 i8Psi4s26N2 i8Psi4s26N3 i8Psi4s26N4 i8Psi4s26dN0
    i8Psi4s26dN1 i8Psi4s26dN2 i8Psi4s26dN3 i8Psi4s26dN4 i8Psi4s26dW i8P4s26
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx]
  field_simp
  ring

end QED.ThreeLoopD
