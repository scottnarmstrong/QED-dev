/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3W

/-!
# Set (d), master `I₈`: a primitive of `p₃`, piece `a`

`p₃` splits as `p₃⁽ᵃ⁾ + p₃⁽ᵇ⁾ + p₃⁽ᶜ⁾` by the power of `λ = log t` (`QED.ThreeLoopD.i8P3xa`).
The piece `Ψ₃⁽a⁾` (`QED.ThreeLoopD.i8Psi3a`), a combination of harmonic polylogarithms of weight
at most four with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the shuffle-algebra engine of
the campaign, is a primitive of `p₃⁽a⁾ dt/dξ` (`QED.ThreeLoopD.i8Psi3aD_mul`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi3a`, `QED.ThreeLoopD.i8Psi3aD_mul`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₃⁽a⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi3aN0 (x : ℝ) : ℝ :=
    (-111 / 8 + π ^ 2 / 6) * hpl [negOne] x +
    (13 / 2) * hpl [negOne, negOne] x +
    (-13 / 2) * hpl [negOne, zero] x +
    (-39 / 4) * hpl [zero, negOne] x +
    (-2) * hpl [negOne, negOne, negOne] x +
    (6) * hpl [negOne, negOne, zero] x +
    (5) * hpl [negOne, zero, negOne] x +
    (-2) * hpl [negOne, zero, zero] x +
    (3) * hpl [zero, negOne, negOne] x +
    (-3) * hpl [zero, negOne, zero] x +
    (-9 / 2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi3aN0`. -/
noncomputable def i8Psi3adN0 (x : ℝ) : ℝ :=
    (-111 / 8 + π ^ 2 / 6) * (negOne.kernel x * hpl [] x) +
    (13 / 2) * (negOne.kernel x * hpl [negOne] x) +
    (-13 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-39 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (6) * (negOne.kernel x * hpl [negOne, zero] x) +
    (5) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (3) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-3) * (zero.kernel x * hpl [negOne, zero] x) +
    (-9 / 2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi3aN0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3aN0 (i8Psi3adN0 x) x := by
  unfold i8Psi3aN0 i8Psi3adN0
  exact ((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-111 / 8 + π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (13 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-13 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-39 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-9 / 2)))

/-- The part of `ξ² Ψ₃⁽a⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi3aN1 (x : ℝ) : ℝ :=
    (781 / 8 - 4 * zeta3 - 13 / 6 * π ^ 2) +
    (-57 / 2 + 4 / 3 * π ^ 2) * hpl [negOne] x +
    (111 / 2 - 2 / 3 * π ^ 2) * hpl [zero] x +
    (6) * hpl [negOne, negOne] x +
    (-58) * hpl [negOne, zero] x +
    (-35) * hpl [zero, negOne] x +
    (26) * hpl [zero, zero] x +
    (32) * hpl [negOne, negOne, zero] x +
    (16) * hpl [negOne, zero, negOne] x +
    (-24) * hpl [negOne, zero, zero] x +
    (8) * hpl [zero, negOne, negOne] x +
    (-24) * hpl [zero, negOne, zero] x +
    (-20) * hpl [zero, zero, negOne] x +
    (8) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi3aN1`. -/
noncomputable def i8Psi3adN1 (x : ℝ) : ℝ :=
    0 +
    (-57 / 2 + 4 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (111 / 2 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (6) * (negOne.kernel x * hpl [negOne] x) +
    (-58) * (negOne.kernel x * hpl [zero] x) +
    (-35) * (zero.kernel x * hpl [negOne] x) +
    (26) * (zero.kernel x * hpl [zero] x) +
    (32) * (negOne.kernel x * hpl [negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-24) * (negOne.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero] x) +
    (-20) * (zero.kernel x * hpl [zero, negOne] x) +
    (8) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi3aN1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3aN1 (i8Psi3adN1 x) x := by
  unfold i8Psi3aN1 i8Psi3adN1
  exact ((((((((((((((hasDerivAt_const x (781 / 8 - 4 * zeta3 - 13 / 6 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-57 / 2 + 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (111 / 2 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-58))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-35))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (26))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₃⁽a⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi3aN2 (x : ℝ) : ℝ :=
    (2 * π ^ 2) * hpl [negOne] x +
    (565 / 8 + π ^ 2 / 2 + 4 * zeta3) * hpl [zero] x +
    (-102) * hpl [negOne, zero] x +
    (-71 / 2 - 2 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (31 / 2 + 4 / 3 * π ^ 2) * hpl [zero, zero] x +
    (48) * hpl [negOne, negOne, zero] x +
    (24) * hpl [negOne, zero, negOne] x +
    (18) * hpl [zero, negOne, negOne] x +
    (-6) * hpl [zero, negOne, zero] x +
    (-21) * hpl [zero, zero, negOne] x +
    (-18) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi3aN2`. -/
noncomputable def i8Psi3adN2 (x : ℝ) : ℝ :=
    (2 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (565 / 8 + π ^ 2 / 2 + 4 * zeta3) * (zero.kernel x * hpl [] x) +
    (-102) * (negOne.kernel x * hpl [zero] x) +
    (-71 / 2 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (31 / 2 + 4 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (48) * (negOne.kernel x * hpl [negOne, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, negOne] x) +
    (18) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-6) * (zero.kernel x * hpl [negOne, zero] x) +
    (-21) * (zero.kernel x * hpl [zero, negOne] x) +
    (-18) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi3aN2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3aN2 (i8Psi3adN2 x) x := by
  unfold i8Psi3aN2 i8Psi3adN2
  exact ((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (565 / 8 + π ^ 2 / 2 + 4 * zeta3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-102))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-71 / 2 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (31 / 2 + 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-21))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-18)))

/-- The part of `ξ² Ψ₃⁽a⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi3aN3 (x : ℝ) : ℝ :=
    (-569 / 8 - 4 * zeta3 - 19 / 6 * π ^ 2) +
    (57 / 2 + 4 / 3 * π ^ 2) * hpl [negOne] x +
    (225 / 2 + 2 / 3 * π ^ 2) * hpl [zero] x +
    (-6) * hpl [negOne, negOne] x +
    (-70) * hpl [negOne, zero] x +
    (-29) * hpl [zero, negOne] x +
    (-26) * hpl [zero, zero] x +
    (32) * hpl [negOne, negOne, zero] x +
    (16) * hpl [negOne, zero, negOne] x +
    (24) * hpl [negOne, zero, zero] x +
    (8) * hpl [zero, negOne, negOne] x +
    (8) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne] x +
    (-16) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi3aN3`. -/
noncomputable def i8Psi3adN3 (x : ℝ) : ℝ :=
    0 +
    (57 / 2 + 4 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (225 / 2 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-6) * (negOne.kernel x * hpl [negOne] x) +
    (-70) * (negOne.kernel x * hpl [zero] x) +
    (-29) * (zero.kernel x * hpl [negOne] x) +
    (-26) * (zero.kernel x * hpl [zero] x) +
    (32) * (negOne.kernel x * hpl [negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, negOne] x) +
    (24) * (negOne.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne] x) +
    (-16) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi3aN3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3aN3 (i8Psi3adN3 x) x := by
  unfold i8Psi3aN3 i8Psi3adN3
  exact ((((((((((((((hasDerivAt_const x (-569 / 8 - 4 * zeta3 - 19 / 6 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (57 / 2 + 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (225 / 2 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-70))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-29))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-26))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₃⁽a⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi3aN4 (x : ℝ) : ℝ :=
    (-781 / 16 - 2 * zeta3 - 13 / 12 * π ^ 2) +
    (111 / 8 + π ^ 2 / 2) * hpl [negOne] x +
    (111 / 4) * hpl [zero] x +
    (-13 / 2) * hpl [negOne, negOne] x +
    (-39 / 2) * hpl [negOne, zero] x +
    (-13 / 4) * hpl [zero, negOne] x +
    (2) * hpl [negOne, negOne, negOne] x +
    (10) * hpl [negOne, negOne, zero] x +
    (3) * hpl [negOne, zero, negOne] x +
    (2) * hpl [negOne, zero, zero] x +
    (1) * hpl [zero, negOne, negOne] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-3 / 2) * hpl [zero, zero, negOne] x +
    (-2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi3aN4`. -/
noncomputable def i8Psi3adN4 (x : ℝ) : ℝ :=
    0 +
    (111 / 8 + π ^ 2 / 2) * (negOne.kernel x * hpl [] x) +
    (111 / 4) * (zero.kernel x * hpl [] x) +
    (-13 / 2) * (negOne.kernel x * hpl [negOne] x) +
    (-39 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-13 / 4) * (zero.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, negOne] x) +
    (10) * (negOne.kernel x * hpl [negOne, zero] x) +
    (3) * (negOne.kernel x * hpl [zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-3 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi3aN4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3aN4 (i8Psi3adN4 x) x := by
  unfold i8Psi3aN4 i8Psi3adN4
  exact ((((((((((((((hasDerivAt_const x (-781 / 16 - 2 * zeta3 - 13 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (111 / 8 + π ^ 2 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (111 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-13 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-39 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-13 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-2)))

/-- The part of `Ψ₃⁽a⁾` with constant coefficients. -/
noncomputable def i8Psi3aW (x : ℝ) : ℝ :=
    (-8) * hpl [zero, negOne, negOne, negOne] x +
    (-8) * hpl [zero, negOne, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, negOne] x +
    (40) * hpl [zero, negOne, zero, zero] x +
    (4) * hpl [zero, zero, negOne, negOne] x +
    (28) * hpl [zero, zero, negOne, zero] x +
    (10) * hpl [zero, zero, zero, negOne] x +
    (-20) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi3aW`. -/
noncomputable def i8Psi3adW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [negOne, negOne, negOne] x) +
    (-8) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (40) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, negOne] x) +
    (28) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (10) * (zero.kernel x * hpl [zero, zero, negOne] x) +
    (-20) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi3aW {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3aW (i8Psi3adW x) x := by
  unfold i8Psi3aW i8Psi3adW
  exact (((((((((hasDerivAt_hpl_cons zero [negOne, negOne, negOne] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-20)))

/-- The piece `Ψ₃⁽a⁾` of the primitive of `p₃ dt/dξ`. -/
noncomputable def i8Psi3a (x : ℝ) : ℝ :=
  (i8Psi3aN0 x + x * i8Psi3aN1 x + x ^ 2 * i8Psi3aN2 x + x ^ 3 * i8Psi3aN3 x +
    x ^ 4 * i8Psi3aN4 x) / x ^ 2 + i8Psi3aW x

/-- The derivative of `Ψ₃⁽a⁾`. -/
noncomputable def i8Psi3aD (x : ℝ) : ℝ :=
  ((i8Psi3adN0 x + (i8Psi3aN1 x + x * i8Psi3adN1 x) +
      (2 * x * i8Psi3aN2 x + x ^ 2 * i8Psi3adN2 x) +
      (3 * x ^ 2 * i8Psi3aN3 x + x ^ 3 * i8Psi3adN3 x) +
      (4 * x ^ 3 * i8Psi3aN4 x + x ^ 4 * i8Psi3adN4 x)) * x ^ 2 -
    (i8Psi3aN0 x + x * i8Psi3aN1 x + x ^ 2 * i8Psi3aN2 x + x ^ 3 * i8Psi3aN3 x +
      x ^ 4 * i8Psi3aN4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi3adW x

theorem hasDerivAt_i8Psi3a {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3a (i8Psi3aD x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := (((((hasDerivAt_i8Psi3aN0 hx).add (X.mul (hasDerivAt_i8Psi3aN1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi3aN2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi3aN3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi3aN4 hx))).div (X.pow 2) (pow_ne_zero 2 h0) |>.add
    (hasDerivAt_i8Psi3aW hx)
  unfold i8Psi3a
  refine e.congr_deriv ?_
  unfold i8Psi3aD
  simp only [Pi.pow_apply]
  norm_num

/-- The part of `p₃` in `ξ` without `λ`. -/
noncomputable def i8P3xa (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * ((2 * ((1 + x) / (1 - x) * (i13PB x - i13P1c)) +
        2 * (2 + Real.log x * (1 + x) / (1 - x)) * i13Be2x x) * (x / (1 - x)) +
      (2 * i13Be2x x + (2 + Real.log x * (1 + x) / (1 - x)) ^ 2) * i8A1x x +
      2 * (2 + Real.log x * (1 + x) / (1 - x)) * i8A2x x + i8A3x x)

/-- **`(Ψ₃⁽a⁾)'(ξ) ξ' = p₃⁽a⁾`**, in terms of `ξ`. -/
theorem i8Psi3aD_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3aD x * (-x ^ 2 / (1 - x ^ 2)) = i8P3xa x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi3aD i8Psi3aN0 i8Psi3aN1 i8Psi3aN2 i8Psi3aN3 i8Psi3aN4 i8Psi3adN0 i8Psi3adN1
    i8Psi3adN2 i8Psi3adN3 i8Psi3adN4 i8Psi3adW i8P3xa i13PB i13PBH i13Be2x i13P1c i8A1x i8A2x i8A3x
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_mm hx,
    i13hw_000, i13hw_0m0 hx, i13hw_m00 hx, i13hw_m0m hx, i13hw_mm0 hx, i8hw_mmm hx, i13_Li₂_neg_eq
    hx, i13_log_one_add_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
