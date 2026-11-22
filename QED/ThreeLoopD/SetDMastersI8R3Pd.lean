/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3Pb

/-!
# Set (d), master `I₈`: a primitive of `p₃`, piece `d`

`p₃` splits as `p₃⁽ᵃ⁾ + p₃⁽ᵇ⁾ + p₃⁽ᶜ⁾` by the power of `λ = log t` (`QED.ThreeLoopD.i8P3xd`).
The piece `Ψ₃⁽d⁾` (`QED.ThreeLoopD.i8Psi3d`), a combination of harmonic polylogarithms of weight
at most four with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the shuffle-algebra engine of
the campaign, is a primitive of `p₃⁽d⁾ dt/dξ` (`QED.ThreeLoopD.i8Psi3dD_mul`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi3d`, `QED.ThreeLoopD.i8Psi3dD_mul`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₃⁽d⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi3dN0 (x : ℝ) : ℝ :=
    (-3 / 2) * hpl [negOne] x +
    (-3) * hpl [negOne, zero] x +
    (-5) * hpl [negOne, one] x +
    (-3) * hpl [zero, negOne] x +
    (-5) * hpl [one, negOne] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-2) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, one, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, zero, negOne] x +
    (-2) * hpl [zero, one, negOne] x +
    (-2) * hpl [one, negOne, zero] x +
    (-2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi3dN0`. -/
noncomputable def i8Psi3ddN0 (x : ℝ) : ℝ :=
    (-3 / 2) * (negOne.kernel x * hpl [] x) +
    (-3) * (negOne.kernel x * hpl [zero] x) +
    (-5) * (negOne.kernel x * hpl [one] x) +
    (-3) * (zero.kernel x * hpl [negOne] x) +
    (-5) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi3dN0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3dN0 (i8Psi3ddN0 x) x := by
  unfold i8Psi3dN0 i8Psi3ddN0
  exact (((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₃⁽d⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi3dN1 (x : ℝ) : ℝ :=
    (3 / 2) +
    (-15) * hpl [negOne] x +
    (3) * hpl [zero] x +
    (5) * hpl [one] x +
    (-10) * hpl [negOne, zero] x +
    (-8) * hpl [negOne, one] x +
    (-10) * hpl [zero, negOne] x +
    (2) * hpl [zero, zero] x +
    (2) * hpl [zero, one] x +
    (-8) * hpl [one, negOne] x +
    (2) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, negOne, one] x +
    (-8) * hpl [zero, zero, negOne] x +
    (-8) * hpl [zero, one, negOne] x +
    (-8) * hpl [one, negOne, zero] x +
    (-8) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi3dN1`. -/
noncomputable def i8Psi3ddN1 (x : ℝ) : ℝ :=
    0 +
    (-15) * (negOne.kernel x * hpl [] x) +
    (3) * (zero.kernel x * hpl [] x) +
    (5) * (one.kernel x * hpl [] x) +
    (-10) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [one] x) +
    (-10) * (zero.kernel x * hpl [negOne] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (-8) * (one.kernel x * hpl [negOne] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, negOne] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi3dN1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3dN1 (i8Psi3ddN1 x) x := by
  unfold i8Psi3dN1 i8Psi3ddN1
  exact ((((((((((((((((((((hasDerivAt_const x (3 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-15))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₃⁽d⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi3dN2 (x : ℝ) : ℝ :=
    (17 / 2) * hpl [zero] x +
    (8) * hpl [one] x +
    (-11) * hpl [negOne, zero] x +
    (13) * hpl [zero, negOne] x +
    (9) * hpl [zero, zero] x +
    (11) * hpl [zero, one] x +
    (-15) * hpl [one, zero] x +
    (-12) * hpl [negOne, zero, zero] x +
    (-12) * hpl [negOne, zero, one] x +
    (-12) * hpl [negOne, one, zero] x +
    (2) * hpl [zero, negOne, zero] x +
    (-16) * hpl [zero, negOne, one] x +
    (2) * hpl [zero, zero, negOne] x +
    (-16) * hpl [zero, one, negOne] x +
    (20) * hpl [one, negOne, zero] x +
    (20) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi3dN2`. -/
noncomputable def i8Psi3ddN2 (x : ℝ) : ℝ :=
    (17 / 2) * (zero.kernel x * hpl [] x) +
    (8) * (one.kernel x * hpl [] x) +
    (-11) * (negOne.kernel x * hpl [zero] x) +
    (13) * (zero.kernel x * hpl [negOne] x) +
    (9) * (zero.kernel x * hpl [zero] x) +
    (11) * (zero.kernel x * hpl [one] x) +
    (-15) * (one.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, one] x) +
    (-12) * (negOne.kernel x * hpl [one, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, one] x) +
    (2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-16) * (zero.kernel x * hpl [one, negOne] x) +
    (20) * (one.kernel x * hpl [negOne, zero] x) +
    (20) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi3dN2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3dN2 (i8Psi3ddN2 x) x := by
  unfold i8Psi3dN2 i8Psi3ddN2
  exact (((((((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (17 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (13))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (11))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-15))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (20)))

/-- The part of `ξ² Ψ₃⁽d⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi3dN3 (x : ℝ) : ℝ :=
    (-75 / 2) +
    (15) * hpl [negOne] x +
    (11) * hpl [zero] x +
    (-5) * hpl [one] x +
    (-2) * hpl [negOne, zero] x +
    (8) * hpl [negOne, one] x +
    (-2) * hpl [zero, negOne] x +
    (10) * hpl [zero, zero] x +
    (10) * hpl [zero, one] x +
    (8) * hpl [one, negOne] x +
    (10) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, negOne, one] x +
    (-8) * hpl [zero, zero, negOne] x +
    (-8) * hpl [zero, one, negOne] x +
    (-8) * hpl [one, negOne, zero] x +
    (-8) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi3dN3`. -/
noncomputable def i8Psi3ddN3 (x : ℝ) : ℝ :=
    0 +
    (15) * (negOne.kernel x * hpl [] x) +
    (11) * (zero.kernel x * hpl [] x) +
    (-5) * (one.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [negOne] x) +
    (10) * (zero.kernel x * hpl [zero] x) +
    (10) * (zero.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [negOne] x) +
    (10) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, negOne] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi3dN3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3dN3 (i8Psi3ddN3 x) x := by
  unfold i8Psi3dN3 i8Psi3ddN3
  exact ((((((((((((((((((((hasDerivAt_const x (-75 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (11))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₃⁽d⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi3dN4 (x : ℝ) : ℝ :=
    (-13 / 4) +
    (3 / 2) * hpl [negOne] x +
    (-3) * hpl [zero] x +
    (-8) * hpl [one] x +
    (2) * hpl [negOne, zero] x +
    (5) * hpl [negOne, one] x +
    (2) * hpl [zero, negOne] x +
    (3) * hpl [zero, zero] x +
    (3) * hpl [zero, one] x +
    (5) * hpl [one, negOne] x +
    (3) * hpl [one, zero] x +
    (-2) * hpl [negOne, zero, zero] x +
    (-2) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, one, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, zero, negOne] x +
    (-2) * hpl [zero, one, negOne] x +
    (-2) * hpl [one, negOne, zero] x +
    (-2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi3dN4`. -/
noncomputable def i8Psi3ddN4 (x : ℝ) : ℝ :=
    0 +
    (3 / 2) * (negOne.kernel x * hpl [] x) +
    (-3) * (zero.kernel x * hpl [] x) +
    (-8) * (one.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [zero] x) +
    (5) * (negOne.kernel x * hpl [one] x) +
    (2) * (zero.kernel x * hpl [negOne] x) +
    (3) * (zero.kernel x * hpl [zero] x) +
    (3) * (zero.kernel x * hpl [one] x) +
    (5) * (one.kernel x * hpl [negOne] x) +
    (3) * (one.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi3dN4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3dN4 (i8Psi3ddN4 x) x := by
  unfold i8Psi3dN4 i8Psi3ddN4
  exact ((((((((((((((((((((hasDerivAt_const x (-13 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₃⁽d⁾` with constant coefficients. -/
noncomputable def i8Psi3dW (x : ℝ) : ℝ :=
    (2) * hpl [zero, zero, zero] x +
    (2) * hpl [zero, zero, one] x +
    (2) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi3dW`. -/
noncomputable def i8Psi3ddW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (2) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi3dW {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3dW (i8Psi3ddW x) x := by
  unfold i8Psi3dW i8Psi3ddW
  exact ((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2)))

/-- The piece `Ψ₃⁽d⁾` of the primitive of `p₃ dt/dξ`. -/
noncomputable def i8Psi3d (x : ℝ) : ℝ :=
  (i8Psi3dN0 x + x * i8Psi3dN1 x + x ^ 2 * i8Psi3dN2 x + x ^ 3 * i8Psi3dN3 x +
    x ^ 4 * i8Psi3dN4 x) / x ^ 2 + i8Psi3dW x

/-- The derivative of `Ψ₃⁽d⁾`. -/
noncomputable def i8Psi3dD (x : ℝ) : ℝ :=
  ((i8Psi3ddN0 x + (i8Psi3dN1 x + x * i8Psi3ddN1 x) +
      (2 * x * i8Psi3dN2 x + x ^ 2 * i8Psi3ddN2 x) +
      (3 * x ^ 2 * i8Psi3dN3 x + x ^ 3 * i8Psi3ddN3 x) +
      (4 * x ^ 3 * i8Psi3dN4 x + x ^ 4 * i8Psi3ddN4 x)) * x ^ 2 -
    (i8Psi3dN0 x + x * i8Psi3dN1 x + x ^ 2 * i8Psi3dN2 x + x ^ 3 * i8Psi3dN3 x +
      x ^ 4 * i8Psi3dN4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi3ddW x

theorem hasDerivAt_i8Psi3d {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3d (i8Psi3dD x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := (((((hasDerivAt_i8Psi3dN0 hx).add (X.mul (hasDerivAt_i8Psi3dN1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi3dN2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi3dN3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi3dN4 hx))).div (X.pow 2) (pow_ne_zero 2 h0) |>.add
    (hasDerivAt_i8Psi3dW hx)
  unfold i8Psi3d
  refine e.congr_deriv ?_
  unfold i8Psi3dD
  simp only [Pi.pow_apply]
  norm_num

/-- The part `-2 t λ β₁ A₁` of `p₃` in `ξ`. -/
noncomputable def i8P3xd (x : ℝ) : ℝ :=
  -((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) *
    (2 * (2 + Real.log x * (1 + x) / (1 - x)) * i8A1x x))

/-- **`(Ψ₃⁽d⁾)'(ξ) ξ' = p₃⁽d⁾`**, in terms of `ξ`. -/
theorem i8Psi3dD_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3dD x * (-x ^ 2 / (1 - x ^ 2)) = i8P3xd x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi3dD i8Psi3dN0 i8Psi3dN1 i8Psi3dN2 i8Psi3dN3 i8Psi3dN4 i8Psi3ddN0 i8Psi3ddN1
    i8Psi3ddN2 i8Psi3ddN3 i8Psi3ddN4 i8Psi3ddW i8P3xd i8A1x
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx,
    i13hw_10 hx, i13hw_1m hx, i13hw_0m0 hx, i13hw_m00 hx, i13hw_m01 hx, i13hw_m10 hx, i13hw_10m hx,
    i13hw_1m0 hx, i13_log_one_sub_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
