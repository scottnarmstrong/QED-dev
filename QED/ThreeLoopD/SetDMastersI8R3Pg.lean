/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3Pf

/-!
# Set (d), master `I₈`: a primitive of `p₃`, piece `g`

`p₃` splits as `p₃⁽ᵃ⁾ + p₃⁽ᵇ⁾ + p₃⁽ᶜ⁾` by the power of `λ = log t` (`QED.ThreeLoopD.i8P3xg`).
The piece `Ψ₃⁽g⁾` (`QED.ThreeLoopD.i8Psi3g`), a combination of harmonic polylogarithms of weight
at most four with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the shuffle-algebra engine of
the campaign, is a primitive of `p₃⁽g⁾ dt/dξ` (`QED.ThreeLoopD.i8Psi3gD_mul`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi3g`, `QED.ThreeLoopD.i8Psi3gD_mul`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₃⁽g⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi3gN0 (x : ℝ) : ℝ :=
    (-1 / 8) * hpl [negOne] x +
    (-1 / 4) * hpl [negOne, zero] x +
    (-1 / 2) * hpl [negOne, one] x +
    (-1 / 4) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [one, negOne] x +
    (-1 / 2) * hpl [negOne, zero, zero] x +
    (-1) * hpl [negOne, zero, one] x +
    (-1) * hpl [negOne, one, zero] x +
    (-2) * hpl [negOne, one, one] x +
    (-1 / 2) * hpl [zero, negOne, zero] x +
    (-1) * hpl [zero, negOne, one] x +
    (-1 / 2) * hpl [zero, zero, negOne] x +
    (-1) * hpl [zero, one, negOne] x +
    (-1) * hpl [one, negOne, zero] x +
    (-2) * hpl [one, negOne, one] x +
    (-1) * hpl [one, zero, negOne] x +
    (-2) * hpl [one, one, negOne] x

/-- The derivative of `i8Psi3gN0`. -/
noncomputable def i8Psi3gdN0 (x : ℝ) : ℝ :=
    (-1 / 8) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, one] x) +
    (-1) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (negOne.kernel x * hpl [one, one] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, one] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [one, negOne] x) +
    (-1) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [negOne, one] x) +
    (-1) * (one.kernel x * hpl [zero, negOne] x) +
    (-2) * (one.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi3gN0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3gN0 (i8Psi3gdN0 x) x := by
  unfold i8Psi3gN0 i8Psi3gdN0
  exact ((((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 8)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₃⁽g⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi3gN1 (x : ℝ) : ℝ :=
    (1 / 8) +
    (-3 / 2) * hpl [negOne] x +
    (1 / 4) * hpl [zero] x +
    (1 / 2) * hpl [one] x +
    (-1) * hpl [negOne, zero] x +
    (-2) * hpl [negOne, one] x +
    (-1) * hpl [zero, negOne] x +
    (1 / 2) * hpl [zero, zero] x +
    (1) * hpl [zero, one] x +
    (-2) * hpl [one, negOne] x +
    (1) * hpl [one, zero] x +
    (2) * hpl [one, one] x

/-- The derivative of `i8Psi3gN1`. -/
noncomputable def i8Psi3gdN1 (x : ℝ) : ℝ :=
    0 +
    (-3 / 2) * (negOne.kernel x * hpl [] x) +
    (1 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [one] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [negOne] x) +
    (1) * (one.kernel x * hpl [zero] x) +
    (2) * (one.kernel x * hpl [one] x)

theorem hasDerivAt_i8Psi3gN1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3gN1 (i8Psi3gdN1 x) x := by
  unfold i8Psi3gN1 i8Psi3gdN1
  exact ((((((((((((hasDerivAt_const x (1 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (2)))

/-- The part of `ξ² Ψ₃⁽g⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi3gN2 (x : ℝ) : ℝ :=
    (7 / 8) * hpl [zero] x +
    (2) * hpl [one] x +
    (5 / 2) * hpl [zero, negOne] x +
    (-1 / 4) * hpl [zero, zero] x +
    (-1 / 2) * hpl [zero, one] x +
    (-5 / 2) * hpl [one, zero] x +
    (-5) * hpl [one, one] x +
    (1) * hpl [zero, negOne, zero] x +
    (2) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, zero, negOne] x +
    (2) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi3gN2`. -/
noncomputable def i8Psi3gdN2 (x : ℝ) : ℝ :=
    (7 / 8) * (zero.kernel x * hpl [] x) +
    (2) * (one.kernel x * hpl [] x) +
    (5 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [one] x) +
    (-5 / 2) * (one.kernel x * hpl [zero] x) +
    (-5) * (one.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, one] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x) +
    (2) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi3gN2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3gN2 (i8Psi3gdN2 x) x := by
  unfold i8Psi3gN2 i8Psi3gdN2
  exact ((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (7 / 8)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₃⁽g⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi3gN3 (x : ℝ) : ℝ :=
    (-25 / 8) +
    (3 / 2) * hpl [negOne] x +
    (-3 / 4) * hpl [zero] x +
    (-3 / 2) * hpl [one] x +
    (1) * hpl [negOne, zero] x +
    (2) * hpl [negOne, one] x +
    (1) * hpl [zero, negOne] x +
    (3 / 2) * hpl [zero, zero] x +
    (3) * hpl [zero, one] x +
    (2) * hpl [one, negOne] x +
    (3) * hpl [one, zero] x +
    (6) * hpl [one, one] x

/-- The derivative of `i8Psi3gN3`. -/
noncomputable def i8Psi3gdN3 (x : ℝ) : ℝ :=
    0 +
    (3 / 2) * (negOne.kernel x * hpl [] x) +
    (-3 / 4) * (zero.kernel x * hpl [] x) +
    (-3 / 2) * (one.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (2) * (negOne.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [negOne] x) +
    (3 / 2) * (zero.kernel x * hpl [zero] x) +
    (3) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [negOne] x) +
    (3) * (one.kernel x * hpl [zero] x) +
    (6) * (one.kernel x * hpl [one] x)

theorem hasDerivAt_i8Psi3gN3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3gN3 (i8Psi3gdN3 x) x := by
  unfold i8Psi3gN3 i8Psi3gdN3
  exact ((((((((((((hasDerivAt_const x (-25 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (6)))

/-- The part of `ξ² Ψ₃⁽g⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi3gN4 (x : ℝ) : ℝ :=
    (-5 / 16) +
    (1 / 8) * hpl [negOne] x +
    (-1 / 2) * hpl [zero] x +
    (-1) * hpl [one] x +
    (1 / 4) * hpl [negOne, zero] x +
    (1 / 2) * hpl [negOne, one] x +
    (1 / 4) * hpl [zero, negOne] x +
    (-3 / 4) * hpl [zero, zero] x +
    (-3 / 2) * hpl [zero, one] x +
    (1 / 2) * hpl [one, negOne] x +
    (-3 / 2) * hpl [one, zero] x +
    (-3) * hpl [one, one] x +
    (1 / 2) * hpl [negOne, zero, zero] x +
    (1) * hpl [negOne, zero, one] x +
    (1) * hpl [negOne, one, zero] x +
    (2) * hpl [negOne, one, one] x +
    (1 / 2) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, negOne, one] x +
    (1 / 2) * hpl [zero, zero, negOne] x +
    (1) * hpl [zero, one, negOne] x +
    (1) * hpl [one, negOne, zero] x +
    (2) * hpl [one, negOne, one] x +
    (1) * hpl [one, zero, negOne] x +
    (2) * hpl [one, one, negOne] x

/-- The derivative of `i8Psi3gN4`. -/
noncomputable def i8Psi3gdN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 8) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (-1) * (one.kernel x * hpl [] x) +
    (1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (1 / 2) * (negOne.kernel x * hpl [one] x) +
    (1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-3 / 4) * (zero.kernel x * hpl [zero] x) +
    (-3 / 2) * (zero.kernel x * hpl [one] x) +
    (1 / 2) * (one.kernel x * hpl [negOne] x) +
    (-3 / 2) * (one.kernel x * hpl [zero] x) +
    (-3) * (one.kernel x * hpl [one] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (1) * (negOne.kernel x * hpl [zero, one] x) +
    (1) * (negOne.kernel x * hpl [one, zero] x) +
    (2) * (negOne.kernel x * hpl [one, one] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x) +
    (1) * (one.kernel x * hpl [negOne, zero] x) +
    (2) * (one.kernel x * hpl [negOne, one] x) +
    (1) * (one.kernel x * hpl [zero, negOne] x) +
    (2) * (one.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi3gN4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3gN4 (i8Psi3gdN4 x) x := by
  unfold i8Psi3gN4 i8Psi3gdN4
  exact ((((((((((((((((((((((((hasDerivAt_const x (-5 / 16)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (2)))

/-- The part of `Ψ₃⁽g⁾` with constant coefficients. -/
noncomputable def i8Psi3gW (x : ℝ) : ℝ :=
    (1 / 2) * hpl [zero, zero, zero] x +
    (1) * hpl [zero, zero, one] x +
    (1) * hpl [zero, one, zero] x +
    (2) * hpl [zero, one, one] x +
    (-2) * hpl [zero, negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, one] x +
    (-4) * hpl [zero, negOne, one, zero] x +
    (-8) * hpl [zero, negOne, one, one] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne, one] x +
    (-2) * hpl [zero, zero, zero, negOne] x +
    (-4) * hpl [zero, zero, one, negOne] x +
    (-4) * hpl [zero, one, negOne, zero] x +
    (-8) * hpl [zero, one, negOne, one] x +
    (-4) * hpl [zero, one, zero, negOne] x +
    (-8) * hpl [zero, one, one, negOne] x

/-- The derivative of `i8Psi3gW`. -/
noncomputable def i8Psi3gdW (x : ℝ) : ℝ :=
    (1 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (1) * (zero.kernel x * hpl [zero, one] x) +
    (1) * (zero.kernel x * hpl [one, zero] x) +
    (2) * (zero.kernel x * hpl [one, one] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (-4) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one, one] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (-2) * (zero.kernel x * hpl [zero, zero, negOne] x) +
    (-4) * (zero.kernel x * hpl [zero, one, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [one, negOne, one] x) +
    (-4) * (zero.kernel x * hpl [one, zero, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, one, negOne] x)

theorem hasDerivAt_i8Psi3gW {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3gW (i8Psi3gdW x) x := by
  unfold i8Psi3gW i8Psi3gdW
  exact (((((((((((((((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1 / 2)).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (-8)))

/-- The piece `Ψ₃⁽g⁾` of the primitive of `p₃ dt/dξ`. -/
noncomputable def i8Psi3g (x : ℝ) : ℝ :=
  (i8Psi3gN0 x + x * i8Psi3gN1 x + x ^ 2 * i8Psi3gN2 x + x ^ 3 * i8Psi3gN3 x +
    x ^ 4 * i8Psi3gN4 x) / x ^ 2 + i8Psi3gW x

/-- The derivative of `Ψ₃⁽g⁾`. -/
noncomputable def i8Psi3gD (x : ℝ) : ℝ :=
  ((i8Psi3gdN0 x + (i8Psi3gN1 x + x * i8Psi3gdN1 x) +
      (2 * x * i8Psi3gN2 x + x ^ 2 * i8Psi3gdN2 x) +
      (3 * x ^ 2 * i8Psi3gN3 x + x ^ 3 * i8Psi3gdN3 x) +
      (4 * x ^ 3 * i8Psi3gN4 x + x ^ 4 * i8Psi3gdN4 x)) * x ^ 2 -
    (i8Psi3gN0 x + x * i8Psi3gN1 x + x ^ 2 * i8Psi3gN2 x + x ^ 3 * i8Psi3gN3 x +
      x ^ 4 * i8Psi3gN4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi3gdW x

theorem hasDerivAt_i8Psi3g {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3g (i8Psi3gD x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := (((((hasDerivAt_i8Psi3gN0 hx).add (X.mul (hasDerivAt_i8Psi3gN1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi3gN2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi3gN3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi3gN4 hx))).div (X.pow 2) (pow_ne_zero 2 h0) |>.add
    (hasDerivAt_i8Psi3gW hx)
  unfold i8Psi3g
  refine e.congr_deriv ?_
  unfold i8Psi3gD
  simp only [Pi.pow_apply]
  norm_num

/-- The part `t λ²/2 A₁` of `p₃` in `ξ`. -/
noncomputable def i8P3xg (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 2 / 2 * i8A1x x

/-- **`(Ψ₃⁽g⁾)'(ξ) ξ' = p₃⁽g⁾`**, in terms of `ξ`. -/
theorem i8Psi3gD_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3gD x * (-x ^ 2 / (1 - x ^ 2)) = i8P3xg x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi3gD i8Psi3gN0 i8Psi3gN1 i8Psi3gN2 i8Psi3gN3 i8Psi3gN4 i8Psi3gdN0 i8Psi3gdN1
    i8Psi3gdN2 i8Psi3gdN3 i8Psi3gdN4 i8Psi3gdW i8P3xg i8A1x
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx,
    i13hw_10 hx, i13hw_1m hx, i13hw_11 hx, i13hw_0m0 hx, i13hw_m00 hx, i13hw_m01 hx, i13hw_m10 hx,
    i13hw_10m hx, i13hw_1m0 hx, i8hw_1m1 hx, i8hw_11m hx, i13_log_one_sub_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
