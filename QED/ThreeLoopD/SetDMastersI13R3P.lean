/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R3C

/-!
# Set (d), master `I₁₃`: the primitive of `p₃`

The primitive of `p₃` is `F₃(t) = Ψ₃(ξ(t))` (`QED.ThreeLoopD.hasDerivAt_i13F3`), where `Ψ₃`
(`QED.ThreeLoopD.i13Psi3`) is a combination of 37 harmonic polylogarithms `H(w; ξ)` of weight at
most four with coefficients in `ℚ[π², ζ(3)][ξ, 1/ξ]` (poles at most `ξ⁻²`). It is assembled from
the parts `ξ ^ j Nⱼ / ξ²` (`QED.ThreeLoopD.i13Psi3N0`, …) and the constant-coefficient part
`QED.ThreeLoopD.i13Psi3W`. The check `Ψ₃'(ξ) ξ'(t) = p₃(t)` rewrites every word in the Lyndon
basis (`QED.ThreeLoopD.i13hw_m0` and its companions), after which it is an identity of rational
functions.

## Main results

* `QED.ThreeLoopD.hasDerivAt_i13Psi3`, `QED.ThreeLoopD.i13Psi3D_mul`.
* `QED.ThreeLoopD.hasDerivAt_i13F3`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### The parts of `Ψ₃` -/

/-- The part of `ξ² Ψ₃` with the factor `ξ ^ 0`. -/
noncomputable def i13Psi3N0 (x : ℝ) : ℝ :=
    (499 / 16 - 2 * zeta3 - 11 / 12 * π ^ 2) +
    (π ^ 2 / 3) * hpl [negOne] x +
    (243 / 8 - π ^ 2 / 2) * hpl [zero] x +
    (81 / 4 - π ^ 2 / 3) * hpl [one] x +
    (-11) * hpl [negOne, zero] x +
    (99 / 4) * hpl [zero, zero] x +
    (33 / 2) * hpl [zero, one] x +
    (33 / 2) * hpl [one, zero] x +
    (11) * hpl [one, one] x +
    (4) * hpl [negOne, negOne, zero] x +
    (-10) * hpl [negOne, zero, zero] x +
    (-4) * hpl [negOne, zero, one] x +
    (-4) * hpl [negOne, one, zero] x +
    (-6) * hpl [zero, negOne, zero] x +
    (27 / 2) * hpl [zero, zero, zero] x +
    (9) * hpl [zero, zero, one] x +
    (9) * hpl [zero, one, zero] x +
    (6) * hpl [zero, one, one] x +
    (-4) * hpl [one, negOne, zero] x +
    (9) * hpl [one, zero, zero] x +
    (6) * hpl [one, zero, one] x +
    (6) * hpl [one, one, zero] x +
    (4) * hpl [one, one, one] x

/-- The derivative of `i13Psi3N0`. -/
noncomputable def i13Psi3dN0 (x : ℝ) : ℝ :=
    0 +
    (π ^ 2 / 3) * (negOne.kernel x * hpl [] x) +
    (243 / 8 - π ^ 2 / 2) * (zero.kernel x * hpl [] x) +
    (81 / 4 - π ^ 2 / 3) * (one.kernel x * hpl [] x) +
    (-11) * (negOne.kernel x * hpl [zero] x) +
    (99 / 4) * (zero.kernel x * hpl [zero] x) +
    (33 / 2) * (zero.kernel x * hpl [one] x) +
    (33 / 2) * (one.kernel x * hpl [zero] x) +
    (11) * (one.kernel x * hpl [one] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-10) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, one] x) +
    (-4) * (negOne.kernel x * hpl [one, zero] x) +
    (-6) * (zero.kernel x * hpl [negOne, zero] x) +
    (27 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (9) * (zero.kernel x * hpl [zero, one] x) +
    (9) * (zero.kernel x * hpl [one, zero] x) +
    (6) * (zero.kernel x * hpl [one, one] x) +
    (-4) * (one.kernel x * hpl [negOne, zero] x) +
    (9) * (one.kernel x * hpl [zero, zero] x) +
    (6) * (one.kernel x * hpl [zero, one] x) +
    (6) * (one.kernel x * hpl [one, zero] x) +
    (4) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i13Psi3N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13Psi3N0 (i13Psi3dN0 x) x := by
  unfold i13Psi3N0 i13Psi3dN0
  exact (((((((((((((((((((((((hasDerivAt_const x (499 / 16 - 2 * zeta3 - 11 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (243 / 8 - π ^ 2 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (81 / 4 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (99 / 4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (33 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (33 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (11))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (27 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (4)))

/-- The part of `ξ² Ψ₃` with the factor `ξ ^ 1`. -/
noncomputable def i13Psi3N1 (x : ℝ) : ℝ :=
    (-133 / 4 - 2 / 3 * π ^ 2) +
    (21 / 2 - 2 / 3 * π ^ 2) * hpl [zero] x +
    (-47) * hpl [one] x +
    (-8) * hpl [negOne, zero] x +
    (29) * hpl [zero, zero] x +
    (-10) * hpl [zero, one] x +
    (-10) * hpl [one, zero] x +
    (-36) * hpl [one, one] x +
    (-16) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (22) * hpl [zero, zero, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (-8) * hpl [zero, one, one] x +
    (4) * hpl [one, zero, zero] x +
    (-8) * hpl [one, zero, one] x +
    (-8) * hpl [one, one, zero] x +
    (-16) * hpl [one, one, one] x

/-- The derivative of `i13Psi3N1`. -/
noncomputable def i13Psi3dN1 (x : ℝ) : ℝ :=
    0 +
    (21 / 2 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-47) * (one.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (29) * (zero.kernel x * hpl [zero] x) +
    (-10) * (zero.kernel x * hpl [one] x) +
    (-10) * (one.kernel x * hpl [zero] x) +
    (-36) * (one.kernel x * hpl [one] x) +
    (-16) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (22) * (zero.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, one] x) +
    (4) * (one.kernel x * hpl [zero, zero] x) +
    (-8) * (one.kernel x * hpl [zero, one] x) +
    (-8) * (one.kernel x * hpl [one, zero] x) +
    (-16) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i13Psi3N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13Psi3N1 (i13Psi3dN1 x) x := by
  unfold i13Psi3N1 i13Psi3dN1
  exact ((((((((((((((((((hasDerivAt_const x (-133 / 4 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (21 / 2 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-47))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (29))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (22))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₃` with the factor `ξ ^ 2`. -/
noncomputable def i13Psi3N2 (x : ℝ) : ℝ :=
    (107 / 4 - 8 * zeta3 - 2 * π ^ 2) * hpl [zero] x +
    (107 / 2) * hpl [one] x +
    (77 / 2 - 4 / 3 * π ^ 2) * hpl [zero, zero] x +
    (25 - 4 / 3 * π ^ 2) * hpl [zero, one] x +
    (25) * hpl [one, zero] x +
    (50) * hpl [one, one] x +
    (-24) * hpl [negOne, zero, zero] x +
    (-24) * hpl [zero, negOne, zero] x +
    (41) * hpl [zero, zero, zero] x +
    (30) * hpl [zero, zero, one] x +
    (30) * hpl [zero, one, zero] x +
    (12) * hpl [zero, one, one] x +
    (-14) * hpl [one, zero, zero] x +
    (12) * hpl [one, zero, one] x +
    (12) * hpl [one, one, zero] x +
    (24) * hpl [one, one, one] x

/-- The derivative of `i13Psi3N2`. -/
noncomputable def i13Psi3dN2 (x : ℝ) : ℝ :=
    (107 / 4 - 8 * zeta3 - 2 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (107 / 2) * (one.kernel x * hpl [] x) +
    (77 / 2 - 4 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (25 - 4 / 3 * π ^ 2) * (zero.kernel x * hpl [one] x) +
    (25) * (one.kernel x * hpl [zero] x) +
    (50) * (one.kernel x * hpl [one] x) +
    (-24) * (negOne.kernel x * hpl [zero, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero] x) +
    (41) * (zero.kernel x * hpl [zero, zero] x) +
    (30) * (zero.kernel x * hpl [zero, one] x) +
    (30) * (zero.kernel x * hpl [one, zero] x) +
    (12) * (zero.kernel x * hpl [one, one] x) +
    (-14) * (one.kernel x * hpl [zero, zero] x) +
    (12) * (one.kernel x * hpl [zero, one] x) +
    (12) * (one.kernel x * hpl [one, zero] x) +
    (24) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i13Psi3N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13Psi3N2 (i13Psi3dN2 x) x := by
  unfold i13Psi3N2 i13Psi3dN2
  exact (((((((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (107 / 4 - 8 * zeta3 -
    2 * π ^ 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (107 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (77 / 2 - 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (25 - 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (25))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (50))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (41))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (30))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (30))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (24)))

/-- The part of `ξ² Ψ₃` with the factor `ξ ^ 3`. -/
noncomputable def i13Psi3N3 (x : ℝ) : ℝ :=
    (-133 / 4 + 2 / 3 * π ^ 2) +
    (-115 / 2 - 2 / 3 * π ^ 2) * hpl [zero] x +
    (-47) * hpl [one] x +
    (8) * hpl [negOne, zero] x +
    (5) * hpl [zero, zero] x +
    (-26) * hpl [zero, one] x +
    (-26) * hpl [one, zero] x +
    (-36) * hpl [one, one] x +
    (-16) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (22) * hpl [zero, zero, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (-8) * hpl [zero, one, one] x +
    (4) * hpl [one, zero, zero] x +
    (-8) * hpl [one, zero, one] x +
    (-8) * hpl [one, one, zero] x +
    (-16) * hpl [one, one, one] x

/-- The derivative of `i13Psi3N3`. -/
noncomputable def i13Psi3dN3 (x : ℝ) : ℝ :=
    0 +
    (-115 / 2 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-47) * (one.kernel x * hpl [] x) +
    (8) * (negOne.kernel x * hpl [zero] x) +
    (5) * (zero.kernel x * hpl [zero] x) +
    (-26) * (zero.kernel x * hpl [one] x) +
    (-26) * (one.kernel x * hpl [zero] x) +
    (-36) * (one.kernel x * hpl [one] x) +
    (-16) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (22) * (zero.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, one] x) +
    (4) * (one.kernel x * hpl [zero, zero] x) +
    (-8) * (one.kernel x * hpl [zero, one] x) +
    (-8) * (one.kernel x * hpl [one, zero] x) +
    (-16) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i13Psi3N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13Psi3N3 (i13Psi3dN3 x) x := by
  unfold i13Psi3N3 i13Psi3dN3
  exact ((((((((((((((((((hasDerivAt_const x (-133 / 4 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-115 / 2 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-47))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-26))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-26))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (22))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₃` with the factor `ξ ^ 4`. -/
noncomputable def i13Psi3N4 (x : ℝ) : ℝ :=
    (499 / 16 + 2 * zeta3 + 11 / 12 * π ^ 2) +
    (-π ^ 2 / 3) * hpl [negOne] x +
    (-81 / 8 + π ^ 2 / 6) * hpl [zero] x +
    (81 / 4 + π ^ 2 / 3) * hpl [one] x +
    (11) * hpl [negOne, zero] x +
    (-33 / 4) * hpl [zero, zero] x +
    (-11 / 2) * hpl [zero, one] x +
    (-11 / 2) * hpl [one, zero] x +
    (11) * hpl [one, one] x +
    (-4) * hpl [negOne, negOne, zero] x +
    (2) * hpl [negOne, zero, zero] x +
    (4) * hpl [negOne, zero, one] x +
    (4) * hpl [negOne, one, zero] x +
    (2) * hpl [zero, negOne, zero] x +
    (-1 / 2) * hpl [zero, zero, zero] x +
    (-3) * hpl [zero, zero, one] x +
    (-3) * hpl [zero, one, zero] x +
    (-2) * hpl [zero, one, one] x +
    (4) * hpl [one, negOne, zero] x +
    (-3) * hpl [one, zero, zero] x +
    (-2) * hpl [one, zero, one] x +
    (-2) * hpl [one, one, zero] x +
    (4) * hpl [one, one, one] x

/-- The derivative of `i13Psi3N4`. -/
noncomputable def i13Psi3dN4 (x : ℝ) : ℝ :=
    0 +
    (-π ^ 2 / 3) * (negOne.kernel x * hpl [] x) +
    (-81 / 8 + π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (81 / 4 + π ^ 2 / 3) * (one.kernel x * hpl [] x) +
    (11) * (negOne.kernel x * hpl [zero] x) +
    (-33 / 4) * (zero.kernel x * hpl [zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [one] x) +
    (-11 / 2) * (one.kernel x * hpl [zero] x) +
    (11) * (one.kernel x * hpl [one] x) +
    (-4) * (negOne.kernel x * hpl [negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, one] x) +
    (4) * (negOne.kernel x * hpl [one, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, one] x) +
    (-3) * (zero.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [one, one] x) +
    (4) * (one.kernel x * hpl [negOne, zero] x) +
    (-3) * (one.kernel x * hpl [zero, zero] x) +
    (-2) * (one.kernel x * hpl [zero, one] x) +
    (-2) * (one.kernel x * hpl [one, zero] x) +
    (4) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i13Psi3N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13Psi3N4 (i13Psi3dN4 x) x := by
  unfold i13Psi3N4 i13Psi3dN4
  exact (((((((((((((((((((((((hasDerivAt_const x (499 / 16 + 2 * zeta3 + 11 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-81 / 8 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (81 / 4 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (11))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-33 / 4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (11))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (4)))

/-- The part of `Ψ₃` with constant coefficients. -/
noncomputable def i13Psi3W (x : ℝ) : ℝ :=
    (4 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (-24) * hpl [zero, negOne, zero, zero] x +
    (-16) * hpl [zero, negOne, zero, one] x +
    (-16) * hpl [zero, negOne, one, zero] x +
    (-16) * hpl [zero, zero, negOne, zero] x +
    (28) * hpl [zero, zero, zero, zero] x +
    (24) * hpl [zero, zero, zero, one] x +
    (24) * hpl [zero, zero, one, zero] x +
    (16) * hpl [zero, zero, one, one] x +
    (-16) * hpl [zero, one, negOne, zero] x +
    (24) * hpl [zero, one, zero, zero] x +
    (16) * hpl [zero, one, zero, one] x +
    (16) * hpl [zero, one, one, zero] x

/-- The derivative of `i13Psi3W`. -/
noncomputable def i13Psi3dW (x : ℝ) : ℝ :=
    (4 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (-16) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (28) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, zero, one] x) +
    (24) * (zero.kernel x * hpl [zero, one, zero] x) +
    (16) * (zero.kernel x * hpl [zero, one, one] x) +
    (-16) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (24) * (zero.kernel x * hpl [one, zero, zero] x) +
    (16) * (zero.kernel x * hpl [one, zero, one] x) +
    (16) * (zero.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i13Psi3W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13Psi3W (i13Psi3dW x) x := by
  unfold i13Psi3W i13Psi3dW
  exact (((((((((((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (4 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (16)))

/-! ### `Ψ₃` and its derivative -/

/-- The primitive `Ψ₃` of `p₃ dt/dξ`, as a function of `ξ`. -/
noncomputable def i13Psi3 (x : ℝ) : ℝ :=
  (i13Psi3N0 x + x * i13Psi3N1 x + x ^ 2 * i13Psi3N2 x + x ^ 3 * i13Psi3N3 x +
    x ^ 4 * i13Psi3N4 x) / x ^ 2 + i13Psi3W x

/-- The derivative of `Ψ₃`. -/
noncomputable def i13Psi3D (x : ℝ) : ℝ :=
  ((i13Psi3dN0 x + (i13Psi3N1 x + x * i13Psi3dN1 x) +
      (2 * x * i13Psi3N2 x + x ^ 2 * i13Psi3dN2 x) +
      (3 * x ^ 2 * i13Psi3N3 x + x ^ 3 * i13Psi3dN3 x) +
      (4 * x ^ 3 * i13Psi3N4 x + x ^ 4 * i13Psi3dN4 x)) * x ^ 2 -
    (i13Psi3N0 x + x * i13Psi3N1 x + x ^ 2 * i13Psi3N2 x + x ^ 3 * i13Psi3N3 x +
      x ^ 4 * i13Psi3N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i13Psi3dW x

theorem hasDerivAt_i13Psi3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i13Psi3 (i13Psi3D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := (((((hasDerivAt_i13Psi3N0 hx).add (X.mul (hasDerivAt_i13Psi3N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i13Psi3N2 hx))).add ((X.pow 3).mul (hasDerivAt_i13Psi3N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i13Psi3N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0) |>.add
    (hasDerivAt_i13Psi3W hx)
  unfold i13Psi3
  refine e.congr_deriv ?_
  unfold i13Psi3D
  simp only [Pi.pow_apply]
  norm_num

/-- `p₃` in the variable `ξ`. -/
noncomputable def i13P3x (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * ((1 + x) / (1 - x) * (i13PB x - i13P1c)) +
    2 * (2 + Real.log x * (1 + x) / (1 - x)) * i13Be2x x -
    (2 * Real.log (1 - x) - Real.log x) *
      (2 * i13Be2x x + (2 + Real.log x * (1 + x) / (1 - x)) ^ 2) +
    (2 * Real.log (1 - x) - Real.log x) ^ 2 * (2 + Real.log x * (1 + x) / (1 - x)) -
    (2 * Real.log (1 - x) - Real.log x) ^ 3 / 6)

theorem i13P3_eq {t : ℝ} (ht : 0 < t) : i13P3 t = i13P3x (i13Xi t) := by
  have hT := (i13Xi_t ht.le).symm
  have hlog := (i13_log_eq_xi ht).symm
  unfold i13P3 i13P3x i13Be3r i13Be1r
  rw [i13Be2r_eq, hT, hlog]

/-- **`Ψ₃'(ξ) ξ' = p₃`**, in terms of `ξ`. -/
theorem i13Psi3D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i13Psi3D x * (-x ^ 2 / (1 - x ^ 2)) = i13P3x x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i13Psi3D i13Psi3N0 i13Psi3N1 i13Psi3N2 i13Psi3N3 i13Psi3N4 i13Psi3dN0 i13Psi3dN1
    i13Psi3dN2 i13Psi3dN3 i13Psi3dN4 i13Psi3dW i13P3x i13PB i13PBH i13Be2x i13P1c
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx,
    i13hw_10 hx, i13hw_11 hx, i13hw_000, i13hw_0m0 hx, i13hw_010 hx, i13hw_m00 hx, i13hw_m01 hx,
    i13hw_mm0 hx, i13hw_m10 hx, i13hw_100 hx, i13hw_101 hx, i13hw_1m0 hx, i13hw_110 hx, i13hw_111
    hx,
    i13_Li₂_neg_eq hx, i13_log_one_add_eq hx, i13_log_one_sub_eq hx]
  field_simp
  ring

/-! ### The primitive `F₃` -/

/-- `F₃(t) = Ψ₃(ξ(t))`. -/
noncomputable def i13F3 (t : ℝ) : ℝ := i13Psi3 (i13Xi t)

theorem hasDerivAt_i13F3 {t : ℝ} (ht : 0 < t) : HasDerivAt i13F3 (i13P3 t) t := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have e := (hasDerivAt_i13Psi3 ⟨hx0, hx1⟩).comp t (hasDerivAt_i13Xi ht)
  rw [i13Psi3D_mul ⟨hx0, hx1⟩, ← i13P3_eq ht] at e
  exact e

end QED.ThreeLoopD
