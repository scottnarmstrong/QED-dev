/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P2

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 11 to 16

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s11`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s11D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s11`, `QED.ThreeLoopD.i8Psi4s11D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽11⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s11N0 (x : ℝ) : ℝ :=
    (-8 + 2 * zeta3 + π ^ 2 / 3) * hpl [negOne] x

/-- The derivative of `i8Psi4s11N0`. -/
noncomputable def i8Psi4s11dN0 (x : ℝ) : ℝ :=
    (-8 + 2 * zeta3 + π ^ 2 / 3) * (negOne.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s11N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s11N0 (i8Psi4s11dN0 x) x := by
  unfold i8Psi4s11N0 i8Psi4s11dN0
  exact ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-8 + 2 * zeta3 + π ^ 2 / 3))

/-- The part of `ξ² Ψ₄⁽11⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s11N1 (x : ℝ) : ℝ :=
    (-8 + 2 * zeta3 + π ^ 2 / 3) +
    (8 * zeta3 + 4 / 3 * π ^ 2) * hpl [negOne] x

/-- The derivative of `i8Psi4s11N1`. -/
noncomputable def i8Psi4s11dN1 (x : ℝ) : ℝ :=
    0 +
    (8 * zeta3 + 4 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s11N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s11N1 (i8Psi4s11dN1 x) x := by
  unfold i8Psi4s11N1 i8Psi4s11dN1
  exact ((hasDerivAt_const x (-8 + 2 * zeta3 + π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (8 * zeta3 + 4 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽11⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s11N2 (x : ℝ) : ℝ :=
    (2 * π ^ 2 + 12 * zeta3) * hpl [negOne] x

/-- The derivative of `i8Psi4s11N2`. -/
noncomputable def i8Psi4s11dN2 (x : ℝ) : ℝ :=
    (2 * π ^ 2 + 12 * zeta3) * (negOne.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s11N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s11N2 (i8Psi4s11dN2 x) x := by
  unfold i8Psi4s11N2 i8Psi4s11dN2
  exact ((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 * π ^ 2 + 12 * zeta3))

/-- The part of `ξ² Ψ₄⁽11⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s11N3 (x : ℝ) : ℝ :=
    (8 - π ^ 2 - 6 * zeta3) +
    (8 * zeta3 + 4 / 3 * π ^ 2) * hpl [negOne] x

/-- The derivative of `i8Psi4s11N3`. -/
noncomputable def i8Psi4s11dN3 (x : ℝ) : ℝ :=
    0 +
    (8 * zeta3 + 4 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s11N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s11N3 (i8Psi4s11dN3 x) x := by
  unfold i8Psi4s11N3 i8Psi4s11dN3
  exact ((hasDerivAt_const x (8 - π ^ 2 - 6 * zeta3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (8 * zeta3 + 4 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽11⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s11N4 (x : ℝ) : ℝ :=
    (-4 - zeta3 - π ^ 2 / 6) +
    (8 + 2 * zeta3 + π ^ 2 / 3) * hpl [negOne] x

/-- The derivative of `i8Psi4s11N4`. -/
noncomputable def i8Psi4s11dN4 (x : ℝ) : ℝ :=
    0 +
    (8 + 2 * zeta3 + π ^ 2 / 3) * (negOne.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s11N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s11N4 (i8Psi4s11dN4 x) x := by
  unfold i8Psi4s11N4 i8Psi4s11dN4
  exact ((hasDerivAt_const x (-4 - zeta3 - π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (8 + 2 * zeta3 + π ^ 2 / 3)))

/-- The part of `Ψ₄⁽11⁾` with constant coefficients. -/
noncomputable def i8Psi4s11W (x : ℝ) : ℝ :=
    (-8 - π ^ 2 - 6 * zeta3) * hpl [zero] x +
    (-32) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s11W`. -/
noncomputable def i8Psi4s11dW (x : ℝ) : ℝ :=
    (-8 - π ^ 2 - 6 * zeta3) * (zero.kernel x * hpl [] x) +
    (-32) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s11W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s11W (i8Psi4s11dW x) x := by
  unfold i8Psi4s11W i8Psi4s11dW
  exact (((hasDerivAt_hpl_cons zero [] hx).const_mul (-8 - π ^ 2 - 6 * zeta3)).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-32)))

/-- The piece `Ψ₄⁽11⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s11 (x : ℝ) : ℝ :=
  (i8Psi4s11N0 x + x * i8Psi4s11N1 x + x ^ 2 * i8Psi4s11N2 x + x ^ 3 * i8Psi4s11N3 x +
    x ^ 4 * i8Psi4s11N4 x) / x ^ 2 + i8Psi4s11W x

/-- The derivative of `Ψ₄⁽11⁾`. -/
noncomputable def i8Psi4s11D (x : ℝ) : ℝ :=
  ((i8Psi4s11dN0 x + (i8Psi4s11N1 x + x * i8Psi4s11dN1 x) + (2 * x * i8Psi4s11N2 x +
    x ^ 2 * i8Psi4s11dN2 x) + (3 * x ^ 2 * i8Psi4s11N3 x + x ^ 3 * i8Psi4s11dN3 x) +
    (4 * x ^ 3 * i8Psi4s11N4 x + x ^ 4 * i8Psi4s11dN4 x)) * x ^ 2 - (i8Psi4s11N0 x +
    x * i8Psi4s11N1 x + x ^ 2 * i8Psi4s11N2 x + x ^ 3 * i8Psi4s11N3 x +
    x ^ 4 * i8Psi4s11N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s11dW x

theorem hasDerivAt_i8Psi4s11 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s11 (i8Psi4s11D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s11N0 hx).add (X.mul (hasDerivAt_i8Psi4s11N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s11N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s11N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s11N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s11W hx)
  unfold i8Psi4s11
  refine e.congr_deriv ?_
  unfold i8Psi4s11D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 11 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s11 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((24 + ((-1) * π ^ 2) + ((-24) * x) +
    ((-6) * zeta3) + ((-1) * π ^ 2 * x) + ((-6) * x * zeta3)) / (3 + (3 * x)))) * ((1 + x) / (1 -
    x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽11⁾)'(ξ) ξ' = p₄⁽11⁾`**, in terms of `ξ`. -/
theorem i8Psi4s11D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s11D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s11 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s11D i8Psi4s11N0 i8Psi4s11N1 i8Psi4s11N2 i8Psi4s11N3 i8Psi4s11N4 i8Psi4s11dN0
    i8Psi4s11dN1 i8Psi4s11dN2 i8Psi4s11dN3 i8Psi4s11dN4 i8Psi4s11dW i8P4s11
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽12⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s12N0 (x : ℝ) : ℝ :=
    (-2 + π ^ 2 / 12) * hpl [negOne] x +
    (-4 + π ^ 2 / 6) * hpl [negOne, zero] x +
    (-4 + π ^ 2 / 6) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s12N0`. -/
noncomputable def i8Psi4s12dN0 (x : ℝ) : ℝ :=
    (-2 + π ^ 2 / 12) * (negOne.kernel x * hpl [] x) +
    (-4 + π ^ 2 / 6) * (negOne.kernel x * hpl [zero] x) +
    (-4 + π ^ 2 / 6) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s12N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s12N0 (i8Psi4s12dN0 x) x := by
  unfold i8Psi4s12N0 i8Psi4s12dN0
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-2 + π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4 + π ^ 2 / 6)))

/-- The part of `ξ² Ψ₄⁽12⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s12N1 (x : ℝ) : ℝ :=
    (-6 + π ^ 2 / 4) +
    (-16 + 2 / 3 * π ^ 2) * hpl [negOne] x +
    (-4 + π ^ 2 / 6) * hpl [zero] x +
    (-16 + 2 / 3 * π ^ 2) * hpl [negOne, zero] x +
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s12N1`. -/
noncomputable def i8Psi4s12dN1 (x : ℝ) : ℝ :=
    0 +
    (-16 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-4 + π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (-16 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (-16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s12N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s12N1 (i8Psi4s12dN1 x) x := by
  unfold i8Psi4s12N1 i8Psi4s12dN1
  exact (((((hasDerivAt_const x (-6 + π ^ 2 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-16 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-16 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-16 + 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽12⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s12N2 (x : ℝ) : ℝ :=
    (14 - 7 / 12 * π ^ 2) * hpl [zero] x +
    (-24 + π ^ 2) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s12N2`. -/
noncomputable def i8Psi4s12dN2 (x : ℝ) : ℝ :=
    (14 - 7 / 12 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-24 + π ^ 2) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s12N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s12N2 (i8Psi4s12dN2 x) x := by
  unfold i8Psi4s12N2 i8Psi4s12dN2
  exact (((hasDerivAt_hpl_cons zero [] hx).const_mul (14 - 7 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-24 + π ^ 2)))

/-- The part of `ξ² Ψ₄⁽12⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s12N3 (x : ℝ) : ℝ :=
    (-26 + 13 / 12 * π ^ 2) +
    (16 - 2 / 3 * π ^ 2) * hpl [negOne] x +
    (12 - π ^ 2 / 2) * hpl [zero] x +
    (-16 + 2 / 3 * π ^ 2) * hpl [negOne, zero] x +
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s12N3`. -/
noncomputable def i8Psi4s12dN3 (x : ℝ) : ℝ :=
    0 +
    (16 - 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (12 - π ^ 2 / 2) * (zero.kernel x * hpl [] x) +
    (-16 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (-16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s12N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s12N3 (i8Psi4s12dN3 x) x := by
  unfold i8Psi4s12N3 i8Psi4s12dN3
  exact (((((hasDerivAt_const x (-26 + 13 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (16 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (12 - π ^ 2 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-16 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-16 + 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽12⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s12N4 (x : ℝ) : ℝ :=
    (-2 + π ^ 2 / 12) +
    (2 - π ^ 2 / 12) * hpl [negOne] x +
    (2 - π ^ 2 / 12) * hpl [zero] x +
    (-4 + π ^ 2 / 6) * hpl [negOne, zero] x +
    (-4 + π ^ 2 / 6) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s12N4`. -/
noncomputable def i8Psi4s12dN4 (x : ℝ) : ℝ :=
    0 +
    (2 - π ^ 2 / 12) * (negOne.kernel x * hpl [] x) +
    (2 - π ^ 2 / 12) * (zero.kernel x * hpl [] x) +
    (-4 + π ^ 2 / 6) * (negOne.kernel x * hpl [zero] x) +
    (-4 + π ^ 2 / 6) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s12N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s12N4 (i8Psi4s12dN4 x) x := by
  unfold i8Psi4s12N4 i8Psi4s12dN4
  exact (((((hasDerivAt_const x (-2 + π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 - π ^ 2 / 12))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2 - π ^ 2 / 12))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4 + π ^ 2 / 6)))

/-- The part of `Ψ₄⁽12⁾` with constant coefficients. -/
noncomputable def i8Psi4s12W (x : ℝ) : ℝ :=
    (12 - π ^ 2 / 2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s12W`. -/
noncomputable def i8Psi4s12dW (x : ℝ) : ℝ :=
    (12 - π ^ 2 / 2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s12W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s12W (i8Psi4s12dW x) x := by
  unfold i8Psi4s12W i8Psi4s12dW
  exact ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (12 - π ^ 2 / 2))

/-- The piece `Ψ₄⁽12⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s12 (x : ℝ) : ℝ :=
  (i8Psi4s12N0 x + x * i8Psi4s12N1 x + x ^ 2 * i8Psi4s12N2 x + x ^ 3 * i8Psi4s12N3 x +
    x ^ 4 * i8Psi4s12N4 x) / x ^ 2 + i8Psi4s12W x

/-- The derivative of `Ψ₄⁽12⁾`. -/
noncomputable def i8Psi4s12D (x : ℝ) : ℝ :=
  ((i8Psi4s12dN0 x + (i8Psi4s12N1 x + x * i8Psi4s12dN1 x) + (2 * x * i8Psi4s12N2 x +
    x ^ 2 * i8Psi4s12dN2 x) + (3 * x ^ 2 * i8Psi4s12N3 x + x ^ 3 * i8Psi4s12dN3 x) +
    (4 * x ^ 3 * i8Psi4s12N4 x + x ^ 4 * i8Psi4s12dN4 x)) * x ^ 2 - (i8Psi4s12N0 x +
    x * i8Psi4s12N1 x + x ^ 2 * i8Psi4s12N2 x + x ^ 3 * i8Psi4s12N3 x +
    x ^ 4 * i8Psi4s12N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s12dW x

theorem hasDerivAt_i8Psi4s12 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s12 (i8Psi4s12D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s12N0 hx).add (X.mul (hasDerivAt_i8Psi4s12N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s12N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s12N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s12N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s12W hx)
  unfold i8Psi4s12
  refine e.congr_deriv ?_
  unfold i8Psi4s12D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 12 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s12 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * (((24 +
    ((-1) * π ^ 2)) / 6) * hpl [zero] x)) * ((1 + x) / (1 - x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽12⁾)'(ξ) ξ' = p₄⁽12⁾`**, in terms of `ξ`. -/
theorem i8Psi4s12D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s12D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s12 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s12D i8Psi4s12N0 i8Psi4s12N1 i8Psi4s12N2 i8Psi4s12N3 i8Psi4s12N4 i8Psi4s12dN0
    i8Psi4s12dN1 i8Psi4s12dN2 i8Psi4s12dN3 i8Psi4s12dN4 i8Psi4s12dW i8P4s12
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽13⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s13N0 (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * hpl [negOne, negOne] x

/-- The derivative of `i8Psi4s13N0`. -/
noncomputable def i8Psi4s13dN0 (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * (negOne.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s13N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s13N0 (i8Psi4s13dN0 x) x := by
  unfold i8Psi4s13N0 i8Psi4s13dN0
  exact ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-2 / 3 * π ^ 2))

/-- The part of `ξ² Ψ₄⁽13⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s13N1 (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * hpl [negOne] x +
    (-8 / 3 * π ^ 2) * hpl [negOne, negOne] x

/-- The derivative of `i8Psi4s13N1`. -/
noncomputable def i8Psi4s13dN1 (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-8 / 3 * π ^ 2) * (negOne.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s13N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s13N1 (i8Psi4s13dN1 x) x := by
  unfold i8Psi4s13N1 i8Psi4s13dN1
  exact (((hasDerivAt_hpl_cons negOne [] hx).const_mul (-2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-8 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽13⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s13N2 (x : ℝ) : ℝ :=
    (π ^ 2) * hpl [negOne] x +
    (-4 * π ^ 2) * hpl [negOne, negOne] x

/-- The derivative of `i8Psi4s13N2`. -/
noncomputable def i8Psi4s13dN2 (x : ℝ) : ℝ :=
    (π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-4 * π ^ 2) * (negOne.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s13N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s13N2 (i8Psi4s13dN2 x) x := by
  unfold i8Psi4s13N2 i8Psi4s13dN2
  exact (((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-4 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽13⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s13N3 (x : ℝ) : ℝ :=
    (-5 / 3 * π ^ 2) +
    (2 * π ^ 2) * hpl [negOne] x +
    (-8 / 3 * π ^ 2) * hpl [negOne, negOne] x

/-- The derivative of `i8Psi4s13N3`. -/
noncomputable def i8Psi4s13dN3 (x : ℝ) : ℝ :=
    0 +
    (2 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-8 / 3 * π ^ 2) * (negOne.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s13N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s13N3 (i8Psi4s13dN3 x) x := by
  unfold i8Psi4s13N3 i8Psi4s13dN3
  exact (((hasDerivAt_const x (-5 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-8 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽13⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s13N4 (x : ℝ) : ℝ :=
    (-π ^ 2 / 6) +
    (π ^ 2 / 3) * hpl [negOne] x +
    (-2 / 3 * π ^ 2) * hpl [negOne, negOne] x

/-- The derivative of `i8Psi4s13N4`. -/
noncomputable def i8Psi4s13dN4 (x : ℝ) : ℝ :=
    0 +
    (π ^ 2 / 3) * (negOne.kernel x * hpl [] x) +
    (-2 / 3 * π ^ 2) * (negOne.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s13N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s13N4 (i8Psi4s13dN4 x) x := by
  unfold i8Psi4s13N4 i8Psi4s13dN4
  exact (((hasDerivAt_const x (-π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-2 / 3 * π ^ 2)))

/-- The part of `Ψ₄⁽13⁾` with constant coefficients. -/
noncomputable def i8Psi4s13W (x : ℝ) : ℝ :=
    (2 / 3 * π ^ 2) * hpl [zero] x +
    (2 * π ^ 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s13W`. -/
noncomputable def i8Psi4s13dW (x : ℝ) : ℝ :=
    (2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (2 * π ^ 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s13W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s13W (i8Psi4s13dW x) x := by
  unfold i8Psi4s13W i8Psi4s13dW
  exact (((hasDerivAt_hpl_cons zero [] hx).const_mul (2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2 * π ^ 2)))

/-- The piece `Ψ₄⁽13⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s13 (x : ℝ) : ℝ :=
  (i8Psi4s13N0 x + x * i8Psi4s13N1 x + x ^ 2 * i8Psi4s13N2 x + x ^ 3 * i8Psi4s13N3 x +
    x ^ 4 * i8Psi4s13N4 x) / x ^ 2 + i8Psi4s13W x

/-- The derivative of `Ψ₄⁽13⁾`. -/
noncomputable def i8Psi4s13D (x : ℝ) : ℝ :=
  ((i8Psi4s13dN0 x + (i8Psi4s13N1 x + x * i8Psi4s13dN1 x) + (2 * x * i8Psi4s13N2 x +
    x ^ 2 * i8Psi4s13dN2 x) + (3 * x ^ 2 * i8Psi4s13N3 x + x ^ 3 * i8Psi4s13dN3 x) +
    (4 * x ^ 3 * i8Psi4s13N4 x + x ^ 4 * i8Psi4s13dN4 x)) * x ^ 2 - (i8Psi4s13N0 x +
    x * i8Psi4s13N1 x + x ^ 2 * i8Psi4s13N2 x + x ^ 3 * i8Psi4s13N3 x +
    x ^ 4 * i8Psi4s13N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s13dW x

theorem hasDerivAt_i8Psi4s13 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s13 (i8Psi4s13D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s13N0 hx).add (X.mul (hasDerivAt_i8Psi4s13N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s13N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s13N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s13N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s13W hx)
  unfold i8Psi4s13
  refine e.congr_deriv ?_
  unfold i8Psi4s13D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 13 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s13 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((π ^ 2 / 3) * hpl [negOne] x)) * ((1 + x) / (1 -
    x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽13⁾)'(ξ) ξ' = p₄⁽13⁾`**, in terms of `ξ`. -/
theorem i8Psi4s13D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s13D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s13 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s13D i8Psi4s13N0 i8Psi4s13N1 i8Psi4s13N2 i8Psi4s13N3 i8Psi4s13N4 i8Psi4s13dN0
    i8Psi4s13dN1 i8Psi4s13dN2 i8Psi4s13dN3 i8Psi4s13dN4 i8Psi4s13dW i8P4s13
  simp only [kernel_zero, kernel_negOne, hpl_nil, i13hw_mm hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽14⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s14N0 (x : ℝ) : ℝ :=
    (2) * hpl [negOne, negOne, zero] x +
    (1) * hpl [negOne, zero, negOne] x +
    (2) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (2) * hpl [zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s14N0`. -/
noncomputable def i8Psi4s14dN0 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s14N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s14N0 (i8Psi4s14dN0 x) x := by
  unfold i8Psi4s14N0 i8Psi4s14dN0
  exact ((((((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽14⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s14N1 (x : ℝ) : ℝ :=
    (1) * hpl [negOne] x +
    (4) * hpl [negOne, zero] x +
    (1) * hpl [zero, negOne] x +
    (16) * hpl [negOne, negOne, zero] x +
    (8) * hpl [negOne, zero, negOne] x +
    (2) * hpl [zero, negOne, zero] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (8) * hpl [zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s14N1`. -/
noncomputable def i8Psi4s14dN1 (x : ℝ) : ℝ :=
    (1) * (negOne.kernel x * hpl [] x) +
    (4) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s14N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s14N1 (i8Psi4s14dN1 x) x := by
  unfold i8Psi4s14N1 i8Psi4s14dN1
  exact ((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽14⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s14N2 (x : ℝ) : ℝ :=
    (-23 / 4) * hpl [negOne] x +
    (-1) * hpl [zero] x +
    (45 / 2) * hpl [negOne, zero] x +
    (-14) * hpl [zero, negOne, zero] x +
    (12) * hpl [negOne, zero, negOne, zero] x

/-- The derivative of `i8Psi4s14N2`. -/
noncomputable def i8Psi4s14dN2 (x : ℝ) : ℝ :=
    (-23 / 4) * (negOne.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [] x) +
    (45 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-14) * (zero.kernel x * hpl [negOne, zero] x) +
    (12) * (negOne.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s14N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s14N2 (i8Psi4s14dN2 x) x := by
  unfold i8Psi4s14N2 i8Psi4s14dN2
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-23 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (45 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽14⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s14N3 (x : ℝ) : ℝ :=
    (101 / 4) +
    (-7) * hpl [negOne] x +
    (-37 / 2) * hpl [zero] x +
    (20) * hpl [negOne, zero] x +
    (7) * hpl [zero, negOne] x +
    (-16) * hpl [negOne, negOne, zero] x +
    (-8) * hpl [negOne, zero, negOne] x +
    (-6) * hpl [zero, negOne, zero] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (8) * hpl [zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s14N3`. -/
noncomputable def i8Psi4s14dN3 (x : ℝ) : ℝ :=
    0 +
    (-7) * (negOne.kernel x * hpl [] x) +
    (-37 / 2) * (zero.kernel x * hpl [] x) +
    (20) * (negOne.kernel x * hpl [zero] x) +
    (7) * (zero.kernel x * hpl [negOne] x) +
    (-16) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-6) * (zero.kernel x * hpl [negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s14N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s14N3 (i8Psi4s14dN3 x) x := by
  unfold i8Psi4s14N3 i8Psi4s14dN3
  exact (((((((((((hasDerivAt_const x (101 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-37 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽14⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s14N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 4) * hpl [negOne] x +
    (-3 / 4) * hpl [zero] x +
    (3 / 2) * hpl [negOne, zero] x +
    (1 / 2) * hpl [zero, negOne] x +
    (-2) * hpl [negOne, negOne, zero] x +
    (-1) * hpl [negOne, zero, negOne] x +
    (-1) * hpl [zero, negOne, zero] x +
    (2) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (2) * hpl [zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s14N4`. -/
noncomputable def i8Psi4s14dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 4) * (negOne.kernel x * hpl [] x) +
    (-3 / 4) * (zero.kernel x * hpl [] x) +
    (3 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s14N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s14N4 (i8Psi4s14dN4 x) x := by
  unfold i8Psi4s14N4 i8Psi4s14dN4
  exact (((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (2)))

/-- The part of `Ψ₄⁽14⁾` with constant coefficients. -/
noncomputable def i8Psi4s14W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, zero] x +
    (-7) * hpl [zero, zero, negOne] x +
    (-6) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s14W`. -/
noncomputable def i8Psi4s14dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [zero] x) +
    (-7) * (zero.kernel x * hpl [zero, negOne] x) +
    (-6) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s14W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s14W (i8Psi4s14dW x) x := by
  unfold i8Psi4s14W i8Psi4s14dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-6)))

/-- The piece `Ψ₄⁽14⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s14 (x : ℝ) : ℝ :=
  (i8Psi4s14N0 x + x * i8Psi4s14N1 x + x ^ 2 * i8Psi4s14N2 x + x ^ 3 * i8Psi4s14N3 x +
    x ^ 4 * i8Psi4s14N4 x) / x ^ 2 + i8Psi4s14W x

/-- The derivative of `Ψ₄⁽14⁾`. -/
noncomputable def i8Psi4s14D (x : ℝ) : ℝ :=
  ((i8Psi4s14dN0 x + (i8Psi4s14N1 x + x * i8Psi4s14dN1 x) + (2 * x * i8Psi4s14N2 x +
    x ^ 2 * i8Psi4s14dN2 x) + (3 * x ^ 2 * i8Psi4s14N3 x + x ^ 3 * i8Psi4s14dN3 x) +
    (4 * x ^ 3 * i8Psi4s14N4 x + x ^ 4 * i8Psi4s14dN4 x)) * x ^ 2 - (i8Psi4s14N0 x +
    x * i8Psi4s14N1 x + x ^ 2 * i8Psi4s14N2 x + x ^ 3 * i8Psi4s14N3 x +
    x ^ 4 * i8Psi4s14N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s14dW x

theorem hasDerivAt_i8Psi4s14 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s14 (i8Psi4s14D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s14N0 hx).add (X.mul (hasDerivAt_i8Psi4s14N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s14N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s14N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s14N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s14W hx)
  unfold i8Psi4s14
  refine e.congr_deriv ?_
  unfold i8Psi4s14D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 14 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s14 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * ((-2) * hpl [zero, negOne, zero] x)) * ((1 +
    x) / (1 - x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽14⁾)'(ξ) ξ' = p₄⁽14⁾`**, in terms of `ξ`. -/
theorem i8Psi4s14D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s14D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s14 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s14D i8Psi4s14N0 i8Psi4s14N1 i8Psi4s14N2 i8Psi4s14N3 i8Psi4s14N4 i8Psi4s14dN0
    i8Psi4s14dN1 i8Psi4s14dN2 i8Psi4s14dN3 i8Psi4s14dN4 i8Psi4s14dW i8P4s14
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_0m0 hx, i13hw_m0m hx,
    i13hw_mm0 hx, i13hw_0m0m hx, i13hw_0mm0 hx, i13hw_m0m0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽15⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s15N0 (x : ℝ) : ℝ :=
    (-12) * hpl [negOne, negOne, negOne, zero] x +
    (-4) * hpl [negOne, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s15N0`. -/
noncomputable def i8Psi4s15dN0 (x : ℝ) : ℝ :=
    (-12) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s15N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s15N0 (i8Psi4s15dN0 x) x := by
  unfold i8Psi4s15N0 i8Psi4s15dN0
  exact (((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-12)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽15⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s15N1 (x : ℝ) : ℝ :=
    (-12) * hpl [negOne, negOne, zero] x +
    (-4) * hpl [negOne, zero, negOne] x +
    (-48) * hpl [negOne, negOne, negOne, zero] x +
    (-16) * hpl [negOne, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s15N1`. -/
noncomputable def i8Psi4s15dN1 (x : ℝ) : ℝ :=
    (-12) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-48) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-16) * (negOne.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s15N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s15N1 (i8Psi4s15dN1 x) x := by
  unfold i8Psi4s15N1 i8Psi4s15dN1
  exact (((((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-12)).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽15⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s15N2 (x : ℝ) : ℝ :=
    (19 / 2) * hpl [negOne] x +
    (-27) * hpl [negOne, zero] x +
    (18) * hpl [negOne, negOne, zero] x +
    (6) * hpl [negOne, zero, negOne] x +
    (-72) * hpl [negOne, negOne, negOne, zero] x +
    (-24) * hpl [negOne, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s15N2`. -/
noncomputable def i8Psi4s15dN2 (x : ℝ) : ℝ :=
    (19 / 2) * (negOne.kernel x * hpl [] x) +
    (-27) * (negOne.kernel x * hpl [zero] x) +
    (18) * (negOne.kernel x * hpl [negOne, zero] x) +
    (6) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-72) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-24) * (negOne.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s15N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s15N2 (i8Psi4s15dN2 x) x := by
  unfold i8Psi4s15N2 i8Psi4s15dN2
  exact (((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (19 / 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-27))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-72))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽15⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s15N3 (x : ℝ) : ℝ :=
    (-73 / 2) +
    (10) * hpl [negOne] x +
    (27) * hpl [zero] x +
    (-30) * hpl [negOne, zero] x +
    (-10) * hpl [zero, negOne] x +
    (36) * hpl [negOne, negOne, zero] x +
    (12) * hpl [negOne, zero, negOne] x +
    (-48) * hpl [negOne, negOne, negOne, zero] x +
    (-16) * hpl [negOne, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s15N3`. -/
noncomputable def i8Psi4s15dN3 (x : ℝ) : ℝ :=
    0 +
    (10) * (negOne.kernel x * hpl [] x) +
    (27) * (zero.kernel x * hpl [] x) +
    (-30) * (negOne.kernel x * hpl [zero] x) +
    (-10) * (zero.kernel x * hpl [negOne] x) +
    (36) * (negOne.kernel x * hpl [negOne, zero] x) +
    (12) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-48) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-16) * (negOne.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s15N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s15N3 (i8Psi4s15dN3 x) x := by
  unfold i8Psi4s15N3 i8Psi4s15dN3
  exact (((((((((hasDerivAt_const x (-73 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (27))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽15⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s15N4 (x : ℝ) : ℝ :=
    (-1) +
    (1 / 2) * hpl [negOne] x +
    (3 / 2) * hpl [zero] x +
    (-3) * hpl [negOne, zero] x +
    (-1) * hpl [zero, negOne] x +
    (6) * hpl [negOne, negOne, zero] x +
    (2) * hpl [negOne, zero, negOne] x +
    (-12) * hpl [negOne, negOne, negOne, zero] x +
    (-4) * hpl [negOne, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s15N4`. -/
noncomputable def i8Psi4s15dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (negOne.kernel x * hpl [] x) +
    (3 / 2) * (zero.kernel x * hpl [] x) +
    (-3) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (6) * (negOne.kernel x * hpl [negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-12) * (negOne.kernel x * hpl [negOne, negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s15N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s15N4 (i8Psi4s15dN4 x) x := by
  unfold i8Psi4s15N4 i8Psi4s15dN4
  exact (((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, negOne] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽15⁾` with constant coefficients. -/
noncomputable def i8Psi4s15W (x : ℝ) : ℝ :=
    (12) * hpl [zero, negOne, zero] x +
    (4) * hpl [zero, zero, negOne] x +
    (36) * hpl [zero, negOne, negOne, zero] x +
    (12) * hpl [zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s15W`. -/
noncomputable def i8Psi4s15dW (x : ℝ) : ℝ :=
    (12) * (zero.kernel x * hpl [negOne, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne] x) +
    (36) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (12) * (zero.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s15W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s15W (i8Psi4s15dW x) x := by
  unfold i8Psi4s15W i8Psi4s15dW
  exact (((((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (12)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (12)))

/-- The piece `Ψ₄⁽15⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s15 (x : ℝ) : ℝ :=
  (i8Psi4s15N0 x + x * i8Psi4s15N1 x + x ^ 2 * i8Psi4s15N2 x + x ^ 3 * i8Psi4s15N3 x +
    x ^ 4 * i8Psi4s15N4 x) / x ^ 2 + i8Psi4s15W x

/-- The derivative of `Ψ₄⁽15⁾`. -/
noncomputable def i8Psi4s15D (x : ℝ) : ℝ :=
  ((i8Psi4s15dN0 x + (i8Psi4s15N1 x + x * i8Psi4s15dN1 x) + (2 * x * i8Psi4s15N2 x +
    x ^ 2 * i8Psi4s15dN2 x) + (3 * x ^ 2 * i8Psi4s15N3 x + x ^ 3 * i8Psi4s15dN3 x) +
    (4 * x ^ 3 * i8Psi4s15N4 x + x ^ 4 * i8Psi4s15dN4 x)) * x ^ 2 - (i8Psi4s15N0 x +
    x * i8Psi4s15N1 x + x ^ 2 * i8Psi4s15N2 x + x ^ 3 * i8Psi4s15N3 x +
    x ^ 4 * i8Psi4s15N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s15dW x

theorem hasDerivAt_i8Psi4s15 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s15 (i8Psi4s15D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s15N0 hx).add (X.mul (hasDerivAt_i8Psi4s15N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s15N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s15N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s15N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s15W hx)
  unfold i8Psi4s15
  refine e.congr_deriv ?_
  unfold i8Psi4s15D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 15 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s15 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * (4 * hpl [negOne, negOne, zero] x)) * ((1 +
    x) / (1 - x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽15⁾)'(ξ) ξ' = p₄⁽15⁾`**, in terms of `ξ`. -/
theorem i8Psi4s15D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s15D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s15 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s15D i8Psi4s15N0 i8Psi4s15N1 i8Psi4s15N2 i8Psi4s15N3 i8Psi4s15N4 i8Psi4s15dN0
    i8Psi4s15dN1 i8Psi4s15dN2 i8Psi4s15dN3 i8Psi4s15dN4 i8Psi4s15dW i8P4s15
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_m0m hx, i13hw_mm0 hx,
    i8hw_mm0m hx, i13hw_mmm0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽16⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s16N0 (x : ℝ) : ℝ :=
    (-1 / 8) * hpl [negOne] x +
    (-1 / 4) * hpl [negOne, zero] x +
    (-1 / 4) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [negOne, zero, zero] x +
    (-1 / 2) * hpl [zero, negOne, zero] x +
    (-1 / 2) * hpl [zero, zero, negOne] x +
    (-1) * hpl [negOne, zero, zero, zero] x +
    (-1) * hpl [zero, negOne, zero, zero] x +
    (-1) * hpl [zero, zero, negOne, zero] x +
    (-1) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s16N0`. -/
noncomputable def i8Psi4s16dN0 (x : ℝ) : ℝ :=
    (-1 / 8) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s16N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s16N0 (i8Psi4s16dN0 x) x := by
  unfold i8Psi4s16N0 i8Psi4s16dN0
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 8)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽16⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s16N1 (x : ℝ) : ℝ :=
    (-15 / 8) +
    (-4) * hpl [negOne] x +
    (-7 / 4) * hpl [zero] x +
    (-4) * hpl [negOne, zero] x +
    (-4) * hpl [zero, negOne] x +
    (-3 / 2) * hpl [zero, zero] x +
    (-4) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, negOne] x +
    (-1) * hpl [zero, zero, zero] x +
    (-4) * hpl [negOne, zero, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, zero] x +
    (-4) * hpl [zero, zero, negOne, zero] x +
    (-4) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s16N1`. -/
noncomputable def i8Psi4s16dN1 (x : ℝ) : ℝ :=
    0 +
    (-4) * (negOne.kernel x * hpl [] x) +
    (-7 / 4) * (zero.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [negOne] x) +
    (-3 / 2) * (zero.kernel x * hpl [zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [zero, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s16N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s16N1 (i8Psi4s16dN1 x) x := by
  unfold i8Psi4s16N1 i8Psi4s16dN1
  exact ((((((((((((((hasDerivAt_const x (-15 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-7 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽16⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s16N2 (x : ℝ) : ℝ :=
    (31 / 8) * hpl [zero] x +
    (-15 / 2) * hpl [negOne, zero] x +
    (15 / 4) * hpl [zero, zero] x +
    (7 / 2) * hpl [zero, zero, zero] x +
    (-6) * hpl [negOne, zero, zero, zero] x

/-- The derivative of `i8Psi4s16N2`. -/
noncomputable def i8Psi4s16dN2 (x : ℝ) : ℝ :=
    (31 / 8) * (zero.kernel x * hpl [] x) +
    (-15 / 2) * (negOne.kernel x * hpl [zero] x) +
    (15 / 4) * (zero.kernel x * hpl [zero] x) +
    (7 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (-6) * (negOne.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s16N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s16N2 (i8Psi4s16dN2 x) x := by
  unfold i8Psi4s16N2 i8Psi4s16dN2
  exact ((((((hasDerivAt_hpl_cons zero [] hx).const_mul (31 / 8)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-15 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (15 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-6)))

/-- The part of `ξ² Ψ₄⁽16⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s16N3 (x : ℝ) : ℝ :=
    (-113 / 8) +
    (4) * hpl [negOne] x +
    (41 / 4) * hpl [zero] x +
    (-4) * hpl [negOne, zero] x +
    (-4) * hpl [zero, negOne] x +
    (-13 / 2) * hpl [zero, zero] x +
    (4) * hpl [negOne, zero, zero] x +
    (4) * hpl [zero, negOne, zero] x +
    (4) * hpl [zero, zero, negOne] x +
    (3) * hpl [zero, zero, zero] x +
    (-4) * hpl [negOne, zero, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, zero] x +
    (-4) * hpl [zero, zero, negOne, zero] x +
    (-4) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s16N3`. -/
noncomputable def i8Psi4s16dN3 (x : ℝ) : ℝ :=
    0 +
    (4) * (negOne.kernel x * hpl [] x) +
    (41 / 4) * (zero.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [negOne] x) +
    (-13 / 2) * (zero.kernel x * hpl [zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne] x) +
    (3) * (zero.kernel x * hpl [zero, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s16N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s16N3 (i8Psi4s16dN3 x) x := by
  unfold i8Psi4s16N3 i8Psi4s16dN3
  exact ((((((((((((((hasDerivAt_const x (-113 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (41 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-13 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽16⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s16N4 (x : ℝ) : ℝ :=
    (-1 / 4) +
    (1 / 8) * hpl [negOne] x +
    (3 / 8) * hpl [zero] x +
    (-1 / 4) * hpl [negOne, zero] x +
    (-1 / 4) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [zero, zero] x +
    (1 / 2) * hpl [negOne, zero, zero] x +
    (1 / 2) * hpl [zero, negOne, zero] x +
    (1 / 2) * hpl [zero, zero, negOne] x +
    (1 / 2) * hpl [zero, zero, zero] x +
    (-1) * hpl [negOne, zero, zero, zero] x +
    (-1) * hpl [zero, negOne, zero, zero] x +
    (-1) * hpl [zero, zero, negOne, zero] x +
    (-1) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s16N4`. -/
noncomputable def i8Psi4s16dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 8) * (negOne.kernel x * hpl [] x) +
    (3 / 8) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s16N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s16N4 (i8Psi4s16dN4 x) x := by
  unfold i8Psi4s16N4 i8Psi4s16dN4
  exact ((((((((((((((hasDerivAt_const x (-1 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-1)))

/-- The part of `Ψ₄⁽16⁾` with constant coefficients. -/
noncomputable def i8Psi4s16W (x : ℝ) : ℝ :=
    (3) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s16W`. -/
noncomputable def i8Psi4s16dW (x : ℝ) : ℝ :=
    (3) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s16W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s16W (i8Psi4s16dW x) x := by
  unfold i8Psi4s16W i8Psi4s16dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (3))

/-- The piece `Ψ₄⁽16⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s16 (x : ℝ) : ℝ :=
  (i8Psi4s16N0 x + x * i8Psi4s16N1 x + x ^ 2 * i8Psi4s16N2 x + x ^ 3 * i8Psi4s16N3 x +
    x ^ 4 * i8Psi4s16N4 x) / x ^ 2 + i8Psi4s16W x

/-- The derivative of `Ψ₄⁽16⁾`. -/
noncomputable def i8Psi4s16D (x : ℝ) : ℝ :=
  ((i8Psi4s16dN0 x + (i8Psi4s16N1 x + x * i8Psi4s16dN1 x) + (2 * x * i8Psi4s16N2 x +
    x ^ 2 * i8Psi4s16dN2 x) + (3 * x ^ 2 * i8Psi4s16N3 x + x ^ 3 * i8Psi4s16dN3 x) +
    (4 * x ^ 3 * i8Psi4s16N4 x + x ^ 4 * i8Psi4s16dN4 x)) * x ^ 2 - (i8Psi4s16N0 x +
    x * i8Psi4s16N1 x + x ^ 2 * i8Psi4s16N2 x + x ^ 3 * i8Psi4s16N3 x +
    x ^ 4 * i8Psi4s16N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s16dW x

theorem hasDerivAt_i8Psi4s16 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s16 (i8Psi4s16D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s16N0 hx).add (X.mul (hasDerivAt_i8Psi4s16N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s16N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s16N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s16N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s16W hx)
  unfold i8Psi4s16
  refine e.congr_deriv ?_
  unfold i8Psi4s16D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 16 of `p₄` in `ξ`: from `t B3 A1 (-λ)^0/0!`, the term with `log^0 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s16 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * ((1 + x) / (1 - x) * (1 * hpl [zero, zero, zero] x)) * ((1 + x) / (1 -
    x) * (-hpl [negOne] x))

/-- **`(Ψ₄⁽16⁾)'(ξ) ξ' = p₄⁽16⁾`**, in terms of `ξ`. -/
theorem i8Psi4s16D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s16D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s16 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s16D i8Psi4s16N0 i8Psi4s16N1 i8Psi4s16N2 i8Psi4s16N3 i8Psi4s16N4 i8Psi4s16dN0
    i8Psi4s16dN1 i8Psi4s16dN2 i8Psi4s16dN3 i8Psi4s16dN4 i8Psi4s16dW i8P4s16
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx, i13hw_000,
    i13hw_0m0 hx, i13hw_m00 hx, i13hw_00m0 hx, i13hw_0m00 hx, i13hw_m000 hx]
  field_simp
  ring

end QED.ThreeLoopD
