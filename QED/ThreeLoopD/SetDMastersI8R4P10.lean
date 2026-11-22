/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P9

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 56 to 61

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s56`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s56D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s56`, `QED.ThreeLoopD.i8Psi4s56D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽56⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s56N0 (x : ℝ) : ℝ :=
    (1 / 2) * hpl [negOne, zero, negOne] x +
    (1) * hpl [negOne, zero, negOne, zero] x +
    (2) * hpl [negOne, zero, zero, negOne] x +
    (1) * hpl [zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s56N0`. -/
noncomputable def i8Psi4s56dN0 (x : ℝ) : ℝ :=
    (1 / 2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (1) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (2) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s56N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s56N0 (i8Psi4s56dN0 x) x := by
  unfold i8Psi4s56N0 i8Psi4s56dN0
  exact (((((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽56⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s56N1 (x : ℝ) : ℝ :=
    (5 / 2) * hpl [negOne] x +
    (1) * hpl [negOne, zero] x +
    (5 / 2) * hpl [zero, negOne] x +
    (1) * hpl [zero, negOne, zero] x +
    (2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s56N1`. -/
noncomputable def i8Psi4s56dN1 (x : ℝ) : ℝ :=
    (5 / 2) * (negOne.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (5 / 2) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s56N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s56N1 (i8Psi4s56dN1 x) x := by
  unfold i8Psi4s56N1 i8Psi4s56dN1
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (5 / 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽56⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s56N2 (x : ℝ) : ℝ :=
    (-3 / 8) * hpl [negOne] x +
    (-5 / 2) * hpl [zero] x +
    (9 / 4) * hpl [negOne, zero] x +
    (-1) * hpl [negOne, zero, negOne] x +
    (1 / 2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s56N2`. -/
noncomputable def i8Psi4s56dN2 (x : ℝ) : ℝ :=
    (-3 / 8) * (negOne.kernel x * hpl [] x) +
    (-5 / 2) * (zero.kernel x * hpl [] x) +
    (9 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s56N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s56N2 (i8Psi4s56dN2 x) x := by
  unfold i8Psi4s56N2 i8Psi4s56dN2
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (9 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽56⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s56N3 (x : ℝ) : ℝ :=
    (33 / 8) +
    (-5 / 2) * hpl [negOne] x +
    (-5 / 4) * hpl [zero] x +
    (1) * hpl [negOne, zero] x +
    (5 / 2) * hpl [zero, negOne] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s56N3`. -/
noncomputable def i8Psi4s56dN3 (x : ℝ) : ℝ :=
    0 +
    (-5 / 2) * (negOne.kernel x * hpl [] x) +
    (-5 / 4) * (zero.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (5 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s56N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s56N3 (i8Psi4s56dN3 x) x := by
  unfold i8Psi4s56N3 i8Psi4s56dN3
  exact (((((((hasDerivAt_const x (33 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-5 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽56⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s56N4 (x : ℝ) : ℝ :=
    (-1 / 4) +
    (3 / 8) * hpl [negOne] x +
    (1 / 8) * hpl [zero] x +
    (-1 / 4) * hpl [negOne, zero] x +
    (-3 / 4) * hpl [zero, negOne] x +
    (1 / 2) * hpl [negOne, zero, negOne] x +
    (1 / 2) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, negOne] x +
    (-1) * hpl [negOne, zero, negOne, zero] x +
    (-2) * hpl [negOne, zero, zero, negOne] x +
    (-1) * hpl [zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s56N4`. -/
noncomputable def i8Psi4s56dN4 (x : ℝ) : ℝ :=
    0 +
    (3 / 8) * (negOne.kernel x * hpl [] x) +
    (1 / 8) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-3 / 4) * (zero.kernel x * hpl [negOne] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s56N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s56N4 (i8Psi4s56dN4 x) x := by
  unfold i8Psi4s56N4 i8Psi4s56dN4
  exact (((((((((((hasDerivAt_const x (-1 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-1)))

/-- The part of `Ψ₄⁽56⁾` with constant coefficients. -/
noncomputable def i8Psi4s56W (x : ℝ) : ℝ :=
    (-1) * hpl [zero, zero] x +
    (1) * hpl [zero, zero, negOne, zero] x +
    (2) * hpl [zero, zero, zero, negOne] x +
    (4) * hpl [zero, negOne, zero, negOne, zero] x +
    (8) * hpl [zero, negOne, zero, zero, negOne] x +
    (4) * hpl [zero, zero, negOne, zero, negOne] x

/-- The derivative of `i8Psi4s56W`. -/
noncomputable def i8Psi4s56dW (x : ℝ) : ℝ :=
    (-1) * (zero.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, zero, negOne] x)

theorem hasDerivAt_i8Psi4s56W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s56W (i8Psi4s56dW x) x := by
  unfold i8Psi4s56W i8Psi4s56dW
  exact (((((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, negOne] hx).const_mul (4)))

/-- The piece `Ψ₄⁽56⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s56 (x : ℝ) : ℝ :=
  (i8Psi4s56N0 x + x * i8Psi4s56N1 x + x ^ 2 * i8Psi4s56N2 x + x ^ 3 * i8Psi4s56N3 x +
    x ^ 4 * i8Psi4s56N4 x) / x ^ 2 + i8Psi4s56W x

/-- The derivative of `Ψ₄⁽56⁾`. -/
noncomputable def i8Psi4s56D (x : ℝ) : ℝ :=
  ((i8Psi4s56dN0 x + (i8Psi4s56N1 x + x * i8Psi4s56dN1 x) + (2 * x * i8Psi4s56N2 x +
    x ^ 2 * i8Psi4s56dN2 x) + (3 * x ^ 2 * i8Psi4s56N3 x + x ^ 3 * i8Psi4s56dN3 x) +
    (4 * x ^ 3 * i8Psi4s56N4 x + x ^ 4 * i8Psi4s56dN4 x)) * x ^ 2 - (i8Psi4s56N0 x +
    x * i8Psi4s56N1 x + x ^ 2 * i8Psi4s56N2 x + x ^ 3 * i8Psi4s56N3 x +
    x ^ 4 * i8Psi4s56N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s56dW x

theorem hasDerivAt_i8Psi4s56 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s56 (i8Psi4s56D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s56N0 hx).add (X.mul (hasDerivAt_i8Psi4s56N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s56N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s56N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s56N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s56W hx)
  unfold i8Psi4s56
  refine e.congr_deriv ?_
  unfold i8Psi4s56D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 56 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s56 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 - x) * (2 * hpl [negOne, zero, negOne] x))

/-- **`(Ψ₄⁽56⁾)'(ξ) ξ' = p₄⁽56⁾`**, in terms of `ξ`. -/
theorem i8Psi4s56D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s56D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s56 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s56D i8Psi4s56N0 i8Psi4s56N1 i8Psi4s56N2 i8Psi4s56N3 i8Psi4s56N4 i8Psi4s56dN0
    i8Psi4s56dN1 i8Psi4s56dN2 i8Psi4s56dN3 i8Psi4s56dN4 i8Psi4s56dW i8P4s56
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_0m0 hx, i13hw_m0m hx,
    i13hw_0m0m hx, i13hw_m00m hx, i13hw_m0m0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽57⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s57N0 (x : ℝ) : ℝ :=
    (1 / 2) * hpl [negOne, negOne] x +
    (1 / 2) * hpl [negOne, negOne, zero] x +
    (1 / 2) * hpl [negOne, zero, negOne] x +
    (1) * hpl [zero, negOne, negOne] x +
    (1) * hpl [zero, negOne, negOne, zero] x +
    (1) * hpl [zero, negOne, zero, negOne] x +
    (2) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s57N0`. -/
noncomputable def i8Psi4s57dN0 (x : ℝ) : ℝ :=
    (1 / 2) * (negOne.kernel x * hpl [negOne] x) +
    (1 / 2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (2) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s57N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s57N0 (i8Psi4s57dN0 x) x := by
  unfold i8Psi4s57N0 i8Psi4s57dN0
  exact ((((((((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽57⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s57N1 (x : ℝ) : ℝ :=
    (1) * hpl [negOne] x +
    (1 / 2) * hpl [negOne, zero] x +
    (1 / 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s57N1`. -/
noncomputable def i8Psi4s57dN1 (x : ℝ) : ℝ :=
    (1) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s57N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s57N1 (i8Psi4s57dN1 x) x := by
  unfold i8Psi4s57N1 i8Psi4s57dN1
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽57⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s57N2 (x : ℝ) : ℝ :=
    (-3 / 8) * hpl [negOne] x +
    (-1) * hpl [zero] x +
    (5 / 4) * hpl [negOne, zero] x +
    (1 / 2) * hpl [zero, negOne] x +
    (-1) * hpl [negOne, negOne, zero] x +
    (-1) * hpl [negOne, zero, negOne] x

/-- The derivative of `i8Psi4s57N2`. -/
noncomputable def i8Psi4s57dN2 (x : ℝ) : ℝ :=
    (-3 / 8) * (negOne.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [] x) +
    (5 / 4) * (negOne.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s57N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s57N2 (i8Psi4s57dN2 x) x := by
  unfold i8Psi4s57N2 i8Psi4s57dN2
  exact (((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (5 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽57⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s57N3 (x : ℝ) : ℝ :=
    (17 / 8) +
    (-1) * hpl [negOne] x +
    (-3 / 4) * hpl [zero] x +
    (1 / 2) * hpl [negOne, zero] x +
    (1 / 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s57N3`. -/
noncomputable def i8Psi4s57dN3 (x : ℝ) : ℝ :=
    0 +
    (-1) * (negOne.kernel x * hpl [] x) +
    (-3 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s57N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s57N3 (i8Psi4s57dN3 x) x := by
  unfold i8Psi4s57N3 i8Psi4s57dN3
  exact (((((hasDerivAt_const x (17 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽57⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s57N4 (x : ℝ) : ℝ :=
    (-1 / 4) +
    (3 / 8) * hpl [negOne] x +
    (1 / 8) * hpl [zero] x +
    (-1 / 2) * hpl [negOne, negOne] x +
    (-1 / 4) * hpl [negOne, zero] x +
    (-1 / 4) * hpl [zero, negOne] x +
    (1 / 2) * hpl [negOne, negOne, zero] x +
    (1 / 2) * hpl [negOne, zero, negOne] x +
    (1) * hpl [zero, negOne, negOne] x +
    (-1) * hpl [zero, negOne, negOne, zero] x +
    (-1) * hpl [zero, negOne, zero, negOne] x +
    (-2) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s57N4`. -/
noncomputable def i8Psi4s57dN4 (x : ℝ) : ℝ :=
    0 +
    (3 / 8) * (negOne.kernel x * hpl [] x) +
    (1 / 8) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [negOne] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (1 / 2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s57N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s57N4 (i8Psi4s57dN4 x) x := by
  unfold i8Psi4s57N4 i8Psi4s57dN4
  exact ((((((((((((hasDerivAt_const x (-1 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽57⁾` with constant coefficients. -/
noncomputable def i8Psi4s57W (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [zero, zero] x +
    (1 / 2) * hpl [zero, negOne, zero] x +
    (1 / 2) * hpl [zero, zero, negOne] x +
    (4) * hpl [zero, zero, negOne, negOne, zero] x +
    (4) * hpl [zero, zero, negOne, zero, negOne] x +
    (8) * hpl [zero, zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s57W`. -/
noncomputable def i8Psi4s57dW (x : ℝ) : ℝ :=
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, zero, negOne] x) +
    (8) * (zero.kernel x * hpl [zero, zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s57W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s57W (i8Psi4s57dW x) x := by
  unfold i8Psi4s57W i8Psi4s57dW
  exact (((((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, negOne] hx).const_mul (8)))

/-- The piece `Ψ₄⁽57⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s57 (x : ℝ) : ℝ :=
  (i8Psi4s57N0 x + x * i8Psi4s57N1 x + x ^ 2 * i8Psi4s57N2 x + x ^ 3 * i8Psi4s57N3 x +
    x ^ 4 * i8Psi4s57N4 x) / x ^ 2 + i8Psi4s57W x

/-- The derivative of `Ψ₄⁽57⁾`. -/
noncomputable def i8Psi4s57D (x : ℝ) : ℝ :=
  ((i8Psi4s57dN0 x + (i8Psi4s57N1 x + x * i8Psi4s57dN1 x) + (2 * x * i8Psi4s57N2 x +
    x ^ 2 * i8Psi4s57dN2 x) + (3 * x ^ 2 * i8Psi4s57N3 x + x ^ 3 * i8Psi4s57dN3 x) +
    (4 * x ^ 3 * i8Psi4s57N4 x + x ^ 4 * i8Psi4s57dN4 x)) * x ^ 2 - (i8Psi4s57N0 x +
    x * i8Psi4s57N1 x + x ^ 2 * i8Psi4s57N2 x + x ^ 3 * i8Psi4s57N3 x +
    x ^ 4 * i8Psi4s57N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s57dW x

theorem hasDerivAt_i8Psi4s57 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s57 (i8Psi4s57D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s57N0 hx).add (X.mul (hasDerivAt_i8Psi4s57N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s57N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s57N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s57N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s57W hx)
  unfold i8Psi4s57
  refine e.congr_deriv ?_
  unfold i8Psi4s57D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 57 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s57 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 - x) * (2 * hpl [zero, negOne, negOne] x))

/-- **`(Ψ₄⁽57⁾)'(ξ) ξ' = p₄⁽57⁾`**, in terms of `ξ`. -/
theorem i8Psi4s57D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s57D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s57 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s57D i8Psi4s57N0 i8Psi4s57N1 i8Psi4s57N2 i8Psi4s57N3 i8Psi4s57N4 i8Psi4s57dN0
    i8Psi4s57dN1 i8Psi4s57dN2 i8Psi4s57dN3 i8Psi4s57dN4 i8Psi4s57dW i8P4s57
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_mm hx, i13hw_m0m hx,
    i13hw_mm0 hx, i13hw_0m0m hx, i13hw_0mm0 hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽58⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s58N0 (x : ℝ) : ℝ :=
    (-3 / 16) * hpl [negOne] x +
    (-1 / 8) * hpl [negOne, zero] x +
    (-3 / 8) * hpl [zero, negOne] x +
    (-1 / 4) * hpl [zero, negOne, zero] x +
    (-3 / 4) * hpl [zero, zero, negOne] x +
    (-1 / 2) * hpl [zero, zero, negOne, zero] x +
    (-3 / 2) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s58N0`. -/
noncomputable def i8Psi4s58dN0 (x : ℝ) : ℝ :=
    (-3 / 16) * (negOne.kernel x * hpl [] x) +
    (-1 / 8) * (negOne.kernel x * hpl [zero] x) +
    (-3 / 8) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-3 / 4) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3 / 2) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s58N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s58N0 (i8Psi4s58dN0 x) x := by
  unfold i8Psi4s58N0 i8Psi4s58dN0
  exact ((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 16)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3 / 8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3 / 2)))

/-- The part of `ξ² Ψ₄⁽58⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s58N1 (x : ℝ) : ℝ :=
    (-5 / 16) +
    (-1 / 8) * hpl [zero] x

/-- The derivative of `i8Psi4s58N1`. -/
noncomputable def i8Psi4s58dN1 (x : ℝ) : ℝ :=
    0 +
    (-1 / 8) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s58N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s58N1 (i8Psi4s58dN1 x) x := by
  unfold i8Psi4s58N1 i8Psi4s58dN1
  exact ((hasDerivAt_const x (-5 / 16)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 8)))

/-- The part of `ξ² Ψ₄⁽58⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s58N2 (x : ℝ) : ℝ :=
    (3 / 8) * hpl [negOne] x +
    (-3 / 16) * hpl [zero] x

/-- The derivative of `i8Psi4s58N2`. -/
noncomputable def i8Psi4s58dN2 (x : ℝ) : ℝ :=
    (3 / 8) * (negOne.kernel x * hpl [] x) +
    (-3 / 16) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s58N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s58N2 (i8Psi4s58dN2 x) x := by
  unfold i8Psi4s58N2 i8Psi4s58dN2
  exact (((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 16)))

/-- The part of `ξ² Ψ₄⁽58⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s58N3 (x : ℝ) : ℝ :=
    (-5 / 16) +
    (1 / 8) * hpl [zero] x

/-- The derivative of `i8Psi4s58N3`. -/
noncomputable def i8Psi4s58dN3 (x : ℝ) : ℝ :=
    0 +
    (1 / 8) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s58N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s58N3 (i8Psi4s58dN3 x) x := by
  unfold i8Psi4s58N3 i8Psi4s58dN3
  exact ((hasDerivAt_const x (-5 / 16)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 8)))

/-- The part of `ξ² Ψ₄⁽58⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s58N4 (x : ℝ) : ℝ :=
    (1 / 8) +
    (-3 / 16) * hpl [negOne] x +
    (-1 / 16) * hpl [zero] x +
    (1 / 8) * hpl [negOne, zero] x +
    (3 / 8) * hpl [zero, negOne] x +
    (-1 / 4) * hpl [zero, negOne, zero] x +
    (-3 / 4) * hpl [zero, zero, negOne] x +
    (1 / 2) * hpl [zero, zero, negOne, zero] x +
    (3 / 2) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s58N4`. -/
noncomputable def i8Psi4s58dN4 (x : ℝ) : ℝ :=
    0 +
    (-3 / 16) * (negOne.kernel x * hpl [] x) +
    (-1 / 16) * (zero.kernel x * hpl [] x) +
    (1 / 8) * (negOne.kernel x * hpl [zero] x) +
    (3 / 8) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-3 / 4) * (zero.kernel x * hpl [zero, negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (3 / 2) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s58N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s58N4 (i8Psi4s58dN4 x) x := by
  unfold i8Psi4s58N4 i8Psi4s58dN4
  exact (((((((((hasDerivAt_const x (1 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 16))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 16))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (3 / 8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (3 / 2)))

/-- The part of `Ψ₄⁽58⁾` with constant coefficients. -/
noncomputable def i8Psi4s58W (x : ℝ) : ℝ :=
    (-1 / 8) * hpl [zero, zero] x +
    (-2) * hpl [zero, zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s58W`. -/
noncomputable def i8Psi4s58dW (x : ℝ) : ℝ :=
    (-1 / 8) * (zero.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [zero, zero, negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s58W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s58W (i8Psi4s58dW x) x := by
  unfold i8Psi4s58W i8Psi4s58dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 8)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, negOne] hx).const_mul (-6)))

/-- The piece `Ψ₄⁽58⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s58 (x : ℝ) : ℝ :=
  (i8Psi4s58N0 x + x * i8Psi4s58N1 x + x ^ 2 * i8Psi4s58N2 x + x ^ 3 * i8Psi4s58N3 x +
    x ^ 4 * i8Psi4s58N4 x) / x ^ 2 + i8Psi4s58W x

/-- The derivative of `Ψ₄⁽58⁾`. -/
noncomputable def i8Psi4s58D (x : ℝ) : ℝ :=
  ((i8Psi4s58dN0 x + (i8Psi4s58N1 x + x * i8Psi4s58dN1 x) + (2 * x * i8Psi4s58N2 x +
    x ^ 2 * i8Psi4s58dN2 x) + (3 * x ^ 2 * i8Psi4s58N3 x + x ^ 3 * i8Psi4s58dN3 x) +
    (4 * x ^ 3 * i8Psi4s58N4 x + x ^ 4 * i8Psi4s58dN4 x)) * x ^ 2 - (i8Psi4s58N0 x +
    x * i8Psi4s58N1 x + x ^ 2 * i8Psi4s58N2 x + x ^ 3 * i8Psi4s58N3 x +
    x ^ 4 * i8Psi4s58N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s58dW x

theorem hasDerivAt_i8Psi4s58 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s58 (i8Psi4s58D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s58N0 hx).add (X.mul (hasDerivAt_i8Psi4s58N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s58N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s58N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s58N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s58W hx)
  unfold i8Psi4s58
  refine e.congr_deriv ?_
  unfold i8Psi4s58D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 58 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s58 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 - x) * (-hpl [zero, zero, negOne] x))

/-- **`(Ψ₄⁽58⁾)'(ξ) ξ' = p₄⁽58⁾`**, in terms of `ξ`. -/
theorem i8Psi4s58D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s58D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s58 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s58D i8Psi4s58N0 i8Psi4s58N1 i8Psi4s58N2 i8Psi4s58N3 i8Psi4s58N4 i8Psi4s58dN0
    i8Psi4s58dN1 i8Psi4s58dN2 i8Psi4s58dN3 i8Psi4s58dN4 i8Psi4s58dW i8P4s58
  simp only [kernel_zero, kernel_negOne, hpl_nil, hpl_zero, i13hw_m0 hx, i13hw_0m0 hx, i13hw_00m0
    hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽59⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s59N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s59N0`. -/
noncomputable def i8Psi4s59dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s59N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s59N0 (i8Psi4s59dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽59⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s59N1 (x : ℝ) : ℝ :=
    (8) * hpl [one] x

/-- The derivative of `i8Psi4s59N1`. -/
noncomputable def i8Psi4s59dN1 (x : ℝ) : ℝ :=
    (8) * (one.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s59N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s59N1 (i8Psi4s59dN1 x) x := by
  unfold i8Psi4s59N1 i8Psi4s59dN1
  exact ((hasDerivAt_hpl_cons one [] hx).const_mul (8))

/-- The part of `ξ² Ψ₄⁽59⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s59N2 (x : ℝ) : ℝ :=
    (-12) * hpl [one] x

/-- The derivative of `i8Psi4s59N2`. -/
noncomputable def i8Psi4s59dN2 (x : ℝ) : ℝ :=
    (-12) * (one.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s59N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s59N2 (i8Psi4s59dN2 x) x := by
  unfold i8Psi4s59N2 i8Psi4s59dN2
  exact ((hasDerivAt_hpl_cons one [] hx).const_mul (-12))

/-- The part of `ξ² Ψ₄⁽59⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s59N3 (x : ℝ) : ℝ :=
    (4) +
    (8) * hpl [one] x

/-- The derivative of `i8Psi4s59N3`. -/
noncomputable def i8Psi4s59dN3 (x : ℝ) : ℝ :=
    0 +
    (8) * (one.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s59N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s59N3 (i8Psi4s59dN3 x) x := by
  unfold i8Psi4s59N3 i8Psi4s59dN3
  exact ((hasDerivAt_const x (4)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽59⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s59N4 (x : ℝ) : ℝ :=
    (-2) +
    (-4) * hpl [one] x

/-- The derivative of `i8Psi4s59N4`. -/
noncomputable def i8Psi4s59dN4 (x : ℝ) : ℝ :=
    0 +
    (-4) * (one.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s59N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s59N4 (i8Psi4s59dN4 x) x := by
  unfold i8Psi4s59N4 i8Psi4s59dN4
  exact ((hasDerivAt_const x (-2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽59⁾` with constant coefficients. -/
noncomputable def i8Psi4s59W (x : ℝ) : ℝ :=
    (-8) * hpl [zero] x +
    (8) * hpl [zero, one] x

/-- The derivative of `i8Psi4s59W`. -/
noncomputable def i8Psi4s59dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [] x) +
    (8) * (zero.kernel x * hpl [one] x)

theorem hasDerivAt_i8Psi4s59W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s59W (i8Psi4s59dW x) x := by
  unfold i8Psi4s59W i8Psi4s59dW
  exact (((hasDerivAt_hpl_cons zero [] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (8)))

/-- The piece `Ψ₄⁽59⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s59 (x : ℝ) : ℝ :=
  (i8Psi4s59N0 x + x * i8Psi4s59N1 x + x ^ 2 * i8Psi4s59N2 x + x ^ 3 * i8Psi4s59N3 x +
    x ^ 4 * i8Psi4s59N4 x) / x ^ 2 + i8Psi4s59W x

/-- The derivative of `Ψ₄⁽59⁾`. -/
noncomputable def i8Psi4s59D (x : ℝ) : ℝ :=
  ((i8Psi4s59dN0 x + (i8Psi4s59N1 x + x * i8Psi4s59dN1 x) + (2 * x * i8Psi4s59N2 x +
    x ^ 2 * i8Psi4s59dN2 x) + (3 * x ^ 2 * i8Psi4s59N3 x + x ^ 3 * i8Psi4s59dN3 x) +
    (4 * x ^ 3 * i8Psi4s59N4 x + x ^ 4 * i8Psi4s59dN4 x)) * x ^ 2 - (i8Psi4s59N0 x +
    x * i8Psi4s59N1 x + x ^ 2 * i8Psi4s59N2 x + x ^ 3 * i8Psi4s59N3 x +
    x ^ 4 * i8Psi4s59N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s59dW x

theorem hasDerivAt_i8Psi4s59 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s59 (i8Psi4s59D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s59N0 hx).add (X.mul (hasDerivAt_i8Psi4s59N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s59N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s59N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s59N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s59W hx)
  unfold i8Psi4s59
  refine e.congr_deriv ?_
  unfold i8Psi4s59D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 59 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s59 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 - x) * (4 * x / (1 + x))))

/-- **`(Ψ₄⁽59⁾)'(ξ) ξ' = p₄⁽59⁾`**, in terms of `ξ`. -/
theorem i8Psi4s59D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s59D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s59 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s59D i8Psi4s59N0 i8Psi4s59N1 i8Psi4s59N2 i8Psi4s59N3 i8Psi4s59N4 i8Psi4s59dN0
    i8Psi4s59dN1 i8Psi4s59dN2 i8Psi4s59dN3 i8Psi4s59dN4 i8Psi4s59dW i8P4s59
  simp only [kernel_zero, kernel_one, hpl_nil, i13_log_one_sub_eq hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽60⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s60N0 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne, one] x +
    (-2) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s60N0`. -/
noncomputable def i8Psi4s60dN0 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s60N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s60N0 (i8Psi4s60dN0 x) x := by
  unfold i8Psi4s60N0 i8Psi4s60dN0
  exact (((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽60⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s60N1 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne] x +
    (-2) * hpl [one] x

/-- The derivative of `i8Psi4s60N1`. -/
noncomputable def i8Psi4s60dN1 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s60N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s60N1 (i8Psi4s60dN1 x) x := by
  unfold i8Psi4s60N1 i8Psi4s60dN1
  exact (((hasDerivAt_hpl_cons negOne [] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽60⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s60N2 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne] x +
    (1) * hpl [one] x

/-- The derivative of `i8Psi4s60N2`. -/
noncomputable def i8Psi4s60dN2 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [] x) +
    (1) * (one.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s60N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s60N2 (i8Psi4s60dN2 x) x := by
  unfold i8Psi4s60N2 i8Psi4s60dN2
  exact (((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽60⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s60N3 (x : ℝ) : ℝ :=
    (2) * hpl [negOne] x +
    (2) * hpl [one] x

/-- The derivative of `i8Psi4s60N3`. -/
noncomputable def i8Psi4s60dN3 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [] x) +
    (2) * (one.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s60N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s60N3 (i8Psi4s60dN3 x) x := by
  unfold i8Psi4s60N3 i8Psi4s60dN3
  exact (((hasDerivAt_hpl_cons negOne [] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽60⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s60N4 (x : ℝ) : ℝ :=
    (-1) +
    (1) * hpl [negOne] x +
    (-1) * hpl [one] x +
    (2) * hpl [negOne, one] x +
    (2) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s60N4`. -/
noncomputable def i8Psi4s60dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (negOne.kernel x * hpl [] x) +
    (-1) * (one.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s60N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s60N4 (i8Psi4s60dN4 x) x := by
  unfold i8Psi4s60N4 i8Psi4s60dN4
  exact (((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2)))

/-- The part of `Ψ₄⁽60⁾` with constant coefficients. -/
noncomputable def i8Psi4s60W (x : ℝ) : ℝ :=
    (4) * hpl [zero] x +
    (2) * hpl [zero, negOne] x +
    (-2) * hpl [zero, one] x +
    (-8) * hpl [zero, negOne, one] x +
    (-8) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi4s60W`. -/
noncomputable def i8Psi4s60dW (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [one] x) +
    (-8) * (zero.kernel x * hpl [negOne, one] x) +
    (-8) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s60W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s60W (i8Psi4s60dW x) x := by
  unfold i8Psi4s60W i8Psi4s60dW
  exact ((((((hasDerivAt_hpl_cons zero [] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-8)))

/-- The piece `Ψ₄⁽60⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s60 (x : ℝ) : ℝ :=
  (i8Psi4s60N0 x + x * i8Psi4s60N1 x + x ^ 2 * i8Psi4s60N2 x + x ^ 3 * i8Psi4s60N3 x +
    x ^ 4 * i8Psi4s60N4 x) / x ^ 2 + i8Psi4s60W x

/-- The derivative of `Ψ₄⁽60⁾`. -/
noncomputable def i8Psi4s60D (x : ℝ) : ℝ :=
  ((i8Psi4s60dN0 x + (i8Psi4s60N1 x + x * i8Psi4s60dN1 x) + (2 * x * i8Psi4s60N2 x +
    x ^ 2 * i8Psi4s60dN2 x) + (3 * x ^ 2 * i8Psi4s60N3 x + x ^ 3 * i8Psi4s60dN3 x) +
    (4 * x ^ 3 * i8Psi4s60N4 x + x ^ 4 * i8Psi4s60dN4 x)) * x ^ 2 - (i8Psi4s60N0 x +
    x * i8Psi4s60N1 x + x ^ 2 * i8Psi4s60N2 x + x ^ 3 * i8Psi4s60N3 x +
    x ^ 4 * i8Psi4s60N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s60dW x

theorem hasDerivAt_i8Psi4s60 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s60 (i8Psi4s60D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s60N0 hx).add (X.mul (hasDerivAt_i8Psi4s60N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s60N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s60N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s60N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s60W hx)
  unfold i8Psi4s60
  refine e.congr_deriv ?_
  unfold i8Psi4s60D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 60 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s60 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 - x) * (-2 * hpl [negOne] x)))

/-- **`(Ψ₄⁽60⁾)'(ξ) ξ' = p₄⁽60⁾`**, in terms of `ξ`. -/
theorem i8Psi4s60D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s60D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s60 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s60D i8Psi4s60N0 i8Psi4s60N1 i8Psi4s60N2 i8Psi4s60N3 i8Psi4s60N4 i8Psi4s60dN0
    i8Psi4s60dN1 i8Psi4s60dN2 i8Psi4s60dN3 i8Psi4s60dN4 i8Psi4s60dW i8P4s60
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, i13hw_1m hx, i13_log_one_sub_eq hx]
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽61⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s61N0 (x : ℝ) : ℝ :=
    (2) * hpl [negOne, negOne, one] x +
    (2) * hpl [negOne, one, negOne] x +
    (2) * hpl [one, negOne, negOne] x

/-- The derivative of `i8Psi4s61N0`. -/
noncomputable def i8Psi4s61dN0 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [negOne, one] x) +
    (2) * (negOne.kernel x * hpl [one, negOne] x) +
    (2) * (one.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s61N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s61N0 (i8Psi4s61dN0 x) x := by
  unfold i8Psi4s61N0 i8Psi4s61dN0
  exact ((((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽61⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s61N1 (x : ℝ) : ℝ :=
    (2) * hpl [negOne, negOne] x +
    (2) * hpl [negOne, one] x +
    (2) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s61N1`. -/
noncomputable def i8Psi4s61dN1 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s61N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s61N1 (i8Psi4s61dN1 x) x := by
  unfold i8Psi4s61N1 i8Psi4s61dN1
  exact ((((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽61⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s61N2 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne] x +
    (-5 / 2) * hpl [one] x +
    (1) * hpl [negOne, negOne] x +
    (-1) * hpl [negOne, one] x +
    (-1) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s61N2`. -/
noncomputable def i8Psi4s61dN2 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [] x) +
    (-5 / 2) * (one.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s61N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s61N2 (i8Psi4s61dN2 x) x := by
  unfold i8Psi4s61N2 i8Psi4s61dN2
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽61⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s61N3 (x : ℝ) : ℝ :=
    (7 / 2) +
    (3) * hpl [one] x +
    (-2) * hpl [negOne, negOne] x +
    (-2) * hpl [negOne, one] x +
    (-2) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s61N3`. -/
noncomputable def i8Psi4s61dN3 (x : ℝ) : ℝ :=
    0 +
    (3) * (one.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s61N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s61N3 (i8Psi4s61dN3 x) x := by
  unfold i8Psi4s61N3 i8Psi4s61dN3
  exact (((((hasDerivAt_const x (7 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽61⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s61N4 (x : ℝ) : ℝ :=
    (-3 / 4) +
    (1) * hpl [negOne] x +
    (-1 / 2) * hpl [one] x +
    (-1) * hpl [negOne, negOne] x +
    (1) * hpl [negOne, one] x +
    (1) * hpl [one, negOne] x +
    (-2) * hpl [negOne, negOne, one] x +
    (-2) * hpl [negOne, one, negOne] x +
    (-2) * hpl [one, negOne, negOne] x

/-- The derivative of `i8Psi4s61N4`. -/
noncomputable def i8Psi4s61dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [negOne, one] x) +
    (-2) * (negOne.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, negOne] x)

theorem hasDerivAt_i8Psi4s61N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s61N4 (i8Psi4s61dN4 x) x := by
  unfold i8Psi4s61N4 i8Psi4s61dN4
  exact (((((((((hasDerivAt_const x (-3 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽61⁾` with constant coefficients. -/
noncomputable def i8Psi4s61W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, negOne] x +
    (-2) * hpl [zero, one] x +
    (-2) * hpl [zero, negOne, negOne] x +
    (2) * hpl [zero, negOne, one] x +
    (2) * hpl [zero, one, negOne] x +
    (8) * hpl [zero, negOne, negOne, one] x +
    (8) * hpl [zero, negOne, one, negOne] x +
    (8) * hpl [zero, one, negOne, negOne] x

/-- The derivative of `i8Psi4s61W`. -/
noncomputable def i8Psi4s61dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [negOne, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, one] x) +
    (2) * (zero.kernel x * hpl [one, negOne] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, one] x) +
    (8) * (zero.kernel x * hpl [negOne, one, negOne] x) +
    (8) * (zero.kernel x * hpl [one, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s61W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s61W (i8Psi4s61dW x) x := by
  unfold i8Psi4s61W i8Psi4s61dW
  exact (((((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne] hx).const_mul (8)))

/-- The piece `Ψ₄⁽61⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s61 (x : ℝ) : ℝ :=
  (i8Psi4s61N0 x + x * i8Psi4s61N1 x + x ^ 2 * i8Psi4s61N2 x + x ^ 3 * i8Psi4s61N3 x +
    x ^ 4 * i8Psi4s61N4 x) / x ^ 2 + i8Psi4s61W x

/-- The derivative of `Ψ₄⁽61⁾`. -/
noncomputable def i8Psi4s61D (x : ℝ) : ℝ :=
  ((i8Psi4s61dN0 x + (i8Psi4s61N1 x + x * i8Psi4s61dN1 x) + (2 * x * i8Psi4s61N2 x +
    x ^ 2 * i8Psi4s61dN2 x) + (3 * x ^ 2 * i8Psi4s61N3 x + x ^ 3 * i8Psi4s61dN3 x) +
    (4 * x ^ 3 * i8Psi4s61N4 x + x ^ 4 * i8Psi4s61dN4 x)) * x ^ 2 - (i8Psi4s61N0 x +
    x * i8Psi4s61N1 x + x ^ 2 * i8Psi4s61N2 x + x ^ 3 * i8Psi4s61N3 x +
    x ^ 4 * i8Psi4s61N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s61dW x

theorem hasDerivAt_i8Psi4s61 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s61 (i8Psi4s61D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s61N0 hx).add (X.mul (hasDerivAt_i8Psi4s61N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s61N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s61N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s61N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s61W hx)
  unfold i8Psi4s61
  refine e.congr_deriv ?_
  unfold i8Psi4s61D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 61 of `p₄` in `ξ`: from `t B0 A3 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s61 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 - x) * (2 * hpl [negOne, negOne] x)))

/-- **`(Ψ₄⁽61⁾)'(ξ) ξ' = p₄⁽61⁾`**, in terms of `ξ`. -/
theorem i8Psi4s61D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s61D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s61 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s61D i8Psi4s61N0 i8Psi4s61N1 i8Psi4s61N2 i8Psi4s61N3 i8Psi4s61N4 i8Psi4s61dN0
    i8Psi4s61dN1 i8Psi4s61dN2 i8Psi4s61dN3 i8Psi4s61dN4 i8Psi4s61dW i8P4s61
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, i13hw_1m hx, i13hw_mm hx, i8hw_m1m hx,
    i13hw_1mm hx, i13_log_one_sub_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
