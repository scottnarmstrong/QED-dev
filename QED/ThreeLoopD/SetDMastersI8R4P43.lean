/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P42

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 141 to 143

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s141`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s141D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s141`, `QED.ThreeLoopD.i8Psi4s141D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽141⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s141N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s141N0`. -/
noncomputable def i8Psi4s141dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s141N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s141N0 (i8Psi4s141dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽141⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s141N1 (x : ℝ) : ℝ :=
    (1) +
    (1) * hpl [zero] x +
    (1) * hpl [zero, zero] x +
    (1) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s141N1`. -/
noncomputable def i8Psi4s141dN1 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s141N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s141N1 (i8Psi4s141dN1 x) x := by
  unfold i8Psi4s141N1 i8Psi4s141dN1
  exact ((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽141⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s141N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s141N2`. -/
noncomputable def i8Psi4s141dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s141N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s141N2 (i8Psi4s141dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽141⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s141N3 (x : ℝ) : ℝ :=
    (-1) +
    (1) * hpl [zero] x +
    (-1) * hpl [zero, zero] x +
    (1) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s141N3`. -/
noncomputable def i8Psi4s141dN3 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s141N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s141N3 (i8Psi4s141dN3 x) x := by
  unfold i8Psi4s141N3 i8Psi4s141dN3
  exact ((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽141⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s141N4 (x : ℝ) : ℝ :=
    (1 / 16) +
    (-1 / 8) * hpl [zero] x +
    (1 / 4) * hpl [zero, zero] x +
    (-1 / 2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s141N4`. -/
noncomputable def i8Psi4s141dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 8) * (zero.kernel x * hpl [] x) +
    (1 / 4) * (zero.kernel x * hpl [zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s141N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s141N4 (i8Psi4s141dN4 x) x := by
  unfold i8Psi4s141N4 i8Psi4s141dN4
  exact ((((hasDerivAt_const x (1 / 16)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1 / 2)))

/-- The part of `Ψ₄⁽141⁾` with constant coefficients. -/
noncomputable def i8Psi4s141W (x : ℝ) : ℝ :=
    (1) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s141W`. -/
noncomputable def i8Psi4s141dW (x : ℝ) : ℝ :=
    (1) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s141W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s141W (i8Psi4s141dW x) x := by
  unfold i8Psi4s141W i8Psi4s141dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (1))

/-- The piece `Ψ₄⁽141⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s141 (x : ℝ) : ℝ :=
  (i8Psi4s141N0 x + x * i8Psi4s141N1 x + x ^ 2 * i8Psi4s141N2 x + x ^ 3 * i8Psi4s141N3 x +
    x ^ 4 * i8Psi4s141N4 x) / x ^ 2 + i8Psi4s141W x

/-- The derivative of `Ψ₄⁽141⁾`. -/
noncomputable def i8Psi4s141D (x : ℝ) : ℝ :=
  ((i8Psi4s141dN0 x + (i8Psi4s141N1 x + x * i8Psi4s141dN1 x) + (2 * x * i8Psi4s141N2 x +
    x ^ 2 * i8Psi4s141dN2 x) + (3 * x ^ 2 * i8Psi4s141N3 x + x ^ 3 * i8Psi4s141dN3 x) +
    (4 * x ^ 3 * i8Psi4s141N4 x + x ^ 4 * i8Psi4s141dN4 x)) * x ^ 2 - (i8Psi4s141N0 x +
    x * i8Psi4s141N1 x + x ^ 2 * i8Psi4s141N2 x + x ^ 3 * i8Psi4s141N3 x +
    x ^ 4 * i8Psi4s141N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s141dW x

theorem hasDerivAt_i8Psi4s141 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s141 (i8Psi4s141D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s141N0 hx).add (X.mul (hasDerivAt_i8Psi4s141N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s141N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s141N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s141N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s141W hx)
  unfold i8Psi4s141
  refine e.congr_deriv ?_
  unfold i8Psi4s141D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 141 of `p₄` in `ξ`: from `t B0 A1 (-λ)^3/3!`, the term with `log^0 (1 -
  ξ) log^3 ξ`. -/
noncomputable def i8P4s141 (x : ℝ) : ℝ :=
  (1 / 6) * (1 - x) ^ 2 / x * Real.log x ^ 3 * ((1 + x) / (1 - x) * (x / (1 + x)))

/-- `p₄⁽141⁾` written over words. -/
noncomputable def i8P4w141 (x : ℝ) : ℝ :=
    (1 - x) * hpl [zero, zero, zero] x

theorem i8P4s141_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s141 x = i8P4w141 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s141 i8P4w141
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [zero] hx
  have e1 := hpl_mul_hpl [zero] [zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  linear_combination (norm := skip) ((1 / 6 - x / 6) * hpl [zero] x) * e0 + ((1 / 3 - x / 3)) * e1
  field_simp
  generalize hpl [zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero] x = v1 at *
  generalize hpl [zero] x = v2 at *
  ring

/-- **`(Ψ₄⁽141⁾)'(ξ) ξ' = p₄⁽141⁾`**, in terms of `ξ`. -/
theorem i8Psi4s141D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s141D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s141 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s141_eq_w hx]
  unfold i8Psi4s141D i8Psi4s141N0 i8Psi4s141N1 i8Psi4s141N2 i8Psi4s141N3 i8Psi4s141N4 i8Psi4s141dN0
    i8Psi4s141dN1 i8Psi4s141dN2 i8Psi4s141dN3 i8Psi4s141dN4 i8Psi4s141dW i8P4w141
  simp only [kernel_zero, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero] x = v1 at *
  generalize hpl [zero, zero] x = v2 at *
  generalize hpl [zero] x = v3 at *
  ring

/-- The part of `ξ² Ψ₄⁽142⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s142N0 (x : ℝ) : ℝ :=
    (-1 / 16) * hpl [negOne] x +
    (-1 / 8) * hpl [negOne, zero] x +
    (-1 / 8) * hpl [zero, negOne] x +
    (-1 / 4) * hpl [negOne, zero, zero] x +
    (-1 / 4) * hpl [zero, negOne, zero] x +
    (-1 / 4) * hpl [zero, zero, negOne] x +
    (-1 / 2) * hpl [negOne, zero, zero, zero] x +
    (-1 / 2) * hpl [zero, negOne, zero, zero] x +
    (-1 / 2) * hpl [zero, zero, negOne, zero] x +
    (-1 / 2) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s142N0`. -/
noncomputable def i8Psi4s142dN0 (x : ℝ) : ℝ :=
    (-1 / 16) * (negOne.kernel x * hpl [] x) +
    (-1 / 8) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 8) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s142N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s142N0 (i8Psi4s142dN0 x) x := by
  unfold i8Psi4s142N0 i8Psi4s142dN0
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 16)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-1 / 2)))

/-- The part of `ξ² Ψ₄⁽142⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s142N1 (x : ℝ) : ℝ :=
    (-15 / 16) +
    (-7 / 8) * hpl [zero] x +
    (-3 / 4) * hpl [zero, zero] x +
    (-1 / 2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s142N1`. -/
noncomputable def i8Psi4s142dN1 (x : ℝ) : ℝ :=
    0 +
    (-7 / 8) * (zero.kernel x * hpl [] x) +
    (-3 / 4) * (zero.kernel x * hpl [zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s142N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s142N1 (i8Psi4s142dN1 x) x := by
  unfold i8Psi4s142N1 i8Psi4s142dN1
  exact ((((hasDerivAt_const x (-15 / 16)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-7 / 8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1 / 2)))

/-- The part of `ξ² Ψ₄⁽142⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s142N2 (x : ℝ) : ℝ :=
    (1 / 8) * hpl [negOne] x +
    (-1 / 16) * hpl [zero] x +
    (-1 / 8) * hpl [zero, zero] x +
    (1 / 2) * hpl [negOne, zero, zero] x +
    (-1 / 4) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s142N2`. -/
noncomputable def i8Psi4s142dN2 (x : ℝ) : ℝ :=
    (1 / 8) * (negOne.kernel x * hpl [] x) +
    (-1 / 16) * (zero.kernel x * hpl [] x) +
    (-1 / 8) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s142N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s142N2 (i8Psi4s142dN2 x) x := by
  unfold i8Psi4s142N2 i8Psi4s142dN2
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 16))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1 / 4)))

/-- The part of `ξ² Ψ₄⁽142⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s142N3 (x : ℝ) : ℝ :=
    (-15 / 16) +
    (7 / 8) * hpl [zero] x +
    (-3 / 4) * hpl [zero, zero] x +
    (1 / 2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s142N3`. -/
noncomputable def i8Psi4s142dN3 (x : ℝ) : ℝ :=
    0 +
    (7 / 8) * (zero.kernel x * hpl [] x) +
    (-3 / 4) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s142N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s142N3 (i8Psi4s142dN3 x) x := by
  unfold i8Psi4s142N3 i8Psi4s142dN3
  exact ((((hasDerivAt_const x (-15 / 16)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (7 / 8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽142⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s142N4 (x : ℝ) : ℝ :=
    (1 / 8) +
    (-1 / 16) * hpl [negOne] x +
    (-3 / 16) * hpl [zero] x +
    (1 / 8) * hpl [negOne, zero] x +
    (1 / 8) * hpl [zero, negOne] x +
    (1 / 4) * hpl [zero, zero] x +
    (-1 / 4) * hpl [negOne, zero, zero] x +
    (-1 / 4) * hpl [zero, negOne, zero] x +
    (-1 / 4) * hpl [zero, zero, negOne] x +
    (-1 / 4) * hpl [zero, zero, zero] x +
    (1 / 2) * hpl [negOne, zero, zero, zero] x +
    (1 / 2) * hpl [zero, negOne, zero, zero] x +
    (1 / 2) * hpl [zero, zero, negOne, zero] x +
    (1 / 2) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s142N4`. -/
noncomputable def i8Psi4s142dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 16) * (negOne.kernel x * hpl [] x) +
    (-3 / 16) * (zero.kernel x * hpl [] x) +
    (1 / 8) * (negOne.kernel x * hpl [zero] x) +
    (1 / 8) * (zero.kernel x * hpl [negOne] x) +
    (1 / 4) * (zero.kernel x * hpl [zero] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero, zero] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s142N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s142N4 (i8Psi4s142dN4 x) x := by
  unfold i8Psi4s142N4 i8Psi4s142dN4
  exact ((((((((((((((hasDerivAt_const x (1 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 16))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 16))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (1 / 2)))

/-- The part of `Ψ₄⁽142⁾` with constant coefficients. -/
noncomputable def i8Psi4s142W (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [zero, zero, zero, zero] x +
    (-2) * hpl [zero, negOne, zero, zero, zero] x +
    (-2) * hpl [zero, zero, negOne, zero, zero] x +
    (-2) * hpl [zero, zero, zero, negOne, zero] x +
    (-2) * hpl [zero, zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s142W`. -/
noncomputable def i8Psi4s142dW (x : ℝ) : ℝ :=
    (-1 / 2) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, zero, negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s142W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s142W (i8Psi4s142dW x) x := by
  unfold i8Psi4s142W i8Psi4s142dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, negOne] hx).const_mul (-2)))

/-- The piece `Ψ₄⁽142⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s142 (x : ℝ) : ℝ :=
  (i8Psi4s142N0 x + x * i8Psi4s142N1 x + x ^ 2 * i8Psi4s142N2 x + x ^ 3 * i8Psi4s142N3 x +
    x ^ 4 * i8Psi4s142N4 x) / x ^ 2 + i8Psi4s142W x

/-- The derivative of `Ψ₄⁽142⁾`. -/
noncomputable def i8Psi4s142D (x : ℝ) : ℝ :=
  ((i8Psi4s142dN0 x + (i8Psi4s142N1 x + x * i8Psi4s142dN1 x) + (2 * x * i8Psi4s142N2 x +
    x ^ 2 * i8Psi4s142dN2 x) + (3 * x ^ 2 * i8Psi4s142N3 x + x ^ 3 * i8Psi4s142dN3 x) +
    (4 * x ^ 3 * i8Psi4s142N4 x + x ^ 4 * i8Psi4s142dN4 x)) * x ^ 2 - (i8Psi4s142N0 x +
    x * i8Psi4s142N1 x + x ^ 2 * i8Psi4s142N2 x + x ^ 3 * i8Psi4s142N3 x +
    x ^ 4 * i8Psi4s142N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s142dW x

theorem hasDerivAt_i8Psi4s142 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s142 (i8Psi4s142D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s142N0 hx).add (X.mul (hasDerivAt_i8Psi4s142N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s142N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s142N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s142N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s142W hx)
  unfold i8Psi4s142
  refine e.congr_deriv ?_
  unfold i8Psi4s142D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 142 of `p₄` in `ξ`: from `t B0 A1 (-λ)^3/3!`, the term with `log^0 (1 -
  ξ) log^3 ξ`. -/
noncomputable def i8P4s142 (x : ℝ) : ℝ :=
  (1 / 6) * (1 - x) ^ 2 / x * Real.log x ^ 3 * ((1 + x) / (1 - x) * (-hpl [negOne] x))

/-- `p₄⁽142⁾` written over words. -/
noncomputable def i8P4w142 (x : ℝ) : ℝ :=
    ((-1 + x ^ 2) / (x)) * hpl [negOne, zero, zero, zero] x +
    ((-1 + x ^ 2) / (x)) * hpl [zero, negOne, zero, zero] x +
    ((-1 + x ^ 2) / (x)) * hpl [zero, zero, negOne, zero] x +
    ((-1 + x ^ 2) / (x)) * hpl [zero, zero, zero, negOne] x

theorem i8P4s142_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s142 x = i8P4w142 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s142 i8P4w142
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [zero] hx
  have e1 := hpl_mul_hpl [zero] [zero, zero] hx
  have e2 := hpl_mul_hpl [negOne] [zero, zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  linear_combination (norm := skip) (((-1 / 6 +
    x ^ 2 / 6) / (x)) * hpl [zero] x * hpl [negOne] x) * e0 + (((-1 / 3 +
    x ^ 2 / 3) / (x)) * hpl [negOne] x) * e1 + (((-1 + x ^ 2) / (x))) * e2
  field_simp
  generalize hpl [negOne, zero, zero, zero] x = v0 at *
  generalize hpl [zero, negOne, zero, zero] x = v1 at *
  generalize hpl [zero, zero, negOne, zero] x = v2 at *
  generalize hpl [zero, zero, zero, negOne] x = v3 at *
  generalize hpl [zero, zero, zero] x = v4 at *
  generalize hpl [zero, zero] x = v5 at *
  generalize hpl [negOne] x = v6 at *
  generalize hpl [zero] x = v7 at *
  ring

/-- **`(Ψ₄⁽142⁾)'(ξ) ξ' = p₄⁽142⁾`**, in terms of `ξ`. -/
theorem i8Psi4s142D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s142D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s142 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s142_eq_w hx]
  unfold i8Psi4s142D i8Psi4s142N0 i8Psi4s142N1 i8Psi4s142N2 i8Psi4s142N3 i8Psi4s142N4 i8Psi4s142dN0
    i8Psi4s142dN1 i8Psi4s142dN2 i8Psi4s142dN3 i8Psi4s142dN4 i8Psi4s142dW i8P4w142
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, zero, zero] x = v1 at *
  generalize hpl [zero, zero, zero, negOne, zero] x = v2 at *
  generalize hpl [zero, zero, zero, zero, negOne] x = v3 at *
  generalize hpl [negOne, zero, zero, zero] x = v4 at *
  generalize hpl [zero, negOne, zero, zero] x = v5 at *
  generalize hpl [zero, zero, negOne, zero] x = v6 at *
  generalize hpl [zero, zero, zero, negOne] x = v7 at *
  generalize hpl [zero, zero, zero, zero] x = v8 at *
  generalize hpl [negOne, zero, zero] x = v9 at *
  generalize hpl [zero, negOne, zero] x = v10 at *
  generalize hpl [zero, zero, negOne] x = v11 at *
  generalize hpl [zero, zero, zero] x = v12 at *
  generalize hpl [negOne, zero] x = v13 at *
  generalize hpl [zero, negOne] x = v14 at *
  generalize hpl [zero, zero] x = v15 at *
  generalize hpl [negOne] x = v16 at *
  generalize hpl [zero] x = v17 at *
  ring

/-- The part of `ξ² Ψ₄⁽143⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s143N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s143N0`. -/
noncomputable def i8Psi4s143dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s143N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s143N0 (i8Psi4s143dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽143⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s143N1 (x : ℝ) : ℝ :=
    (2) * hpl [one] x +
    (2) * hpl [zero, one] x +
    (2) * hpl [one, zero] x +
    (2) * hpl [zero, zero, one] x +
    (2) * hpl [zero, one, zero] x +
    (2) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s143N1`. -/
noncomputable def i8Psi4s143dN1 (x : ℝ) : ℝ :=
    (2) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (2) * (zero.kernel x * hpl [one, zero] x) +
    (2) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s143N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s143N1 (i8Psi4s143dN1 x) x := by
  unfold i8Psi4s143N1 i8Psi4s143dN1
  exact (((((((hasDerivAt_hpl_cons one [] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽143⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s143N2 (x : ℝ) : ℝ :=
    (-2) * hpl [zero] x +
    (-15 / 4) * hpl [one] x +
    (-2) * hpl [zero, zero] x +
    (-1 / 2) * hpl [one, zero] x +
    (-3) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s143N2`. -/
noncomputable def i8Psi4s143dN2 (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [] x) +
    (-15 / 4) * (one.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [zero] x) +
    (-1 / 2) * (one.kernel x * hpl [zero] x) +
    (-3) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s143N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s143N2 (i8Psi4s143dN2 x) x := by
  unfold i8Psi4s143N2 i8Psi4s143dN2
  exact ((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-15 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-3)))

/-- The part of `ξ² Ψ₄⁽143⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s143N3 (x : ℝ) : ℝ :=
    (17 / 4) +
    (-5 / 2) * hpl [zero] x +
    (2) * hpl [one] x +
    (1) * hpl [zero, zero] x +
    (-2) * hpl [zero, one] x +
    (-2) * hpl [one, zero] x +
    (2) * hpl [zero, zero, one] x +
    (2) * hpl [zero, one, zero] x +
    (2) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s143N3`. -/
noncomputable def i8Psi4s143dN3 (x : ℝ) : ℝ :=
    0 +
    (-5 / 2) * (zero.kernel x * hpl [] x) +
    (2) * (one.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (2) * (zero.kernel x * hpl [one, zero] x) +
    (2) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s143N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s143N3 (i8Psi4s143dN3 x) x := by
  unfold i8Psi4s143N3 i8Psi4s143dN3
  exact (((((((((hasDerivAt_const x (17 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽143⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s143N4 (x : ℝ) : ℝ :=
    (-3 / 8) +
    (1 / 2) * hpl [zero] x +
    (-1 / 4) * hpl [one] x +
    (-1 / 2) * hpl [zero, zero] x +
    (1 / 2) * hpl [zero, one] x +
    (1 / 2) * hpl [one, zero] x +
    (-1) * hpl [zero, zero, one] x +
    (-1) * hpl [zero, one, zero] x +
    (-1) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s143N4`. -/
noncomputable def i8Psi4s143dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (one.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [one] x) +
    (1 / 2) * (one.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [zero, one] x) +
    (-1) * (zero.kernel x * hpl [one, zero] x) +
    (-1) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s143N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s143N4 (i8Psi4s143dN4 x) x := by
  unfold i8Psi4s143N4 i8Psi4s143dN4
  exact (((((((((hasDerivAt_const x (-3 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-1)))

/-- The part of `Ψ₄⁽143⁾` with constant coefficients. -/
noncomputable def i8Psi4s143W (x : ℝ) : ℝ :=
    (-2) * hpl [zero, zero, zero] x +
    (2) * hpl [zero, zero, zero, one] x +
    (2) * hpl [zero, zero, one, zero] x +
    (2) * hpl [zero, one, zero, zero] x

/-- The derivative of `i8Psi4s143W`. -/
noncomputable def i8Psi4s143dW (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero, one] x) +
    (2) * (zero.kernel x * hpl [zero, one, zero] x) +
    (2) * (zero.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s143W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s143W (i8Psi4s143dW x) x := by
  unfold i8Psi4s143W i8Psi4s143dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (2)))

/-- The piece `Ψ₄⁽143⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s143 (x : ℝ) : ℝ :=
  (i8Psi4s143N0 x + x * i8Psi4s143N1 x + x ^ 2 * i8Psi4s143N2 x + x ^ 3 * i8Psi4s143N3 x +
    x ^ 4 * i8Psi4s143N4 x) / x ^ 2 + i8Psi4s143W x

/-- The derivative of `Ψ₄⁽143⁾`. -/
noncomputable def i8Psi4s143D (x : ℝ) : ℝ :=
  ((i8Psi4s143dN0 x + (i8Psi4s143N1 x + x * i8Psi4s143dN1 x) + (2 * x * i8Psi4s143N2 x +
    x ^ 2 * i8Psi4s143dN2 x) + (3 * x ^ 2 * i8Psi4s143N3 x + x ^ 3 * i8Psi4s143dN3 x) +
    (4 * x ^ 3 * i8Psi4s143N4 x + x ^ 4 * i8Psi4s143dN4 x)) * x ^ 2 - (i8Psi4s143N0 x +
    x * i8Psi4s143N1 x + x ^ 2 * i8Psi4s143N2 x + x ^ 3 * i8Psi4s143N3 x +
    x ^ 4 * i8Psi4s143N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s143dW x

theorem hasDerivAt_i8Psi4s143 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s143 (i8Psi4s143D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s143N0 hx).add (X.mul (hasDerivAt_i8Psi4s143N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s143N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s143N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s143N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s143W hx)
  unfold i8Psi4s143
  refine e.congr_deriv ?_
  unfold i8Psi4s143D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 143 of `p₄` in `ξ`: from `t B0 A1 (-λ)^3/3!`, the term with `log^1 (1 -
  ξ) log^2 ξ`. -/
noncomputable def i8P4s143 (x : ℝ) : ℝ :=
  -((1 - x) ^ 2 / x * Real.log (1 - x) * Real.log x ^ 2 * ((1 + x) / (1 - x) * (x / (1 + x))))

/-- `p₄⁽143⁾` written over words. -/
noncomputable def i8P4w143 (x : ℝ) : ℝ :=
    (2 - 2 * x) * hpl [zero, zero, one] x +
    (2 - 2 * x) * hpl [zero, one, zero] x +
    (2 - 2 * x) * hpl [one, zero, zero] x

theorem i8P4s143_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s143 x = i8P4w143 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s143 i8P4w143
  rw [i13_log_one_sub_eq hx]
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [one] hx
  have e1 := hpl_mul_hpl [zero] [zero, one] hx
  have e2 := hpl_mul_hpl [zero] [one, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  linear_combination (norm := skip) ((1 - x) * hpl [zero] x) * e0 + ((1 - x)) * e1 + ((1 - x)) * e2
  field_simp
  generalize hpl [zero, zero, one] x = v0 at *
  generalize hpl [zero, one, zero] x = v1 at *
  generalize hpl [one, zero, zero] x = v2 at *
  generalize hpl [zero, one] x = v3 at *
  generalize hpl [one, zero] x = v4 at *
  generalize hpl [zero] x = v5 at *
  generalize hpl [one] x = v6 at *
  ring

/-- **`(Ψ₄⁽143⁾)'(ξ) ξ' = p₄⁽143⁾`**, in terms of `ξ`. -/
theorem i8Psi4s143D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s143D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s143 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s143_eq_w hx]
  unfold i8Psi4s143D i8Psi4s143N0 i8Psi4s143N1 i8Psi4s143N2 i8Psi4s143N3 i8Psi4s143N4 i8Psi4s143dN0
    i8Psi4s143dN1 i8Psi4s143dN2 i8Psi4s143dN3 i8Psi4s143dN4 i8Psi4s143dW i8P4w143
  simp only [kernel_zero, kernel_one, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero, one] x = v0 at *
  generalize hpl [zero, zero, one, zero] x = v1 at *
  generalize hpl [zero, one, zero, zero] x = v2 at *
  generalize hpl [zero, zero, zero] x = v3 at *
  generalize hpl [zero, zero, one] x = v4 at *
  generalize hpl [zero, one, zero] x = v5 at *
  generalize hpl [one, zero, zero] x = v6 at *
  generalize hpl [zero, zero] x = v7 at *
  generalize hpl [zero, one] x = v8 at *
  generalize hpl [one, zero] x = v9 at *
  generalize hpl [zero] x = v10 at *
  generalize hpl [one] x = v11 at *
  ring

end QED.ThreeLoopD
