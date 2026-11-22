/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P23

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 93 to 98

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s93`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s93D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s93`, `QED.ThreeLoopD.i8Psi4s93D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽93⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s93N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s93N0`. -/
noncomputable def i8Psi4s93dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s93N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s93N0 (i8Psi4s93dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽93⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s93N1 (x : ℝ) : ℝ :=
    (8) +
    (8) * hpl [zero] x +
    (8) * hpl [zero, zero] x +
    (8) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s93N1`. -/
noncomputable def i8Psi4s93dN1 (x : ℝ) : ℝ :=
    0 +
    (8) * (zero.kernel x * hpl [] x) +
    (8) * (zero.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s93N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s93N1 (i8Psi4s93dN1 x) x := by
  unfold i8Psi4s93N1 i8Psi4s93dN1
  exact (((((hasDerivAt_const x (8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽93⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s93N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s93N2`. -/
noncomputable def i8Psi4s93dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s93N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s93N2 (i8Psi4s93dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽93⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s93N3 (x : ℝ) : ℝ :=
    (8) +
    (-8) * hpl [zero] x +
    (8) * hpl [zero, zero] x +
    (-8) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s93N3`. -/
noncomputable def i8Psi4s93dN3 (x : ℝ) : ℝ :=
    0 +
    (-8) * (zero.kernel x * hpl [] x) +
    (8) * (zero.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s93N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s93N3 (i8Psi4s93dN3 x) x := by
  unfold i8Psi4s93N3 i8Psi4s93dN3
  exact (((((hasDerivAt_const x (8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽93⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s93N4 (x : ℝ) : ℝ :=
    (1 / 4) +
    (-1 / 2) * hpl [zero] x +
    (1) * hpl [zero, zero] x +
    (-2) * hpl [zero, zero, zero] x +
    (4) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s93N4`. -/
noncomputable def i8Psi4s93dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s93N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s93N4 (i8Psi4s93dN4 x) x := by
  unfold i8Psi4s93N4 i8Psi4s93dN4
  exact (((((hasDerivAt_const x (1 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽93⁾` with constant coefficients. -/
noncomputable def i8Psi4s93W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s93W`. -/
noncomputable def i8Psi4s93dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s93W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s93W (i8Psi4s93dW x) x := by
  unfold i8Psi4s93W i8Psi4s93dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero, zero] hx).const_mul (-8))

/-- The piece `Ψ₄⁽93⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s93 (x : ℝ) : ℝ :=
  (i8Psi4s93N0 x + x * i8Psi4s93N1 x + x ^ 2 * i8Psi4s93N2 x + x ^ 3 * i8Psi4s93N3 x +
    x ^ 4 * i8Psi4s93N4 x) / x ^ 2 + i8Psi4s93W x

/-- The derivative of `Ψ₄⁽93⁾`. -/
noncomputable def i8Psi4s93D (x : ℝ) : ℝ :=
  ((i8Psi4s93dN0 x + (i8Psi4s93N1 x + x * i8Psi4s93dN1 x) + (2 * x * i8Psi4s93N2 x +
    x ^ 2 * i8Psi4s93dN2 x) + (3 * x ^ 2 * i8Psi4s93N3 x + x ^ 3 * i8Psi4s93dN3 x) +
    (4 * x ^ 3 * i8Psi4s93N4 x + x ^ 4 * i8Psi4s93dN4 x)) * x ^ 2 - (i8Psi4s93N0 x +
    x * i8Psi4s93N1 x + x ^ 2 * i8Psi4s93N2 x + x ^ 3 * i8Psi4s93N3 x +
    x ^ 4 * i8Psi4s93N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s93dW x

theorem hasDerivAt_i8Psi4s93 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s93 (i8Psi4s93D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s93N0 hx).add (X.mul (hasDerivAt_i8Psi4s93N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s93N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s93N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s93N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s93W hx)
  unfold i8Psi4s93
  refine e.congr_deriv ?_
  unfold i8Psi4s93D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 93 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s93 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 -
    x) * (1 * hpl [zero, zero, zero] x)) * (x / (1 - x))

/-- `p₄⁽93⁾` written over words. -/
noncomputable def i8P4w93 (x : ℝ) : ℝ :=
    (8 + 8 * x) * hpl [zero, zero, zero, zero] x

theorem i8P4s93_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s93 x = i8P4w93 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s93 i8P4w93
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero, zero, zero] [zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((2 + 2 * x)) * e0
  field_simp
  generalize hpl [zero, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero] x = v1 at *
  generalize hpl [zero] x = v2 at *
  ring

/-- **`(Ψ₄⁽93⁾)'(ξ) ξ' = p₄⁽93⁾`**, in terms of `ξ`. -/
theorem i8Psi4s93D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s93D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s93 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s93_eq_w hx]
  unfold i8Psi4s93D i8Psi4s93N0 i8Psi4s93N1 i8Psi4s93N2 i8Psi4s93N3 i8Psi4s93N4 i8Psi4s93dN0
    i8Psi4s93dN1 i8Psi4s93dN2 i8Psi4s93dN3 i8Psi4s93dN4 i8Psi4s93dW i8P4w93
  simp only [kernel_zero, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero, zero] x = v1 at *
  generalize hpl [zero, zero, zero] x = v2 at *
  generalize hpl [zero, zero] x = v3 at *
  generalize hpl [zero] x = v4 at *
  ring

/-- The part of `ξ² Ψ₄⁽94⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s94N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s94N0`. -/
noncomputable def i8Psi4s94dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s94N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s94N0 (i8Psi4s94dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽94⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s94N1 (x : ℝ) : ℝ :=
    (-4) * hpl [negOne, zero, zero] x +
    (-12) * hpl [negOne, zero, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s94N1`. -/
noncomputable def i8Psi4s94dN1 (x : ℝ) : ℝ :=
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s94N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s94N1 (i8Psi4s94dN1 x) x := by
  unfold i8Psi4s94N1 i8Psi4s94dN1
  exact ((((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽94⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s94N2 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne, zero, zero] x +
    (4) * hpl [zero, zero, zero] x +
    (-18) * hpl [negOne, zero, zero, zero] x

/-- The derivative of `i8Psi4s94N2`. -/
noncomputable def i8Psi4s94dN2 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, zero] x) +
    (-18) * (negOne.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s94N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s94N2 (i8Psi4s94dN2 x) x := by
  unfold i8Psi4s94N2 i8Psi4s94dN2
  exact ((((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-18)))

/-- The part of `ξ² Ψ₄⁽94⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s94N3 (x : ℝ) : ℝ :=
    (-9) +
    (9) * hpl [zero] x +
    (-9) * hpl [zero, zero] x +
    (4) * hpl [negOne, zero, zero] x +
    (6) * hpl [zero, zero, zero] x +
    (-12) * hpl [negOne, zero, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s94N3`. -/
noncomputable def i8Psi4s94dN3 (x : ℝ) : ℝ :=
    0 +
    (9) * (zero.kernel x * hpl [] x) +
    (-9) * (zero.kernel x * hpl [zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s94N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s94N3 (i8Psi4s94dN3 x) x := by
  unfold i8Psi4s94N3 i8Psi4s94dN3
  exact (((((((hasDerivAt_const x (-9)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-9))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽94⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s94N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (1) * hpl [zero] x +
    (-2) * hpl [zero, zero] x +
    (1) * hpl [negOne, zero, zero] x +
    (3) * hpl [zero, zero, zero] x +
    (-6) * hpl [negOne, zero, zero, zero] x +
    (-2) * hpl [zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s94N4`. -/
noncomputable def i8Psi4s94dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [zero, zero] x) +
    (3) * (zero.kernel x * hpl [zero, zero] x) +
    (-6) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s94N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s94N4 (i8Psi4s94dN4 x) x := by
  unfold i8Psi4s94N4 i8Psi4s94dN4
  exact (((((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽94⁾` with constant coefficients. -/
noncomputable def i8Psi4s94W (x : ℝ) : ℝ :=
    (12) * hpl [zero, zero, zero, zero] x +
    (12) * hpl [zero, negOne, zero, zero, zero] x +
    (4) * hpl [zero, zero, negOne, zero, zero] x

/-- The derivative of `i8Psi4s94W`. -/
noncomputable def i8Psi4s94dW (x : ℝ) : ℝ :=
    (12) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (12) * (zero.kernel x * hpl [negOne, zero, zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s94W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s94W (i8Psi4s94dW x) x := by
  unfold i8Psi4s94W i8Psi4s94dW
  exact ((((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (12)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (4)))

/-- The piece `Ψ₄⁽94⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s94 (x : ℝ) : ℝ :=
  (i8Psi4s94N0 x + x * i8Psi4s94N1 x + x ^ 2 * i8Psi4s94N2 x + x ^ 3 * i8Psi4s94N3 x +
    x ^ 4 * i8Psi4s94N4 x) / x ^ 2 + i8Psi4s94W x

/-- The derivative of `Ψ₄⁽94⁾`. -/
noncomputable def i8Psi4s94D (x : ℝ) : ℝ :=
  ((i8Psi4s94dN0 x + (i8Psi4s94N1 x + x * i8Psi4s94dN1 x) + (2 * x * i8Psi4s94N2 x +
    x ^ 2 * i8Psi4s94dN2 x) + (3 * x ^ 2 * i8Psi4s94N3 x + x ^ 3 * i8Psi4s94dN3 x) +
    (4 * x ^ 3 * i8Psi4s94N4 x + x ^ 4 * i8Psi4s94dN4 x)) * x ^ 2 - (i8Psi4s94N0 x +
    x * i8Psi4s94N1 x + x ^ 2 * i8Psi4s94N2 x + x ^ 3 * i8Psi4s94N3 x +
    x ^ 4 * i8Psi4s94N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s94dW x

theorem hasDerivAt_i8Psi4s94 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s94 (i8Psi4s94D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s94N0 hx).add (X.mul (hasDerivAt_i8Psi4s94N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s94N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s94N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s94N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s94W hx)
  unfold i8Psi4s94
  refine e.congr_deriv ?_
  unfold i8Psi4s94D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 94 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s94 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 -
    x) * ((-2) * hpl [negOne, zero, zero] x)) * (x / (1 - x))

/-- `p₄⁽94⁾` written over words. -/
noncomputable def i8P4w94 (x : ℝ) : ℝ :=
    (-12 - 12 * x) * hpl [negOne, zero, zero, zero] x +
    (-4 - 4 * x) * hpl [zero, negOne, zero, zero] x

theorem i8P4s94_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s94 x = i8P4w94 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s94 i8P4w94
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [negOne, zero, zero] [zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((-4 - 4 * x)) * e0
  field_simp
  generalize hpl [negOne, zero, zero, zero] x = v0 at *
  generalize hpl [zero, negOne, zero, zero] x = v1 at *
  generalize hpl [negOne, zero, zero] x = v2 at *
  generalize hpl [zero] x = v3 at *
  ring

/-- **`(Ψ₄⁽94⁾)'(ξ) ξ' = p₄⁽94⁾`**, in terms of `ξ`. -/
theorem i8Psi4s94D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s94D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s94 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s94_eq_w hx]
  unfold i8Psi4s94D i8Psi4s94N0 i8Psi4s94N1 i8Psi4s94N2 i8Psi4s94N3 i8Psi4s94N4 i8Psi4s94dN0
    i8Psi4s94dN1 i8Psi4s94dN2 i8Psi4s94dN3 i8Psi4s94dN4 i8Psi4s94dW i8P4w94
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, zero, zero] x = v1 at *
  generalize hpl [negOne, zero, zero, zero] x = v2 at *
  generalize hpl [zero, negOne, zero, zero] x = v3 at *
  generalize hpl [zero, zero, zero, zero] x = v4 at *
  generalize hpl [negOne, zero, zero] x = v5 at *
  generalize hpl [zero, zero, zero] x = v6 at *
  generalize hpl [zero, zero] x = v7 at *
  generalize hpl [zero] x = v8 at *
  ring

/-- The part of `ξ² Ψ₄⁽95⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s95N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s95N0`. -/
noncomputable def i8Psi4s95dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s95N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s95N0 (i8Psi4s95dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽95⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s95N1 (x : ℝ) : ℝ :=
    (-8) * hpl [negOne, zero] x +
    (-16) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s95N1`. -/
noncomputable def i8Psi4s95dN1 (x : ℝ) : ℝ :=
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s95N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s95N1 (i8Psi4s95dN1 x) x := by
  unfold i8Psi4s95N1 i8Psi4s95dN1
  exact ((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽95⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s95N2 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne, zero] x +
    (8) * hpl [zero, zero] x +
    (-24) * hpl [negOne, zero, zero] x

/-- The derivative of `i8Psi4s95N2`. -/
noncomputable def i8Psi4s95dN2 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s95N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s95N2 (i8Psi4s95dN2 x) x := by
  unfold i8Psi4s95N2 i8Psi4s95dN2
  exact ((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽95⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s95N3 (x : ℝ) : ℝ :=
    (14) +
    (-14) * hpl [zero] x +
    (8) * hpl [negOne, zero] x +
    (8) * hpl [zero, zero] x +
    (-16) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s95N3`. -/
noncomputable def i8Psi4s95dN3 (x : ℝ) : ℝ :=
    0 +
    (-14) * (zero.kernel x * hpl [] x) +
    (8) * (negOne.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s95N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s95N3 (i8Psi4s95dN3 x) x := by
  unfold i8Psi4s95N3 i8Psi4s95dN3
  exact ((((((hasDerivAt_const x (14)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽95⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s95N4 (x : ℝ) : ℝ :=
    (3 / 2) +
    (-3) * hpl [zero] x +
    (2) * hpl [negOne, zero] x +
    (4) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s95N4`. -/
noncomputable def i8Psi4s95dN4 (x : ℝ) : ℝ :=
    0 +
    (-3) * (zero.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s95N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s95N4 (i8Psi4s95dN4 x) x := by
  unfold i8Psi4s95N4 i8Psi4s95dN4
  exact ((((((hasDerivAt_const x (3 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽95⁾` with constant coefficients. -/
noncomputable def i8Psi4s95W (x : ℝ) : ℝ :=
    (16) * hpl [zero, zero, zero] x +
    (16) * hpl [zero, negOne, zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s95W`. -/
noncomputable def i8Psi4s95dW (x : ℝ) : ℝ :=
    (16) * (zero.kernel x * hpl [zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s95W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s95W (i8Psi4s95dW x) x := by
  unfold i8Psi4s95W i8Psi4s95dW
  exact ((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (8)))

/-- The piece `Ψ₄⁽95⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s95 (x : ℝ) : ℝ :=
  (i8Psi4s95N0 x + x * i8Psi4s95N1 x + x ^ 2 * i8Psi4s95N2 x + x ^ 3 * i8Psi4s95N3 x +
    x ^ 4 * i8Psi4s95N4 x) / x ^ 2 + i8Psi4s95W x

/-- The derivative of `Ψ₄⁽95⁾`. -/
noncomputable def i8Psi4s95D (x : ℝ) : ℝ :=
  ((i8Psi4s95dN0 x + (i8Psi4s95N1 x + x * i8Psi4s95dN1 x) + (2 * x * i8Psi4s95N2 x +
    x ^ 2 * i8Psi4s95dN2 x) + (3 * x ^ 2 * i8Psi4s95N3 x + x ^ 3 * i8Psi4s95dN3 x) +
    (4 * x ^ 3 * i8Psi4s95N4 x + x ^ 4 * i8Psi4s95dN4 x)) * x ^ 2 - (i8Psi4s95N0 x +
    x * i8Psi4s95N1 x + x ^ 2 * i8Psi4s95N2 x + x ^ 3 * i8Psi4s95N3 x +
    x ^ 4 * i8Psi4s95N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s95dW x

theorem hasDerivAt_i8Psi4s95 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s95 (i8Psi4s95D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s95N0 hx).add (X.mul (hasDerivAt_i8Psi4s95N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s95N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s95N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s95N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s95W hx)
  unfold i8Psi4s95
  refine e.congr_deriv ?_
  unfold i8Psi4s95D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 95 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s95 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 -
    x) * ((-4) * hpl [negOne, zero] x)) * (x / (1 - x))

/-- `p₄⁽95⁾` written over words. -/
noncomputable def i8P4w95 (x : ℝ) : ℝ :=
    (-16 - 16 * x) * hpl [negOne, zero, zero] x +
    (-8 - 8 * x) * hpl [zero, negOne, zero] x

theorem i8P4s95_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s95 x = i8P4w95 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s95 i8P4w95
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [negOne, zero] [zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((-8 - 8 * x)) * e0
  field_simp
  generalize hpl [negOne, zero, zero] x = v0 at *
  generalize hpl [zero, negOne, zero] x = v1 at *
  generalize hpl [negOne, zero] x = v2 at *
  generalize hpl [zero] x = v3 at *
  ring

/-- **`(Ψ₄⁽95⁾)'(ξ) ξ' = p₄⁽95⁾`**, in terms of `ξ`. -/
theorem i8Psi4s95D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s95D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s95 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s95_eq_w hx]
  unfold i8Psi4s95D i8Psi4s95N0 i8Psi4s95N1 i8Psi4s95N2 i8Psi4s95N3 i8Psi4s95N4 i8Psi4s95dN0
    i8Psi4s95dN1 i8Psi4s95dN2 i8Psi4s95dN3 i8Psi4s95dN4 i8Psi4s95dW i8P4w95
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, zero, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, zero] x = v1 at *
  generalize hpl [negOne, zero, zero] x = v2 at *
  generalize hpl [zero, negOne, zero] x = v3 at *
  generalize hpl [zero, zero, zero] x = v4 at *
  generalize hpl [negOne, zero] x = v5 at *
  generalize hpl [zero, zero] x = v6 at *
  generalize hpl [zero] x = v7 at *
  ring

/-- The part of `ξ² Ψ₄⁽96⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s96N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s96N0`. -/
noncomputable def i8Psi4s96dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s96N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s96N0 (i8Psi4s96dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽96⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s96N1 (x : ℝ) : ℝ :=
    (12) +
    (12) * hpl [zero] x +
    (12) * hpl [zero, zero] x +
    (12) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s96N1`. -/
noncomputable def i8Psi4s96dN1 (x : ℝ) : ℝ :=
    0 +
    (12) * (zero.kernel x * hpl [] x) +
    (12) * (zero.kernel x * hpl [zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s96N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s96N1 (i8Psi4s96dN1 x) x := by
  unfold i8Psi4s96N1 i8Psi4s96dN1
  exact ((((hasDerivAt_const x (12)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽96⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s96N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s96N2`. -/
noncomputable def i8Psi4s96dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s96N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s96N2 (i8Psi4s96dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽96⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s96N3 (x : ℝ) : ℝ :=
    (-12) +
    (12) * hpl [zero] x +
    (-12) * hpl [zero, zero] x +
    (12) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s96N3`. -/
noncomputable def i8Psi4s96dN3 (x : ℝ) : ℝ :=
    0 +
    (12) * (zero.kernel x * hpl [] x) +
    (-12) * (zero.kernel x * hpl [zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s96N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s96N3 (i8Psi4s96dN3 x) x := by
  unfold i8Psi4s96N3 i8Psi4s96dN3
  exact ((((hasDerivAt_const x (-12)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽96⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s96N4 (x : ℝ) : ℝ :=
    (-3 / 4) +
    (3 / 2) * hpl [zero] x +
    (-3) * hpl [zero, zero] x +
    (6) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s96N4`. -/
noncomputable def i8Psi4s96dN4 (x : ℝ) : ℝ :=
    0 +
    (3 / 2) * (zero.kernel x * hpl [] x) +
    (-3) * (zero.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s96N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s96N4 (i8Psi4s96dN4 x) x := by
  unfold i8Psi4s96N4 i8Psi4s96dN4
  exact ((((hasDerivAt_const x (-3 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6)))

/-- The part of `Ψ₄⁽96⁾` with constant coefficients. -/
noncomputable def i8Psi4s96W (x : ℝ) : ℝ :=
    (-12) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s96W`. -/
noncomputable def i8Psi4s96dW (x : ℝ) : ℝ :=
    (-12) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s96W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s96W (i8Psi4s96dW x) x := by
  unfold i8Psi4s96W i8Psi4s96dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-12))

/-- The piece `Ψ₄⁽96⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s96 (x : ℝ) : ℝ :=
  (i8Psi4s96N0 x + x * i8Psi4s96N1 x + x ^ 2 * i8Psi4s96N2 x + x ^ 3 * i8Psi4s96N3 x +
    x ^ 4 * i8Psi4s96N4 x) / x ^ 2 + i8Psi4s96W x

/-- The derivative of `Ψ₄⁽96⁾`. -/
noncomputable def i8Psi4s96D (x : ℝ) : ℝ :=
  ((i8Psi4s96dN0 x + (i8Psi4s96N1 x + x * i8Psi4s96dN1 x) + (2 * x * i8Psi4s96N2 x +
    x ^ 2 * i8Psi4s96dN2 x) + (3 * x ^ 2 * i8Psi4s96N3 x + x ^ 3 * i8Psi4s96dN3 x) +
    (4 * x ^ 3 * i8Psi4s96N4 x + x ^ 4 * i8Psi4s96dN4 x)) * x ^ 2 - (i8Psi4s96N0 x +
    x * i8Psi4s96N1 x + x ^ 2 * i8Psi4s96N2 x + x ^ 3 * i8Psi4s96N3 x +
    x ^ 4 * i8Psi4s96N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s96dW x

theorem hasDerivAt_i8Psi4s96 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s96 (i8Psi4s96D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s96N0 hx).add (X.mul (hasDerivAt_i8Psi4s96N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s96N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s96N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s96N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s96W hx)
  unfold i8Psi4s96
  refine e.congr_deriv ?_
  unfold i8Psi4s96D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 96 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s96 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 - x) * (2 * hpl [zero, zero] x)) * (x / (1 - x))

/-- `p₄⁽96⁾` written over words. -/
noncomputable def i8P4w96 (x : ℝ) : ℝ :=
    (12 + 12 * x) * hpl [zero, zero, zero] x

theorem i8P4s96_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s96 x = i8P4w96 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s96 i8P4w96
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero, zero] [zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((4 + 4 * x)) * e0
  field_simp
  generalize hpl [zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero] x = v1 at *
  generalize hpl [zero] x = v2 at *
  ring

/-- **`(Ψ₄⁽96⁾)'(ξ) ξ' = p₄⁽96⁾`**, in terms of `ξ`. -/
theorem i8Psi4s96D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s96D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s96 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s96_eq_w hx]
  unfold i8Psi4s96D i8Psi4s96N0 i8Psi4s96N1 i8Psi4s96N2 i8Psi4s96N3 i8Psi4s96N4 i8Psi4s96dN0
    i8Psi4s96dN1 i8Psi4s96dN2 i8Psi4s96dN3 i8Psi4s96dN4 i8Psi4s96dW i8P4w96
  simp only [kernel_zero, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero] x = v1 at *
  generalize hpl [zero, zero] x = v2 at *
  generalize hpl [zero] x = v3 at *
  ring

/-- The part of `ξ² Ψ₄⁽97⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s97N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s97N0`. -/
noncomputable def i8Psi4s97dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s97N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s97N0 (i8Psi4s97dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽97⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s97N1 (x : ℝ) : ℝ :=
    (32 - 8 * zeta3 - 4 / 3 * π ^ 2) * hpl [one] x

/-- The derivative of `i8Psi4s97N1`. -/
noncomputable def i8Psi4s97dN1 (x : ℝ) : ℝ :=
    (32 - 8 * zeta3 - 4 / 3 * π ^ 2) * (one.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s97N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s97N1 (i8Psi4s97dN1 x) x := by
  unfold i8Psi4s97N1 i8Psi4s97dN1
  exact ((hasDerivAt_hpl_cons one [] hx).const_mul (32 - 8 * zeta3 - 4 / 3 * π ^ 2))

/-- The part of `ξ² Ψ₄⁽97⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s97N2 (x : ℝ) : ℝ :=
    (-48 + 20 * zeta3 + 10 / 3 * π ^ 2) * hpl [one] x

/-- The derivative of `i8Psi4s97N2`. -/
noncomputable def i8Psi4s97dN2 (x : ℝ) : ℝ :=
    (-48 + 20 * zeta3 + 10 / 3 * π ^ 2) * (one.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s97N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s97N2 (i8Psi4s97dN2 x) x := by
  unfold i8Psi4s97N2 i8Psi4s97dN2
  exact ((hasDerivAt_hpl_cons one [] hx).const_mul (-48 + 20 * zeta3 + 10 / 3 * π ^ 2))

/-- The part of `ξ² Ψ₄⁽97⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s97N3 (x : ℝ) : ℝ :=
    (16 - 12 * zeta3 - 2 * π ^ 2) +
    (32 - 8 * zeta3 - 4 / 3 * π ^ 2) * hpl [one] x

/-- The derivative of `i8Psi4s97N3`. -/
noncomputable def i8Psi4s97dN3 (x : ℝ) : ℝ :=
    0 +
    (32 - 8 * zeta3 - 4 / 3 * π ^ 2) * (one.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s97N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s97N3 (i8Psi4s97dN3 x) x := by
  unfold i8Psi4s97N3 i8Psi4s97dN3
  exact ((hasDerivAt_const x (16 - 12 * zeta3 - 2 * π ^ 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (32 - 8 * zeta3 - 4 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽97⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s97N4 (x : ℝ) : ℝ :=
    (-8 - 2 * zeta3 - π ^ 2 / 3) +
    (-16 - 4 * zeta3 - 2 / 3 * π ^ 2) * hpl [one] x

/-- The derivative of `i8Psi4s97N4`. -/
noncomputable def i8Psi4s97dN4 (x : ℝ) : ℝ :=
    0 +
    (-16 - 4 * zeta3 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s97N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s97N4 (i8Psi4s97dN4 x) x := by
  unfold i8Psi4s97N4 i8Psi4s97dN4
  exact ((hasDerivAt_const x (-8 - 2 * zeta3 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-16 - 4 * zeta3 - 2 / 3 * π ^ 2)))

/-- The part of `Ψ₄⁽97⁾` with constant coefficients. -/
noncomputable def i8Psi4s97W (x : ℝ) : ℝ :=
    (-32 + 8 * zeta3 + 4 / 3 * π ^ 2) * hpl [zero] x +
    (32 + 8 * zeta3 + 4 / 3 * π ^ 2) * hpl [zero, one] x

/-- The derivative of `i8Psi4s97W`. -/
noncomputable def i8Psi4s97dW (x : ℝ) : ℝ :=
    (-32 + 8 * zeta3 + 4 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (32 + 8 * zeta3 + 4 / 3 * π ^ 2) * (zero.kernel x * hpl [one] x)

theorem hasDerivAt_i8Psi4s97W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s97W (i8Psi4s97dW x) x := by
  unfold i8Psi4s97W i8Psi4s97dW
  exact (((hasDerivAt_hpl_cons zero [] hx).const_mul (-32 + 8 * zeta3 + 4 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (32 + 8 * zeta3 + 4 / 3 * π ^ 2)))

/-- The piece `Ψ₄⁽97⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s97 (x : ℝ) : ℝ :=
  (i8Psi4s97N0 x + x * i8Psi4s97N1 x + x ^ 2 * i8Psi4s97N2 x + x ^ 3 * i8Psi4s97N3 x +
    x ^ 4 * i8Psi4s97N4 x) / x ^ 2 + i8Psi4s97W x

/-- The derivative of `Ψ₄⁽97⁾`. -/
noncomputable def i8Psi4s97D (x : ℝ) : ℝ :=
  ((i8Psi4s97dN0 x + (i8Psi4s97N1 x + x * i8Psi4s97dN1 x) + (2 * x * i8Psi4s97N2 x +
    x ^ 2 * i8Psi4s97dN2 x) + (3 * x ^ 2 * i8Psi4s97N3 x + x ^ 3 * i8Psi4s97dN3 x) +
    (4 * x ^ 3 * i8Psi4s97N4 x + x ^ 4 * i8Psi4s97dN4 x)) * x ^ 2 - (i8Psi4s97N0 x +
    x * i8Psi4s97N1 x + x ^ 2 * i8Psi4s97N2 x + x ^ 3 * i8Psi4s97N3 x +
    x ^ 4 * i8Psi4s97N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s97dW x

theorem hasDerivAt_i8Psi4s97 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s97 (i8Psi4s97D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s97N0 hx).add (X.mul (hasDerivAt_i8Psi4s97N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s97N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s97N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s97N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s97W hx)
  unfold i8Psi4s97
  refine e.congr_deriv ?_
  unfold i8Psi4s97D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 97 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s97 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 - x) * ((24 + ((-1) * π ^ 2) +
    ((-24) * x) + ((-6) * zeta3) + ((-1) * π ^ 2 * x) + ((-6) * x * zeta3)) / (3 +
    (3 * x)))) * (x / (1 - x)))

/-- `p₄⁽97⁾` written over words. -/
noncomputable def i8P4w97 (x : ℝ) : ℝ :=
    (32 - 32 * x - 8 * zeta3 - 4 / 3 * π ^ 2 - 8 * x * zeta3 - 4 / 3 * π ^ 2 * x) * hpl [one] x

theorem i8P4s97_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s97 x = i8P4w97 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s97 i8P4w97
  rw [i13_log_one_sub_eq hx]
  field_simp
  generalize hpl [one] x = v0 at *
  ring

/-- **`(Ψ₄⁽97⁾)'(ξ) ξ' = p₄⁽97⁾`**, in terms of `ξ`. -/
theorem i8Psi4s97D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s97D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s97 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s97_eq_w hx]
  unfold i8Psi4s97D i8Psi4s97N0 i8Psi4s97N1 i8Psi4s97N2 i8Psi4s97N3 i8Psi4s97N4 i8Psi4s97dN0
    i8Psi4s97dN1 i8Psi4s97dN2 i8Psi4s97dN3 i8Psi4s97dN4 i8Psi4s97dW i8P4w97
  simp only [kernel_zero, kernel_one, hpl_nil]
  field_simp
  generalize hpl [zero, one] x = v0 at *
  generalize hpl [zero] x = v1 at *
  generalize hpl [one] x = v2 at *
  ring

/-- The part of `ξ² Ψ₄⁽98⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s98N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s98N0`. -/
noncomputable def i8Psi4s98dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s98N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s98N0 (i8Psi4s98dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽98⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s98N1 (x : ℝ) : ℝ :=
    (16 - 2 / 3 * π ^ 2) * hpl [one] x +
    (16 - 2 / 3 * π ^ 2) * hpl [zero, one] x +
    (16 - 2 / 3 * π ^ 2) * hpl [one, zero] x

/-- The derivative of `i8Psi4s98N1`. -/
noncomputable def i8Psi4s98dN1 (x : ℝ) : ℝ :=
    (16 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (16 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [one] x) +
    (16 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s98N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s98N1 (i8Psi4s98dN1 x) x := by
  unfold i8Psi4s98N1 i8Psi4s98dN1
  exact ((((hasDerivAt_hpl_cons one [] hx).const_mul (16 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (16 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (16 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽98⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s98N2 (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * hpl [zero] x +
    (4 - π ^ 2 / 6) * hpl [one] x +
    (-40 + 5 / 3 * π ^ 2) * hpl [one, zero] x

/-- The derivative of `i8Psi4s98N2`. -/
noncomputable def i8Psi4s98dN2 (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (4 - π ^ 2 / 6) * (one.kernel x * hpl [] x) +
    (-40 + 5 / 3 * π ^ 2) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s98N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s98N2 (i8Psi4s98dN2 x) x := by
  unfold i8Psi4s98N2 i8Psi4s98dN2
  exact ((((hasDerivAt_hpl_cons zero [] hx).const_mul (-16 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-40 + 5 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽98⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s98N3 (x : ℝ) : ℝ :=
    (-44 + 11 / 6 * π ^ 2) +
    (24 - π ^ 2) * hpl [zero] x +
    (-16 + 2 / 3 * π ^ 2) * hpl [one] x +
    (16 - 2 / 3 * π ^ 2) * hpl [zero, one] x +
    (16 - 2 / 3 * π ^ 2) * hpl [one, zero] x

/-- The derivative of `i8Psi4s98N3`. -/
noncomputable def i8Psi4s98dN3 (x : ℝ) : ℝ :=
    0 +
    (24 - π ^ 2) * (zero.kernel x * hpl [] x) +
    (-16 + 2 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (16 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [one] x) +
    (16 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s98N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s98N3 (i8Psi4s98dN3 x) x := by
  unfold i8Psi4s98N3 i8Psi4s98dN3
  exact (((((hasDerivAt_const x (-44 + 11 / 6 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (24 - π ^ 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-16 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (16 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (16 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽98⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s98N4 (x : ℝ) : ℝ :=
    (-4 + π ^ 2 / 6) +
    (4 - π ^ 2 / 6) * hpl [zero] x +
    (-4 + π ^ 2 / 6) * hpl [one] x +
    (8 - π ^ 2 / 3) * hpl [zero, one] x +
    (8 - π ^ 2 / 3) * hpl [one, zero] x

/-- The derivative of `i8Psi4s98N4`. -/
noncomputable def i8Psi4s98dN4 (x : ℝ) : ℝ :=
    0 +
    (4 - π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (-4 + π ^ 2 / 6) * (one.kernel x * hpl [] x) +
    (8 - π ^ 2 / 3) * (zero.kernel x * hpl [one] x) +
    (8 - π ^ 2 / 3) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s98N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s98N4 (i8Psi4s98dN4 x) x := by
  unfold i8Psi4s98N4 i8Psi4s98dN4
  exact (((((hasDerivAt_const x (-4 + π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (8 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (8 - π ^ 2 / 3)))

/-- The part of `Ψ₄⁽98⁾` with constant coefficients. -/
noncomputable def i8Psi4s98W (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, zero, one] x +
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s98W`. -/
noncomputable def i8Psi4s98dW (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (-16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero, one] x) +
    (-16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s98W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s98W (i8Psi4s98dW x) x := by
  unfold i8Psi4s98W i8Psi4s98dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-16 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-16 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-16 + 2 / 3 * π ^ 2)))

/-- The piece `Ψ₄⁽98⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s98 (x : ℝ) : ℝ :=
  (i8Psi4s98N0 x + x * i8Psi4s98N1 x + x ^ 2 * i8Psi4s98N2 x + x ^ 3 * i8Psi4s98N3 x +
    x ^ 4 * i8Psi4s98N4 x) / x ^ 2 + i8Psi4s98W x

/-- The derivative of `Ψ₄⁽98⁾`. -/
noncomputable def i8Psi4s98D (x : ℝ) : ℝ :=
  ((i8Psi4s98dN0 x + (i8Psi4s98N1 x + x * i8Psi4s98dN1 x) + (2 * x * i8Psi4s98N2 x +
    x ^ 2 * i8Psi4s98dN2 x) + (3 * x ^ 2 * i8Psi4s98N3 x + x ^ 3 * i8Psi4s98dN3 x) +
    (4 * x ^ 3 * i8Psi4s98N4 x + x ^ 4 * i8Psi4s98dN4 x)) * x ^ 2 - (i8Psi4s98N0 x +
    x * i8Psi4s98N1 x + x ^ 2 * i8Psi4s98N2 x + x ^ 3 * i8Psi4s98N3 x +
    x ^ 4 * i8Psi4s98N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s98dW x

theorem hasDerivAt_i8Psi4s98 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s98 (i8Psi4s98D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s98N0 hx).add (X.mul (hasDerivAt_i8Psi4s98N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s98N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s98N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s98N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s98W hx)
  unfold i8Psi4s98
  refine e.congr_deriv ?_
  unfold i8Psi4s98D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 98 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s98 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 - x) * (((24 +
    ((-1) * π ^ 2)) / 6) * hpl [zero] x)) * (x / (1 - x)))

/-- `p₄⁽98⁾` written over words. -/
noncomputable def i8P4w98 (x : ℝ) : ℝ :=
    (16 + 16 * x - 2 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x) * hpl [zero, one] x +
    (16 + 16 * x - 2 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x) * hpl [one, zero] x

theorem i8P4s98_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s98 x = i8P4w98 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s98 i8P4w98
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [zero] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((16 + 16 * x - 2 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x)) * e0
  field_simp
  generalize hpl [zero, one] x = v0 at *
  generalize hpl [one, zero] x = v1 at *
  generalize hpl [zero] x = v2 at *
  generalize hpl [one] x = v3 at *
  ring

/-- **`(Ψ₄⁽98⁾)'(ξ) ξ' = p₄⁽98⁾`**, in terms of `ξ`. -/
theorem i8Psi4s98D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s98D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s98 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s98_eq_w hx]
  unfold i8Psi4s98D i8Psi4s98N0 i8Psi4s98N1 i8Psi4s98N2 i8Psi4s98N3 i8Psi4s98N4 i8Psi4s98dN0
    i8Psi4s98dN1 i8Psi4s98dN2 i8Psi4s98dN3 i8Psi4s98dN4 i8Psi4s98dW i8P4w98
  simp only [kernel_zero, kernel_one, hpl_nil]
  field_simp
  generalize hpl [zero, zero, one] x = v0 at *
  generalize hpl [zero, one, zero] x = v1 at *
  generalize hpl [zero, zero] x = v2 at *
  generalize hpl [zero, one] x = v3 at *
  generalize hpl [one, zero] x = v4 at *
  generalize hpl [zero] x = v5 at *
  generalize hpl [one] x = v6 at *
  ring

end QED.ThreeLoopD
