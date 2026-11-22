/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P24

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 99 to 102

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s99`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s99D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s99`, `QED.ThreeLoopD.i8Psi4s99D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽99⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s99N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s99N0`. -/
noncomputable def i8Psi4s99dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s99N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s99N0 (i8Psi4s99dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽99⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s99N1 (x : ℝ) : ℝ :=
    (4 / 3 * π ^ 2) * hpl [negOne, one] x +
    (4 / 3 * π ^ 2) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s99N1`. -/
noncomputable def i8Psi4s99dN1 (x : ℝ) : ℝ :=
    (4 / 3 * π ^ 2) * (negOne.kernel x * hpl [one] x) +
    (4 / 3 * π ^ 2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s99N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s99N1 (i8Psi4s99dN1 x) x := by
  unfold i8Psi4s99N1 i8Psi4s99dN1
  exact (((hasDerivAt_hpl_cons negOne [one] hx).const_mul (4 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (4 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽99⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s99N2 (x : ℝ) : ℝ :=
    (5 / 3 * π ^ 2) * hpl [negOne] x +
    (π ^ 2) * hpl [one] x +
    (2 * π ^ 2) * hpl [negOne, one] x +
    (-10 / 3 * π ^ 2) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s99N2`. -/
noncomputable def i8Psi4s99dN2 (x : ℝ) : ℝ :=
    (5 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (π ^ 2) * (one.kernel x * hpl [] x) +
    (2 * π ^ 2) * (negOne.kernel x * hpl [one] x) +
    (-10 / 3 * π ^ 2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s99N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s99N2 (i8Psi4s99dN2 x) x := by
  unfold i8Psi4s99N2 i8Psi4s99dN2
  exact (((((hasDerivAt_hpl_cons negOne [] hx).const_mul (5 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-10 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽99⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s99N3 (x : ℝ) : ℝ :=
    (-8 / 3 * π ^ 2) +
    (2 * π ^ 2) * hpl [negOne] x +
    (-2 / 3 * π ^ 2) * hpl [one] x +
    (4 / 3 * π ^ 2) * hpl [negOne, one] x +
    (4 / 3 * π ^ 2) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s99N3`. -/
noncomputable def i8Psi4s99dN3 (x : ℝ) : ℝ :=
    0 +
    (2 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-2 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (4 / 3 * π ^ 2) * (negOne.kernel x * hpl [one] x) +
    (4 / 3 * π ^ 2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s99N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s99N3 (i8Psi4s99dN3 x) x := by
  unfold i8Psi4s99N3 i8Psi4s99dN3
  exact (((((hasDerivAt_const x (-8 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (4 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽99⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s99N4 (x : ℝ) : ℝ :=
    (-π ^ 2 / 3) +
    (π ^ 2 / 3) * hpl [negOne] x +
    (-π ^ 2 / 3) * hpl [one] x +
    (2 / 3 * π ^ 2) * hpl [negOne, one] x +
    (2 / 3 * π ^ 2) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s99N4`. -/
noncomputable def i8Psi4s99dN4 (x : ℝ) : ℝ :=
    0 +
    (π ^ 2 / 3) * (negOne.kernel x * hpl [] x) +
    (-π ^ 2 / 3) * (one.kernel x * hpl [] x) +
    (2 / 3 * π ^ 2) * (negOne.kernel x * hpl [one] x) +
    (2 / 3 * π ^ 2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s99N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s99N4 (i8Psi4s99dN4 x) x := by
  unfold i8Psi4s99N4 i8Psi4s99dN4
  exact (((((hasDerivAt_const x (-π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2 / 3 * π ^ 2)))

/-- The part of `Ψ₄⁽99⁾` with constant coefficients. -/
noncomputable def i8Psi4s99W (x : ℝ) : ℝ :=
    (-4 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (-4 / 3 * π ^ 2) * hpl [zero, one] x +
    (-4 / 3 * π ^ 2) * hpl [zero, negOne, one] x +
    (-4 / 3 * π ^ 2) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi4s99W`. -/
noncomputable def i8Psi4s99dW (x : ℝ) : ℝ :=
    (-4 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (-4 / 3 * π ^ 2) * (zero.kernel x * hpl [one] x) +
    (-4 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne, one] x) +
    (-4 / 3 * π ^ 2) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s99W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s99W (i8Psi4s99dW x) x := by
  unfold i8Psi4s99W i8Psi4s99dW
  exact (((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-4 / 3 * π ^ 2)))

/-- The piece `Ψ₄⁽99⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s99 (x : ℝ) : ℝ :=
  (i8Psi4s99N0 x + x * i8Psi4s99N1 x + x ^ 2 * i8Psi4s99N2 x + x ^ 3 * i8Psi4s99N3 x +
    x ^ 4 * i8Psi4s99N4 x) / x ^ 2 + i8Psi4s99W x

/-- The derivative of `Ψ₄⁽99⁾`. -/
noncomputable def i8Psi4s99D (x : ℝ) : ℝ :=
  ((i8Psi4s99dN0 x + (i8Psi4s99N1 x + x * i8Psi4s99dN1 x) + (2 * x * i8Psi4s99N2 x +
    x ^ 2 * i8Psi4s99dN2 x) + (3 * x ^ 2 * i8Psi4s99N3 x + x ^ 3 * i8Psi4s99dN3 x) +
    (4 * x ^ 3 * i8Psi4s99N4 x + x ^ 4 * i8Psi4s99dN4 x)) * x ^ 2 - (i8Psi4s99N0 x +
    x * i8Psi4s99N1 x + x ^ 2 * i8Psi4s99N2 x + x ^ 3 * i8Psi4s99N3 x +
    x ^ 4 * i8Psi4s99N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s99dW x

theorem hasDerivAt_i8Psi4s99 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s99 (i8Psi4s99D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s99N0 hx).add (X.mul (hasDerivAt_i8Psi4s99N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s99N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s99N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s99N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s99W hx)
  unfold i8Psi4s99
  refine e.congr_deriv ?_
  unfold i8Psi4s99D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 99 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s99 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 -
    x) * ((π ^ 2 / 3) * hpl [negOne] x)) * (x / (1 - x)))

/-- `p₄⁽99⁾` written over words. -/
noncomputable def i8P4w99 (x : ℝ) : ℝ :=
    (4 / 3 * π ^ 2 + 4 / 3 * π ^ 2 * x) * hpl [negOne, one] x +
    (4 / 3 * π ^ 2 + 4 / 3 * π ^ 2 * x) * hpl [one, negOne] x

theorem i8P4s99_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s99 x = i8P4w99 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s99 i8P4w99
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [negOne] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((4 / 3 * π ^ 2 + 4 / 3 * π ^ 2 * x)) * e0
  field_simp
  generalize hpl [negOne, one] x = v0 at *
  generalize hpl [one, negOne] x = v1 at *
  generalize hpl [negOne] x = v2 at *
  generalize hpl [one] x = v3 at *
  ring

/-- **`(Ψ₄⁽99⁾)'(ξ) ξ' = p₄⁽99⁾`**, in terms of `ξ`. -/
theorem i8Psi4s99D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s99D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s99 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s99_eq_w hx]
  unfold i8Psi4s99D i8Psi4s99N0 i8Psi4s99N1 i8Psi4s99N2 i8Psi4s99N3 i8Psi4s99N4 i8Psi4s99dN0
    i8Psi4s99dN1 i8Psi4s99dN2 i8Psi4s99dN3 i8Psi4s99dN4 i8Psi4s99dW i8P4w99
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, one] x = v0 at *
  generalize hpl [zero, one, negOne] x = v1 at *
  generalize hpl [negOne, one] x = v2 at *
  generalize hpl [zero, negOne] x = v3 at *
  generalize hpl [zero, one] x = v4 at *
  generalize hpl [one, negOne] x = v5 at *
  generalize hpl [negOne] x = v6 at *
  generalize hpl [one] x = v7 at *
  ring

/-- The part of `ξ² Ψ₄⁽100⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s100N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s100N0`. -/
noncomputable def i8Psi4s100dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s100N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s100N0 (i8Psi4s100dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽100⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s100N1 (x : ℝ) : ℝ :=
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (-8) * hpl [one, negOne, zero] x +
    (-8) * hpl [zero, negOne, zero, one] x +
    (-8) * hpl [zero, negOne, one, zero] x +
    (-8) * hpl [zero, one, negOne, zero] x +
    (-8) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s100N1`. -/
noncomputable def i8Psi4s100dN1 (x : ℝ) : ℝ :=
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (-8) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s100N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s100N1 (i8Psi4s100dN1 x) x := by
  unfold i8Psi4s100N1 i8Psi4s100dN1
  exact ((((((((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽100⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s100N2 (x : ℝ) : ℝ :=
    (-13 / 2) * hpl [one] x +
    (20) * hpl [negOne, zero] x +
    (7) * hpl [one, zero] x +
    (-2) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, one, zero] x +
    (8) * hpl [zero, negOne, zero] x +
    (-2) * hpl [one, negOne, zero] x +
    (20) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s100N2`. -/
noncomputable def i8Psi4s100dN2 (x : ℝ) : ℝ :=
    (-13 / 2) * (one.kernel x * hpl [] x) +
    (20) * (negOne.kernel x * hpl [zero] x) +
    (7) * (one.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (20) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s100N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s100N2 (i8Psi4s100dN2 x) x := by
  unfold i8Psi4s100N2 i8Psi4s100dN2
  exact (((((((((hasDerivAt_hpl_cons one [] hx).const_mul (-13 / 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (20)))

/-- The part of `ξ² Ψ₄⁽100⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s100N3 (x : ℝ) : ℝ :=
    (67 / 2) +
    (-27) * hpl [zero] x +
    (6) * hpl [one] x +
    (22) * hpl [negOne, zero] x +
    (-6) * hpl [zero, one] x +
    (-6) * hpl [one, zero] x +
    (8) * hpl [negOne, zero, one] x +
    (8) * hpl [negOne, one, zero] x +
    (-12) * hpl [zero, negOne, zero] x +
    (8) * hpl [one, negOne, zero] x +
    (-8) * hpl [zero, negOne, zero, one] x +
    (-8) * hpl [zero, negOne, one, zero] x +
    (-8) * hpl [zero, one, negOne, zero] x +
    (-8) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s100N3`. -/
noncomputable def i8Psi4s100dN3 (x : ℝ) : ℝ :=
    0 +
    (-27) * (zero.kernel x * hpl [] x) +
    (6) * (one.kernel x * hpl [] x) +
    (22) * (negOne.kernel x * hpl [zero] x) +
    (-6) * (zero.kernel x * hpl [one] x) +
    (-6) * (one.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [zero, one] x) +
    (8) * (negOne.kernel x * hpl [one, zero] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero] x) +
    (8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (-8) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s100N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s100N3 (i8Psi4s100dN3 x) x := by
  unfold i8Psi4s100N3 i8Psi4s100dN3
  exact ((((((((((((((hasDerivAt_const x (67 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-27))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (22))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽100⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s100N4 (x : ℝ) : ℝ :=
    (1) +
    (-3 / 2) * hpl [zero] x +
    (1 / 2) * hpl [one] x +
    (2) * hpl [negOne, zero] x +
    (-1) * hpl [zero, one] x +
    (-1) * hpl [one, zero] x +
    (2) * hpl [negOne, zero, one] x +
    (2) * hpl [negOne, one, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (2) * hpl [one, negOne, zero] x +
    (-4) * hpl [zero, negOne, zero, one] x +
    (-4) * hpl [zero, negOne, one, zero] x +
    (-4) * hpl [zero, one, negOne, zero] x +
    (-4) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s100N4`. -/
noncomputable def i8Psi4s100dN4 (x : ℝ) : ℝ :=
    0 +
    (-3 / 2) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (one.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [zero] x) +
    (2) * (negOne.kernel x * hpl [zero, one] x) +
    (2) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (one.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (-4) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-4) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-4) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s100N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s100N4 (i8Psi4s100dN4 x) x := by
  unfold i8Psi4s100N4 i8Psi4s100dN4
  exact ((((((((((((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽100⁾` with constant coefficients. -/
noncomputable def i8Psi4s100W (x : ℝ) : ℝ :=
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x +
    (8) * hpl [zero, zero, negOne, zero, one] x +
    (8) * hpl [zero, zero, negOne, one, zero] x +
    (8) * hpl [zero, zero, one, negOne, zero] x +
    (8) * hpl [zero, one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s100W`. -/
noncomputable def i8Psi4s100dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, zero, one] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, one, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [one, zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s100W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s100W (i8Psi4s100dW x) x := by
  unfold i8Psi4s100W i8Psi4s100dW
  exact ((((((((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne, zero] hx).const_mul (8)))

/-- The piece `Ψ₄⁽100⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s100 (x : ℝ) : ℝ :=
  (i8Psi4s100N0 x + x * i8Psi4s100N1 x + x ^ 2 * i8Psi4s100N2 x + x ^ 3 * i8Psi4s100N3 x +
    x ^ 4 * i8Psi4s100N4 x) / x ^ 2 + i8Psi4s100W x

/-- The derivative of `Ψ₄⁽100⁾`. -/
noncomputable def i8Psi4s100D (x : ℝ) : ℝ :=
  ((i8Psi4s100dN0 x + (i8Psi4s100N1 x + x * i8Psi4s100dN1 x) + (2 * x * i8Psi4s100N2 x +
    x ^ 2 * i8Psi4s100dN2 x) + (3 * x ^ 2 * i8Psi4s100N3 x + x ^ 3 * i8Psi4s100dN3 x) +
    (4 * x ^ 3 * i8Psi4s100N4 x + x ^ 4 * i8Psi4s100dN4 x)) * x ^ 2 - (i8Psi4s100N0 x +
    x * i8Psi4s100N1 x + x ^ 2 * i8Psi4s100N2 x + x ^ 3 * i8Psi4s100N3 x +
    x ^ 4 * i8Psi4s100N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s100dW x

theorem hasDerivAt_i8Psi4s100 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s100 (i8Psi4s100D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s100N0 hx).add (X.mul (hasDerivAt_i8Psi4s100N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s100N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s100N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s100N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s100W hx)
  unfold i8Psi4s100
  refine e.congr_deriv ?_
  unfold i8Psi4s100D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 100 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s100 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 -
    x) * ((-2) * hpl [zero, negOne, zero] x)) * (x / (1 - x)))

/-- `p₄⁽100⁾` written over words. -/
noncomputable def i8P4w100 (x : ℝ) : ℝ :=
    (-8 - 8 * x) * hpl [zero, negOne, zero, one] x +
    (-8 - 8 * x) * hpl [zero, negOne, one, zero] x +
    (-8 - 8 * x) * hpl [zero, one, negOne, zero] x +
    (-8 - 8 * x) * hpl [one, zero, negOne, zero] x

theorem i8P4s100_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s100 x = i8P4w100 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s100 i8P4w100
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [zero, negOne, zero] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((-8 - 8 * x)) * e0
  field_simp
  generalize hpl [zero, negOne, zero, one] x = v0 at *
  generalize hpl [zero, negOne, one, zero] x = v1 at *
  generalize hpl [zero, one, negOne, zero] x = v2 at *
  generalize hpl [one, zero, negOne, zero] x = v3 at *
  generalize hpl [zero, negOne, zero] x = v4 at *
  generalize hpl [one] x = v5 at *
  ring

/-- **`(Ψ₄⁽100⁾)'(ξ) ξ' = p₄⁽100⁾`**, in terms of `ξ`. -/
theorem i8Psi4s100D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s100D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s100 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s100_eq_w hx]
  unfold i8Psi4s100D i8Psi4s100N0 i8Psi4s100N1 i8Psi4s100N2 i8Psi4s100N3 i8Psi4s100N4 i8Psi4s100dN0
    i8Psi4s100dN1 i8Psi4s100dN2 i8Psi4s100dN3 i8Psi4s100dN4 i8Psi4s100dW i8P4w100
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, zero, negOne, zero, one] x = v0 at *
  generalize hpl [zero, zero, negOne, one, zero] x = v1 at *
  generalize hpl [zero, zero, one, negOne, zero] x = v2 at *
  generalize hpl [zero, one, zero, negOne, zero] x = v3 at *
  generalize hpl [zero, negOne, zero, one] x = v4 at *
  generalize hpl [zero, negOne, one, zero] x = v5 at *
  generalize hpl [zero, zero, negOne, zero] x = v6 at *
  generalize hpl [zero, one, negOne, zero] x = v7 at *
  generalize hpl [one, zero, negOne, zero] x = v8 at *
  generalize hpl [negOne, zero, one] x = v9 at *
  generalize hpl [negOne, one, zero] x = v10 at *
  generalize hpl [zero, negOne, zero] x = v11 at *
  generalize hpl [zero, zero, one] x = v12 at *
  generalize hpl [zero, one, zero] x = v13 at *
  generalize hpl [one, negOne, zero] x = v14 at *
  generalize hpl [negOne, zero] x = v15 at *
  generalize hpl [zero, one] x = v16 at *
  generalize hpl [one, zero] x = v17 at *
  generalize hpl [zero] x = v18 at *
  generalize hpl [one] x = v19 at *
  ring

/-- The part of `ξ² Ψ₄⁽101⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s101N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s101N0`. -/
noncomputable def i8Psi4s101dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s101N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s101N0 (i8Psi4s101dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽101⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s101N1 (x : ℝ) : ℝ :=
    (16) * hpl [negOne, negOne, zero, one] x +
    (16) * hpl [negOne, negOne, one, zero] x +
    (16) * hpl [negOne, one, negOne, zero] x +
    (16) * hpl [one, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s101N1`. -/
noncomputable def i8Psi4s101dN1 (x : ℝ) : ℝ :=
    (16) * (negOne.kernel x * hpl [negOne, zero, one] x) +
    (16) * (negOne.kernel x * hpl [negOne, one, zero] x) +
    (16) * (negOne.kernel x * hpl [one, negOne, zero] x) +
    (16) * (one.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s101N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s101N1 (i8Psi4s101dN1 x) x := by
  unfold i8Psi4s101N1 i8Psi4s101dN1
  exact (((((hasDerivAt_hpl_cons negOne [negOne, zero, one] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽101⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s101N2 (x : ℝ) : ℝ :=
    (5) * hpl [one] x +
    (-28) * hpl [negOne, zero] x +
    (-6) * hpl [one, zero] x +
    (20) * hpl [negOne, negOne, zero] x +
    (-4) * hpl [negOne, zero, one] x +
    (-4) * hpl [negOne, one, zero] x +
    (12) * hpl [one, negOne, zero] x +
    (24) * hpl [negOne, negOne, zero, one] x +
    (24) * hpl [negOne, negOne, one, zero] x +
    (24) * hpl [negOne, one, negOne, zero] x +
    (-40) * hpl [one, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s101N2`. -/
noncomputable def i8Psi4s101dN2 (x : ℝ) : ℝ :=
    (5) * (one.kernel x * hpl [] x) +
    (-28) * (negOne.kernel x * hpl [zero] x) +
    (-6) * (one.kernel x * hpl [zero] x) +
    (20) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, one] x) +
    (-4) * (negOne.kernel x * hpl [one, zero] x) +
    (12) * (one.kernel x * hpl [negOne, zero] x) +
    (24) * (negOne.kernel x * hpl [negOne, zero, one] x) +
    (24) * (negOne.kernel x * hpl [negOne, one, zero] x) +
    (24) * (negOne.kernel x * hpl [one, negOne, zero] x) +
    (-40) * (one.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s101N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s101N2 (i8Psi4s101dN2 x) x := by
  unfold i8Psi4s101N2 i8Psi4s101dN2
  exact ((((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (5)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, zero] hx).const_mul (-40)))

/-- The part of `ξ² Ψ₄⁽101⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s101N3 (x : ℝ) : ℝ :=
    (-39) +
    (34) * hpl [zero] x +
    (-4) * hpl [one] x +
    (-32) * hpl [negOne, zero] x +
    (4) * hpl [zero, one] x +
    (4) * hpl [one, zero] x +
    (24) * hpl [negOne, negOne, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (-8) * hpl [one, negOne, zero] x +
    (16) * hpl [negOne, negOne, zero, one] x +
    (16) * hpl [negOne, negOne, one, zero] x +
    (16) * hpl [negOne, one, negOne, zero] x +
    (16) * hpl [one, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s101N3`. -/
noncomputable def i8Psi4s101dN3 (x : ℝ) : ℝ :=
    0 +
    (34) * (zero.kernel x * hpl [] x) +
    (-4) * (one.kernel x * hpl [] x) +
    (-32) * (negOne.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [zero] x) +
    (24) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, one] x) +
    (16) * (negOne.kernel x * hpl [negOne, one, zero] x) +
    (16) * (negOne.kernel x * hpl [one, negOne, zero] x) +
    (16) * (one.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s101N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s101N3 (i8Psi4s101dN3 x) x := by
  unfold i8Psi4s101N3 i8Psi4s101dN3
  exact ((((((((((((((hasDerivAt_const x (-39)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (34))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽101⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s101N4 (x : ℝ) : ℝ :=
    (-2) +
    (3) * hpl [zero] x +
    (-1) * hpl [one] x +
    (-4) * hpl [negOne, zero] x +
    (2) * hpl [zero, one] x +
    (2) * hpl [one, zero] x +
    (4) * hpl [negOne, negOne, zero] x +
    (-4) * hpl [negOne, zero, one] x +
    (-4) * hpl [negOne, one, zero] x +
    (-4) * hpl [one, negOne, zero] x +
    (8) * hpl [negOne, negOne, zero, one] x +
    (8) * hpl [negOne, negOne, one, zero] x +
    (8) * hpl [negOne, one, negOne, zero] x +
    (8) * hpl [one, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s101N4`. -/
noncomputable def i8Psi4s101dN4 (x : ℝ) : ℝ :=
    0 +
    (3) * (zero.kernel x * hpl [] x) +
    (-1) * (one.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (4) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, one] x) +
    (-4) * (negOne.kernel x * hpl [one, zero] x) +
    (-4) * (one.kernel x * hpl [negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero, one] x) +
    (8) * (negOne.kernel x * hpl [negOne, one, zero] x) +
    (8) * (negOne.kernel x * hpl [one, negOne, zero] x) +
    (8) * (one.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s101N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s101N4 (i8Psi4s101dN4 x) x := by
  unfold i8Psi4s101N4 i8Psi4s101dN4
  exact ((((((((((((((hasDerivAt_const x (-2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [negOne, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [one, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [negOne, negOne, zero] hx).const_mul (8)))

/-- The part of `Ψ₄⁽101⁾` with constant coefficients. -/
noncomputable def i8Psi4s101W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, negOne, negOne, zero] x +
    (-16) * hpl [zero, negOne, zero, one] x +
    (-16) * hpl [zero, negOne, one, zero] x +
    (-16) * hpl [zero, one, negOne, zero] x +
    (-16) * hpl [zero, negOne, negOne, zero, one] x +
    (-16) * hpl [zero, negOne, negOne, one, zero] x +
    (-16) * hpl [zero, negOne, one, negOne, zero] x +
    (-16) * hpl [zero, one, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s101W`. -/
noncomputable def i8Psi4s101dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (-16) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-16) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, negOne, zero, one] x) +
    (-16) * (zero.kernel x * hpl [negOne, negOne, one, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, one, negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [one, negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s101W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s101W (i8Psi4s101dW x) x := by
  unfold i8Psi4s101W i8Psi4s101dW
  exact (((((((((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, negOne, zero] hx).const_mul (-16)))

/-- The piece `Ψ₄⁽101⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s101 (x : ℝ) : ℝ :=
  (i8Psi4s101N0 x + x * i8Psi4s101N1 x + x ^ 2 * i8Psi4s101N2 x + x ^ 3 * i8Psi4s101N3 x +
    x ^ 4 * i8Psi4s101N4 x) / x ^ 2 + i8Psi4s101W x

/-- The derivative of `Ψ₄⁽101⁾`. -/
noncomputable def i8Psi4s101D (x : ℝ) : ℝ :=
  ((i8Psi4s101dN0 x + (i8Psi4s101N1 x + x * i8Psi4s101dN1 x) + (2 * x * i8Psi4s101N2 x +
    x ^ 2 * i8Psi4s101dN2 x) + (3 * x ^ 2 * i8Psi4s101N3 x + x ^ 3 * i8Psi4s101dN3 x) +
    (4 * x ^ 3 * i8Psi4s101N4 x + x ^ 4 * i8Psi4s101dN4 x)) * x ^ 2 - (i8Psi4s101N0 x +
    x * i8Psi4s101N1 x + x ^ 2 * i8Psi4s101N2 x + x ^ 3 * i8Psi4s101N3 x +
    x ^ 4 * i8Psi4s101N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s101dW x

theorem hasDerivAt_i8Psi4s101 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s101 (i8Psi4s101D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s101N0 hx).add (X.mul (hasDerivAt_i8Psi4s101N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s101N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s101N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s101N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s101W hx)
  unfold i8Psi4s101
  refine e.congr_deriv ?_
  unfold i8Psi4s101D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 101 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s101 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 -
    x) * (4 * hpl [negOne, negOne, zero] x)) * (x / (1 - x)))

/-- `p₄⁽101⁾` written over words. -/
noncomputable def i8P4w101 (x : ℝ) : ℝ :=
    (16 + 16 * x) * hpl [negOne, negOne, zero, one] x +
    (16 + 16 * x) * hpl [negOne, negOne, one, zero] x +
    (16 + 16 * x) * hpl [negOne, one, negOne, zero] x +
    (16 + 16 * x) * hpl [one, negOne, negOne, zero] x

theorem i8P4s101_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s101 x = i8P4w101 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s101 i8P4w101
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [negOne, negOne, zero] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((16 + 16 * x)) * e0
  field_simp
  generalize hpl [negOne, negOne, zero, one] x = v0 at *
  generalize hpl [negOne, negOne, one, zero] x = v1 at *
  generalize hpl [negOne, one, negOne, zero] x = v2 at *
  generalize hpl [one, negOne, negOne, zero] x = v3 at *
  generalize hpl [negOne, negOne, zero] x = v4 at *
  generalize hpl [one] x = v5 at *
  ring

/-- **`(Ψ₄⁽101⁾)'(ξ) ξ' = p₄⁽101⁾`**, in terms of `ξ`. -/
theorem i8Psi4s101D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s101D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s101 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s101_eq_w hx]
  unfold i8Psi4s101D i8Psi4s101N0 i8Psi4s101N1 i8Psi4s101N2 i8Psi4s101N3 i8Psi4s101N4 i8Psi4s101dN0
    i8Psi4s101dN1 i8Psi4s101dN2 i8Psi4s101dN3 i8Psi4s101dN4 i8Psi4s101dW i8P4w101
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, negOne, zero, one] x = v0 at *
  generalize hpl [zero, negOne, negOne, one, zero] x = v1 at *
  generalize hpl [zero, negOne, one, negOne, zero] x = v2 at *
  generalize hpl [zero, one, negOne, negOne, zero] x = v3 at *
  generalize hpl [negOne, negOne, zero, one] x = v4 at *
  generalize hpl [negOne, negOne, one, zero] x = v5 at *
  generalize hpl [negOne, one, negOne, zero] x = v6 at *
  generalize hpl [zero, negOne, negOne, zero] x = v7 at *
  generalize hpl [zero, negOne, zero, one] x = v8 at *
  generalize hpl [zero, negOne, one, zero] x = v9 at *
  generalize hpl [zero, one, negOne, zero] x = v10 at *
  generalize hpl [one, negOne, negOne, zero] x = v11 at *
  generalize hpl [negOne, negOne, zero] x = v12 at *
  generalize hpl [negOne, zero, one] x = v13 at *
  generalize hpl [negOne, one, zero] x = v14 at *
  generalize hpl [one, negOne, zero] x = v15 at *
  generalize hpl [negOne, zero] x = v16 at *
  generalize hpl [zero, one] x = v17 at *
  generalize hpl [one, zero] x = v18 at *
  generalize hpl [zero] x = v19 at *
  generalize hpl [one] x = v20 at *
  ring

/-- The part of `ξ² Ψ₄⁽102⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s102N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s102N0`. -/
noncomputable def i8Psi4s102dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s102N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s102N0 (i8Psi4s102dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽102⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s102N1 (x : ℝ) : ℝ :=
    (4) * hpl [one] x +
    (4) * hpl [zero, one] x +
    (4) * hpl [one, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (4) * hpl [one, zero, zero] x +
    (4) * hpl [zero, zero, zero, one] x +
    (4) * hpl [zero, zero, one, zero] x +
    (4) * hpl [zero, one, zero, zero] x +
    (4) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s102N1`. -/
noncomputable def i8Psi4s102dN1 (x : ℝ) : ℝ :=
    (4) * (one.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, zero, one] x) +
    (4) * (zero.kernel x * hpl [zero, one, zero] x) +
    (4) * (zero.kernel x * hpl [one, zero, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s102N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s102N1 (i8Psi4s102dN1 x) x := by
  unfold i8Psi4s102N1 i8Psi4s102dN1
  exact (((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽102⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s102N2 (x : ℝ) : ℝ :=
    (-4) * hpl [zero] x +
    (1 / 4) * hpl [one] x +
    (-4) * hpl [zero, zero] x +
    (-17 / 2) * hpl [one, zero] x +
    (-4) * hpl [zero, zero, zero] x +
    (1) * hpl [one, zero, zero] x +
    (-10) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s102N2`. -/
noncomputable def i8Psi4s102dN2 (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [] x) +
    (1 / 4) * (one.kernel x * hpl [] x) +
    (-4) * (zero.kernel x * hpl [zero] x) +
    (-17 / 2) * (one.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero] x) +
    (1) * (one.kernel x * hpl [zero, zero] x) +
    (-10) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s102N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s102N2 (i8Psi4s102dN2 x) x := by
  unfold i8Psi4s102N2 i8Psi4s102dN2
  exact ((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-17 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (-10)))

/-- The part of `ξ² Ψ₄⁽102⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s102N3 (x : ℝ) : ℝ :=
    (-79 / 4) +
    (31 / 2) * hpl [zero] x +
    (-4) * hpl [one] x +
    (-11) * hpl [zero, zero] x +
    (4) * hpl [zero, one] x +
    (4) * hpl [one, zero] x +
    (6) * hpl [zero, zero, zero] x +
    (-4) * hpl [zero, zero, one] x +
    (-4) * hpl [zero, one, zero] x +
    (-4) * hpl [one, zero, zero] x +
    (4) * hpl [zero, zero, zero, one] x +
    (4) * hpl [zero, zero, one, zero] x +
    (4) * hpl [zero, one, zero, zero] x +
    (4) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s102N3`. -/
noncomputable def i8Psi4s102dN3 (x : ℝ) : ℝ :=
    0 +
    (31 / 2) * (zero.kernel x * hpl [] x) +
    (-4) * (one.kernel x * hpl [] x) +
    (-11) * (zero.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, one] x) +
    (-4) * (zero.kernel x * hpl [one, zero] x) +
    (-4) * (one.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, zero, one] x) +
    (4) * (zero.kernel x * hpl [zero, one, zero] x) +
    (4) * (zero.kernel x * hpl [one, zero, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s102N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s102N3 (i8Psi4s102dN3 x) x := by
  unfold i8Psi4s102N3 i8Psi4s102dN3
  exact ((((((((((((((hasDerivAt_const x (-79 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (31 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽102⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s102N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (3 / 4) * hpl [zero] x +
    (-1 / 4) * hpl [one] x +
    (-1) * hpl [zero, zero] x +
    (1 / 2) * hpl [zero, one] x +
    (1 / 2) * hpl [one, zero] x +
    (1) * hpl [zero, zero, zero] x +
    (-1) * hpl [zero, zero, one] x +
    (-1) * hpl [zero, one, zero] x +
    (-1) * hpl [one, zero, zero] x +
    (2) * hpl [zero, zero, zero, one] x +
    (2) * hpl [zero, zero, one, zero] x +
    (2) * hpl [zero, one, zero, zero] x +
    (2) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s102N4`. -/
noncomputable def i8Psi4s102dN4 (x : ℝ) : ℝ :=
    0 +
    (3 / 4) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (one.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [one] x) +
    (1 / 2) * (one.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [zero, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, one] x) +
    (-1) * (zero.kernel x * hpl [one, zero] x) +
    (-1) * (one.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero, one] x) +
    (2) * (zero.kernel x * hpl [zero, one, zero] x) +
    (2) * (zero.kernel x * hpl [one, zero, zero] x) +
    (2) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s102N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s102N4 (i8Psi4s102dN4 x) x := by
  unfold i8Psi4s102N4 i8Psi4s102dN4
  exact ((((((((((((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (2)))

/-- The part of `Ψ₄⁽102⁾` with constant coefficients. -/
noncomputable def i8Psi4s102W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, zero, zero, zero] x +
    (-4) * hpl [zero, zero, zero, zero, one] x +
    (-4) * hpl [zero, zero, zero, one, zero] x +
    (-4) * hpl [zero, zero, one, zero, zero] x +
    (-4) * hpl [zero, one, zero, zero, zero] x

/-- The derivative of `i8Psi4s102W`. -/
noncomputable def i8Psi4s102dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, zero, one] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, one, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, one, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [one, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s102W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s102W (i8Psi4s102dW x) x := by
  unfold i8Psi4s102W i8Psi4s102dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero, zero] hx).const_mul (-4)))

/-- The piece `Ψ₄⁽102⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s102 (x : ℝ) : ℝ :=
  (i8Psi4s102N0 x + x * i8Psi4s102N1 x + x ^ 2 * i8Psi4s102N2 x + x ^ 3 * i8Psi4s102N3 x +
    x ^ 4 * i8Psi4s102N4 x) / x ^ 2 + i8Psi4s102W x

/-- The derivative of `Ψ₄⁽102⁾`. -/
noncomputable def i8Psi4s102D (x : ℝ) : ℝ :=
  ((i8Psi4s102dN0 x + (i8Psi4s102N1 x + x * i8Psi4s102dN1 x) + (2 * x * i8Psi4s102N2 x +
    x ^ 2 * i8Psi4s102dN2 x) + (3 * x ^ 2 * i8Psi4s102N3 x + x ^ 3 * i8Psi4s102dN3 x) +
    (4 * x ^ 3 * i8Psi4s102N4 x + x ^ 4 * i8Psi4s102dN4 x)) * x ^ 2 - (i8Psi4s102N0 x +
    x * i8Psi4s102N1 x + x ^ 2 * i8Psi4s102N2 x + x ^ 3 * i8Psi4s102N3 x +
    x ^ 4 * i8Psi4s102N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s102dW x

theorem hasDerivAt_i8Psi4s102 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s102 (i8Psi4s102D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s102N0 hx).add (X.mul (hasDerivAt_i8Psi4s102N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s102N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s102N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s102N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s102W hx)
  unfold i8Psi4s102
  refine e.congr_deriv ?_
  unfold i8Psi4s102D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 102 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s102 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 -
    x) * (1 * hpl [zero, zero, zero] x)) * (x / (1 - x)))

/-- `p₄⁽102⁾` written over words. -/
noncomputable def i8P4w102 (x : ℝ) : ℝ :=
    (4 + 4 * x) * hpl [zero, zero, zero, one] x +
    (4 + 4 * x) * hpl [zero, zero, one, zero] x +
    (4 + 4 * x) * hpl [zero, one, zero, zero] x +
    (4 + 4 * x) * hpl [one, zero, zero, zero] x

theorem i8P4s102_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s102 x = i8P4w102 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s102 i8P4w102
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [zero, zero, zero] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((4 + 4 * x)) * e0
  field_simp
  generalize hpl [zero, zero, zero, one] x = v0 at *
  generalize hpl [zero, zero, one, zero] x = v1 at *
  generalize hpl [zero, one, zero, zero] x = v2 at *
  generalize hpl [one, zero, zero, zero] x = v3 at *
  generalize hpl [zero, zero, zero] x = v4 at *
  generalize hpl [one] x = v5 at *
  ring

/-- **`(Ψ₄⁽102⁾)'(ξ) ξ' = p₄⁽102⁾`**, in terms of `ξ`. -/
theorem i8Psi4s102D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s102D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s102 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s102_eq_w hx]
  unfold i8Psi4s102D i8Psi4s102N0 i8Psi4s102N1 i8Psi4s102N2 i8Psi4s102N3 i8Psi4s102N4 i8Psi4s102dN0
    i8Psi4s102dN1 i8Psi4s102dN2 i8Psi4s102dN3 i8Psi4s102dN4 i8Psi4s102dW i8P4w102
  simp only [kernel_zero, kernel_one, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero, zero, one] x = v0 at *
  generalize hpl [zero, zero, zero, one, zero] x = v1 at *
  generalize hpl [zero, zero, one, zero, zero] x = v2 at *
  generalize hpl [zero, one, zero, zero, zero] x = v3 at *
  generalize hpl [zero, zero, zero, zero] x = v4 at *
  generalize hpl [zero, zero, zero, one] x = v5 at *
  generalize hpl [zero, zero, one, zero] x = v6 at *
  generalize hpl [zero, one, zero, zero] x = v7 at *
  generalize hpl [one, zero, zero, zero] x = v8 at *
  generalize hpl [zero, zero, zero] x = v9 at *
  generalize hpl [zero, zero, one] x = v10 at *
  generalize hpl [zero, one, zero] x = v11 at *
  generalize hpl [one, zero, zero] x = v12 at *
  generalize hpl [zero, zero] x = v13 at *
  generalize hpl [zero, one] x = v14 at *
  generalize hpl [one, zero] x = v15 at *
  generalize hpl [zero] x = v16 at *
  generalize hpl [one] x = v17 at *
  ring

end QED.ThreeLoopD
