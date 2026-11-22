/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P48

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 156 to 157

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s156`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s156D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s156`, `QED.ThreeLoopD.i8Psi4s156D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽156⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s156N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s156N0`. -/
noncomputable def i8Psi4s156dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s156N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s156N0 (i8Psi4s156dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽156⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s156N1 (x : ℝ) : ℝ :=
    (8) * hpl [one, one, one] x +
    (8) * hpl [zero, one, one, one] x +
    (8) * hpl [one, zero, one, one] x +
    (8) * hpl [one, one, zero, one] x +
    (8) * hpl [one, one, one, zero] x

/-- The derivative of `i8Psi4s156N1`. -/
noncomputable def i8Psi4s156dN1 (x : ℝ) : ℝ :=
    (8) * (one.kernel x * hpl [one, one] x) +
    (8) * (zero.kernel x * hpl [one, one, one] x) +
    (8) * (one.kernel x * hpl [zero, one, one] x) +
    (8) * (one.kernel x * hpl [one, zero, one] x) +
    (8) * (one.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s156N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s156N1 (i8Psi4s156dN1 x) x := by
  unfold i8Psi4s156N1 i8Psi4s156dN1
  exact ((((((hasDerivAt_hpl_cons one [one, one] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, one, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽156⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s156N2 (x : ℝ) : ℝ :=
    (17 / 2) * hpl [one] x +
    (-1) * hpl [one, zero] x +
    (8) * hpl [one, one] x +
    (-8) * hpl [zero, one, one] x +
    (-2) * hpl [one, zero, one] x +
    (-2) * hpl [one, one, zero] x +
    (-2) * hpl [one, one, one] x +
    (-12) * hpl [one, zero, one, one] x +
    (-12) * hpl [one, one, zero, one] x +
    (-12) * hpl [one, one, one, zero] x

/-- The derivative of `i8Psi4s156N2`. -/
noncomputable def i8Psi4s156dN2 (x : ℝ) : ℝ :=
    (17 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (one.kernel x * hpl [zero] x) +
    (8) * (one.kernel x * hpl [one] x) +
    (-8) * (zero.kernel x * hpl [one, one] x) +
    (-2) * (one.kernel x * hpl [zero, one] x) +
    (-2) * (one.kernel x * hpl [one, zero] x) +
    (-2) * (one.kernel x * hpl [one, one] x) +
    (-12) * (one.kernel x * hpl [zero, one, one] x) +
    (-12) * (one.kernel x * hpl [one, zero, one] x) +
    (-12) * (one.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s156N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s156N2 (i8Psi4s156dN2 x) x := by
  unfold i8Psi4s156N2 i8Psi4s156dN2
  exact (((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (17 / 2)).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, one, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [one, zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [one, one, zero] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽156⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s156N3 (x : ℝ) : ℝ :=
    (-19 / 2) +
    (1) * hpl [zero] x +
    (-10) * hpl [one] x +
    (2) * hpl [zero, one] x +
    (2) * hpl [one, zero] x +
    (-10) * hpl [one, one] x +
    (4) * hpl [zero, one, one] x +
    (4) * hpl [one, zero, one] x +
    (4) * hpl [one, one, zero] x +
    (-8) * hpl [one, one, one] x +
    (8) * hpl [zero, one, one, one] x +
    (8) * hpl [one, zero, one, one] x +
    (8) * hpl [one, one, zero, one] x +
    (8) * hpl [one, one, one, zero] x

/-- The derivative of `i8Psi4s156N3`. -/
noncomputable def i8Psi4s156dN3 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (-10) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (-10) * (one.kernel x * hpl [one] x) +
    (4) * (zero.kernel x * hpl [one, one] x) +
    (4) * (one.kernel x * hpl [zero, one] x) +
    (4) * (one.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [one, one] x) +
    (8) * (zero.kernel x * hpl [one, one, one] x) +
    (8) * (one.kernel x * hpl [zero, one, one] x) +
    (8) * (one.kernel x * hpl [one, zero, one] x) +
    (8) * (one.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s156N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s156N3 (i8Psi4s156dN3 x) x := by
  unfold i8Psi4s156N3 i8Psi4s156dN3
  exact ((((((((((((((hasDerivAt_const x (-19 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, one, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽156⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s156N4 (x : ℝ) : ℝ :=
    (1) +
    (-1 / 2) * hpl [zero] x +
    (3 / 2) * hpl [one] x +
    (-1) * hpl [zero, one] x +
    (-1) * hpl [one, zero] x +
    (2) * hpl [one, one] x +
    (-2) * hpl [zero, one, one] x +
    (-2) * hpl [one, zero, one] x +
    (-2) * hpl [one, one, zero] x +
    (2) * hpl [one, one, one] x +
    (-4) * hpl [zero, one, one, one] x +
    (-4) * hpl [one, zero, one, one] x +
    (-4) * hpl [one, one, zero, one] x +
    (-4) * hpl [one, one, one, zero] x

/-- The derivative of `i8Psi4s156N4`. -/
noncomputable def i8Psi4s156dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (3 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [zero] x) +
    (2) * (one.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [one, one] x) +
    (-2) * (one.kernel x * hpl [zero, one] x) +
    (-2) * (one.kernel x * hpl [one, zero] x) +
    (2) * (one.kernel x * hpl [one, one] x) +
    (-4) * (zero.kernel x * hpl [one, one, one] x) +
    (-4) * (one.kernel x * hpl [zero, one, one] x) +
    (-4) * (one.kernel x * hpl [one, zero, one] x) +
    (-4) * (one.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s156N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s156N4 (i8Psi4s156dN4 x) x := by
  unfold i8Psi4s156N4 i8Psi4s156dN4
  exact ((((((((((((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, one, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽156⁾` with constant coefficients. -/
noncomputable def i8Psi4s156W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, one, one] x +
    (-8) * hpl [zero, one, zero, one] x +
    (-8) * hpl [zero, one, one, zero] x +
    (8) * hpl [zero, zero, one, one, one] x +
    (8) * hpl [zero, one, zero, one, one] x +
    (8) * hpl [zero, one, one, zero, one] x +
    (8) * hpl [zero, one, one, one, zero] x

/-- The derivative of `i8Psi4s156W`. -/
noncomputable def i8Psi4s156dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero, one, one] x) +
    (-8) * (zero.kernel x * hpl [one, zero, one] x) +
    (-8) * (zero.kernel x * hpl [one, one, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one, one, one] x) +
    (8) * (zero.kernel x * hpl [one, zero, one, one] x) +
    (8) * (zero.kernel x * hpl [one, one, zero, one] x) +
    (8) * (zero.kernel x * hpl [one, one, one, zero] x)

theorem hasDerivAt_i8Psi4s156W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s156W (i8Psi4s156dW x) x := by
  unfold i8Psi4s156W i8Psi4s156dW
  exact ((((((((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, one, one, zero] hx).const_mul (8)))

/-- The piece `Ψ₄⁽156⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s156 (x : ℝ) : ℝ :=
  (i8Psi4s156N0 x + x * i8Psi4s156N1 x + x ^ 2 * i8Psi4s156N2 x + x ^ 3 * i8Psi4s156N3 x +
    x ^ 4 * i8Psi4s156N4 x) / x ^ 2 + i8Psi4s156W x

/-- The derivative of `Ψ₄⁽156⁾`. -/
noncomputable def i8Psi4s156D (x : ℝ) : ℝ :=
  ((i8Psi4s156dN0 x + (i8Psi4s156N1 x + x * i8Psi4s156dN1 x) + (2 * x * i8Psi4s156N2 x +
    x ^ 2 * i8Psi4s156dN2 x) + (3 * x ^ 2 * i8Psi4s156N3 x + x ^ 3 * i8Psi4s156dN3 x) +
    (4 * x ^ 3 * i8Psi4s156N4 x + x ^ 4 * i8Psi4s156dN4 x)) * x ^ 2 - (i8Psi4s156N0 x +
    x * i8Psi4s156N1 x + x ^ 2 * i8Psi4s156N2 x + x ^ 3 * i8Psi4s156N3 x +
    x ^ 4 * i8Psi4s156N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s156dW x

theorem hasDerivAt_i8Psi4s156 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s156 (i8Psi4s156D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s156N0 hx).add (X.mul (hasDerivAt_i8Psi4s156N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s156N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s156N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s156N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s156W hx)
  unfold i8Psi4s156
  refine e.congr_deriv ?_
  unfold i8Psi4s156D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 156 of `p₄` in `ξ`: from `t B0 A0 (-λ)^4/4!`, the term with `log^3 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s156 (x : ℝ) : ℝ :=
  -((4 / 3) * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 3 * Real.log x * (x / (1 - x)))

/-- `p₄⁽156⁾` written over words. -/
noncomputable def i8P4w156 (x : ℝ) : ℝ :=
    (8 - 8 * x) * hpl [zero, one, one, one] x +
    (8 - 8 * x) * hpl [one, zero, one, one] x +
    (8 - 8 * x) * hpl [one, one, zero, one] x +
    (8 - 8 * x) * hpl [one, one, one, zero] x

theorem i8P4s156_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s156 x = i8P4w156 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s156 i8P4w156
  rw [i13_log_one_sub_eq hx]
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [one] [one] hx
  have e1 := hpl_mul_hpl [one] [one, one] hx
  have e2 := hpl_mul_hpl [zero] [one, one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  linear_combination (norm := skip) ((4 / 3 - 4 / 3 * x) * hpl [one] x * hpl [zero] x) * e0 +
    ((8 / 3 - 8 / 3 * x) * hpl [zero] x) * e1 + ((8 - 8 * x)) * e2
  field_simp
  generalize hpl [zero, one, one, one] x = v0 at *
  generalize hpl [one, zero, one, one] x = v1 at *
  generalize hpl [one, one, zero, one] x = v2 at *
  generalize hpl [one, one, one, zero] x = v3 at *
  generalize hpl [one, one, one] x = v4 at *
  generalize hpl [one, one] x = v5 at *
  generalize hpl [zero] x = v6 at *
  generalize hpl [one] x = v7 at *
  ring

/-- **`(Ψ₄⁽156⁾)'(ξ) ξ' = p₄⁽156⁾`**, in terms of `ξ`. -/
theorem i8Psi4s156D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s156D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s156 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s156_eq_w hx]
  unfold i8Psi4s156D i8Psi4s156N0 i8Psi4s156N1 i8Psi4s156N2 i8Psi4s156N3 i8Psi4s156N4 i8Psi4s156dN0
    i8Psi4s156dN1 i8Psi4s156dN2 i8Psi4s156dN3 i8Psi4s156dN4 i8Psi4s156dW i8P4w156
  simp only [kernel_zero, kernel_one, hpl_nil]
  field_simp
  generalize hpl [zero, zero, one, one, one] x = v0 at *
  generalize hpl [zero, one, zero, one, one] x = v1 at *
  generalize hpl [zero, one, one, zero, one] x = v2 at *
  generalize hpl [zero, one, one, one, zero] x = v3 at *
  generalize hpl [zero, zero, one, one] x = v4 at *
  generalize hpl [zero, one, zero, one] x = v5 at *
  generalize hpl [zero, one, one, zero] x = v6 at *
  generalize hpl [zero, one, one, one] x = v7 at *
  generalize hpl [one, zero, one, one] x = v8 at *
  generalize hpl [one, one, zero, one] x = v9 at *
  generalize hpl [one, one, one, zero] x = v10 at *
  generalize hpl [zero, one, one] x = v11 at *
  generalize hpl [one, zero, one] x = v12 at *
  generalize hpl [one, one, zero] x = v13 at *
  generalize hpl [one, one, one] x = v14 at *
  generalize hpl [zero, one] x = v15 at *
  generalize hpl [one, zero] x = v16 at *
  generalize hpl [one, one] x = v17 at *
  generalize hpl [zero] x = v18 at *
  generalize hpl [one] x = v19 at *
  ring

/-- The part of `ξ² Ψ₄⁽157⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s157N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s157N0`. -/
noncomputable def i8Psi4s157dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s157N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s157N0 (i8Psi4s157dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽157⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s157N1 (x : ℝ) : ℝ :=
    (16) * hpl [one, one, one, one] x

/-- The derivative of `i8Psi4s157N1`. -/
noncomputable def i8Psi4s157dN1 (x : ℝ) : ℝ :=
    (16) * (one.kernel x * hpl [one, one, one] x)

theorem hasDerivAt_i8Psi4s157N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s157N1 (i8Psi4s157dN1 x) x := by
  unfold i8Psi4s157N1 i8Psi4s157dN1
  exact ((hasDerivAt_hpl_cons one [one, one, one] hx).const_mul (16))

/-- The part of `ξ² Ψ₄⁽157⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s157N2 (x : ℝ) : ℝ :=
    (-1) * hpl [one] x +
    (-2) * hpl [one, one] x +
    (-4) * hpl [one, one, one] x +
    (-24) * hpl [one, one, one, one] x

/-- The derivative of `i8Psi4s157N2`. -/
noncomputable def i8Psi4s157dN2 (x : ℝ) : ℝ :=
    (-1) * (one.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [one] x) +
    (-4) * (one.kernel x * hpl [one, one] x) +
    (-24) * (one.kernel x * hpl [one, one, one] x)

theorem hasDerivAt_i8Psi4s157N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s157N2 (i8Psi4s157dN2 x) x := by
  unfold i8Psi4s157N2 i8Psi4s157dN2
  exact (((((hasDerivAt_hpl_cons one [] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, one, one] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽157⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s157N3 (x : ℝ) : ℝ :=
    (1) +
    (2) * hpl [one] x +
    (4) * hpl [one, one] x +
    (8) * hpl [one, one, one] x +
    (16) * hpl [one, one, one, one] x

/-- The derivative of `i8Psi4s157N3`. -/
noncomputable def i8Psi4s157dN3 (x : ℝ) : ℝ :=
    0 +
    (2) * (one.kernel x * hpl [] x) +
    (4) * (one.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [one, one] x) +
    (16) * (one.kernel x * hpl [one, one, one] x)

theorem hasDerivAt_i8Psi4s157N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s157N3 (i8Psi4s157dN3 x) x := by
  unfold i8Psi4s157N3 i8Psi4s157dN3
  exact (((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, one, one] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽157⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s157N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (-1) * hpl [one] x +
    (-2) * hpl [one, one] x +
    (-4) * hpl [one, one, one] x +
    (-8) * hpl [one, one, one, one] x

/-- The derivative of `i8Psi4s157N4`. -/
noncomputable def i8Psi4s157dN4 (x : ℝ) : ℝ :=
    0 +
    (-1) * (one.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [one] x) +
    (-4) * (one.kernel x * hpl [one, one] x) +
    (-8) * (one.kernel x * hpl [one, one, one] x)

theorem hasDerivAt_i8Psi4s157N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s157N4 (i8Psi4s157dN4 x) x := by
  unfold i8Psi4s157N4 i8Psi4s157dN4
  exact (((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, one, one] hx).const_mul (-8)))

/-- The part of `Ψ₄⁽157⁾` with constant coefficients. -/
noncomputable def i8Psi4s157W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, one, one, one] x +
    (16) * hpl [zero, one, one, one, one] x

/-- The derivative of `i8Psi4s157W`. -/
noncomputable def i8Psi4s157dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [one, one, one] x) +
    (16) * (zero.kernel x * hpl [one, one, one, one] x)

theorem hasDerivAt_i8Psi4s157W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s157W (i8Psi4s157dW x) x := by
  unfold i8Psi4s157W i8Psi4s157dW
  exact (((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [one, one, one, one] hx).const_mul (16)))

/-- The piece `Ψ₄⁽157⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s157 (x : ℝ) : ℝ :=
  (i8Psi4s157N0 x + x * i8Psi4s157N1 x + x ^ 2 * i8Psi4s157N2 x + x ^ 3 * i8Psi4s157N3 x +
    x ^ 4 * i8Psi4s157N4 x) / x ^ 2 + i8Psi4s157W x

/-- The derivative of `Ψ₄⁽157⁾`. -/
noncomputable def i8Psi4s157D (x : ℝ) : ℝ :=
  ((i8Psi4s157dN0 x + (i8Psi4s157N1 x + x * i8Psi4s157dN1 x) + (2 * x * i8Psi4s157N2 x +
    x ^ 2 * i8Psi4s157dN2 x) + (3 * x ^ 2 * i8Psi4s157N3 x + x ^ 3 * i8Psi4s157dN3 x) +
    (4 * x ^ 3 * i8Psi4s157N4 x + x ^ 4 * i8Psi4s157dN4 x)) * x ^ 2 - (i8Psi4s157N0 x +
    x * i8Psi4s157N1 x + x ^ 2 * i8Psi4s157N2 x + x ^ 3 * i8Psi4s157N3 x +
    x ^ 4 * i8Psi4s157N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s157dW x

theorem hasDerivAt_i8Psi4s157 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s157 (i8Psi4s157D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s157N0 hx).add (X.mul (hasDerivAt_i8Psi4s157N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s157N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s157N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s157N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s157W hx)
  unfold i8Psi4s157
  refine e.congr_deriv ?_
  unfold i8Psi4s157D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 157 of `p₄` in `ξ`: from `t B0 A0 (-λ)^4/4!`, the term with `log^4 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s157 (x : ℝ) : ℝ :=
  (2 / 3) * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 4 * (x / (1 - x))

/-- `p₄⁽157⁾` written over words. -/
noncomputable def i8P4w157 (x : ℝ) : ℝ :=
    (16 - 16 * x) * hpl [one, one, one, one] x

theorem i8P4s157_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s157 x = i8P4w157 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s157 i8P4w157
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [one] [one] hx
  have e1 := hpl_mul_hpl [one] [one, one] hx
  have e2 := hpl_mul_hpl [one] [one, one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  linear_combination (norm := skip) ((2 / 3 - 2 / 3 * x) * hpl [one] x * hpl [one] x) * e0 +
    ((4 / 3 - 4 / 3 * x) * hpl [one] x) * e1 + ((4 - 4 * x)) * e2
  field_simp
  generalize hpl [one, one, one, one] x = v0 at *
  generalize hpl [one, one, one] x = v1 at *
  generalize hpl [one, one] x = v2 at *
  generalize hpl [one] x = v3 at *
  ring

/-- **`(Ψ₄⁽157⁾)'(ξ) ξ' = p₄⁽157⁾`**, in terms of `ξ`. -/
theorem i8Psi4s157D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s157D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s157 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s157_eq_w hx]
  unfold i8Psi4s157D i8Psi4s157N0 i8Psi4s157N1 i8Psi4s157N2 i8Psi4s157N3 i8Psi4s157N4 i8Psi4s157dN0
    i8Psi4s157dN1 i8Psi4s157dN2 i8Psi4s157dN3 i8Psi4s157dN4 i8Psi4s157dW i8P4w157
  simp only [kernel_zero, kernel_one, hpl_nil]
  field_simp
  generalize hpl [zero, one, one, one, one] x = v0 at *
  generalize hpl [zero, one, one, one] x = v1 at *
  generalize hpl [one, one, one, one] x = v2 at *
  generalize hpl [one, one, one] x = v3 at *
  generalize hpl [one, one] x = v4 at *
  generalize hpl [one] x = v5 at *
  ring

end QED.ThreeLoopD
