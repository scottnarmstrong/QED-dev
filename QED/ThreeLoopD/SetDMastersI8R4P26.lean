/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P25

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 103 to 106

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s103`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s103D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s103`, `QED.ThreeLoopD.i8Psi4s103D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽103⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s103N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s103N0`. -/
noncomputable def i8Psi4s103dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s103N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s103N0 (i8Psi4s103dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽103⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s103N1 (x : ℝ) : ℝ :=
    (-8) * hpl [negOne, zero, zero, one] x +
    (-8) * hpl [negOne, zero, one, zero] x +
    (-8) * hpl [negOne, one, zero, zero] x +
    (-8) * hpl [one, negOne, zero, zero] x

/-- The derivative of `i8Psi4s103N1`. -/
noncomputable def i8Psi4s103dN1 (x : ℝ) : ℝ :=
    (-8) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-8) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-8) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s103N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s103N1 (i8Psi4s103dN1 x) x := by
  unfold i8Psi4s103N1 i8Psi4s103dN1
  exact (((((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽103⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s103N2 (x : ℝ) : ℝ :=
    (-9 / 2) * hpl [one] x +
    (5) * hpl [one, zero] x +
    (-10) * hpl [negOne, zero, zero] x +
    (-6) * hpl [one, zero, zero] x +
    (-12) * hpl [negOne, zero, zero, one] x +
    (-12) * hpl [negOne, zero, one, zero] x +
    (-12) * hpl [negOne, one, zero, zero] x +
    (20) * hpl [one, negOne, zero, zero] x

/-- The derivative of `i8Psi4s103N2`. -/
noncomputable def i8Psi4s103dN2 (x : ℝ) : ℝ :=
    (-9 / 2) * (one.kernel x * hpl [] x) +
    (5) * (one.kernel x * hpl [zero] x) +
    (-10) * (negOne.kernel x * hpl [zero, zero] x) +
    (-6) * (one.kernel x * hpl [zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-12) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-12) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (20) * (one.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s103N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s103N2 (i8Psi4s103dN2 x) x := by
  unfold i8Psi4s103N2 i8Psi4s103dN2
  exact (((((((((hasDerivAt_hpl_cons one [] hx).const_mul (-9 / 2)).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (20)))

/-- The part of `ξ² Ψ₄⁽103⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s103N3 (x : ℝ) : ℝ :=
    (51 / 2) +
    (-21) * hpl [zero] x +
    (4) * hpl [one] x +
    (16) * hpl [zero, zero] x +
    (-4) * hpl [zero, one] x +
    (-4) * hpl [one, zero] x +
    (-12) * hpl [negOne, zero, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (4) * hpl [one, zero, zero] x +
    (-8) * hpl [negOne, zero, zero, one] x +
    (-8) * hpl [negOne, zero, one, zero] x +
    (-8) * hpl [negOne, one, zero, zero] x +
    (-8) * hpl [one, negOne, zero, zero] x

/-- The derivative of `i8Psi4s103N3`. -/
noncomputable def i8Psi4s103dN3 (x : ℝ) : ℝ :=
    0 +
    (-21) * (zero.kernel x * hpl [] x) +
    (4) * (one.kernel x * hpl [] x) +
    (16) * (zero.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [one] x) +
    (-4) * (one.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-8) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-8) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s103N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s103N3 (i8Psi4s103dN3 x) x := by
  unfold i8Psi4s103N3 i8Psi4s103dN3
  exact ((((((((((((((hasDerivAt_const x (51 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-21))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽103⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s103N4 (x : ℝ) : ℝ :=
    (1) +
    (-3 / 2) * hpl [zero] x +
    (1 / 2) * hpl [one] x +
    (2) * hpl [zero, zero] x +
    (-1) * hpl [zero, one] x +
    (-1) * hpl [one, zero] x +
    (-2) * hpl [negOne, zero, zero] x +
    (2) * hpl [zero, zero, one] x +
    (2) * hpl [zero, one, zero] x +
    (2) * hpl [one, zero, zero] x +
    (-4) * hpl [negOne, zero, zero, one] x +
    (-4) * hpl [negOne, zero, one, zero] x +
    (-4) * hpl [negOne, one, zero, zero] x +
    (-4) * hpl [one, negOne, zero, zero] x

/-- The derivative of `i8Psi4s103N4`. -/
noncomputable def i8Psi4s103dN4 (x : ℝ) : ℝ :=
    0 +
    (-3 / 2) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (2) * (zero.kernel x * hpl [one, zero] x) +
    (2) * (one.kernel x * hpl [zero, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-4) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-4) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-4) * (one.kernel x * hpl [negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s103N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s103N4 (i8Psi4s103dN4 x) x := by
  unfold i8Psi4s103N4 i8Psi4s103dN4
  exact ((((((((((((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽103⁾` with constant coefficients. -/
noncomputable def i8Psi4s103W (x : ℝ) : ℝ :=
    (8) * hpl [zero, negOne, zero, zero] x +
    (8) * hpl [zero, zero, zero, one] x +
    (8) * hpl [zero, zero, one, zero] x +
    (8) * hpl [zero, one, zero, zero] x +
    (8) * hpl [zero, negOne, zero, zero, one] x +
    (8) * hpl [zero, negOne, zero, one, zero] x +
    (8) * hpl [zero, negOne, one, zero, zero] x +
    (8) * hpl [zero, one, negOne, zero, zero] x

/-- The derivative of `i8Psi4s103W`. -/
noncomputable def i8Psi4s103dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, zero, one] x) +
    (8) * (zero.kernel x * hpl [zero, one, zero] x) +
    (8) * (zero.kernel x * hpl [one, zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, zero, one] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, one, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, one, zero, zero] x) +
    (8) * (zero.kernel x * hpl [one, negOne, zero, zero] x)

theorem hasDerivAt_i8Psi4s103W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s103W (i8Psi4s103dW x) x := by
  unfold i8Psi4s103W i8Psi4s103dW
  exact (((((((((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero, zero] hx).const_mul (8)))

/-- The piece `Ψ₄⁽103⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s103 (x : ℝ) : ℝ :=
  (i8Psi4s103N0 x + x * i8Psi4s103N1 x + x ^ 2 * i8Psi4s103N2 x + x ^ 3 * i8Psi4s103N3 x +
    x ^ 4 * i8Psi4s103N4 x) / x ^ 2 + i8Psi4s103W x

/-- The derivative of `Ψ₄⁽103⁾`. -/
noncomputable def i8Psi4s103D (x : ℝ) : ℝ :=
  ((i8Psi4s103dN0 x + (i8Psi4s103N1 x + x * i8Psi4s103dN1 x) + (2 * x * i8Psi4s103N2 x +
    x ^ 2 * i8Psi4s103dN2 x) + (3 * x ^ 2 * i8Psi4s103N3 x + x ^ 3 * i8Psi4s103dN3 x) +
    (4 * x ^ 3 * i8Psi4s103N4 x + x ^ 4 * i8Psi4s103dN4 x)) * x ^ 2 - (i8Psi4s103N0 x +
    x * i8Psi4s103N1 x + x ^ 2 * i8Psi4s103N2 x + x ^ 3 * i8Psi4s103N3 x +
    x ^ 4 * i8Psi4s103N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s103dW x

theorem hasDerivAt_i8Psi4s103 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s103 (i8Psi4s103D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s103N0 hx).add (X.mul (hasDerivAt_i8Psi4s103N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s103N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s103N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s103N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s103W hx)
  unfold i8Psi4s103
  refine e.congr_deriv ?_
  unfold i8Psi4s103D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 103 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s103 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 -
    x) * ((-2) * hpl [negOne, zero, zero] x)) * (x / (1 - x)))

/-- `p₄⁽103⁾` written over words. -/
noncomputable def i8P4w103 (x : ℝ) : ℝ :=
    (-8 - 8 * x) * hpl [negOne, zero, zero, one] x +
    (-8 - 8 * x) * hpl [negOne, zero, one, zero] x +
    (-8 - 8 * x) * hpl [negOne, one, zero, zero] x +
    (-8 - 8 * x) * hpl [one, negOne, zero, zero] x

theorem i8P4s103_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s103 x = i8P4w103 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s103 i8P4w103
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [negOne, zero, zero] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((-8 - 8 * x)) * e0
  field_simp
  generalize hpl [negOne, zero, zero, one] x = v0 at *
  generalize hpl [negOne, zero, one, zero] x = v1 at *
  generalize hpl [negOne, one, zero, zero] x = v2 at *
  generalize hpl [one, negOne, zero, zero] x = v3 at *
  generalize hpl [negOne, zero, zero] x = v4 at *
  generalize hpl [one] x = v5 at *
  ring

/-- **`(Ψ₄⁽103⁾)'(ξ) ξ' = p₄⁽103⁾`**, in terms of `ξ`. -/
theorem i8Psi4s103D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s103D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s103 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s103_eq_w hx]
  unfold i8Psi4s103D i8Psi4s103N0 i8Psi4s103N1 i8Psi4s103N2 i8Psi4s103N3 i8Psi4s103N4 i8Psi4s103dN0
    i8Psi4s103dN1 i8Psi4s103dN2 i8Psi4s103dN3 i8Psi4s103dN4 i8Psi4s103dW i8P4w103
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, zero, zero, one] x = v0 at *
  generalize hpl [zero, negOne, zero, one, zero] x = v1 at *
  generalize hpl [zero, negOne, one, zero, zero] x = v2 at *
  generalize hpl [zero, one, negOne, zero, zero] x = v3 at *
  generalize hpl [negOne, zero, zero, one] x = v4 at *
  generalize hpl [negOne, zero, one, zero] x = v5 at *
  generalize hpl [negOne, one, zero, zero] x = v6 at *
  generalize hpl [zero, negOne, zero, zero] x = v7 at *
  generalize hpl [zero, zero, zero, one] x = v8 at *
  generalize hpl [zero, zero, one, zero] x = v9 at *
  generalize hpl [zero, one, zero, zero] x = v10 at *
  generalize hpl [one, negOne, zero, zero] x = v11 at *
  generalize hpl [negOne, zero, zero] x = v12 at *
  generalize hpl [zero, zero, one] x = v13 at *
  generalize hpl [zero, one, zero] x = v14 at *
  generalize hpl [one, zero, zero] x = v15 at *
  generalize hpl [zero, zero] x = v16 at *
  generalize hpl [zero, one] x = v17 at *
  generalize hpl [one, zero] x = v18 at *
  generalize hpl [zero] x = v19 at *
  generalize hpl [one] x = v20 at *
  ring

/-- The part of `ξ² Ψ₄⁽104⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s104N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s104N0`. -/
noncomputable def i8Psi4s104dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s104N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s104N0 (i8Psi4s104dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽104⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s104N1 (x : ℝ) : ℝ :=
    (-16) * hpl [negOne, zero, one] x +
    (-16) * hpl [negOne, one, zero] x +
    (-16) * hpl [one, negOne, zero] x

/-- The derivative of `i8Psi4s104N1`. -/
noncomputable def i8Psi4s104dN1 (x : ℝ) : ℝ :=
    (-16) * (negOne.kernel x * hpl [zero, one] x) +
    (-16) * (negOne.kernel x * hpl [one, zero] x) +
    (-16) * (one.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s104N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s104N1 (i8Psi4s104dN1 x) x := by
  unfold i8Psi4s104N1 i8Psi4s104dN1
  exact ((((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽104⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s104N2 (x : ℝ) : ℝ :=
    (10) * hpl [one] x +
    (-20) * hpl [negOne, zero] x +
    (-12) * hpl [one, zero] x +
    (-24) * hpl [negOne, zero, one] x +
    (-24) * hpl [negOne, one, zero] x +
    (40) * hpl [one, negOne, zero] x

/-- The derivative of `i8Psi4s104N2`. -/
noncomputable def i8Psi4s104dN2 (x : ℝ) : ℝ :=
    (10) * (one.kernel x * hpl [] x) +
    (-20) * (negOne.kernel x * hpl [zero] x) +
    (-12) * (one.kernel x * hpl [zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, one] x) +
    (-24) * (negOne.kernel x * hpl [one, zero] x) +
    (40) * (one.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s104N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s104N2 (i8Psi4s104dN2 x) x := by
  unfold i8Psi4s104N2 i8Psi4s104dN2
  exact (((((((hasDerivAt_hpl_cons one [] hx).const_mul (10)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (40)))

/-- The part of `ξ² Ψ₄⁽104⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s104N3 (x : ℝ) : ℝ :=
    (-42) +
    (32) * hpl [zero] x +
    (-8) * hpl [one] x +
    (-24) * hpl [negOne, zero] x +
    (8) * hpl [zero, one] x +
    (8) * hpl [one, zero] x +
    (-16) * hpl [negOne, zero, one] x +
    (-16) * hpl [negOne, one, zero] x +
    (-16) * hpl [one, negOne, zero] x

/-- The derivative of `i8Psi4s104N3`. -/
noncomputable def i8Psi4s104dN3 (x : ℝ) : ℝ :=
    0 +
    (32) * (zero.kernel x * hpl [] x) +
    (-8) * (one.kernel x * hpl [] x) +
    (-24) * (negOne.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, one] x) +
    (-16) * (negOne.kernel x * hpl [one, zero] x) +
    (-16) * (one.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s104N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s104N3 (i8Psi4s104dN3 x) x := by
  unfold i8Psi4s104N3 i8Psi4s104dN3
  exact (((((((((hasDerivAt_const x (-42)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽104⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s104N4 (x : ℝ) : ℝ :=
    (-3) +
    (4) * hpl [zero] x +
    (-2) * hpl [one] x +
    (-4) * hpl [negOne, zero] x +
    (4) * hpl [zero, one] x +
    (4) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (-8) * hpl [one, negOne, zero] x

/-- The derivative of `i8Psi4s104N4`. -/
noncomputable def i8Psi4s104dN4 (x : ℝ) : ℝ :=
    0 +
    (4) * (zero.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s104N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s104N4 (i8Psi4s104dN4 x) x := by
  unfold i8Psi4s104N4 i8Psi4s104dN4
  exact (((((((((hasDerivAt_const x (-3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8)))

/-- The part of `Ψ₄⁽104⁾` with constant coefficients. -/
noncomputable def i8Psi4s104W (x : ℝ) : ℝ :=
    (16) * hpl [zero, negOne, zero] x +
    (16) * hpl [zero, zero, one] x +
    (16) * hpl [zero, one, zero] x +
    (16) * hpl [zero, negOne, zero, one] x +
    (16) * hpl [zero, negOne, one, zero] x +
    (16) * hpl [zero, one, negOne, zero] x

/-- The derivative of `i8Psi4s104W`. -/
noncomputable def i8Psi4s104dW (x : ℝ) : ℝ :=
    (16) * (zero.kernel x * hpl [negOne, zero] x) +
    (16) * (zero.kernel x * hpl [zero, one] x) +
    (16) * (zero.kernel x * hpl [one, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (16) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (16) * (zero.kernel x * hpl [one, negOne, zero] x)

theorem hasDerivAt_i8Psi4s104W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s104W (i8Psi4s104dW x) x := by
  unfold i8Psi4s104W i8Psi4s104dW
  exact (((((((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (16)))

/-- The piece `Ψ₄⁽104⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s104 (x : ℝ) : ℝ :=
  (i8Psi4s104N0 x + x * i8Psi4s104N1 x + x ^ 2 * i8Psi4s104N2 x + x ^ 3 * i8Psi4s104N3 x +
    x ^ 4 * i8Psi4s104N4 x) / x ^ 2 + i8Psi4s104W x

/-- The derivative of `Ψ₄⁽104⁾`. -/
noncomputable def i8Psi4s104D (x : ℝ) : ℝ :=
  ((i8Psi4s104dN0 x + (i8Psi4s104N1 x + x * i8Psi4s104dN1 x) + (2 * x * i8Psi4s104N2 x +
    x ^ 2 * i8Psi4s104dN2 x) + (3 * x ^ 2 * i8Psi4s104N3 x + x ^ 3 * i8Psi4s104dN3 x) +
    (4 * x ^ 3 * i8Psi4s104N4 x + x ^ 4 * i8Psi4s104dN4 x)) * x ^ 2 - (i8Psi4s104N0 x +
    x * i8Psi4s104N1 x + x ^ 2 * i8Psi4s104N2 x + x ^ 3 * i8Psi4s104N3 x +
    x ^ 4 * i8Psi4s104N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s104dW x

theorem hasDerivAt_i8Psi4s104 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s104 (i8Psi4s104D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s104N0 hx).add (X.mul (hasDerivAt_i8Psi4s104N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s104N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s104N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s104N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s104W hx)
  unfold i8Psi4s104
  refine e.congr_deriv ?_
  unfold i8Psi4s104D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 104 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s104 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 -
    x) * ((-4) * hpl [negOne, zero] x)) * (x / (1 - x)))

/-- `p₄⁽104⁾` written over words. -/
noncomputable def i8P4w104 (x : ℝ) : ℝ :=
    (-16 - 16 * x) * hpl [negOne, zero, one] x +
    (-16 - 16 * x) * hpl [negOne, one, zero] x +
    (-16 - 16 * x) * hpl [one, negOne, zero] x

theorem i8P4s104_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s104 x = i8P4w104 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s104 i8P4w104
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [negOne, zero] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((-16 - 16 * x)) * e0
  field_simp
  generalize hpl [negOne, zero, one] x = v0 at *
  generalize hpl [negOne, one, zero] x = v1 at *
  generalize hpl [one, negOne, zero] x = v2 at *
  generalize hpl [negOne, zero] x = v3 at *
  generalize hpl [one] x = v4 at *
  ring

/-- **`(Ψ₄⁽104⁾)'(ξ) ξ' = p₄⁽104⁾`**, in terms of `ξ`. -/
theorem i8Psi4s104D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s104D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s104 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s104_eq_w hx]
  unfold i8Psi4s104D i8Psi4s104N0 i8Psi4s104N1 i8Psi4s104N2 i8Psi4s104N3 i8Psi4s104N4 i8Psi4s104dN0
    i8Psi4s104dN1 i8Psi4s104dN2 i8Psi4s104dN3 i8Psi4s104dN4 i8Psi4s104dW i8P4w104
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, zero, one] x = v0 at *
  generalize hpl [zero, negOne, one, zero] x = v1 at *
  generalize hpl [zero, one, negOne, zero] x = v2 at *
  generalize hpl [negOne, zero, one] x = v3 at *
  generalize hpl [negOne, one, zero] x = v4 at *
  generalize hpl [zero, negOne, zero] x = v5 at *
  generalize hpl [zero, zero, one] x = v6 at *
  generalize hpl [zero, one, zero] x = v7 at *
  generalize hpl [one, negOne, zero] x = v8 at *
  generalize hpl [negOne, zero] x = v9 at *
  generalize hpl [zero, one] x = v10 at *
  generalize hpl [one, zero] x = v11 at *
  generalize hpl [zero] x = v12 at *
  generalize hpl [one] x = v13 at *
  ring

/-- The part of `ξ² Ψ₄⁽105⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s105N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s105N0`. -/
noncomputable def i8Psi4s105dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s105N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s105N0 (i8Psi4s105dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽105⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s105N1 (x : ℝ) : ℝ :=
    (8) * hpl [one] x +
    (8) * hpl [zero, one] x +
    (8) * hpl [one, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (8) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s105N1`. -/
noncomputable def i8Psi4s105dN1 (x : ℝ) : ℝ :=
    (8) * (one.kernel x * hpl [] x) +
    (8) * (zero.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s105N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s105N1 (i8Psi4s105dN1 x) x := by
  unfold i8Psi4s105N1 i8Psi4s105dN1
  exact (((((((hasDerivAt_hpl_cons one [] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽105⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s105N2 (x : ℝ) : ℝ :=
    (-8) * hpl [zero] x +
    (-17) * hpl [one] x +
    (-8) * hpl [zero, zero] x +
    (2) * hpl [one, zero] x +
    (-20) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s105N2`. -/
noncomputable def i8Psi4s105dN2 (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [] x) +
    (-17) * (one.kernel x * hpl [] x) +
    (-8) * (zero.kernel x * hpl [zero] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (-20) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s105N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s105N2 (i8Psi4s105dN2 x) x := by
  unfold i8Psi4s105N2 i8Psi4s105dN2
  exact ((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-17))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-20)))

/-- The part of `ξ² Ψ₄⁽105⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s105N3 (x : ℝ) : ℝ :=
    (31) +
    (-22) * hpl [zero] x +
    (8) * hpl [one] x +
    (12) * hpl [zero, zero] x +
    (-8) * hpl [zero, one] x +
    (-8) * hpl [one, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (8) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s105N3`. -/
noncomputable def i8Psi4s105dN3 (x : ℝ) : ℝ :=
    0 +
    (-22) * (zero.kernel x * hpl [] x) +
    (8) * (one.kernel x * hpl [] x) +
    (12) * (zero.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [one] x) +
    (-8) * (one.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s105N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s105N3 (i8Psi4s105dN3 x) x := by
  unfold i8Psi4s105N3 i8Psi4s105dN3
  exact (((((((((hasDerivAt_const x (31)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽105⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s105N4 (x : ℝ) : ℝ :=
    (3 / 2) +
    (-2) * hpl [zero] x +
    (1) * hpl [one] x +
    (2) * hpl [zero, zero] x +
    (-2) * hpl [zero, one] x +
    (-2) * hpl [one, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (4) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s105N4`. -/
noncomputable def i8Psi4s105dN4 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x) +
    (1) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s105N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s105N4 (i8Psi4s105dN4 x) x := by
  unfold i8Psi4s105N4 i8Psi4s105dN4
  exact (((((((((hasDerivAt_const x (3 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽105⁾` with constant coefficients. -/
noncomputable def i8Psi4s105W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, zero] x +
    (-8) * hpl [zero, zero, zero, one] x +
    (-8) * hpl [zero, zero, one, zero] x +
    (-8) * hpl [zero, one, zero, zero] x

/-- The derivative of `i8Psi4s105W`. -/
noncomputable def i8Psi4s105dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-8) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s105W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s105W (i8Psi4s105dW x) x := by
  unfold i8Psi4s105W i8Psi4s105dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-8)))

/-- The piece `Ψ₄⁽105⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s105 (x : ℝ) : ℝ :=
  (i8Psi4s105N0 x + x * i8Psi4s105N1 x + x ^ 2 * i8Psi4s105N2 x + x ^ 3 * i8Psi4s105N3 x +
    x ^ 4 * i8Psi4s105N4 x) / x ^ 2 + i8Psi4s105W x

/-- The derivative of `Ψ₄⁽105⁾`. -/
noncomputable def i8Psi4s105D (x : ℝ) : ℝ :=
  ((i8Psi4s105dN0 x + (i8Psi4s105N1 x + x * i8Psi4s105dN1 x) + (2 * x * i8Psi4s105N2 x +
    x ^ 2 * i8Psi4s105dN2 x) + (3 * x ^ 2 * i8Psi4s105N3 x + x ^ 3 * i8Psi4s105dN3 x) +
    (4 * x ^ 3 * i8Psi4s105N4 x + x ^ 4 * i8Psi4s105dN4 x)) * x ^ 2 - (i8Psi4s105N0 x +
    x * i8Psi4s105N1 x + x ^ 2 * i8Psi4s105N2 x + x ^ 3 * i8Psi4s105N3 x +
    x ^ 4 * i8Psi4s105N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s105dW x

theorem hasDerivAt_i8Psi4s105 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s105 (i8Psi4s105D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s105N0 hx).add (X.mul (hasDerivAt_i8Psi4s105N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s105N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s105N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s105N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s105W hx)
  unfold i8Psi4s105
  refine e.congr_deriv ?_
  unfold i8Psi4s105D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 105 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s105 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 -
    x) * (2 * hpl [zero, zero] x)) * (x / (1 - x)))

/-- `p₄⁽105⁾` written over words. -/
noncomputable def i8P4w105 (x : ℝ) : ℝ :=
    (8 + 8 * x) * hpl [zero, zero, one] x +
    (8 + 8 * x) * hpl [zero, one, zero] x +
    (8 + 8 * x) * hpl [one, zero, zero] x

theorem i8P4s105_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s105 x = i8P4w105 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s105 i8P4w105
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [zero, zero] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((8 + 8 * x)) * e0
  field_simp
  generalize hpl [zero, zero, one] x = v0 at *
  generalize hpl [zero, one, zero] x = v1 at *
  generalize hpl [one, zero, zero] x = v2 at *
  generalize hpl [zero, zero] x = v3 at *
  generalize hpl [one] x = v4 at *
  ring

/-- **`(Ψ₄⁽105⁾)'(ξ) ξ' = p₄⁽105⁾`**, in terms of `ξ`. -/
theorem i8Psi4s105D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s105D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s105 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s105_eq_w hx]
  unfold i8Psi4s105D i8Psi4s105N0 i8Psi4s105N1 i8Psi4s105N2 i8Psi4s105N3 i8Psi4s105N4 i8Psi4s105dN0
    i8Psi4s105dN1 i8Psi4s105dN2 i8Psi4s105dN3 i8Psi4s105dN4 i8Psi4s105dW i8P4w105
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

/-- The part of `ξ² Ψ₄⁽106⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s106N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s106N0`. -/
noncomputable def i8Psi4s106dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s106N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s106N0 (i8Psi4s106dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽106⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s106N1 (x : ℝ) : ℝ :=
    (108 - 4 / 3 * π ^ 2) +
    (108 - 4 / 3 * π ^ 2) * hpl [zero] x +
    (-16) * hpl [negOne, zero] x +
    (92 - 2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (-32) * hpl [negOne, zero, zero] x +
    (-16) * hpl [zero, negOne, zero] x +
    (60) * hpl [zero, zero, zero] x +
    (-24) * hpl [negOne, zero, zero, zero] x +
    (-16) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x +
    (24) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s106N1`. -/
noncomputable def i8Psi4s106dN1 (x : ℝ) : ℝ :=
    0 +
    (108 - 4 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-16) * (negOne.kernel x * hpl [zero] x) +
    (92 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (-32) * (negOne.kernel x * hpl [zero, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, zero] x) +
    (60) * (zero.kernel x * hpl [zero, zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (24) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s106N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s106N1 (i8Psi4s106dN1 x) x := by
  unfold i8Psi4s106N1 i8Psi4s106dN1
  exact (((((((((((hasDerivAt_const x (108 - 4 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (108 - 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (92 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (60))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (24)))

/-- The part of `ξ² Ψ₄⁽106⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s106N2 (x : ℝ) : ℝ :=
    (13) * hpl [negOne, zero] x +
    (32 + 2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (-84) * hpl [negOne, zero, zero] x +
    (2 * π ^ 2) * hpl [zero, zero, zero] x +
    (36) * hpl [negOne, zero, zero, zero] x +
    (16) * hpl [zero, negOne, zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x +
    (-60) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s106N2`. -/
noncomputable def i8Psi4s106dN2 (x : ℝ) : ℝ :=
    (13) * (negOne.kernel x * hpl [zero] x) +
    (32 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (-84) * (negOne.kernel x * hpl [zero, zero] x) +
    (2 * π ^ 2) * (zero.kernel x * hpl [zero, zero] x) +
    (36) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-60) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s106N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s106N2 (i8Psi4s106dN2 x) x := by
  unfold i8Psi4s106N2 i8Psi4s106dN2
  exact (((((((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (13)).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (32 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-84))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-60)))

/-- The part of `ξ² Ψ₄⁽106⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s106N3 (x : ℝ) : ℝ :=
    (145 + 8 / 3 * π ^ 2) +
    (-145 - 8 / 3 * π ^ 2) * hpl [zero] x +
    (32) * hpl [negOne, zero] x +
    (132 + 2 * π ^ 2) * hpl [zero, zero] x +
    (-64) * hpl [negOne, zero, zero] x +
    (-32) * hpl [zero, negOne, zero] x +
    (-48) * hpl [zero, zero, zero] x +
    (72) * hpl [negOne, zero, zero, zero] x +
    (48) * hpl [zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, negOne, zero] x +
    (-72) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s106N3`. -/
noncomputable def i8Psi4s106dN3 (x : ℝ) : ℝ :=
    0 +
    (-145 - 8 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (32) * (negOne.kernel x * hpl [zero] x) +
    (132 + 2 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (-64) * (negOne.kernel x * hpl [zero, zero] x) +
    (-32) * (zero.kernel x * hpl [negOne, zero] x) +
    (-48) * (zero.kernel x * hpl [zero, zero] x) +
    (72) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (48) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-72) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s106N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s106N3 (i8Psi4s106dN3 x) x := by
  unfold i8Psi4s106N3 i8Psi4s106dN3
  exact (((((((((((hasDerivAt_const x (145 + 8 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-145 - 8 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (132 + 2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-64))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (72))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-72)))

/-- The part of `ξ² Ψ₄⁽106⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s106N4 (x : ℝ) : ℝ :=
    (11 + π ^ 2 / 4) +
    (-22 - π ^ 2 / 2) * hpl [zero] x +
    (3) * hpl [negOne, zero] x +
    (25 + π ^ 2 / 3) * hpl [zero, zero] x +
    (-12) * hpl [negOne, zero, zero] x +
    (-6) * hpl [zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero] x +
    (12) * hpl [negOne, zero, zero, zero] x +
    (8) * hpl [zero, negOne, zero, zero] x +
    (4) * hpl [zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s106N4`. -/
noncomputable def i8Psi4s106dN4 (x : ℝ) : ℝ :=
    0 +
    (-22 - π ^ 2 / 2) * (zero.kernel x * hpl [] x) +
    (3) * (negOne.kernel x * hpl [zero] x) +
    (25 + π ^ 2 / 3) * (zero.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero] x) +
    (-6) * (zero.kernel x * hpl [negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero] x) +
    (12) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s106N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s106N4 (i8Psi4s106dN4 x) x := by
  unfold i8Psi4s106N4 i8Psi4s106dN4
  exact (((((((((((hasDerivAt_const x (11 + π ^ 2 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-22 - π ^ 2 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (25 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-12)))

/-- The part of `Ψ₄⁽106⁾` with constant coefficients. -/
noncomputable def i8Psi4s106W (x : ℝ) : ℝ :=
    (72) * hpl [zero, negOne, zero, zero, zero] x +
    (48) * hpl [zero, zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, zero, negOne, zero] x +
    (-72) * hpl [zero, zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s106W`. -/
noncomputable def i8Psi4s106dW (x : ℝ) : ℝ :=
    (72) * (zero.kernel x * hpl [negOne, zero, zero, zero] x) +
    (48) * (zero.kernel x * hpl [zero, negOne, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, zero, negOne, zero] x) +
    (-72) * (zero.kernel x * hpl [zero, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s106W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s106W (i8Psi4s106dW x) x := by
  unfold i8Psi4s106W i8Psi4s106dW
  exact (((((hasDerivAt_hpl_cons zero [negOne, zero, zero, zero] hx).const_mul (72)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, zero] hx).const_mul (-72)))

/-- The piece `Ψ₄⁽106⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s106 (x : ℝ) : ℝ :=
  (i8Psi4s106N0 x + x * i8Psi4s106N1 x + x ^ 2 * i8Psi4s106N2 x + x ^ 3 * i8Psi4s106N3 x +
    x ^ 4 * i8Psi4s106N4 x) / x ^ 2 + i8Psi4s106W x

/-- The derivative of `Ψ₄⁽106⁾`. -/
noncomputable def i8Psi4s106D (x : ℝ) : ℝ :=
  ((i8Psi4s106dN0 x + (i8Psi4s106N1 x + x * i8Psi4s106dN1 x) + (2 * x * i8Psi4s106N2 x +
    x ^ 2 * i8Psi4s106dN2 x) + (3 * x ^ 2 * i8Psi4s106N3 x + x ^ 3 * i8Psi4s106dN3 x) +
    (4 * x ^ 3 * i8Psi4s106N4 x + x ^ 4 * i8Psi4s106dN4 x)) * x ^ 2 - (i8Psi4s106N0 x +
    x * i8Psi4s106N1 x + x ^ 2 * i8Psi4s106N2 x + x ^ 3 * i8Psi4s106N3 x +
    x ^ 4 * i8Psi4s106N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s106dW x

theorem hasDerivAt_i8Psi4s106 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s106 (i8Psi4s106D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s106N0 hx).add (X.mul (hasDerivAt_i8Psi4s106N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s106N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s106N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s106N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s106W hx)
  unfold i8Psi4s106
  refine e.congr_deriv ?_
  unfold i8Psi4s106D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 106 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s106 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * (2 + Real.log x * (1 + x) / (1 -
    x)) * i13Be2x x * (x / (1 - x))

/-- `p₄⁽106⁾` written over words. -/
noncomputable def i8P4w106 (x : ℝ) : ℝ :=
    (16 - 16 * x - 2 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x) * hpl [zero] x +
    ((32 - 32 * x ^ 2 - 2 / 3 * π ^ 2 - 4 / 3 * π ^ 2 * x - 2 / 3 * π ^ 2 * x ^ 2) / ((1 -
      x))) * hpl [zero, zero] x +
    (-16 - 16 * x) * hpl [negOne, zero, zero] x +
    (-8 - 8 * x) * hpl [zero, negOne, zero] x +
    ((36 + 12 * x ^ 2 + 48 * x) / ((1 - x))) * hpl [zero, zero, zero] x +
    ((-24 - 48 * x - 24 * x ^ 2) / ((1 - x))) * hpl [negOne, zero, zero, zero] x +
    ((-16 - 32 * x - 16 * x ^ 2) / ((1 - x))) * hpl [zero, negOne, zero, zero] x +
    ((-8 - 16 * x - 8 * x ^ 2) / ((1 - x))) * hpl [zero, zero, negOne, zero] x +
    ((24 + 24 * x ^ 2 + 48 * x) / ((1 - x))) * hpl [zero, zero, zero, zero] x

theorem i8P4s106_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s106 x = i8P4w106 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s106 i8P4w106 i13Be2x
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0m0 hx, i13hw_m00 hx, i13hw_0000, i13hw_00m0 hx,
    i13hw_0m00 hx, i13hw_m000 hx, i13_Li₂_neg_eq hx, i13_log_one_add_eq hx]
  field_simp
  generalize hpl [zero, negOne, negOne, negOne, negOne] x = v0 at *
  generalize hpl [zero, negOne, negOne, negOne, one] x = v1 at *
  generalize hpl [zero, negOne, negOne, zero, one] x = v2 at *
  generalize hpl [zero, negOne, negOne, one, negOne] x = v3 at *
  generalize hpl [zero, negOne, negOne, one, one] x = v4 at *
  generalize hpl [zero, negOne, zero, negOne, negOne] x = v5 at *
  generalize hpl [zero, negOne, zero, negOne, one] x = v6 at *
  generalize hpl [zero, negOne, zero, zero, zero] x = v7 at *
  generalize hpl [zero, negOne, zero, one, negOne] x = v8 at *
  generalize hpl [zero, negOne, zero, one, one] x = v9 at *
  generalize hpl [zero, negOne, one, negOne, negOne] x = v10 at *
  generalize hpl [zero, negOne, one, negOne, one] x = v11 at *
  generalize hpl [zero, negOne, one, zero, one] x = v12 at *
  generalize hpl [zero, negOne, one, one, negOne] x = v13 at *
  generalize hpl [zero, negOne, one, one, one] x = v14 at *
  generalize hpl [zero, zero, negOne, negOne, negOne] x = v15 at *
  generalize hpl [zero, zero, negOne, negOne, one] x = v16 at *
  generalize hpl [zero, zero, negOne, zero, negOne] x = v17 at *
  generalize hpl [zero, zero, negOne, zero, zero] x = v18 at *
  generalize hpl [zero, zero, negOne, zero, one] x = v19 at *
  generalize hpl [zero, zero, negOne, one, negOne] x = v20 at *
  generalize hpl [zero, zero, negOne, one, one] x = v21 at *
  generalize hpl [zero, zero, zero, negOne, negOne] x = v22 at *
  generalize hpl [zero, zero, zero, negOne, zero] x = v23 at *
  generalize hpl [zero, zero, zero, negOne, one] x = v24 at *
  generalize hpl [zero, zero, zero, zero, negOne] x = v25 at *
  generalize hpl [zero, zero, zero, zero, zero] x = v26 at *
  generalize hpl [zero, zero, zero, zero, one] x = v27 at *
  generalize hpl [zero, zero, zero, one, negOne] x = v28 at *
  generalize hpl [zero, zero, zero, one, one] x = v29 at *
  generalize hpl [zero, zero, one, negOne, negOne] x = v30 at *
  generalize hpl [zero, zero, one, negOne, one] x = v31 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v32 at *
  generalize hpl [zero, zero, one, zero, one] x = v33 at *
  generalize hpl [zero, zero, one, one, negOne] x = v34 at *
  generalize hpl [zero, zero, one, one, one] x = v35 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v36 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v37 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v38 at *
  generalize hpl [zero, one, negOne, one, one] x = v39 at *
  generalize hpl [zero, one, zero, one, negOne] x = v40 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v41 at *
  generalize hpl [zero, one, one, negOne, one] x = v42 at *
  generalize hpl [zero, one, one, one, negOne] x = v43 at *
  generalize hpl [zero, one, one, one, one] x = v44 at *
  generalize hpl [negOne, negOne, one, one] x = v45 at *
  generalize hpl [negOne, zero, zero, zero] x = v46 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v47 at *
  generalize hpl [zero, negOne, negOne, one] x = v48 at *
  generalize hpl [zero, negOne, zero, zero] x = v49 at *
  generalize hpl [zero, negOne, zero, one] x = v50 at *
  generalize hpl [zero, negOne, one, negOne] x = v51 at *
  generalize hpl [zero, negOne, one, one] x = v52 at *
  generalize hpl [zero, zero, negOne, negOne] x = v53 at *
  generalize hpl [zero, zero, negOne, zero] x = v54 at *
  generalize hpl [zero, zero, negOne, one] x = v55 at *
  generalize hpl [zero, zero, zero, negOne] x = v56 at *
  generalize hpl [zero, zero, zero, zero] x = v57 at *
  generalize hpl [zero, zero, zero, one] x = v58 at *
  generalize hpl [zero, zero, one, negOne] x = v59 at *
  generalize hpl [zero, zero, one, one] x = v60 at *
  generalize hpl [zero, one, negOne, negOne] x = v61 at *
  generalize hpl [zero, one, negOne, one] x = v62 at *
  generalize hpl [zero, one, one, negOne] x = v63 at *
  generalize hpl [zero, one, one, one] x = v64 at *
  generalize hpl [negOne, negOne, one] x = v65 at *
  generalize hpl [negOne, zero, zero] x = v66 at *
  generalize hpl [negOne, one, one] x = v67 at *
  generalize hpl [zero, negOne, negOne] x = v68 at *
  generalize hpl [zero, negOne, zero] x = v69 at *
  generalize hpl [zero, negOne, one] x = v70 at *
  generalize hpl [zero, zero, negOne] x = v71 at *
  generalize hpl [zero, zero, zero] x = v72 at *
  generalize hpl [zero, zero, one] x = v73 at *
  generalize hpl [zero, one, negOne] x = v74 at *
  generalize hpl [zero, one, one] x = v75 at *
  generalize hpl [negOne, zero] x = v76 at *
  generalize hpl [negOne, one] x = v77 at *
  generalize hpl [zero, negOne] x = v78 at *
  generalize hpl [zero, zero] x = v79 at *
  generalize hpl [zero, one] x = v80 at *
  generalize hpl [negOne] x = v81 at *
  generalize hpl [zero] x = v82 at *
  generalize hpl [one] x = v83 at *
  ring

/-- **`(Ψ₄⁽106⁾)'(ξ) ξ' = p₄⁽106⁾`**, in terms of `ξ`. -/
theorem i8Psi4s106D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s106D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s106 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s106_eq_w hx]
  unfold i8Psi4s106D i8Psi4s106N0 i8Psi4s106N1 i8Psi4s106N2 i8Psi4s106N3 i8Psi4s106N4 i8Psi4s106dN0
    i8Psi4s106dN1 i8Psi4s106dN2 i8Psi4s106dN3 i8Psi4s106dN4 i8Psi4s106dW i8P4w106
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, zero, zero] x = v1 at *
  generalize hpl [zero, zero, zero, negOne, zero] x = v2 at *
  generalize hpl [zero, zero, zero, zero, zero] x = v3 at *
  generalize hpl [negOne, zero, zero, zero] x = v4 at *
  generalize hpl [zero, negOne, zero, zero] x = v5 at *
  generalize hpl [zero, zero, negOne, zero] x = v6 at *
  generalize hpl [zero, zero, zero, zero] x = v7 at *
  generalize hpl [negOne, zero, zero] x = v8 at *
  generalize hpl [zero, negOne, zero] x = v9 at *
  generalize hpl [zero, zero, zero] x = v10 at *
  generalize hpl [negOne, zero] x = v11 at *
  generalize hpl [zero, zero] x = v12 at *
  generalize hpl [zero] x = v13 at *
  ring

end QED.ThreeLoopD
