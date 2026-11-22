/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P16

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 78 to 79

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s78`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s78D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s78`, `QED.ThreeLoopD.i8Psi4s78D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽78⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s78N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s78N0`. -/
noncomputable def i8Psi4s78dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s78N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s78N0 (i8Psi4s78dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽78⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s78N1 (x : ℝ) : ℝ :=
    (28 - 2 / 3 * π ^ 2) * hpl [one] x +
    (12) * hpl [zero, one] x +
    (12) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (-8) * hpl [one, negOne, zero] x +
    (4) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s78N1`. -/
noncomputable def i8Psi4s78dN1 (x : ℝ) : ℝ :=
    (28 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (12) * (zero.kernel x * hpl [one] x) +
    (12) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s78N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s78N1 (i8Psi4s78dN1 x) x := by
  unfold i8Psi4s78N1 i8Psi4s78dN1
  exact ((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (28 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽78⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s78N2 (x : ℝ) : ℝ :=
    (-28 + 2 / 3 * π ^ 2) * hpl [zero] x +
    (-51 / 2 + 5 / 3 * π ^ 2) * hpl [one] x +
    (-10) * hpl [negOne, zero] x +
    (-12) * hpl [zero, zero] x +
    (16 + 2 / 3 * π ^ 2) * hpl [zero, one] x +
    (-25) * hpl [one, zero] x +
    (-12) * hpl [negOne, zero, one] x +
    (-12) * hpl [negOne, one, zero] x +
    (20) * hpl [one, negOne, zero] x +
    (-10) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s78N2`. -/
noncomputable def i8Psi4s78dN2 (x : ℝ) : ℝ :=
    (-28 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-51 / 2 + 5 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (-10) * (negOne.kernel x * hpl [zero] x) +
    (-12) * (zero.kernel x * hpl [zero] x) +
    (16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [one] x) +
    (-25) * (one.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, one] x) +
    (-12) * (negOne.kernel x * hpl [one, zero] x) +
    (20) * (one.kernel x * hpl [negOne, zero] x) +
    (-10) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s78N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s78N2 (i8Psi4s78dN2 x) x := by
  unfold i8Psi4s78N2 i8Psi4s78dN2
  exact (((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-28 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-51 / 2 + 5 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (16 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-25))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-10)))

/-- The part of `ξ² Ψ₄⁽78⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s78N3 (x : ℝ) : ℝ :=
    (-39 / 2 - π ^ 2) +
    (17) * hpl [zero] x +
    (8 - 2 / 3 * π ^ 2) * hpl [one] x +
    (-12) * hpl [negOne, zero] x +
    (6) * hpl [zero, zero] x +
    (8) * hpl [zero, one] x +
    (8) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (-8) * hpl [one, negOne, zero] x +
    (4) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s78N3`. -/
noncomputable def i8Psi4s78dN3 (x : ℝ) : ℝ :=
    0 +
    (17) * (zero.kernel x * hpl [] x) +
    (8 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (-12) * (negOne.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s78N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s78N3 (i8Psi4s78dN3 x) x := by
  unfold i8Psi4s78N3 i8Psi4s78dN3
  exact (((((((((((((hasDerivAt_const x (-39 / 2 - π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (17))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (8 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽78⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s78N4 (x : ℝ) : ℝ :=
    (-27 / 4 - π ^ 2 / 6) +
    (3) * hpl [zero] x +
    (-21 / 2 - π ^ 2 / 3) * hpl [one] x +
    (-2) * hpl [negOne, zero] x +
    (1) * hpl [zero, zero] x +
    (5) * hpl [zero, one] x +
    (5) * hpl [one, zero] x +
    (-4) * hpl [negOne, zero, one] x +
    (-4) * hpl [negOne, one, zero] x +
    (2) * hpl [zero, zero, one] x +
    (2) * hpl [zero, one, zero] x +
    (-4) * hpl [one, negOne, zero] x +
    (2) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s78N4`. -/
noncomputable def i8Psi4s78dN4 (x : ℝ) : ℝ :=
    0 +
    (3) * (zero.kernel x * hpl [] x) +
    (-21 / 2 - π ^ 2 / 3) * (one.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (5) * (zero.kernel x * hpl [one] x) +
    (5) * (one.kernel x * hpl [zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, one] x) +
    (-4) * (negOne.kernel x * hpl [one, zero] x) +
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (2) * (zero.kernel x * hpl [one, zero] x) +
    (-4) * (one.kernel x * hpl [negOne, zero] x) +
    (2) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s78N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s78N4 (i8Psi4s78dN4 x) x := by
  unfold i8Psi4s78N4 i8Psi4s78dN4
  exact (((((((((((((hasDerivAt_const x (-27 / 4 - π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-21 / 2 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (2)))

/-- The part of `Ψ₄⁽78⁾` with constant coefficients. -/
noncomputable def i8Psi4s78W (x : ℝ) : ℝ :=
    (8) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, negOne, zero, one] x +
    (8) * hpl [zero, negOne, one, zero] x +
    (-4) * hpl [zero, zero, zero, one] x +
    (-4) * hpl [zero, zero, one, zero] x +
    (8) * hpl [zero, one, negOne, zero] x +
    (-4) * hpl [zero, one, zero, zero] x

/-- The derivative of `i8Psi4s78W`. -/
noncomputable def i8Psi4s78dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (8) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-4) * (zero.kernel x * hpl [zero, one, zero] x) +
    (8) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s78W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s78W (i8Psi4s78dW x) x := by
  unfold i8Psi4s78W i8Psi4s78dW
  exact (((((((((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-4)))

/-- The piece `Ψ₄⁽78⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s78 (x : ℝ) : ℝ :=
  (i8Psi4s78N0 x + x * i8Psi4s78N1 x + x ^ 2 * i8Psi4s78N2 x + x ^ 3 * i8Psi4s78N3 x +
    x ^ 4 * i8Psi4s78N4 x) / x ^ 2 + i8Psi4s78W x

/-- The derivative of `Ψ₄⁽78⁾`. -/
noncomputable def i8Psi4s78D (x : ℝ) : ℝ :=
  ((i8Psi4s78dN0 x + (i8Psi4s78N1 x + x * i8Psi4s78dN1 x) + (2 * x * i8Psi4s78N2 x +
    x ^ 2 * i8Psi4s78dN2 x) + (3 * x ^ 2 * i8Psi4s78N3 x + x ^ 3 * i8Psi4s78dN3 x) +
    (4 * x ^ 3 * i8Psi4s78N4 x + x ^ 4 * i8Psi4s78dN4 x)) * x ^ 2 - (i8Psi4s78N0 x +
    x * i8Psi4s78N1 x + x ^ 2 * i8Psi4s78N2 x + x ^ 3 * i8Psi4s78N3 x +
    x ^ 4 * i8Psi4s78N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s78dW x

theorem hasDerivAt_i8Psi4s78 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s78 (i8Psi4s78D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s78N0 hx).add (X.mul (hasDerivAt_i8Psi4s78N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s78N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s78N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s78N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s78W hx)
  unfold i8Psi4s78
  refine e.congr_deriv ?_
  unfold i8Psi4s78D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 78 of `p₄` in `ξ`: from `t B2 A1 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s78 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * i13Be2x x * ((1 + x) / (1 - x) * (x / (1 + x))))

/-- `p₄⁽78⁾` written over words. -/
noncomputable def i8P4w78 (x : ℝ) : ℝ :=
    (16 - 16 * x - 2 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x) * hpl [one] x +
    (8 + 8 * x) * hpl [zero, one] x +
    (8 + 8 * x) * hpl [one, zero] x +
    (-8 - 8 * x) * hpl [negOne, zero, one] x +
    (-8 - 8 * x) * hpl [negOne, one, zero] x +
    (4 + 4 * x) * hpl [zero, zero, one] x +
    (4 + 4 * x) * hpl [zero, one, zero] x +
    (-8 - 8 * x) * hpl [one, negOne, zero] x +
    (4 + 4 * x) * hpl [one, zero, zero] x

theorem i8P4s78_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s78 x = i8P4w78 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s78 i8P4w78 i13Be2x
  simp only [i13hw_10 hx, i13hw_010 hx, i13hw_100 hx, i13hw_1m0 hx, i13hw_m01 hx, i13hw_m10 hx,
    i13_Li₂_neg_eq hx, i13_log_one_add_eq hx, i13_log_one_sub_eq hx]
  field_simp
  generalize hpl [zero, negOne, negOne, negOne, negOne] x = v0 at *
  generalize hpl [zero, negOne, negOne, negOne, one] x = v1 at *
  generalize hpl [zero, negOne, negOne, zero, one] x = v2 at *
  generalize hpl [zero, negOne, negOne, one, negOne] x = v3 at *
  generalize hpl [zero, negOne, negOne, one, one] x = v4 at *
  generalize hpl [zero, negOne, zero, negOne, negOne] x = v5 at *
  generalize hpl [zero, negOne, zero, negOne, one] x = v6 at *
  generalize hpl [zero, negOne, zero, one, negOne] x = v7 at *
  generalize hpl [zero, negOne, zero, one, one] x = v8 at *
  generalize hpl [zero, negOne, one, negOne, negOne] x = v9 at *
  generalize hpl [zero, negOne, one, negOne, one] x = v10 at *
  generalize hpl [zero, negOne, one, zero, one] x = v11 at *
  generalize hpl [zero, negOne, one, one, negOne] x = v12 at *
  generalize hpl [zero, negOne, one, one, one] x = v13 at *
  generalize hpl [zero, zero, negOne, negOne, negOne] x = v14 at *
  generalize hpl [zero, zero, negOne, negOne, one] x = v15 at *
  generalize hpl [zero, zero, negOne, zero, negOne] x = v16 at *
  generalize hpl [zero, zero, negOne, zero, one] x = v17 at *
  generalize hpl [zero, zero, negOne, one, negOne] x = v18 at *
  generalize hpl [zero, zero, negOne, one, one] x = v19 at *
  generalize hpl [zero, zero, zero, negOne, negOne] x = v20 at *
  generalize hpl [zero, zero, zero, negOne, one] x = v21 at *
  generalize hpl [zero, zero, zero, zero, negOne] x = v22 at *
  generalize hpl [zero, zero, zero, zero, one] x = v23 at *
  generalize hpl [zero, zero, zero, one, negOne] x = v24 at *
  generalize hpl [zero, zero, zero, one, one] x = v25 at *
  generalize hpl [zero, zero, one, negOne, negOne] x = v26 at *
  generalize hpl [zero, zero, one, negOne, one] x = v27 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v28 at *
  generalize hpl [zero, zero, one, zero, one] x = v29 at *
  generalize hpl [zero, zero, one, one, negOne] x = v30 at *
  generalize hpl [zero, zero, one, one, one] x = v31 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v32 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v33 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v34 at *
  generalize hpl [zero, one, negOne, one, one] x = v35 at *
  generalize hpl [zero, one, zero, one, negOne] x = v36 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v37 at *
  generalize hpl [zero, one, one, negOne, one] x = v38 at *
  generalize hpl [zero, one, one, one, negOne] x = v39 at *
  generalize hpl [zero, one, one, one, one] x = v40 at *
  generalize hpl [negOne, negOne, one, one] x = v41 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v42 at *
  generalize hpl [zero, negOne, negOne, one] x = v43 at *
  generalize hpl [zero, negOne, zero, one] x = v44 at *
  generalize hpl [zero, negOne, one, negOne] x = v45 at *
  generalize hpl [zero, negOne, one, zero] x = v46 at *
  generalize hpl [zero, negOne, one, one] x = v47 at *
  generalize hpl [zero, zero, negOne, negOne] x = v48 at *
  generalize hpl [zero, zero, negOne, one] x = v49 at *
  generalize hpl [zero, zero, zero, negOne] x = v50 at *
  generalize hpl [zero, zero, zero, one] x = v51 at *
  generalize hpl [zero, zero, one, negOne] x = v52 at *
  generalize hpl [zero, zero, one, zero] x = v53 at *
  generalize hpl [zero, zero, one, one] x = v54 at *
  generalize hpl [zero, one, negOne, negOne] x = v55 at *
  generalize hpl [zero, one, negOne, zero] x = v56 at *
  generalize hpl [zero, one, negOne, one] x = v57 at *
  generalize hpl [zero, one, zero, zero] x = v58 at *
  generalize hpl [zero, one, one, negOne] x = v59 at *
  generalize hpl [zero, one, one, one] x = v60 at *
  generalize hpl [negOne, negOne, one] x = v61 at *
  generalize hpl [negOne, zero, one] x = v62 at *
  generalize hpl [negOne, one, zero] x = v63 at *
  generalize hpl [negOne, one, one] x = v64 at *
  generalize hpl [zero, negOne, negOne] x = v65 at *
  generalize hpl [zero, negOne, zero] x = v66 at *
  generalize hpl [zero, negOne, one] x = v67 at *
  generalize hpl [zero, zero, negOne] x = v68 at *
  generalize hpl [zero, zero, zero] x = v69 at *
  generalize hpl [zero, zero, one] x = v70 at *
  generalize hpl [zero, one, negOne] x = v71 at *
  generalize hpl [zero, one, zero] x = v72 at *
  generalize hpl [zero, one, one] x = v73 at *
  generalize hpl [one, negOne, zero] x = v74 at *
  generalize hpl [one, zero, zero] x = v75 at *
  generalize hpl [negOne, zero] x = v76 at *
  generalize hpl [negOne, one] x = v77 at *
  generalize hpl [zero, negOne] x = v78 at *
  generalize hpl [zero, zero] x = v79 at *
  generalize hpl [zero, one] x = v80 at *
  generalize hpl [one, zero] x = v81 at *
  generalize hpl [negOne] x = v82 at *
  generalize hpl [zero] x = v83 at *
  generalize hpl [one] x = v84 at *
  ring

/-- **`(Ψ₄⁽78⁾)'(ξ) ξ' = p₄⁽78⁾`**, in terms of `ξ`. -/
theorem i8Psi4s78D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s78D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s78 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s78_eq_w hx]
  unfold i8Psi4s78D i8Psi4s78N0 i8Psi4s78N1 i8Psi4s78N2 i8Psi4s78N3 i8Psi4s78N4 i8Psi4s78dN0
    i8Psi4s78dN1 i8Psi4s78dN2 i8Psi4s78dN3 i8Psi4s78dN4 i8Psi4s78dW i8P4w78
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, zero, one] x = v0 at *
  generalize hpl [zero, negOne, one, zero] x = v1 at *
  generalize hpl [zero, zero, zero, one] x = v2 at *
  generalize hpl [zero, zero, one, zero] x = v3 at *
  generalize hpl [zero, one, negOne, zero] x = v4 at *
  generalize hpl [zero, one, zero, zero] x = v5 at *
  generalize hpl [negOne, zero, one] x = v6 at *
  generalize hpl [negOne, one, zero] x = v7 at *
  generalize hpl [zero, negOne, zero] x = v8 at *
  generalize hpl [zero, zero, zero] x = v9 at *
  generalize hpl [zero, zero, one] x = v10 at *
  generalize hpl [zero, one, zero] x = v11 at *
  generalize hpl [one, negOne, zero] x = v12 at *
  generalize hpl [one, zero, zero] x = v13 at *
  generalize hpl [negOne, zero] x = v14 at *
  generalize hpl [zero, zero] x = v15 at *
  generalize hpl [zero, one] x = v16 at *
  generalize hpl [one, zero] x = v17 at *
  generalize hpl [zero] x = v18 at *
  generalize hpl [one] x = v19 at *
  ring

/-- The part of `ξ² Ψ₄⁽79⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s79N0 (x : ℝ) : ℝ :=
    (-8 + π ^ 2 / 3) * hpl [negOne, one] x +
    (-8 + π ^ 2 / 3) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s79N0`. -/
noncomputable def i8Psi4s79dN0 (x : ℝ) : ℝ :=
    (-8 + π ^ 2 / 3) * (negOne.kernel x * hpl [one] x) +
    (-8 + π ^ 2 / 3) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s79N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s79N0 (i8Psi4s79dN0 x) x := by
  unfold i8Psi4s79N0 i8Psi4s79dN0
  exact (((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-8 + π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-8 + π ^ 2 / 3)))

/-- The part of `ξ² Ψ₄⁽79⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s79N1 (x : ℝ) : ℝ :=
    (-8 + π ^ 2 / 3) * hpl [negOne] x +
    (-8 + π ^ 2 / 3) * hpl [one] x +
    (4 / 3 * π ^ 2) * hpl [negOne, one] x +
    (4 / 3 * π ^ 2) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s79N1`. -/
noncomputable def i8Psi4s79dN1 (x : ℝ) : ℝ :=
    (-8 + π ^ 2 / 3) * (negOne.kernel x * hpl [] x) +
    (-8 + π ^ 2 / 3) * (one.kernel x * hpl [] x) +
    (4 / 3 * π ^ 2) * (negOne.kernel x * hpl [one] x) +
    (4 / 3 * π ^ 2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s79N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s79N1 (i8Psi4s79dN1 x) x := by
  unfold i8Psi4s79N1 i8Psi4s79dN1
  exact (((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-8 + π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-8 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (4 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽79⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s79N2 (x : ℝ) : ℝ :=
    (-4 + 11 / 6 * π ^ 2) * hpl [negOne] x +
    (4 + 5 / 6 * π ^ 2) * hpl [one] x +
    (2 * π ^ 2) * hpl [negOne, one] x +
    (-10 / 3 * π ^ 2) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s79N2`. -/
noncomputable def i8Psi4s79dN2 (x : ℝ) : ℝ :=
    (-4 + 11 / 6 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (4 + 5 / 6 * π ^ 2) * (one.kernel x * hpl [] x) +
    (2 * π ^ 2) * (negOne.kernel x * hpl [one] x) +
    (-10 / 3 * π ^ 2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s79N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s79N2 (i8Psi4s79dN2 x) x := by
  unfold i8Psi4s79N2 i8Psi4s79dN2
  exact (((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-4 + 11 / 6 * π ^ 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (4 + 5 / 6 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-10 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽79⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s79N3 (x : ℝ) : ℝ :=
    (-8 / 3 * π ^ 2) +
    (8 + 5 / 3 * π ^ 2) * hpl [negOne] x +
    (8 - π ^ 2) * hpl [one] x +
    (4 / 3 * π ^ 2) * hpl [negOne, one] x +
    (4 / 3 * π ^ 2) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s79N3`. -/
noncomputable def i8Psi4s79dN3 (x : ℝ) : ℝ :=
    0 +
    (8 + 5 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (8 - π ^ 2) * (one.kernel x * hpl [] x) +
    (4 / 3 * π ^ 2) * (negOne.kernel x * hpl [one] x) +
    (4 / 3 * π ^ 2) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s79N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s79N3 (i8Psi4s79dN3 x) x := by
  unfold i8Psi4s79N3 i8Psi4s79dN3
  exact (((((hasDerivAt_const x (-8 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (8 + 5 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (8 - π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (4 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽79⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s79N4 (x : ℝ) : ℝ :=
    (-4 - π ^ 2 / 6) +
    (4 + π ^ 2 / 6) * hpl [negOne] x +
    (-4 - π ^ 2 / 6) * hpl [one] x +
    (8 + π ^ 2 / 3) * hpl [negOne, one] x +
    (8 + π ^ 2 / 3) * hpl [one, negOne] x

/-- The derivative of `i8Psi4s79N4`. -/
noncomputable def i8Psi4s79dN4 (x : ℝ) : ℝ :=
    0 +
    (4 + π ^ 2 / 6) * (negOne.kernel x * hpl [] x) +
    (-4 - π ^ 2 / 6) * (one.kernel x * hpl [] x) +
    (8 + π ^ 2 / 3) * (negOne.kernel x * hpl [one] x) +
    (8 + π ^ 2 / 3) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s79N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s79N4 (i8Psi4s79dN4 x) x := by
  unfold i8Psi4s79N4 i8Psi4s79dN4
  exact (((((hasDerivAt_const x (-4 - π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (8 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (8 + π ^ 2 / 3)))

/-- The part of `Ψ₄⁽79⁾` with constant coefficients. -/
noncomputable def i8Psi4s79W (x : ℝ) : ℝ :=
    (16 - 2 / 3 * π ^ 2) * hpl [zero] x +
    (8 - 5 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (-8 - π ^ 2) * hpl [zero, one] x +
    (-32) * hpl [zero, negOne, one] x +
    (-32) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi4s79W`. -/
noncomputable def i8Psi4s79dW (x : ℝ) : ℝ :=
    (16 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (8 - 5 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (-8 - π ^ 2) * (zero.kernel x * hpl [one] x) +
    (-32) * (zero.kernel x * hpl [negOne, one] x) +
    (-32) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s79W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s79W (i8Psi4s79dW x) x := by
  unfold i8Psi4s79W i8Psi4s79dW
  exact ((((((hasDerivAt_hpl_cons zero [] hx).const_mul (16 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (8 - 5 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-8 - π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-32)))

/-- The piece `Ψ₄⁽79⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s79 (x : ℝ) : ℝ :=
  (i8Psi4s79N0 x + x * i8Psi4s79N1 x + x ^ 2 * i8Psi4s79N2 x + x ^ 3 * i8Psi4s79N3 x +
    x ^ 4 * i8Psi4s79N4 x) / x ^ 2 + i8Psi4s79W x

/-- The derivative of `Ψ₄⁽79⁾`. -/
noncomputable def i8Psi4s79D (x : ℝ) : ℝ :=
  ((i8Psi4s79dN0 x + (i8Psi4s79N1 x + x * i8Psi4s79dN1 x) + (2 * x * i8Psi4s79N2 x +
    x ^ 2 * i8Psi4s79dN2 x) + (3 * x ^ 2 * i8Psi4s79N3 x + x ^ 3 * i8Psi4s79dN3 x) +
    (4 * x ^ 3 * i8Psi4s79N4 x + x ^ 4 * i8Psi4s79dN4 x)) * x ^ 2 - (i8Psi4s79N0 x +
    x * i8Psi4s79N1 x + x ^ 2 * i8Psi4s79N2 x + x ^ 3 * i8Psi4s79N3 x +
    x ^ 4 * i8Psi4s79N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s79dW x

theorem hasDerivAt_i8Psi4s79 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s79 (i8Psi4s79D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s79N0 hx).add (X.mul (hasDerivAt_i8Psi4s79N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s79N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s79N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s79N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s79W hx)
  unfold i8Psi4s79
  refine e.congr_deriv ?_
  unfold i8Psi4s79D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 79 of `p₄` in `ξ`: from `t B2 A1 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s79 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 - x) * ((24 + ((-1) * π ^ 2) +
    ((-24) * x) + ((-1) * π ^ 2 * x)) / (6 + (6 * x)))) * ((1 + x) / (1 - x) * (-hpl [negOne] x)))

/-- `p₄⁽79⁾` written over words. -/
noncomputable def i8P4w79 (x : ℝ) : ℝ :=
    ((-16 + 16 * x ^ 2 + 2 / 3 * π ^ 2 + 2 / 3 * π ^ 2 * x ^ 2 +
      4 / 3 * π ^ 2 * x) / (x)) * hpl [negOne, one] x +
    ((-16 + 16 * x ^ 2 + 2 / 3 * π ^ 2 + 2 / 3 * π ^ 2 * x ^ 2 +
      4 / 3 * π ^ 2 * x) / (x)) * hpl [one, negOne] x

theorem i8P4s79_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s79 x = i8P4w79 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s79 i8P4w79
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [negOne] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) (((-16 + 16 * x ^ 2 + 2 / 3 * π ^ 2 + 2 / 3 * π ^ 2 * x ^ 2 +
    4 / 3 * π ^ 2 * x) / (x))) * e0
  field_simp
  generalize hpl [negOne, one] x = v0 at *
  generalize hpl [one, negOne] x = v1 at *
  generalize hpl [negOne] x = v2 at *
  generalize hpl [one] x = v3 at *
  ring

/-- **`(Ψ₄⁽79⁾)'(ξ) ξ' = p₄⁽79⁾`**, in terms of `ξ`. -/
theorem i8Psi4s79D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s79D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s79 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s79_eq_w hx]
  unfold i8Psi4s79D i8Psi4s79N0 i8Psi4s79N1 i8Psi4s79N2 i8Psi4s79N3 i8Psi4s79N4 i8Psi4s79dN0
    i8Psi4s79dN1 i8Psi4s79dN2 i8Psi4s79dN3 i8Psi4s79dN4 i8Psi4s79dW i8P4w79
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, one] x = v0 at *
  generalize hpl [zero, one, negOne] x = v1 at *
  generalize hpl [negOne, one] x = v2 at *
  generalize hpl [zero, negOne] x = v3 at *
  generalize hpl [zero, one] x = v4 at *
  generalize hpl [one, negOne] x = v5 at *
  generalize hpl [negOne] x = v6 at *
  generalize hpl [zero] x = v7 at *
  generalize hpl [one] x = v8 at *
  ring

end QED.ThreeLoopD
