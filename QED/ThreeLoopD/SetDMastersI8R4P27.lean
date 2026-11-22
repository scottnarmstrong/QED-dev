/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P26

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 107 to 107

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s107`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s107D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s107`, `QED.ThreeLoopD.i8Psi4s107D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽107⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s107N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s107N0`. -/
noncomputable def i8Psi4s107dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s107N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s107N0 (i8Psi4s107dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽107⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s107N1 (x : ℝ) : ℝ :=
    (56 - 4 / 3 * π ^ 2) * hpl [one] x +
    (24) * hpl [zero, one] x +
    (24) * hpl [one, zero] x +
    (-16) * hpl [negOne, zero, one] x +
    (-16) * hpl [negOne, one, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (-16) * hpl [one, negOne, zero] x +
    (8) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s107N1`. -/
noncomputable def i8Psi4s107dN1 (x : ℝ) : ℝ :=
    (56 - 4 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (24) * (zero.kernel x * hpl [one] x) +
    (24) * (one.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, one] x) +
    (-16) * (negOne.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (-16) * (one.kernel x * hpl [negOne, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s107N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s107N1 (i8Psi4s107dN1 x) x := by
  unfold i8Psi4s107N1 i8Psi4s107dN1
  exact ((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (56 - 4 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽107⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s107N2 (x : ℝ) : ℝ :=
    (-56 + 4 / 3 * π ^ 2) * hpl [zero] x +
    (-51 + 10 / 3 * π ^ 2) * hpl [one] x +
    (-20) * hpl [negOne, zero] x +
    (-24) * hpl [zero, zero] x +
    (32 + 4 / 3 * π ^ 2) * hpl [zero, one] x +
    (-50) * hpl [one, zero] x +
    (-24) * hpl [negOne, zero, one] x +
    (-24) * hpl [negOne, one, zero] x +
    (40) * hpl [one, negOne, zero] x +
    (-20) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s107N2`. -/
noncomputable def i8Psi4s107dN2 (x : ℝ) : ℝ :=
    (-56 + 4 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-51 + 10 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (-20) * (negOne.kernel x * hpl [zero] x) +
    (-24) * (zero.kernel x * hpl [zero] x) +
    (32 + 4 / 3 * π ^ 2) * (zero.kernel x * hpl [one] x) +
    (-50) * (one.kernel x * hpl [zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, one] x) +
    (-24) * (negOne.kernel x * hpl [one, zero] x) +
    (40) * (one.kernel x * hpl [negOne, zero] x) +
    (-20) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s107N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s107N2 (i8Psi4s107dN2 x) x := by
  unfold i8Psi4s107N2 i8Psi4s107dN2
  exact (((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-56 + 4 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-51 + 10 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (32 + 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-50))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-20)))

/-- The part of `ξ² Ψ₄⁽107⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s107N3 (x : ℝ) : ℝ :=
    (-39 - 2 * π ^ 2) +
    (34) * hpl [zero] x +
    (16 - 4 / 3 * π ^ 2) * hpl [one] x +
    (-24) * hpl [negOne, zero] x +
    (12) * hpl [zero, zero] x +
    (16) * hpl [zero, one] x +
    (16) * hpl [one, zero] x +
    (-16) * hpl [negOne, zero, one] x +
    (-16) * hpl [negOne, one, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (-16) * hpl [one, negOne, zero] x +
    (8) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s107N3`. -/
noncomputable def i8Psi4s107dN3 (x : ℝ) : ℝ :=
    0 +
    (34) * (zero.kernel x * hpl [] x) +
    (16 - 4 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (-24) * (negOne.kernel x * hpl [zero] x) +
    (12) * (zero.kernel x * hpl [zero] x) +
    (16) * (zero.kernel x * hpl [one] x) +
    (16) * (one.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, one] x) +
    (-16) * (negOne.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (-16) * (one.kernel x * hpl [negOne, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s107N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s107N3 (i8Psi4s107dN3 x) x := by
  unfold i8Psi4s107N3 i8Psi4s107dN3
  exact (((((((((((((hasDerivAt_const x (-39 - 2 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (34))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (16 - 4 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽107⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s107N4 (x : ℝ) : ℝ :=
    (-27 / 2 - π ^ 2 / 3) +
    (6) * hpl [zero] x +
    (-21 - 2 / 3 * π ^ 2) * hpl [one] x +
    (-4) * hpl [negOne, zero] x +
    (2) * hpl [zero, zero] x +
    (10) * hpl [zero, one] x +
    (10) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (-8) * hpl [one, negOne, zero] x +
    (4) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s107N4`. -/
noncomputable def i8Psi4s107dN4 (x : ℝ) : ℝ :=
    0 +
    (6) * (zero.kernel x * hpl [] x) +
    (-21 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (10) * (zero.kernel x * hpl [one] x) +
    (10) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s107N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s107N4 (i8Psi4s107dN4 x) x := by
  unfold i8Psi4s107N4 i8Psi4s107dN4
  exact (((((((((((((hasDerivAt_const x (-27 / 2 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-21 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽107⁾` with constant coefficients. -/
noncomputable def i8Psi4s107W (x : ℝ) : ℝ :=
    (16) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, zero] x +
    (16) * hpl [zero, negOne, zero, one] x +
    (16) * hpl [zero, negOne, one, zero] x +
    (-8) * hpl [zero, zero, zero, one] x +
    (-8) * hpl [zero, zero, one, zero] x +
    (16) * hpl [zero, one, negOne, zero] x +
    (-8) * hpl [zero, one, zero, zero] x

/-- The derivative of `i8Psi4s107W`. -/
noncomputable def i8Psi4s107dW (x : ℝ) : ℝ :=
    (16) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (16) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-8) * (zero.kernel x * hpl [zero, one, zero] x) +
    (16) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s107W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s107W (i8Psi4s107dW x) x := by
  unfold i8Psi4s107W i8Psi4s107dW
  exact (((((((((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-8)))

/-- The piece `Ψ₄⁽107⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s107 (x : ℝ) : ℝ :=
  (i8Psi4s107N0 x + x * i8Psi4s107N1 x + x ^ 2 * i8Psi4s107N2 x + x ^ 3 * i8Psi4s107N3 x +
    x ^ 4 * i8Psi4s107N4 x) / x ^ 2 + i8Psi4s107W x

/-- The derivative of `Ψ₄⁽107⁾`. -/
noncomputable def i8Psi4s107D (x : ℝ) : ℝ :=
  ((i8Psi4s107dN0 x + (i8Psi4s107N1 x + x * i8Psi4s107dN1 x) + (2 * x * i8Psi4s107N2 x +
    x ^ 2 * i8Psi4s107dN2 x) + (3 * x ^ 2 * i8Psi4s107N3 x + x ^ 3 * i8Psi4s107dN3 x) +
    (4 * x ^ 3 * i8Psi4s107N4 x + x ^ 4 * i8Psi4s107dN4 x)) * x ^ 2 - (i8Psi4s107N0 x +
    x * i8Psi4s107N1 x + x ^ 2 * i8Psi4s107N2 x + x ^ 3 * i8Psi4s107N3 x +
    x ^ 4 * i8Psi4s107N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s107dW x

theorem hasDerivAt_i8Psi4s107 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s107 (i8Psi4s107D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s107N0 hx).add (X.mul (hasDerivAt_i8Psi4s107N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s107N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s107N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s107N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s107W hx)
  unfold i8Psi4s107
  refine e.congr_deriv ?_
  unfold i8Psi4s107D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 107 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s107 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * i13Be2x x * ((1 + x) / (1 - x) * ((2 +
    ((-2) * x)) / (1 + x))) * (x / (1 - x)))

/-- `p₄⁽107⁾` written over words. -/
noncomputable def i8P4w107 (x : ℝ) : ℝ :=
    (32 - 32 * x - 4 / 3 * π ^ 2 - 4 / 3 * π ^ 2 * x) * hpl [one] x +
    (16 + 16 * x) * hpl [zero, one] x +
    (16 + 16 * x) * hpl [one, zero] x +
    (-16 - 16 * x) * hpl [negOne, zero, one] x +
    (-16 - 16 * x) * hpl [negOne, one, zero] x +
    (8 + 8 * x) * hpl [zero, zero, one] x +
    (8 + 8 * x) * hpl [zero, one, zero] x +
    (-16 - 16 * x) * hpl [one, negOne, zero] x +
    (8 + 8 * x) * hpl [one, zero, zero] x

theorem i8P4s107_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s107 x = i8P4w107 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s107 i8P4w107 i13Be2x
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

/-- **`(Ψ₄⁽107⁾)'(ξ) ξ' = p₄⁽107⁾`**, in terms of `ξ`. -/
theorem i8Psi4s107D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s107D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s107 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s107_eq_w hx]
  unfold i8Psi4s107D i8Psi4s107N0 i8Psi4s107N1 i8Psi4s107N2 i8Psi4s107N3 i8Psi4s107N4 i8Psi4s107dN0
    i8Psi4s107dN1 i8Psi4s107dN2 i8Psi4s107dN3 i8Psi4s107dN4 i8Psi4s107dW i8P4w107
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

end QED.ThreeLoopD
