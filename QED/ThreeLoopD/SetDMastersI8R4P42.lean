/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P41

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 139 to 140

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s139`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s139D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s139`, `QED.ThreeLoopD.i8Psi4s139D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽139⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s139N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s139N0`. -/
noncomputable def i8Psi4s139dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s139N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s139N0 (i8Psi4s139dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽139⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s139N1 (x : ℝ) : ℝ :=
    (36) * hpl [one] x +
    (36) * hpl [zero, one] x +
    (36) * hpl [one, zero] x +
    (28) * hpl [zero, zero, one] x +
    (28) * hpl [zero, one, zero] x +
    (28) * hpl [one, zero, zero] x +
    (12) * hpl [zero, zero, zero, one] x +
    (12) * hpl [zero, zero, one, zero] x +
    (12) * hpl [zero, one, zero, zero] x +
    (12) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s139N1`. -/
noncomputable def i8Psi4s139dN1 (x : ℝ) : ℝ :=
    (36) * (one.kernel x * hpl [] x) +
    (36) * (zero.kernel x * hpl [one] x) +
    (36) * (one.kernel x * hpl [zero] x) +
    (28) * (zero.kernel x * hpl [zero, one] x) +
    (28) * (zero.kernel x * hpl [one, zero] x) +
    (28) * (one.kernel x * hpl [zero, zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero, one] x) +
    (12) * (zero.kernel x * hpl [zero, one, zero] x) +
    (12) * (zero.kernel x * hpl [one, zero, zero] x) +
    (12) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s139N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s139N1 (i8Psi4s139dN1 x) x := by
  unfold i8Psi4s139N1 i8Psi4s139dN1
  exact (((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (36)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽139⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s139N2 (x : ℝ) : ℝ :=
    (-36) * hpl [zero] x +
    (-339 / 4) * hpl [one] x +
    (-36) * hpl [zero, zero] x +
    (35 / 2) * hpl [one, zero] x +
    (-28) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (-91) * hpl [one, zero, zero] x +
    (-16) * hpl [zero, zero, zero, one] x +
    (-16) * hpl [zero, zero, one, zero] x +
    (-16) * hpl [zero, one, zero, zero] x +
    (30) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s139N2`. -/
noncomputable def i8Psi4s139dN2 (x : ℝ) : ℝ :=
    (-36) * (zero.kernel x * hpl [] x) +
    (-339 / 4) * (one.kernel x * hpl [] x) +
    (-36) * (zero.kernel x * hpl [zero] x) +
    (35 / 2) * (one.kernel x * hpl [zero] x) +
    (-28) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (-91) * (one.kernel x * hpl [zero, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-16) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-16) * (zero.kernel x * hpl [one, zero, zero] x) +
    (30) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s139N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s139N2 (i8Psi4s139dN2 x) x := by
  unfold i8Psi4s139N2 i8Psi4s139dN2
  exact (((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-36)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-339 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (35 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-91))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (30)))

/-- The part of `ξ² Ψ₄⁽139⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s139N3 (x : ℝ) : ℝ :=
    (829 / 4) +
    (-317 / 2) * hpl [zero] x +
    (44) * hpl [one] x +
    (105) * hpl [zero, zero] x +
    (-44) * hpl [zero, one] x +
    (-44) * hpl [one, zero] x +
    (-42) * hpl [zero, zero, zero] x +
    (52) * hpl [zero, zero, one] x +
    (52) * hpl [zero, one, zero] x +
    (52) * hpl [one, zero, zero] x +
    (-36) * hpl [zero, zero, zero, one] x +
    (-36) * hpl [zero, zero, one, zero] x +
    (-36) * hpl [zero, one, zero, zero] x +
    (-36) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s139N3`. -/
noncomputable def i8Psi4s139dN3 (x : ℝ) : ℝ :=
    0 +
    (-317 / 2) * (zero.kernel x * hpl [] x) +
    (44) * (one.kernel x * hpl [] x) +
    (105) * (zero.kernel x * hpl [zero] x) +
    (-44) * (zero.kernel x * hpl [one] x) +
    (-44) * (one.kernel x * hpl [zero] x) +
    (-42) * (zero.kernel x * hpl [zero, zero] x) +
    (52) * (zero.kernel x * hpl [zero, one] x) +
    (52) * (zero.kernel x * hpl [one, zero] x) +
    (52) * (one.kernel x * hpl [zero, zero] x) +
    (-36) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-36) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-36) * (zero.kernel x * hpl [one, zero, zero] x) +
    (-36) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s139N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s139N3 (i8Psi4s139dN3 x) x := by
  unfold i8Psi4s139N3 i8Psi4s139dN3
  exact ((((((((((((((hasDerivAt_const x (829 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-317 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (44))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (105))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-44))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-44))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-42))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (52))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (52))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (52))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (-36)))

/-- The part of `ξ² Ψ₄⁽139⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s139N4 (x : ℝ) : ℝ :=
    (13 / 2) +
    (-33 / 4) * hpl [zero] x +
    (19 / 4) * hpl [one] x +
    (7) * hpl [zero, zero] x +
    (-19 / 2) * hpl [zero, one] x +
    (-19 / 2) * hpl [one, zero] x +
    (-3) * hpl [zero, zero, zero] x +
    (11) * hpl [zero, zero, one] x +
    (11) * hpl [zero, one, zero] x +
    (11) * hpl [one, zero, zero] x +
    (-6) * hpl [zero, zero, zero, one] x +
    (-6) * hpl [zero, zero, one, zero] x +
    (-6) * hpl [zero, one, zero, zero] x +
    (-6) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s139N4`. -/
noncomputable def i8Psi4s139dN4 (x : ℝ) : ℝ :=
    0 +
    (-33 / 4) * (zero.kernel x * hpl [] x) +
    (19 / 4) * (one.kernel x * hpl [] x) +
    (7) * (zero.kernel x * hpl [zero] x) +
    (-19 / 2) * (zero.kernel x * hpl [one] x) +
    (-19 / 2) * (one.kernel x * hpl [zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero] x) +
    (11) * (zero.kernel x * hpl [zero, one] x) +
    (11) * (zero.kernel x * hpl [one, zero] x) +
    (11) * (one.kernel x * hpl [zero, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-6) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-6) * (zero.kernel x * hpl [one, zero, zero] x) +
    (-6) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s139N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s139N4 (i8Psi4s139dN4 x) x := by
  unfold i8Psi4s139N4 i8Psi4s139dN4
  exact ((((((((((((((hasDerivAt_const x (13 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-33 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (19 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-19 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-19 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (11))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (11))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (11))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (-6)))

/-- The part of `Ψ₄⁽139⁾` with constant coefficients. -/
noncomputable def i8Psi4s139W (x : ℝ) : ℝ :=
    (-12) * hpl [zero, zero, zero, zero] x +
    (-36) * hpl [zero, zero, zero, zero, one] x +
    (-36) * hpl [zero, zero, zero, one, zero] x +
    (-36) * hpl [zero, zero, one, zero, zero] x +
    (-36) * hpl [zero, one, zero, zero, zero] x

/-- The derivative of `i8Psi4s139W`. -/
noncomputable def i8Psi4s139dW (x : ℝ) : ℝ :=
    (-12) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (-36) * (zero.kernel x * hpl [zero, zero, zero, one] x) +
    (-36) * (zero.kernel x * hpl [zero, zero, one, zero] x) +
    (-36) * (zero.kernel x * hpl [zero, one, zero, zero] x) +
    (-36) * (zero.kernel x * hpl [one, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s139W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s139W (i8Psi4s139dW x) x := by
  unfold i8Psi4s139W i8Psi4s139dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-12)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, one] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one, zero] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero, zero] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero, zero] hx).const_mul (-36)))

/-- The piece `Ψ₄⁽139⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s139 (x : ℝ) : ℝ :=
  (i8Psi4s139N0 x + x * i8Psi4s139N1 x + x ^ 2 * i8Psi4s139N2 x + x ^ 3 * i8Psi4s139N3 x +
    x ^ 4 * i8Psi4s139N4 x) / x ^ 2 + i8Psi4s139W x

/-- The derivative of `Ψ₄⁽139⁾`. -/
noncomputable def i8Psi4s139D (x : ℝ) : ℝ :=
  ((i8Psi4s139dN0 x + (i8Psi4s139N1 x + x * i8Psi4s139dN1 x) + (2 * x * i8Psi4s139N2 x +
    x ^ 2 * i8Psi4s139dN2 x) + (3 * x ^ 2 * i8Psi4s139N3 x + x ^ 3 * i8Psi4s139dN3 x) +
    (4 * x ^ 3 * i8Psi4s139N4 x + x ^ 4 * i8Psi4s139dN4 x)) * x ^ 2 - (i8Psi4s139N0 x +
    x * i8Psi4s139N1 x + x ^ 2 * i8Psi4s139N2 x + x ^ 3 * i8Psi4s139N3 x +
    x ^ 4 * i8Psi4s139N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s139dW x

theorem hasDerivAt_i8Psi4s139 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s139 (i8Psi4s139D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s139N0 hx).add (X.mul (hasDerivAt_i8Psi4s139N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s139N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s139N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s139N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s139W hx)
  unfold i8Psi4s139
  refine e.congr_deriv ?_
  unfold i8Psi4s139D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 139 of `p₄` in `ξ`: from `t B2 A0 (-λ)^2/2!`, the term with `log^1 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s139 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * Real.log x * (2 + Real.log x * (1 + x) / (1 -
    x)) * (2 + Real.log x * (1 + x) / (1 - x)) * (x / (1 - x)))

/-- `p₄⁽139⁾` written over words. -/
noncomputable def i8P4w139 (x : ℝ) : ℝ :=
    (8 - 8 * x) * hpl [zero, one] x +
    (8 - 8 * x) * hpl [one, zero] x +
    (16 + 16 * x) * hpl [zero, zero, one] x +
    (16 + 16 * x) * hpl [zero, one, zero] x +
    (16 + 16 * x) * hpl [one, zero, zero] x +
    ((12 + 12 * x ^ 2 + 24 * x) / ((1 - x))) * hpl [zero, zero, zero, one] x +
    ((12 + 12 * x ^ 2 + 24 * x) / ((1 - x))) * hpl [zero, zero, one, zero] x +
    ((12 + 12 * x ^ 2 + 24 * x) / ((1 - x))) * hpl [zero, one, zero, zero] x +
    ((12 + 12 * x ^ 2 + 24 * x) / ((1 - x))) * hpl [one, zero, zero, zero] x

theorem i8P4s139_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s139 x = i8P4w139 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s139 i8P4w139
  simp only [i13hw_10 hx, i13hw_010 hx, i13hw_100 hx, i13hw_0010 hx, i13hw_0100 hx, i13hw_1000 hx,
    i13_log_one_sub_eq hx]
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
  generalize hpl [zero, zero, zero, one, zero] x = v25 at *
  generalize hpl [zero, zero, zero, one, one] x = v26 at *
  generalize hpl [zero, zero, one, negOne, negOne] x = v27 at *
  generalize hpl [zero, zero, one, negOne, one] x = v28 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v29 at *
  generalize hpl [zero, zero, one, zero, zero] x = v30 at *
  generalize hpl [zero, zero, one, zero, one] x = v31 at *
  generalize hpl [zero, zero, one, one, negOne] x = v32 at *
  generalize hpl [zero, zero, one, one, one] x = v33 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v34 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v35 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v36 at *
  generalize hpl [zero, one, negOne, one, one] x = v37 at *
  generalize hpl [zero, one, zero, zero, zero] x = v38 at *
  generalize hpl [zero, one, zero, one, negOne] x = v39 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v40 at *
  generalize hpl [zero, one, one, negOne, one] x = v41 at *
  generalize hpl [zero, one, one, one, negOne] x = v42 at *
  generalize hpl [zero, one, one, one, one] x = v43 at *
  generalize hpl [negOne, negOne, one, one] x = v44 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v45 at *
  generalize hpl [zero, negOne, negOne, one] x = v46 at *
  generalize hpl [zero, negOne, zero, one] x = v47 at *
  generalize hpl [zero, negOne, one, negOne] x = v48 at *
  generalize hpl [zero, negOne, one, one] x = v49 at *
  generalize hpl [zero, zero, negOne, negOne] x = v50 at *
  generalize hpl [zero, zero, negOne, one] x = v51 at *
  generalize hpl [zero, zero, zero, negOne] x = v52 at *
  generalize hpl [zero, zero, zero, zero] x = v53 at *
  generalize hpl [zero, zero, zero, one] x = v54 at *
  generalize hpl [zero, zero, one, negOne] x = v55 at *
  generalize hpl [zero, zero, one, zero] x = v56 at *
  generalize hpl [zero, zero, one, one] x = v57 at *
  generalize hpl [zero, one, negOne, negOne] x = v58 at *
  generalize hpl [zero, one, negOne, one] x = v59 at *
  generalize hpl [zero, one, zero, zero] x = v60 at *
  generalize hpl [zero, one, one, negOne] x = v61 at *
  generalize hpl [zero, one, one, one] x = v62 at *
  generalize hpl [one, zero, zero, zero] x = v63 at *
  generalize hpl [negOne, negOne, one] x = v64 at *
  generalize hpl [negOne, one, one] x = v65 at *
  generalize hpl [zero, negOne, negOne] x = v66 at *
  generalize hpl [zero, negOne, one] x = v67 at *
  generalize hpl [zero, zero, negOne] x = v68 at *
  generalize hpl [zero, zero, zero] x = v69 at *
  generalize hpl [zero, zero, one] x = v70 at *
  generalize hpl [zero, one, negOne] x = v71 at *
  generalize hpl [zero, one, zero] x = v72 at *
  generalize hpl [zero, one, one] x = v73 at *
  generalize hpl [one, zero, zero] x = v74 at *
  generalize hpl [negOne, one] x = v75 at *
  generalize hpl [zero, negOne] x = v76 at *
  generalize hpl [zero, zero] x = v77 at *
  generalize hpl [zero, one] x = v78 at *
  generalize hpl [one, zero] x = v79 at *
  generalize hpl [negOne] x = v80 at *
  generalize hpl [zero] x = v81 at *
  generalize hpl [one] x = v82 at *
  ring

/-- **`(Ψ₄⁽139⁾)'(ξ) ξ' = p₄⁽139⁾`**, in terms of `ξ`. -/
theorem i8Psi4s139D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s139D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s139 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s139_eq_w hx]
  unfold i8Psi4s139D i8Psi4s139N0 i8Psi4s139N1 i8Psi4s139N2 i8Psi4s139N3 i8Psi4s139N4 i8Psi4s139dN0
    i8Psi4s139dN1 i8Psi4s139dN2 i8Psi4s139dN3 i8Psi4s139dN4 i8Psi4s139dW i8P4w139
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

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s140k0N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s140k0N0`. -/
noncomputable def i8Psi4s140k0dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s140k0N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k0N0 (i8Psi4s140k0dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s140k0N1 (x : ℝ) : ℝ :=
    (32) * hpl [one, one] x +
    (16) * hpl [zero, one, one] x +
    (16) * hpl [one, zero, one] x +
    (16) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s140k0N1`. -/
noncomputable def i8Psi4s140k0dN1 (x : ℝ) : ℝ :=
    (32) * (one.kernel x * hpl [one] x) +
    (16) * (zero.kernel x * hpl [one, one] x) +
    (16) * (one.kernel x * hpl [zero, one] x) +
    (16) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s140k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k0N1 (i8Psi4s140k0dN1 x) x := by
  unfold i8Psi4s140k0N1 i8Psi4s140k0dN1
  exact (((((hasDerivAt_hpl_cons one [one] hx).const_mul (32)).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s140k0N2 (x : ℝ) : ℝ :=
    (44) * hpl [one] x +
    (-32) * hpl [zero, one] x +
    (-28) * hpl [one, zero] x +
    (-20) * hpl [one, one] x +
    (16) * hpl [zero, one, one] x +
    (-40) * hpl [one, zero, one] x +
    (-40) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s140k0N2`. -/
noncomputable def i8Psi4s140k0dN2 (x : ℝ) : ℝ :=
    (44) * (one.kernel x * hpl [] x) +
    (-32) * (zero.kernel x * hpl [one] x) +
    (-28) * (one.kernel x * hpl [zero] x) +
    (-20) * (one.kernel x * hpl [one] x) +
    (16) * (zero.kernel x * hpl [one, one] x) +
    (-40) * (one.kernel x * hpl [zero, one] x) +
    (-40) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s140k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k0N2 (i8Psi4s140k0dN2 x) x := by
  unfold i8Psi4s140k0N2 i8Psi4s140k0dN2
  exact ((((((((hasDerivAt_hpl_cons one [] hx).const_mul (44)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-40)))

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s140k0N3 (x : ℝ) : ℝ :=
    (-72) +
    (28) * hpl [zero] x +
    (-36) * hpl [one] x +
    (24) * hpl [zero, one] x +
    (24) * hpl [one, zero] x +
    (16) * hpl [zero, one, one] x +
    (16) * hpl [one, zero, one] x +
    (16) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s140k0N3`. -/
noncomputable def i8Psi4s140k0dN3 (x : ℝ) : ℝ :=
    0 +
    (28) * (zero.kernel x * hpl [] x) +
    (-36) * (one.kernel x * hpl [] x) +
    (24) * (zero.kernel x * hpl [one] x) +
    (24) * (one.kernel x * hpl [zero] x) +
    (16) * (zero.kernel x * hpl [one, one] x) +
    (16) * (one.kernel x * hpl [zero, one] x) +
    (16) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s140k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k0N3 (i8Psi4s140k0dN3 x) x := by
  unfold i8Psi4s140k0N3 i8Psi4s140k0dN3
  exact ((((((((hasDerivAt_const x (-72)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s140k0N4 (x : ℝ) : ℝ :=
    (-5) +
    (2) * hpl [zero] x +
    (-8) * hpl [one] x +
    (4) * hpl [zero, one] x +
    (4) * hpl [one, zero] x +
    (-12) * hpl [one, one] x +
    (8) * hpl [zero, one, one] x +
    (8) * hpl [one, zero, one] x +
    (8) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s140k0N4`. -/
noncomputable def i8Psi4s140k0dN4 (x : ℝ) : ℝ :=
    0 +
    (2) * (zero.kernel x * hpl [] x) +
    (-8) * (one.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [zero] x) +
    (-12) * (one.kernel x * hpl [one] x) +
    (8) * (zero.kernel x * hpl [one, one] x) +
    (8) * (one.kernel x * hpl [zero, one] x) +
    (8) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s140k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k0N4 (i8Psi4s140k0dN4 x) x := by
  unfold i8Psi4s140k0N4 i8Psi4s140k0dN4
  exact (((((((((hasDerivAt_const x (-5)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (8)))

/-- The part of `Ψ₄⁽140⁾` with constant coefficients. -/
noncomputable def i8Psi4s140k0W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, zero, one] x +
    (-16) * hpl [zero, one, zero] x +
    (-16) * hpl [zero, zero, one, one] x +
    (-16) * hpl [zero, one, zero, one] x +
    (-16) * hpl [zero, one, one, zero] x

/-- The derivative of `i8Psi4s140k0W`. -/
noncomputable def i8Psi4s140k0dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [zero, one] x) +
    (-16) * (zero.kernel x * hpl [one, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, one, one] x) +
    (-16) * (zero.kernel x * hpl [one, zero, one] x) +
    (-16) * (zero.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s140k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k0W (i8Psi4s140k0dW x) x := by
  unfold i8Psi4s140k0W i8Psi4s140k0dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (-16)))

/-- Chunk 0 of the piece `Ψ₄⁽140⁾`. -/
noncomputable def i8Psi4s140k0 (x : ℝ) : ℝ :=
  (i8Psi4s140k0N0 x + x * i8Psi4s140k0N1 x + x ^ 2 * i8Psi4s140k0N2 x + x ^ 3 * i8Psi4s140k0N3 x +
    x ^ 4 * i8Psi4s140k0N4 x) / x ^ 2 + i8Psi4s140k0W x

/-- The derivative of `i8Psi4s140k0`. -/
noncomputable def i8Psi4s140k0D (x : ℝ) : ℝ :=
  ((i8Psi4s140k0dN0 x + (i8Psi4s140k0N1 x + x * i8Psi4s140k0dN1 x) + (2 * x * i8Psi4s140k0N2 x +
    x ^ 2 * i8Psi4s140k0dN2 x) + (3 * x ^ 2 * i8Psi4s140k0N3 x + x ^ 3 * i8Psi4s140k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s140k0N4 x + x ^ 4 * i8Psi4s140k0dN4 x)) * x ^ 2 - (i8Psi4s140k0N0 x +
    x * i8Psi4s140k0N1 x + x ^ 2 * i8Psi4s140k0N2 x + x ^ 3 * i8Psi4s140k0N3 x +
    x ^ 4 * i8Psi4s140k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s140k0dW x

theorem hasDerivAt_i8Psi4s140k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k0 (i8Psi4s140k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s140k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s140k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s140k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s140k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s140k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s140k0W hx)
  unfold i8Psi4s140k0
  refine e.congr_deriv ?_
  unfold i8Psi4s140k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽140⁾` over words. -/
noncomputable def i8P4w140k0 (x : ℝ) : ℝ :=
    (16 - 16 * x) * hpl [one, one] x +
    (16 + 16 * x) * hpl [zero, one, one] x +
    (16 + 16 * x) * hpl [one, zero, one] x +
    (16 + 16 * x) * hpl [one, one, zero] x

theorem i8Psi4s140k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s140k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w140k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s140k0D i8Psi4s140k0N0 i8Psi4s140k0N1 i8Psi4s140k0N2 i8Psi4s140k0N3 i8Psi4s140k0N4
    i8Psi4s140k0dN0 i8Psi4s140k0dN1 i8Psi4s140k0dN2 i8Psi4s140k0dN3 i8Psi4s140k0dN4 i8Psi4s140k0dW
    i8P4w140k0
  simp only [kernel_zero, kernel_one, hpl_nil]
  generalize hpl [zero, zero, one, one] x = v0 at *
  generalize hpl [zero, one, zero, one] x = v1 at *
  generalize hpl [zero, one, one, zero] x = v2 at *
  generalize hpl [zero, zero, one] x = v3 at *
  generalize hpl [zero, one, zero] x = v4 at *
  generalize hpl [zero, one, one] x = v5 at *
  generalize hpl [one, zero, one] x = v6 at *
  generalize hpl [one, one, zero] x = v7 at *
  generalize hpl [zero, one] x = v8 at *
  generalize hpl [one, zero] x = v9 at *
  generalize hpl [one, one] x = v10 at *
  generalize hpl [zero] x = v11 at *
  generalize hpl [one] x = v12 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s140k1N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s140k1N0`. -/
noncomputable def i8Psi4s140k1dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s140k1N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k1N0 (i8Psi4s140k1dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s140k1N1 (x : ℝ) : ℝ :=
    (8) * hpl [one, one] x +
    (8) * hpl [zero, one, one] x +
    (8) * hpl [one, zero, one] x +
    (8) * hpl [one, one, zero] x +
    (8) * hpl [zero, zero, one, one] x +
    (8) * hpl [zero, one, zero, one] x +
    (8) * hpl [zero, one, one, zero] x +
    (8) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s140k1N1`. -/
noncomputable def i8Psi4s140k1dN1 (x : ℝ) : ℝ :=
    (8) * (one.kernel x * hpl [one] x) +
    (8) * (zero.kernel x * hpl [one, one] x) +
    (8) * (one.kernel x * hpl [zero, one] x) +
    (8) * (one.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one, one] x) +
    (8) * (zero.kernel x * hpl [one, zero, one] x) +
    (8) * (zero.kernel x * hpl [one, one, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s140k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k1N1 (i8Psi4s140k1dN1 x) x := by
  unfold i8Psi4s140k1N1 i8Psi4s140k1dN1
  exact (((((((((hasDerivAt_hpl_cons one [one] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s140k1N2 (x : ℝ) : ℝ :=
    (161 / 2) * hpl [one] x +
    (-8) * hpl [zero, one] x +
    (-27) * hpl [one, zero] x +
    (17) * hpl [one, one] x +
    (-8) * hpl [zero, zero, one] x +
    (-34) * hpl [one, zero, one] x +
    (-34) * hpl [one, one, zero] x +
    (20) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s140k1N2`. -/
noncomputable def i8Psi4s140k1dN2 (x : ℝ) : ℝ :=
    (161 / 2) * (one.kernel x * hpl [] x) +
    (-8) * (zero.kernel x * hpl [one] x) +
    (-27) * (one.kernel x * hpl [zero] x) +
    (17) * (one.kernel x * hpl [one] x) +
    (-8) * (zero.kernel x * hpl [zero, one] x) +
    (-34) * (one.kernel x * hpl [zero, one] x) +
    (-34) * (one.kernel x * hpl [one, zero] x) +
    (20) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s140k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k1N2 (i8Psi4s140k1dN2 x) x := by
  unfold i8Psi4s140k1N2 i8Psi4s140k1dN2
  exact (((((((((hasDerivAt_hpl_cons one [] hx).const_mul (161 / 2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-27))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (17))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-34))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-34))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (20)))

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s140k1N3 (x : ℝ) : ℝ :=
    (-215 / 2) +
    (27) * hpl [zero] x +
    (-79) * hpl [one] x +
    (54) * hpl [zero, one] x +
    (26) * hpl [one, zero] x +
    (-24) * hpl [one, one] x +
    (-28) * hpl [zero, zero, one] x +
    (24) * hpl [zero, one, one] x +
    (24) * hpl [one, zero, one] x +
    (24) * hpl [one, one, zero] x +
    (-24) * hpl [zero, zero, one, one] x +
    (-24) * hpl [zero, one, zero, one] x +
    (-24) * hpl [zero, one, one, zero] x +
    (-24) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s140k1N3`. -/
noncomputable def i8Psi4s140k1dN3 (x : ℝ) : ℝ :=
    0 +
    (27) * (zero.kernel x * hpl [] x) +
    (-79) * (one.kernel x * hpl [] x) +
    (54) * (zero.kernel x * hpl [one] x) +
    (26) * (one.kernel x * hpl [zero] x) +
    (-24) * (one.kernel x * hpl [one] x) +
    (-28) * (zero.kernel x * hpl [zero, one] x) +
    (24) * (zero.kernel x * hpl [one, one] x) +
    (24) * (one.kernel x * hpl [zero, one] x) +
    (24) * (one.kernel x * hpl [one, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, one, one] x) +
    (-24) * (zero.kernel x * hpl [one, zero, one] x) +
    (-24) * (zero.kernel x * hpl [one, one, zero] x) +
    (-24) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s140k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k1N3 (i8Psi4s140k1dN3 x) x := by
  unfold i8Psi4s140k1N3 i8Psi4s140k1dN3
  exact ((((((((((((((hasDerivAt_const x (-215 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (27))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-79))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (54))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (26))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s140k1N4 (x : ℝ) : ℝ :=
    (-1) +
    (1 / 2) * hpl [zero] x +
    (-3 / 2) * hpl [one] x +
    (2) * hpl [zero, one] x +
    (1) * hpl [one, zero] x +
    (-1) * hpl [one, one] x +
    (-2) * hpl [zero, zero, one] x +
    (2) * hpl [zero, one, one] x +
    (2) * hpl [one, zero, one] x +
    (2) * hpl [one, one, zero] x +
    (-4) * hpl [zero, zero, one, one] x +
    (-4) * hpl [zero, one, zero, one] x +
    (-4) * hpl [zero, one, one, zero] x +
    (-4) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s140k1N4`. -/
noncomputable def i8Psi4s140k1dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-3 / 2) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [zero] x) +
    (-1) * (one.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [zero, one] x) +
    (2) * (zero.kernel x * hpl [one, one] x) +
    (2) * (one.kernel x * hpl [zero, one] x) +
    (2) * (one.kernel x * hpl [one, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, one, one] x) +
    (-4) * (zero.kernel x * hpl [one, zero, one] x) +
    (-4) * (zero.kernel x * hpl [one, one, zero] x) +
    (-4) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s140k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k1N4 (i8Psi4s140k1dN4 x) x := by
  unfold i8Psi4s140k1N4 i8Psi4s140k1dN4
  exact ((((((((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽140⁾` with constant coefficients. -/
noncomputable def i8Psi4s140k1W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, one, zero] x +
    (-8) * hpl [zero, zero, zero, one] x +
    (-24) * hpl [zero, zero, zero, one, one] x +
    (-24) * hpl [zero, zero, one, zero, one] x +
    (-24) * hpl [zero, zero, one, one, zero] x +
    (-24) * hpl [zero, one, zero, zero, one] x

/-- The derivative of `i8Psi4s140k1W`. -/
noncomputable def i8Psi4s140k1dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-24) * (zero.kernel x * hpl [zero, zero, one, one] x) +
    (-24) * (zero.kernel x * hpl [zero, one, zero, one] x) +
    (-24) * (zero.kernel x * hpl [zero, one, one, zero] x) +
    (-24) * (zero.kernel x * hpl [one, zero, zero, one] x)

theorem hasDerivAt_i8Psi4s140k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k1W (i8Psi4s140k1dW x) x := by
  unfold i8Psi4s140k1W i8Psi4s140k1dW
  exact (((((((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero, one] hx).const_mul (-24)))

/-- Chunk 1 of the piece `Ψ₄⁽140⁾`. -/
noncomputable def i8Psi4s140k1 (x : ℝ) : ℝ :=
  (i8Psi4s140k1N0 x + x * i8Psi4s140k1N1 x + x ^ 2 * i8Psi4s140k1N2 x + x ^ 3 * i8Psi4s140k1N3 x +
    x ^ 4 * i8Psi4s140k1N4 x) / x ^ 2 + i8Psi4s140k1W x

/-- The derivative of `i8Psi4s140k1`. -/
noncomputable def i8Psi4s140k1D (x : ℝ) : ℝ :=
  ((i8Psi4s140k1dN0 x + (i8Psi4s140k1N1 x + x * i8Psi4s140k1dN1 x) + (2 * x * i8Psi4s140k1N2 x +
    x ^ 2 * i8Psi4s140k1dN2 x) + (3 * x ^ 2 * i8Psi4s140k1N3 x + x ^ 3 * i8Psi4s140k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s140k1N4 x + x ^ 4 * i8Psi4s140k1dN4 x)) * x ^ 2 - (i8Psi4s140k1N0 x +
    x * i8Psi4s140k1N1 x + x ^ 2 * i8Psi4s140k1N2 x + x ^ 3 * i8Psi4s140k1N3 x +
    x ^ 4 * i8Psi4s140k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s140k1dW x

theorem hasDerivAt_i8Psi4s140k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k1 (i8Psi4s140k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s140k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s140k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s140k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s140k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s140k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s140k1W hx)
  unfold i8Psi4s140k1
  refine e.congr_deriv ?_
  unfold i8Psi4s140k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽140⁾` over words. -/
noncomputable def i8P4w140k1 (x : ℝ) : ℝ :=
    ((8 + 8 * x ^ 2 + 16 * x) / ((1 - x))) * hpl [zero, zero, one, one] x +
    ((8 + 8 * x ^ 2 + 16 * x) / ((1 - x))) * hpl [zero, one, zero, one] x +
    ((8 + 8 * x ^ 2 + 16 * x) / ((1 - x))) * hpl [zero, one, one, zero] x +
    ((8 + 8 * x ^ 2 + 16 * x) / ((1 - x))) * hpl [one, zero, zero, one] x

theorem i8Psi4s140k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s140k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w140k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s140k1D i8Psi4s140k1N0 i8Psi4s140k1N1 i8Psi4s140k1N2 i8Psi4s140k1N3 i8Psi4s140k1N4
    i8Psi4s140k1dN0 i8Psi4s140k1dN1 i8Psi4s140k1dN2 i8Psi4s140k1dN3 i8Psi4s140k1dN4 i8Psi4s140k1dW
    i8P4w140k1
  simp only [kernel_zero, kernel_one, hpl_nil]
  generalize hpl [zero, zero, zero, one, one] x = v0 at *
  generalize hpl [zero, zero, one, zero, one] x = v1 at *
  generalize hpl [zero, zero, one, one, zero] x = v2 at *
  generalize hpl [zero, one, zero, zero, one] x = v3 at *
  generalize hpl [zero, zero, zero, one] x = v4 at *
  generalize hpl [zero, zero, one, one] x = v5 at *
  generalize hpl [zero, one, zero, one] x = v6 at *
  generalize hpl [zero, one, one, zero] x = v7 at *
  generalize hpl [one, zero, zero, one] x = v8 at *
  generalize hpl [zero, zero, one] x = v9 at *
  generalize hpl [zero, one, zero] x = v10 at *
  generalize hpl [zero, one, one] x = v11 at *
  generalize hpl [one, zero, one] x = v12 at *
  generalize hpl [one, one, zero] x = v13 at *
  generalize hpl [zero, one] x = v14 at *
  generalize hpl [one, zero] x = v15 at *
  generalize hpl [one, one] x = v16 at *
  generalize hpl [zero] x = v17 at *
  generalize hpl [one] x = v18 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s140k2N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s140k2N0`. -/
noncomputable def i8Psi4s140k2dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s140k2N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k2N0 (i8Psi4s140k2dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s140k2N1 (x : ℝ) : ℝ :=
    (8) * hpl [one, zero, one, zero] x +
    (8) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s140k2N1`. -/
noncomputable def i8Psi4s140k2dN1 (x : ℝ) : ℝ :=
    (8) * (one.kernel x * hpl [zero, one, zero] x) +
    (8) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s140k2N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k2N1 (i8Psi4s140k2dN1 x) x := by
  unfold i8Psi4s140k2N1 i8Psi4s140k2dN1
  exact (((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s140k2N2 (x : ℝ) : ℝ :=
    (-29) * hpl [one, zero] x +
    (30) * hpl [one, zero, zero] x +
    (20) * hpl [one, zero, one, zero] x +
    (20) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s140k2N2`. -/
noncomputable def i8Psi4s140k2dN2 (x : ℝ) : ℝ :=
    (-29) * (one.kernel x * hpl [zero] x) +
    (30) * (one.kernel x * hpl [zero, zero] x) +
    (20) * (one.kernel x * hpl [zero, one, zero] x) +
    (20) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s140k2N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k2N2 (i8Psi4s140k2dN2 x) x := by
  unfold i8Psi4s140k2N2 i8Psi4s140k2dN2
  exact (((((hasDerivAt_hpl_cons one [zero] hx).const_mul (-29)).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (30))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (20)))

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s140k2N3 (x : ℝ) : ℝ :=
    (-59) +
    (59) * hpl [zero] x +
    (-30) * hpl [zero, zero] x +
    (28) * hpl [one, zero] x +
    (-28) * hpl [zero, one, zero] x +
    (-28) * hpl [one, zero, zero] x +
    (-24) * hpl [one, zero, one, zero] x +
    (-24) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s140k2N3`. -/
noncomputable def i8Psi4s140k2dN3 (x : ℝ) : ℝ :=
    0 +
    (59) * (zero.kernel x * hpl [] x) +
    (-30) * (zero.kernel x * hpl [zero] x) +
    (28) * (one.kernel x * hpl [zero] x) +
    (-28) * (zero.kernel x * hpl [one, zero] x) +
    (-28) * (one.kernel x * hpl [zero, zero] x) +
    (-24) * (one.kernel x * hpl [zero, one, zero] x) +
    (-24) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s140k2N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k2N3 (i8Psi4s140k2dN3 x) x := by
  unfold i8Psi4s140k2N3 i8Psi4s140k2dN3
  exact ((((((((hasDerivAt_const x (-59)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (59))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽140⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s140k2N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (1) * hpl [zero] x +
    (-1) * hpl [zero, zero] x +
    (1) * hpl [one, zero] x +
    (-2) * hpl [zero, one, zero] x +
    (-2) * hpl [one, zero, zero] x +
    (-4) * hpl [one, zero, one, zero] x +
    (-4) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s140k2N4`. -/
noncomputable def i8Psi4s140k2dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [zero] x) +
    (1) * (one.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [one, zero] x) +
    (-2) * (one.kernel x * hpl [zero, zero] x) +
    (-4) * (one.kernel x * hpl [zero, one, zero] x) +
    (-4) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s140k2N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k2N4 (i8Psi4s140k2dN4 x) x := by
  unfold i8Psi4s140k2N4 i8Psi4s140k2dN4
  exact ((((((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽140⁾` with constant coefficients. -/
noncomputable def i8Psi4s140k2W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, one, zero] x +
    (-8) * hpl [zero, one, zero, zero] x +
    (-24) * hpl [zero, one, zero, one, zero] x +
    (-24) * hpl [zero, one, one, zero, zero] x

/-- The derivative of `i8Psi4s140k2W`. -/
noncomputable def i8Psi4s140k2dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, zero, zero] x) +
    (-24) * (zero.kernel x * hpl [one, zero, one, zero] x) +
    (-24) * (zero.kernel x * hpl [one, one, zero, zero] x)

theorem hasDerivAt_i8Psi4s140k2W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k2W (i8Psi4s140k2dW x) x := by
  unfold i8Psi4s140k2W i8Psi4s140k2dW
  exact (((((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero, zero] hx).const_mul (-24)))

/-- Chunk 2 of the piece `Ψ₄⁽140⁾`. -/
noncomputable def i8Psi4s140k2 (x : ℝ) : ℝ :=
  (i8Psi4s140k2N0 x + x * i8Psi4s140k2N1 x + x ^ 2 * i8Psi4s140k2N2 x + x ^ 3 * i8Psi4s140k2N3 x +
    x ^ 4 * i8Psi4s140k2N4 x) / x ^ 2 + i8Psi4s140k2W x

/-- The derivative of `i8Psi4s140k2`. -/
noncomputable def i8Psi4s140k2D (x : ℝ) : ℝ :=
  ((i8Psi4s140k2dN0 x + (i8Psi4s140k2N1 x + x * i8Psi4s140k2dN1 x) + (2 * x * i8Psi4s140k2N2 x +
    x ^ 2 * i8Psi4s140k2dN2 x) + (3 * x ^ 2 * i8Psi4s140k2N3 x + x ^ 3 * i8Psi4s140k2dN3 x) +
    (4 * x ^ 3 * i8Psi4s140k2N4 x + x ^ 4 * i8Psi4s140k2dN4 x)) * x ^ 2 - (i8Psi4s140k2N0 x +
    x * i8Psi4s140k2N1 x + x ^ 2 * i8Psi4s140k2N2 x + x ^ 3 * i8Psi4s140k2N3 x +
    x ^ 4 * i8Psi4s140k2N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s140k2dW x

theorem hasDerivAt_i8Psi4s140k2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140k2 (i8Psi4s140k2D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s140k2N0 hx).add (X.mul (hasDerivAt_i8Psi4s140k2N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s140k2N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s140k2N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s140k2N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s140k2W hx)
  unfold i8Psi4s140k2
  refine e.congr_deriv ?_
  unfold i8Psi4s140k2D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 2 of `p₄⁽140⁾` over words. -/
noncomputable def i8P4w140k2 (x : ℝ) : ℝ :=
    ((8 + 8 * x ^ 2 + 16 * x) / ((1 - x))) * hpl [one, zero, one, zero] x +
    ((8 + 8 * x ^ 2 + 16 * x) / ((1 - x))) * hpl [one, one, zero, zero] x

theorem i8Psi4s140k2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s140k2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w140k2 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s140k2D i8Psi4s140k2N0 i8Psi4s140k2N1 i8Psi4s140k2N2 i8Psi4s140k2N3 i8Psi4s140k2N4
    i8Psi4s140k2dN0 i8Psi4s140k2dN1 i8Psi4s140k2dN2 i8Psi4s140k2dN3 i8Psi4s140k2dN4 i8Psi4s140k2dW
    i8P4w140k2
  simp only [kernel_zero, kernel_one, hpl_nil]
  generalize hpl [zero, one, zero, one, zero] x = v0 at *
  generalize hpl [zero, one, one, zero, zero] x = v1 at *
  generalize hpl [zero, zero, one, zero] x = v2 at *
  generalize hpl [zero, one, zero, zero] x = v3 at *
  generalize hpl [one, zero, one, zero] x = v4 at *
  generalize hpl [one, one, zero, zero] x = v5 at *
  generalize hpl [zero, one, zero] x = v6 at *
  generalize hpl [one, zero, zero] x = v7 at *
  generalize hpl [zero, zero] x = v8 at *
  generalize hpl [one, zero] x = v9 at *
  generalize hpl [zero] x = v10 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽140⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s140 (x : ℝ) : ℝ :=
  i8Psi4s140k0 x + i8Psi4s140k1 x + i8Psi4s140k2 x

/-- The derivative of `Ψ₄⁽140⁾`. -/
noncomputable def i8Psi4s140D (x : ℝ) : ℝ :=
  i8Psi4s140k0D x + i8Psi4s140k1D x + i8Psi4s140k2D x

theorem hasDerivAt_i8Psi4s140 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s140 (i8Psi4s140D x) x := by
  unfold i8Psi4s140 i8Psi4s140D
  exact (((hasDerivAt_i8Psi4s140k0 hx).add (hasDerivAt_i8Psi4s140k1 hx)).add
    (hasDerivAt_i8Psi4s140k2 hx))

/-- The sub-piece 140 of `p₄` in `ξ`: from `t B2 A0 (-λ)^2/2!`, the term with `log^2 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s140 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 2 * (2 + Real.log x * (1 + x) / (1 - x)) * (2 +
    Real.log x * (1 + x) / (1 - x)) * (x / (1 - x))

/-- `p₄⁽140⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w140 (x : ℝ) : ℝ :=
  i8P4w140k0 x + i8P4w140k1 x + i8P4w140k2 x

theorem i8P4s140_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s140 x = i8P4w140 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s140 i8P4w140 i8P4w140k0 i8P4w140k1 i8P4w140k2
  simp only [i13hw_11 hx, i13hw_101 hx, i13hw_110 hx, i13hw_0101 hx, i13hw_0110 hx, i13hw_1001 hx,
    i13hw_1010 hx, i13hw_1100 hx, i13_log_one_sub_eq hx]
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
  generalize hpl [zero, zero, one, one, zero] x = v31 at *
  generalize hpl [zero, zero, one, one, one] x = v32 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v33 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v34 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v35 at *
  generalize hpl [zero, one, negOne, one, one] x = v36 at *
  generalize hpl [zero, one, zero, zero, one] x = v37 at *
  generalize hpl [zero, one, zero, one, negOne] x = v38 at *
  generalize hpl [zero, one, zero, one, zero] x = v39 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v40 at *
  generalize hpl [zero, one, one, negOne, one] x = v41 at *
  generalize hpl [zero, one, one, zero, zero] x = v42 at *
  generalize hpl [zero, one, one, one, negOne] x = v43 at *
  generalize hpl [zero, one, one, one, one] x = v44 at *
  generalize hpl [negOne, negOne, one, one] x = v45 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v46 at *
  generalize hpl [zero, negOne, negOne, one] x = v47 at *
  generalize hpl [zero, negOne, zero, one] x = v48 at *
  generalize hpl [zero, negOne, one, negOne] x = v49 at *
  generalize hpl [zero, negOne, one, one] x = v50 at *
  generalize hpl [zero, zero, negOne, negOne] x = v51 at *
  generalize hpl [zero, zero, negOne, one] x = v52 at *
  generalize hpl [zero, zero, zero, negOne] x = v53 at *
  generalize hpl [zero, zero, zero, one] x = v54 at *
  generalize hpl [zero, zero, one, negOne] x = v55 at *
  generalize hpl [zero, zero, one, zero] x = v56 at *
  generalize hpl [zero, zero, one, one] x = v57 at *
  generalize hpl [zero, one, negOne, negOne] x = v58 at *
  generalize hpl [zero, one, negOne, one] x = v59 at *
  generalize hpl [zero, one, zero, zero] x = v60 at *
  generalize hpl [zero, one, zero, one] x = v61 at *
  generalize hpl [zero, one, one, negOne] x = v62 at *
  generalize hpl [zero, one, one, zero] x = v63 at *
  generalize hpl [zero, one, one, one] x = v64 at *
  generalize hpl [one, zero, zero, one] x = v65 at *
  generalize hpl [one, zero, one, zero] x = v66 at *
  generalize hpl [one, one, zero, zero] x = v67 at *
  generalize hpl [negOne, negOne, one] x = v68 at *
  generalize hpl [negOne, one, one] x = v69 at *
  generalize hpl [zero, negOne, negOne] x = v70 at *
  generalize hpl [zero, negOne, one] x = v71 at *
  generalize hpl [zero, zero, negOne] x = v72 at *
  generalize hpl [zero, zero, one] x = v73 at *
  generalize hpl [zero, one, negOne] x = v74 at *
  generalize hpl [zero, one, zero] x = v75 at *
  generalize hpl [zero, one, one] x = v76 at *
  generalize hpl [one, zero, zero] x = v77 at *
  generalize hpl [one, zero, one] x = v78 at *
  generalize hpl [one, one, zero] x = v79 at *
  generalize hpl [negOne, one] x = v80 at *
  generalize hpl [zero, negOne] x = v81 at *
  generalize hpl [zero, zero] x = v82 at *
  generalize hpl [zero, one] x = v83 at *
  generalize hpl [one, zero] x = v84 at *
  generalize hpl [one, one] x = v85 at *
  generalize hpl [negOne] x = v86 at *
  generalize hpl [zero] x = v87 at *
  generalize hpl [one] x = v88 at *
  ring

/-- **`(Ψ₄⁽140⁾)'(ξ) ξ' = p₄⁽140⁾`**, in terms of `ξ`. -/
theorem i8Psi4s140D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s140D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s140 x := by
  rw [i8P4s140_eq_w hx]
  unfold i8Psi4s140D i8P4w140
  rw [← i8Psi4s140k0D_mul hx, ← i8Psi4s140k1D_mul hx, ← i8Psi4s140k2D_mul hx]
  ring

end QED.ThreeLoopD
