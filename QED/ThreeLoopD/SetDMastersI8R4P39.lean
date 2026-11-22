/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P38

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 129 to 131

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s129`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s129D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s129`, `QED.ThreeLoopD.i8Psi4s129D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽129⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s129N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s129N0`. -/
noncomputable def i8Psi4s129dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s129N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s129N0 (i8Psi4s129dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽129⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s129N1 (x : ℝ) : ℝ :=
    (32 - π ^ 2 / 3) +
    (32 - π ^ 2 / 3) * hpl [zero] x +
    (-4) * hpl [negOne, zero] x +
    (32 - π ^ 2 / 3) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (24) * hpl [zero, zero, zero] x +
    (-12) * hpl [negOne, zero, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-4) * hpl [zero, zero, negOne, zero] x +
    (12) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s129N1`. -/
noncomputable def i8Psi4s129dN1 (x : ℝ) : ℝ :=
    0 +
    (32 - π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (32 - π ^ 2 / 3) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (24) * (zero.kernel x * hpl [zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s129N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s129N1 (i8Psi4s129dN1 x) x := by
  unfold i8Psi4s129N1 i8Psi4s129dN1
  exact (((((((((((hasDerivAt_const x (32 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (32 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (32 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽129⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s129N2 (x : ℝ) : ℝ :=
    (-15 / 2) * hpl [negOne, zero] x +
    (4) * hpl [zero, zero] x +
    (-2) * hpl [negOne, zero, zero] x +
    (16 + π ^ 2 / 3) * hpl [zero, zero, zero] x +
    (-18) * hpl [negOne, zero, zero, zero] x

/-- The derivative of `i8Psi4s129N2`. -/
noncomputable def i8Psi4s129dN2 (x : ℝ) : ℝ :=
    (-15 / 2) * (negOne.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x) +
    (16 + π ^ 2 / 3) * (zero.kernel x * hpl [zero, zero] x) +
    (-18) * (negOne.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s129N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s129N2 (i8Psi4s129dN2 x) x := by
  unfold i8Psi4s129N2 i8Psi4s129dN2
  exact ((((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-15 / 2)).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (16 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-18)))

/-- The part of `ξ² Ψ₄⁽129⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s129N3 (x : ℝ) : ℝ :=
    (-15 / 2 - π ^ 2 / 3) +
    (15 / 2 + π ^ 2 / 3) * hpl [zero] x +
    (-4) * hpl [negOne, zero] x +
    (-4 - π ^ 2 / 3) * hpl [zero, zero] x +
    (8) * hpl [negOne, zero, zero] x +
    (4) * hpl [zero, negOne, zero] x +
    (6) * hpl [zero, zero, zero] x +
    (-12) * hpl [negOne, zero, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-4) * hpl [zero, zero, negOne, zero] x +
    (12) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s129N3`. -/
noncomputable def i8Psi4s129dN3 (x : ℝ) : ℝ :=
    0 +
    (15 / 2 + π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (-4 - π ^ 2 / 3) * (zero.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s129N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s129N3 (i8Psi4s129dN3 x) x := by
  unfold i8Psi4s129N3 i8Psi4s129dN3
  exact (((((((((((hasDerivAt_const x (-15 / 2 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (15 / 2 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-4 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽129⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s129N4 (x : ℝ) : ℝ :=
    (-17 / 8 - π ^ 2 / 24) +
    (17 / 4 + π ^ 2 / 12) * hpl [zero] x +
    (-1 / 2) * hpl [negOne, zero] x +
    (-8 - π ^ 2 / 6) * hpl [zero, zero] x +
    (2) * hpl [negOne, zero, zero] x +
    (1) * hpl [zero, negOne, zero] x +
    (6) * hpl [zero, zero, zero] x +
    (-6) * hpl [negOne, zero, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, zero] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (6) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s129N4`. -/
noncomputable def i8Psi4s129dN4 (x : ℝ) : ℝ :=
    0 +
    (17 / 4 + π ^ 2 / 12) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-8 - π ^ 2 / 6) * (zero.kernel x * hpl [zero] x) +
    (2) * (negOne.kernel x * hpl [zero, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x) +
    (-6) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s129N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s129N4 (i8Psi4s129dN4 x) x := by
  unfold i8Psi4s129N4 i8Psi4s129dN4
  exact (((((((((((hasDerivAt_const x (-17 / 8 - π ^ 2 / 24)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (17 / 4 + π ^ 2 / 12))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-8 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (6)))

/-- The part of `Ψ₄⁽129⁾` with constant coefficients. -/
noncomputable def i8Psi4s129W (x : ℝ) : ℝ :=
    (12) * hpl [zero, negOne, zero, zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero, zero] x +
    (4) * hpl [zero, zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s129W`. -/
noncomputable def i8Psi4s129dW (x : ℝ) : ℝ :=
    (12) * (zero.kernel x * hpl [negOne, zero, zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, zero, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s129W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s129W (i8Psi4s129dW x) x := by
  unfold i8Psi4s129W i8Psi4s129dW
  exact (((((hasDerivAt_hpl_cons zero [negOne, zero, zero, zero] hx).const_mul (12)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, zero] hx).const_mul (-12)))

/-- The piece `Ψ₄⁽129⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s129 (x : ℝ) : ℝ :=
  (i8Psi4s129N0 x + x * i8Psi4s129N1 x + x ^ 2 * i8Psi4s129N2 x + x ^ 3 * i8Psi4s129N3 x +
    x ^ 4 * i8Psi4s129N4 x) / x ^ 2 + i8Psi4s129W x

/-- The derivative of `Ψ₄⁽129⁾`. -/
noncomputable def i8Psi4s129D (x : ℝ) : ℝ :=
  ((i8Psi4s129dN0 x + (i8Psi4s129N1 x + x * i8Psi4s129dN1 x) + (2 * x * i8Psi4s129N2 x +
    x ^ 2 * i8Psi4s129dN2 x) + (3 * x ^ 2 * i8Psi4s129N3 x + x ^ 3 * i8Psi4s129dN3 x) +
    (4 * x ^ 3 * i8Psi4s129N4 x + x ^ 4 * i8Psi4s129dN4 x)) * x ^ 2 - (i8Psi4s129N0 x +
    x * i8Psi4s129N1 x + x ^ 2 * i8Psi4s129N2 x + x ^ 3 * i8Psi4s129N3 x +
    x ^ 4 * i8Psi4s129N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s129dW x

theorem hasDerivAt_i8Psi4s129 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s129 (i8Psi4s129D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s129N0 hx).add (X.mul (hasDerivAt_i8Psi4s129N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s129N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s129N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s129N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s129W hx)
  unfold i8Psi4s129
  refine e.congr_deriv ?_
  unfold i8Psi4s129D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 129 of `p₄` in `ξ`: from `t B2 A0 (-λ)^2/2!`, the term with `log^0 (1 -
  ξ) log^2 ξ`. -/
noncomputable def i8P4s129 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x ^ 2 * i13Be2x x * (x / (1 - x))

/-- `p₄⁽129⁾` written over words. -/
noncomputable def i8P4w129 (x : ℝ) : ℝ :=
    (8 - 8 * x - π ^ 2 / 3 - π ^ 2 * x / 3) * hpl [zero, zero] x +
    (12 + 12 * x) * hpl [zero, zero, zero] x +
    (-12 - 12 * x) * hpl [negOne, zero, zero, zero] x +
    (-8 - 8 * x) * hpl [zero, negOne, zero, zero] x +
    (-4 - 4 * x) * hpl [zero, zero, negOne, zero] x +
    (12 + 12 * x) * hpl [zero, zero, zero, zero] x

theorem i8P4s129_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s129 x = i8P4w129 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s129 i8P4w129 i13Be2x
  simp only [i13hw_00, i13hw_000, i13hw_0000, i13hw_00m0 hx, i13hw_0m00 hx, i13hw_m000 hx,
    i13_Li₂_neg_eq hx, i13_log_one_add_eq hx]
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

/-- **`(Ψ₄⁽129⁾)'(ξ) ξ' = p₄⁽129⁾`**, in terms of `ξ`. -/
theorem i8Psi4s129D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s129D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s129 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s129_eq_w hx]
  unfold i8Psi4s129D i8Psi4s129N0 i8Psi4s129N1 i8Psi4s129N2 i8Psi4s129N3 i8Psi4s129N4 i8Psi4s129dN0
    i8Psi4s129dN1 i8Psi4s129dN2 i8Psi4s129dN3 i8Psi4s129dN4 i8Psi4s129dW i8P4w129
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

/-- The part of `ξ² Ψ₄⁽130⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s130N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s130N0`. -/
noncomputable def i8Psi4s130dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s130N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s130N0 (i8Psi4s130dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽130⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s130N1 (x : ℝ) : ℝ :=
    (16 - 2 / 3 * π ^ 2) * hpl [one] x +
    (16 - 2 / 3 * π ^ 2) * hpl [zero, one] x +
    (16 - 2 / 3 * π ^ 2) * hpl [one, zero] x

/-- The derivative of `i8Psi4s130N1`. -/
noncomputable def i8Psi4s130dN1 (x : ℝ) : ℝ :=
    (16 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (16 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [one] x) +
    (16 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s130N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s130N1 (i8Psi4s130dN1 x) x := by
  unfold i8Psi4s130N1 i8Psi4s130dN1
  exact ((((hasDerivAt_hpl_cons one [] hx).const_mul (16 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (16 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (16 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽130⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s130N2 (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * hpl [zero] x +
    (-4 - π ^ 2 / 6) * hpl [one] x +
    (-24 + 5 / 3 * π ^ 2) * hpl [one, zero] x

/-- The derivative of `i8Psi4s130N2`. -/
noncomputable def i8Psi4s130dN2 (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-4 - π ^ 2 / 6) * (one.kernel x * hpl [] x) +
    (-24 + 5 / 3 * π ^ 2) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s130N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s130N2 (i8Psi4s130dN2 x) x := by
  unfold i8Psi4s130N2 i8Psi4s130dN2
  exact ((((hasDerivAt_hpl_cons zero [] hx).const_mul (-16 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-24 + 5 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽130⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s130N3 (x : ℝ) : ℝ :=
    (-20 + 11 / 6 * π ^ 2) +
    (8 - π ^ 2) * hpl [zero] x +
    (-16 + 2 / 3 * π ^ 2) * hpl [one] x +
    (16 - 2 / 3 * π ^ 2) * hpl [zero, one] x +
    (16 - 2 / 3 * π ^ 2) * hpl [one, zero] x

/-- The derivative of `i8Psi4s130N3`. -/
noncomputable def i8Psi4s130dN3 (x : ℝ) : ℝ :=
    0 +
    (8 - π ^ 2) * (zero.kernel x * hpl [] x) +
    (-16 + 2 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (16 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [one] x) +
    (16 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s130N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s130N3 (i8Psi4s130dN3 x) x := by
  unfold i8Psi4s130N3 i8Psi4s130dN3
  exact (((((hasDerivAt_const x (-20 + 11 / 6 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (8 - π ^ 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-16 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (16 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (16 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽130⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s130N4 (x : ℝ) : ℝ :=
    (4 + π ^ 2 / 6) +
    (-4 - π ^ 2 / 6) * hpl [zero] x +
    (4 + π ^ 2 / 6) * hpl [one] x +
    (-8 - π ^ 2 / 3) * hpl [zero, one] x +
    (-8 - π ^ 2 / 3) * hpl [one, zero] x

/-- The derivative of `i8Psi4s130N4`. -/
noncomputable def i8Psi4s130dN4 (x : ℝ) : ℝ :=
    0 +
    (-4 - π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (4 + π ^ 2 / 6) * (one.kernel x * hpl [] x) +
    (-8 - π ^ 2 / 3) * (zero.kernel x * hpl [one] x) +
    (-8 - π ^ 2 / 3) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s130N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s130N4 (i8Psi4s130dN4 x) x := by
  unfold i8Psi4s130N4 i8Psi4s130dN4
  exact (((((hasDerivAt_const x (4 + π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-8 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-8 - π ^ 2 / 3)))

/-- The part of `Ψ₄⁽130⁾` with constant coefficients. -/
noncomputable def i8Psi4s130W (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (16 + 2 / 3 * π ^ 2) * hpl [zero, zero, one] x +
    (16 + 2 / 3 * π ^ 2) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s130W`. -/
noncomputable def i8Psi4s130dW (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero, one] x) +
    (16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s130W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s130W (i8Psi4s130dW x) x := by
  unfold i8Psi4s130W i8Psi4s130dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-16 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (16 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (16 + 2 / 3 * π ^ 2)))

/-- The piece `Ψ₄⁽130⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s130 (x : ℝ) : ℝ :=
  (i8Psi4s130N0 x + x * i8Psi4s130N1 x + x ^ 2 * i8Psi4s130N2 x + x ^ 3 * i8Psi4s130N3 x +
    x ^ 4 * i8Psi4s130N4 x) / x ^ 2 + i8Psi4s130W x

/-- The derivative of `Ψ₄⁽130⁾`. -/
noncomputable def i8Psi4s130D (x : ℝ) : ℝ :=
  ((i8Psi4s130dN0 x + (i8Psi4s130N1 x + x * i8Psi4s130dN1 x) + (2 * x * i8Psi4s130N2 x +
    x ^ 2 * i8Psi4s130dN2 x) + (3 * x ^ 2 * i8Psi4s130N3 x + x ^ 3 * i8Psi4s130dN3 x) +
    (4 * x ^ 3 * i8Psi4s130N4 x + x ^ 4 * i8Psi4s130dN4 x)) * x ^ 2 - (i8Psi4s130N0 x +
    x * i8Psi4s130N1 x + x ^ 2 * i8Psi4s130N2 x + x ^ 3 * i8Psi4s130N3 x +
    x ^ 4 * i8Psi4s130N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s130dW x

theorem hasDerivAt_i8Psi4s130 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s130 (i8Psi4s130D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s130N0 hx).add (X.mul (hasDerivAt_i8Psi4s130N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s130N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s130N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s130N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s130W hx)
  unfold i8Psi4s130
  refine e.congr_deriv ?_
  unfold i8Psi4s130D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 130 of `p₄` in `ξ`: from `t B2 A0 (-λ)^2/2!`, the term with `log^1 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s130 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * Real.log x * ((1 + x) / (1 - x) * ((24 +
    ((-1) * π ^ 2) + ((-24) * x) + ((-1) * π ^ 2 * x)) / (6 + (6 * x)))) * (x / (1 - x)))

/-- `p₄⁽130⁾` written over words. -/
noncomputable def i8P4w130 (x : ℝ) : ℝ :=
    (16 - 16 * x - 2 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x) * hpl [zero, one] x +
    (16 - 16 * x - 2 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x) * hpl [one, zero] x

theorem i8P4s130_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s130 x = i8P4w130 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s130 i8P4w130
  rw [i13_log_one_sub_eq hx]
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((16 - 16 * x - 2 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x)) * e0
  field_simp
  generalize hpl [zero, one] x = v0 at *
  generalize hpl [one, zero] x = v1 at *
  generalize hpl [zero] x = v2 at *
  generalize hpl [one] x = v3 at *
  ring

/-- **`(Ψ₄⁽130⁾)'(ξ) ξ' = p₄⁽130⁾`**, in terms of `ξ`. -/
theorem i8Psi4s130D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s130D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s130 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s130_eq_w hx]
  unfold i8Psi4s130D i8Psi4s130N0 i8Psi4s130N1 i8Psi4s130N2 i8Psi4s130N3 i8Psi4s130N4 i8Psi4s130dN0
    i8Psi4s130dN1 i8Psi4s130dN2 i8Psi4s130dN3 i8Psi4s130dN4 i8Psi4s130dW i8P4w130
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

/-- The part of `ξ² Ψ₄⁽131⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s131k0N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s131k0N0`. -/
noncomputable def i8Psi4s131k0dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s131k0N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k0N0 (i8Psi4s131k0dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽131⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s131k0N1 (x : ℝ) : ℝ :=
    (-8) * hpl [negOne, zero, one] x +
    (-16) * hpl [negOne, zero, zero, one] x +
    (-16) * hpl [negOne, zero, one, zero] x +
    (-16) * hpl [negOne, one, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, one] x

/-- The derivative of `i8Psi4s131k0N1`. -/
noncomputable def i8Psi4s131k0dN1 (x : ℝ) : ℝ :=
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-16) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-16) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-16) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, one] x)

theorem hasDerivAt_i8Psi4s131k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k0N1 (i8Psi4s131k0dN1 x) x := by
  unfold i8Psi4s131k0N1 i8Psi4s131k0dN1
  exact ((((((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽131⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s131k0N2 (x : ℝ) : ℝ :=
    (-31 / 2) * hpl [one] x +
    (10) * hpl [one, zero] x +
    (-2) * hpl [negOne, zero, one] x +
    (8) * hpl [zero, zero, one] x +
    (-12) * hpl [one, zero, zero] x +
    (-24) * hpl [negOne, zero, zero, one] x +
    (-24) * hpl [negOne, zero, one, zero] x +
    (-24) * hpl [negOne, one, zero, zero] x

/-- The derivative of `i8Psi4s131k0N2`. -/
noncomputable def i8Psi4s131k0dN2 (x : ℝ) : ℝ :=
    (-31 / 2) * (one.kernel x * hpl [] x) +
    (10) * (one.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (-12) * (one.kernel x * hpl [zero, zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-24) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-24) * (negOne.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s131k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k0N2 (i8Psi4s131k0dN2 x) x := by
  unfold i8Psi4s131k0N2 i8Psi4s131k0dN2
  exact (((((((((hasDerivAt_hpl_cons one [] hx).const_mul (-31 / 2)).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽131⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s131k0N3 (x : ℝ) : ℝ :=
    (75 / 2) +
    (-22) * hpl [zero] x +
    (14) * hpl [one] x +
    (12) * hpl [zero, zero] x +
    (-14) * hpl [zero, one] x +
    (-8) * hpl [one, zero] x +
    (8) * hpl [negOne, zero, one] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (8) * hpl [one, zero, zero] x +
    (-16) * hpl [negOne, zero, zero, one] x +
    (-16) * hpl [negOne, zero, one, zero] x +
    (-16) * hpl [negOne, one, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, one] x

/-- The derivative of `i8Psi4s131k0N3`. -/
noncomputable def i8Psi4s131k0dN3 (x : ℝ) : ℝ :=
    0 +
    (-22) * (zero.kernel x * hpl [] x) +
    (14) * (one.kernel x * hpl [] x) +
    (12) * (zero.kernel x * hpl [zero] x) +
    (-14) * (zero.kernel x * hpl [one] x) +
    (-8) * (one.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-16) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-16) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, one] x)

theorem hasDerivAt_i8Psi4s131k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k0N3 (i8Psi4s131k0dN3 x) x := by
  unfold i8Psi4s131k0N3 i8Psi4s131k0dN3
  exact ((((((((((((((hasDerivAt_const x (75 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽131⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s131k0N4 (x : ℝ) : ℝ :=
    (7 / 4) +
    (-2) * hpl [zero] x +
    (3 / 2) * hpl [one] x +
    (2) * hpl [zero, zero] x +
    (-3) * hpl [zero, one] x +
    (-2) * hpl [one, zero] x +
    (2) * hpl [negOne, zero, one] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (4) * hpl [one, zero, zero] x +
    (-8) * hpl [negOne, zero, zero, one] x +
    (-8) * hpl [negOne, zero, one, zero] x +
    (-8) * hpl [negOne, one, zero, zero] x +
    (-4) * hpl [zero, negOne, zero, one] x

/-- The derivative of `i8Psi4s131k0N4`. -/
noncomputable def i8Psi4s131k0dN4 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x) +
    (3 / 2) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (-3) * (zero.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [zero] x) +
    (2) * (negOne.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero, one] x) +
    (-8) * (negOne.kernel x * hpl [zero, one, zero] x) +
    (-8) * (negOne.kernel x * hpl [one, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, one] x)

theorem hasDerivAt_i8Psi4s131k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k0N4 (i8Psi4s131k0dN4 x) x := by
  unfold i8Psi4s131k0N4 i8Psi4s131k0dN4
  exact ((((((((((((((hasDerivAt_const x (7 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽131⁾` with constant coefficients. -/
noncomputable def i8Psi4s131k0W (x : ℝ) : ℝ :=
    (16) * hpl [zero, zero, zero, one] x +
    (16) * hpl [zero, zero, one, zero] x +
    (16) * hpl [zero, one, zero, zero] x +
    (16) * hpl [zero, negOne, zero, zero, one] x +
    (16) * hpl [zero, negOne, zero, one, zero] x +
    (16) * hpl [zero, negOne, one, zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero, one] x

/-- The derivative of `i8Psi4s131k0W`. -/
noncomputable def i8Psi4s131k0dW (x : ℝ) : ℝ :=
    (16) * (zero.kernel x * hpl [zero, zero, one] x) +
    (16) * (zero.kernel x * hpl [zero, one, zero] x) +
    (16) * (zero.kernel x * hpl [one, zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, zero, one] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, one, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, one, zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, zero, one] x)

theorem hasDerivAt_i8Psi4s131k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k0W (i8Psi4s131k0dW x) x := by
  unfold i8Psi4s131k0W i8Psi4s131k0dW
  exact ((((((((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, one] hx).const_mul (8)))

/-- Chunk 0 of the piece `Ψ₄⁽131⁾`. -/
noncomputable def i8Psi4s131k0 (x : ℝ) : ℝ :=
  (i8Psi4s131k0N0 x + x * i8Psi4s131k0N1 x + x ^ 2 * i8Psi4s131k0N2 x + x ^ 3 * i8Psi4s131k0N3 x +
    x ^ 4 * i8Psi4s131k0N4 x) / x ^ 2 + i8Psi4s131k0W x

/-- The derivative of `i8Psi4s131k0`. -/
noncomputable def i8Psi4s131k0D (x : ℝ) : ℝ :=
  ((i8Psi4s131k0dN0 x + (i8Psi4s131k0N1 x + x * i8Psi4s131k0dN1 x) + (2 * x * i8Psi4s131k0N2 x +
    x ^ 2 * i8Psi4s131k0dN2 x) + (3 * x ^ 2 * i8Psi4s131k0N3 x + x ^ 3 * i8Psi4s131k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s131k0N4 x + x ^ 4 * i8Psi4s131k0dN4 x)) * x ^ 2 - (i8Psi4s131k0N0 x +
    x * i8Psi4s131k0N1 x + x ^ 2 * i8Psi4s131k0N2 x + x ^ 3 * i8Psi4s131k0N3 x +
    x ^ 4 * i8Psi4s131k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s131k0dW x

theorem hasDerivAt_i8Psi4s131k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k0 (i8Psi4s131k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s131k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s131k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s131k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s131k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s131k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s131k0W hx)
  unfold i8Psi4s131k0
  refine e.congr_deriv ?_
  unfold i8Psi4s131k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽131⁾` over words. -/
noncomputable def i8P4w131k0 (x : ℝ) : ℝ :=
    (-16 - 16 * x) * hpl [negOne, zero, zero, one] x +
    (-16 - 16 * x) * hpl [negOne, zero, one, zero] x +
    (-16 - 16 * x) * hpl [negOne, one, zero, zero] x +
    (-8 - 8 * x) * hpl [zero, negOne, zero, one] x

theorem i8Psi4s131k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s131k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w131k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s131k0D i8Psi4s131k0N0 i8Psi4s131k0N1 i8Psi4s131k0N2 i8Psi4s131k0N3 i8Psi4s131k0N4
    i8Psi4s131k0dN0 i8Psi4s131k0dN1 i8Psi4s131k0dN2 i8Psi4s131k0dN3 i8Psi4s131k0dN4 i8Psi4s131k0dW
    i8P4w131k0
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, zero, zero, one] x = v0 at *
  generalize hpl [zero, negOne, zero, one, zero] x = v1 at *
  generalize hpl [zero, negOne, one, zero, zero] x = v2 at *
  generalize hpl [zero, zero, negOne, zero, one] x = v3 at *
  generalize hpl [negOne, zero, zero, one] x = v4 at *
  generalize hpl [negOne, zero, one, zero] x = v5 at *
  generalize hpl [negOne, one, zero, zero] x = v6 at *
  generalize hpl [zero, negOne, zero, one] x = v7 at *
  generalize hpl [zero, zero, zero, one] x = v8 at *
  generalize hpl [zero, zero, one, zero] x = v9 at *
  generalize hpl [zero, one, zero, zero] x = v10 at *
  generalize hpl [negOne, zero, one] x = v11 at *
  generalize hpl [zero, zero, one] x = v12 at *
  generalize hpl [zero, one, zero] x = v13 at *
  generalize hpl [one, zero, zero] x = v14 at *
  generalize hpl [zero, zero] x = v15 at *
  generalize hpl [zero, one] x = v16 at *
  generalize hpl [one, zero] x = v17 at *
  generalize hpl [zero] x = v18 at *
  generalize hpl [one] x = v19 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽131⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s131k1N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s131k1N0`. -/
noncomputable def i8Psi4s131k1dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s131k1N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k1N0 (i8Psi4s131k1dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽131⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s131k1N1 (x : ℝ) : ℝ :=
    (-8) * hpl [negOne, one, zero] x +
    (-8) * hpl [one, negOne, zero] x +
    (-8) * hpl [zero, negOne, one, zero] x +
    (-8) * hpl [zero, one, negOne, zero] x +
    (-16) * hpl [one, negOne, zero, zero] x +
    (-8) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s131k1N1`. -/
noncomputable def i8Psi4s131k1dN1 (x : ℝ) : ℝ :=
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-16) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s131k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k1N1 (i8Psi4s131k1dN1 x) x := by
  unfold i8Psi4s131k1N1 i8Psi4s131k1dN1
  exact (((((((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽131⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s131k1N2 (x : ℝ) : ℝ :=
    (20) * hpl [negOne, zero] x +
    (7) * hpl [one, zero] x +
    (-20) * hpl [negOne, zero, zero] x +
    (-2) * hpl [negOne, one, zero] x +
    (8) * hpl [zero, negOne, zero] x +
    (-2) * hpl [one, negOne, zero] x +
    (40) * hpl [one, negOne, zero, zero] x +
    (20) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s131k1N2`. -/
noncomputable def i8Psi4s131k1dN2 (x : ℝ) : ℝ :=
    (20) * (negOne.kernel x * hpl [zero] x) +
    (7) * (one.kernel x * hpl [zero] x) +
    (-20) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (40) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (20) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s131k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k1N2 (i8Psi4s131k1dN2 x) x := by
  unfold i8Psi4s131k1N2 i8Psi4s131k1dN2
  exact (((((((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (20)).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (20)))

/-- The part of `ξ² Ψ₄⁽131⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s131k1N3 (x : ℝ) : ℝ :=
    (47) +
    (-47) * hpl [zero] x +
    (22) * hpl [negOne, zero] x +
    (20) * hpl [zero, zero] x +
    (-6) * hpl [one, zero] x +
    (-24) * hpl [negOne, zero, zero] x +
    (8) * hpl [negOne, one, zero] x +
    (-12) * hpl [zero, negOne, zero] x +
    (8) * hpl [one, negOne, zero] x +
    (-8) * hpl [zero, negOne, one, zero] x +
    (-8) * hpl [zero, one, negOne, zero] x +
    (-16) * hpl [one, negOne, zero, zero] x +
    (-8) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s131k1N3`. -/
noncomputable def i8Psi4s131k1dN3 (x : ℝ) : ℝ :=
    0 +
    (-47) * (zero.kernel x * hpl [] x) +
    (22) * (negOne.kernel x * hpl [zero] x) +
    (20) * (zero.kernel x * hpl [zero] x) +
    (-6) * (one.kernel x * hpl [zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, zero] x) +
    (8) * (negOne.kernel x * hpl [one, zero] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero] x) +
    (8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-16) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s131k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k1N3 (i8Psi4s131k1dN3 x) x := by
  unfold i8Psi4s131k1N3 i8Psi4s131k1dN3
  exact (((((((((((((hasDerivAt_const x (47)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-47))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (22))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽131⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s131k1N4 (x : ℝ) : ℝ :=
    (5 / 4) +
    (-5 / 2) * hpl [zero] x +
    (2) * hpl [negOne, zero] x +
    (2) * hpl [zero, zero] x +
    (-1) * hpl [one, zero] x +
    (-4) * hpl [negOne, zero, zero] x +
    (2) * hpl [negOne, one, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (2) * hpl [one, negOne, zero] x +
    (-4) * hpl [zero, negOne, one, zero] x +
    (-4) * hpl [zero, one, negOne, zero] x +
    (-8) * hpl [one, negOne, zero, zero] x +
    (-4) * hpl [one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s131k1N4`. -/
noncomputable def i8Psi4s131k1dN4 (x : ℝ) : ℝ :=
    0 +
    (-5 / 2) * (zero.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (-1) * (one.kernel x * hpl [zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (2) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (2) * (one.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-4) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (one.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s131k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k1N4 (i8Psi4s131k1dN4 x) x := by
  unfold i8Psi4s131k1N4 i8Psi4s131k1dN4
  exact (((((((((((((hasDerivAt_const x (5 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽131⁾` with constant coefficients. -/
noncomputable def i8Psi4s131k1W (x : ℝ) : ℝ :=
    (8) * hpl [zero, one, zero] x +
    (16) * hpl [zero, negOne, zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero] x +
    (8) * hpl [zero, zero, negOne, one, zero] x +
    (8) * hpl [zero, zero, one, negOne, zero] x +
    (16) * hpl [zero, one, negOne, zero, zero] x +
    (8) * hpl [zero, one, zero, negOne, zero] x

/-- The derivative of `i8Psi4s131k1W`. -/
noncomputable def i8Psi4s131k1dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, one, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one, negOne, zero] x) +
    (16) * (zero.kernel x * hpl [one, negOne, zero, zero] x) +
    (8) * (zero.kernel x * hpl [one, zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s131k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k1W (i8Psi4s131k1dW x) x := by
  unfold i8Psi4s131k1W i8Psi4s131k1dW
  exact ((((((((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne, zero] hx).const_mul (8)))

/-- Chunk 1 of the piece `Ψ₄⁽131⁾`. -/
noncomputable def i8Psi4s131k1 (x : ℝ) : ℝ :=
  (i8Psi4s131k1N0 x + x * i8Psi4s131k1N1 x + x ^ 2 * i8Psi4s131k1N2 x + x ^ 3 * i8Psi4s131k1N3 x +
    x ^ 4 * i8Psi4s131k1N4 x) / x ^ 2 + i8Psi4s131k1W x

/-- The derivative of `i8Psi4s131k1`. -/
noncomputable def i8Psi4s131k1D (x : ℝ) : ℝ :=
  ((i8Psi4s131k1dN0 x + (i8Psi4s131k1N1 x + x * i8Psi4s131k1dN1 x) + (2 * x * i8Psi4s131k1N2 x +
    x ^ 2 * i8Psi4s131k1dN2 x) + (3 * x ^ 2 * i8Psi4s131k1N3 x + x ^ 3 * i8Psi4s131k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s131k1N4 x + x ^ 4 * i8Psi4s131k1dN4 x)) * x ^ 2 - (i8Psi4s131k1N0 x +
    x * i8Psi4s131k1N1 x + x ^ 2 * i8Psi4s131k1N2 x + x ^ 3 * i8Psi4s131k1N3 x +
    x ^ 4 * i8Psi4s131k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s131k1dW x

theorem hasDerivAt_i8Psi4s131k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131k1 (i8Psi4s131k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s131k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s131k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s131k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s131k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s131k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s131k1W hx)
  unfold i8Psi4s131k1
  refine e.congr_deriv ?_
  unfold i8Psi4s131k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽131⁾` over words. -/
noncomputable def i8P4w131k1 (x : ℝ) : ℝ :=
    (-8 - 8 * x) * hpl [zero, negOne, one, zero] x +
    (-8 - 8 * x) * hpl [zero, one, negOne, zero] x +
    (-16 - 16 * x) * hpl [one, negOne, zero, zero] x +
    (-8 - 8 * x) * hpl [one, zero, negOne, zero] x

theorem i8Psi4s131k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s131k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w131k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s131k1D i8Psi4s131k1N0 i8Psi4s131k1N1 i8Psi4s131k1N2 i8Psi4s131k1N3 i8Psi4s131k1N4
    i8Psi4s131k1dN0 i8Psi4s131k1dN1 i8Psi4s131k1dN2 i8Psi4s131k1dN3 i8Psi4s131k1dN4 i8Psi4s131k1dW
    i8P4w131k1
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, zero, negOne, one, zero] x = v0 at *
  generalize hpl [zero, zero, one, negOne, zero] x = v1 at *
  generalize hpl [zero, one, negOne, zero, zero] x = v2 at *
  generalize hpl [zero, one, zero, negOne, zero] x = v3 at *
  generalize hpl [zero, negOne, zero, zero] x = v4 at *
  generalize hpl [zero, negOne, one, zero] x = v5 at *
  generalize hpl [zero, zero, negOne, zero] x = v6 at *
  generalize hpl [zero, one, negOne, zero] x = v7 at *
  generalize hpl [one, negOne, zero, zero] x = v8 at *
  generalize hpl [one, zero, negOne, zero] x = v9 at *
  generalize hpl [negOne, zero, zero] x = v10 at *
  generalize hpl [negOne, one, zero] x = v11 at *
  generalize hpl [zero, negOne, zero] x = v12 at *
  generalize hpl [zero, one, zero] x = v13 at *
  generalize hpl [one, negOne, zero] x = v14 at *
  generalize hpl [negOne, zero] x = v15 at *
  generalize hpl [zero, zero] x = v16 at *
  generalize hpl [one, zero] x = v17 at *
  generalize hpl [zero] x = v18 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽131⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s131 (x : ℝ) : ℝ :=
  i8Psi4s131k0 x + i8Psi4s131k1 x

/-- The derivative of `Ψ₄⁽131⁾`. -/
noncomputable def i8Psi4s131D (x : ℝ) : ℝ :=
  i8Psi4s131k0D x + i8Psi4s131k1D x

theorem hasDerivAt_i8Psi4s131 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s131 (i8Psi4s131D x) x := by
  unfold i8Psi4s131 i8Psi4s131D
  exact ((hasDerivAt_i8Psi4s131k0 hx).add (hasDerivAt_i8Psi4s131k1 hx))

/-- The sub-piece 131 of `p₄` in `ξ`: from `t B2 A0 (-λ)^2/2!`, the term with `log^1 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s131 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * Real.log x * ((1 + x) / (1 -
    x) * ((-2) * hpl [negOne, zero] x)) * (x / (1 - x)))

/-- `p₄⁽131⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w131 (x : ℝ) : ℝ :=
  i8P4w131k0 x + i8P4w131k1 x

theorem i8P4s131_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s131 x = i8P4w131 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s131 i8P4w131 i8P4w131k0 i8P4w131k1
  rw [i13_log_one_sub_eq hx]
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [one] hx
  have e1 := hpl_mul_hpl [negOne, zero] [zero, one] hx
  have e2 := hpl_mul_hpl [negOne, zero] [one, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  linear_combination (norm := skip) ((-8 - 8 * x) * hpl [negOne, zero] x) * e0 + ((-8 -
    8 * x)) * e1 + ((-8 - 8 * x)) * e2
  field_simp
  generalize hpl [negOne, zero, zero, one] x = v0 at *
  generalize hpl [negOne, zero, one, zero] x = v1 at *
  generalize hpl [negOne, one, zero, zero] x = v2 at *
  generalize hpl [zero, negOne, zero, one] x = v3 at *
  generalize hpl [zero, negOne, one, zero] x = v4 at *
  generalize hpl [zero, one, negOne, zero] x = v5 at *
  generalize hpl [one, negOne, zero, zero] x = v6 at *
  generalize hpl [one, zero, negOne, zero] x = v7 at *
  generalize hpl [negOne, zero] x = v8 at *
  generalize hpl [zero, one] x = v9 at *
  generalize hpl [one, zero] x = v10 at *
  generalize hpl [zero] x = v11 at *
  generalize hpl [one] x = v12 at *
  ring

/-- **`(Ψ₄⁽131⁾)'(ξ) ξ' = p₄⁽131⁾`**, in terms of `ξ`. -/
theorem i8Psi4s131D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s131D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s131 x := by
  rw [i8P4s131_eq_w hx]
  unfold i8Psi4s131D i8P4w131
  rw [← i8Psi4s131k0D_mul hx, ← i8Psi4s131k1D_mul hx]
  ring

end QED.ThreeLoopD
