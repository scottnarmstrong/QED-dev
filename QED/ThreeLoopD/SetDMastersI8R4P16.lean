/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P15

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 76 to 77

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s76`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s76D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s76`, `QED.ThreeLoopD.i8Psi4s76D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽76⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s76N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s76N0`. -/
noncomputable def i8Psi4s76dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s76N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s76N0 (i8Psi4s76dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽76⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s76N1 (x : ℝ) : ℝ :=
    (22 - π ^ 2 / 3) +
    (22 - π ^ 2 / 3) * hpl [zero] x +
    (-4) * hpl [negOne, zero] x +
    (14) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (6) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s76N1`. -/
noncomputable def i8Psi4s76dN1 (x : ℝ) : ℝ :=
    0 +
    (22 - π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (14) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s76N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s76N1 (i8Psi4s76dN1 x) x := by
  unfold i8Psi4s76N1 i8Psi4s76dN1
  exact (((((((hasDerivAt_const x (22 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (22 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6)))

/-- The part of `ξ² Ψ₄⁽76⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s76N2 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne, zero] x +
    (12 + π ^ 2 / 3) * hpl [zero, zero] x +
    (-12) * hpl [negOne, zero, zero] x

/-- The derivative of `i8Psi4s76N2`. -/
noncomputable def i8Psi4s76dN2 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (12 + π ^ 2 / 3) * (zero.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s76N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s76N2 (i8Psi4s76dN2 x) x := by
  unfold i8Psi4s76N2 i8Psi4s76dN2
  exact ((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (12 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽76⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s76N3 (x : ℝ) : ℝ :=
    (1 + π ^ 2 / 3) +
    (-1 - π ^ 2 / 3) * hpl [zero] x +
    (4) * hpl [negOne, zero] x +
    (6) * hpl [zero, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (6) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s76N3`. -/
noncomputable def i8Psi4s76dN3 (x : ℝ) : ℝ :=
    0 +
    (-1 - π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (4) * (negOne.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s76N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s76N3 (i8Psi4s76dN3 x) x := by
  unfold i8Psi4s76N3 i8Psi4s76dN3
  exact (((((((hasDerivAt_const x (1 + π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6)))

/-- The part of `ξ² Ψ₄⁽76⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s76N4 (x : ℝ) : ℝ :=
    (27 / 8 + π ^ 2 / 12) +
    (-27 / 4 - π ^ 2 / 6) * hpl [zero] x +
    (1) * hpl [negOne, zero] x +
    (9 / 2) * hpl [zero, zero] x +
    (-4) * hpl [negOne, zero, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (3) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s76N4`. -/
noncomputable def i8Psi4s76dN4 (x : ℝ) : ℝ :=
    0 +
    (-27 / 4 - π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (9 / 2) * (zero.kernel x * hpl [zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (3) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s76N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s76N4 (i8Psi4s76dN4 x) x := by
  unfold i8Psi4s76N4 i8Psi4s76dN4
  exact (((((((hasDerivAt_const x (27 / 8 + π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-27 / 4 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (9 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (3)))

/-- The part of `Ψ₄⁽76⁾` with constant coefficients. -/
noncomputable def i8Psi4s76W (x : ℝ) : ℝ :=
    (8) * hpl [zero, negOne, zero, zero] x +
    (4) * hpl [zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s76W`. -/
noncomputable def i8Psi4s76dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s76W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s76W (i8Psi4s76dW x) x := by
  unfold i8Psi4s76W i8Psi4s76dW
  exact ((((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-6)))

/-- The piece `Ψ₄⁽76⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s76 (x : ℝ) : ℝ :=
  (i8Psi4s76N0 x + x * i8Psi4s76N1 x + x ^ 2 * i8Psi4s76N2 x + x ^ 3 * i8Psi4s76N3 x +
    x ^ 4 * i8Psi4s76N4 x) / x ^ 2 + i8Psi4s76W x

/-- The derivative of `Ψ₄⁽76⁾`. -/
noncomputable def i8Psi4s76D (x : ℝ) : ℝ :=
  ((i8Psi4s76dN0 x + (i8Psi4s76N1 x + x * i8Psi4s76dN1 x) + (2 * x * i8Psi4s76N2 x +
    x ^ 2 * i8Psi4s76dN2 x) + (3 * x ^ 2 * i8Psi4s76N3 x + x ^ 3 * i8Psi4s76dN3 x) +
    (4 * x ^ 3 * i8Psi4s76N4 x + x ^ 4 * i8Psi4s76dN4 x)) * x ^ 2 - (i8Psi4s76N0 x +
    x * i8Psi4s76N1 x + x ^ 2 * i8Psi4s76N2 x + x ^ 3 * i8Psi4s76N3 x +
    x ^ 4 * i8Psi4s76N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s76dW x

theorem hasDerivAt_i8Psi4s76 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s76 (i8Psi4s76D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s76N0 hx).add (X.mul (hasDerivAt_i8Psi4s76N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s76N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s76N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s76N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s76W hx)
  unfold i8Psi4s76
  refine e.congr_deriv ?_
  unfold i8Psi4s76D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 76 of `p₄` in `ξ`: from `t B2 A1 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s76 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * i13Be2x x * ((1 + x) / (1 - x) * (x / (1 + x)))

/-- `p₄⁽76⁾` written over words. -/
noncomputable def i8P4w76 (x : ℝ) : ℝ :=
    (8 - 8 * x - π ^ 2 / 3 - π ^ 2 * x / 3) * hpl [zero] x +
    (8 + 8 * x) * hpl [zero, zero] x +
    (-8 - 8 * x) * hpl [negOne, zero, zero] x +
    (-4 - 4 * x) * hpl [zero, negOne, zero] x +
    (6 + 6 * x) * hpl [zero, zero, zero] x

theorem i8P4s76_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s76 x = i8P4w76 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s76 i8P4w76 i13Be2x
  simp only [hpl_zero, i13hw_00, i13hw_000, i13hw_0m0 hx, i13hw_m00 hx, i13_Li₂_neg_eq hx,
    i13_log_one_add_eq hx]
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
  generalize hpl [zero, negOne, one, one, negOne] x = v11 at *
  generalize hpl [zero, negOne, one, one, one] x = v12 at *
  generalize hpl [zero, zero, negOne, negOne, negOne] x = v13 at *
  generalize hpl [zero, zero, negOne, negOne, one] x = v14 at *
  generalize hpl [zero, zero, negOne, zero, negOne] x = v15 at *
  generalize hpl [zero, zero, negOne, zero, one] x = v16 at *
  generalize hpl [zero, zero, negOne, one, negOne] x = v17 at *
  generalize hpl [zero, zero, negOne, one, one] x = v18 at *
  generalize hpl [zero, zero, zero, negOne, negOne] x = v19 at *
  generalize hpl [zero, zero, zero, negOne, one] x = v20 at *
  generalize hpl [zero, zero, zero, zero, negOne] x = v21 at *
  generalize hpl [zero, zero, zero, zero, one] x = v22 at *
  generalize hpl [zero, zero, zero, one, negOne] x = v23 at *
  generalize hpl [zero, zero, zero, one, one] x = v24 at *
  generalize hpl [zero, zero, one, negOne, negOne] x = v25 at *
  generalize hpl [zero, zero, one, negOne, one] x = v26 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v27 at *
  generalize hpl [zero, zero, one, one, negOne] x = v28 at *
  generalize hpl [zero, zero, one, one, one] x = v29 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v30 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v31 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v32 at *
  generalize hpl [zero, one, negOne, one, one] x = v33 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v34 at *
  generalize hpl [zero, one, one, negOne, one] x = v35 at *
  generalize hpl [zero, one, one, one, negOne] x = v36 at *
  generalize hpl [zero, one, one, one, one] x = v37 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v38 at *
  generalize hpl [zero, negOne, negOne, one] x = v39 at *
  generalize hpl [zero, negOne, zero, zero] x = v40 at *
  generalize hpl [zero, negOne, zero, one] x = v41 at *
  generalize hpl [zero, negOne, one, negOne] x = v42 at *
  generalize hpl [zero, negOne, one, one] x = v43 at *
  generalize hpl [zero, zero, negOne, negOne] x = v44 at *
  generalize hpl [zero, zero, negOne, zero] x = v45 at *
  generalize hpl [zero, zero, negOne, one] x = v46 at *
  generalize hpl [zero, zero, zero, negOne] x = v47 at *
  generalize hpl [zero, zero, zero, zero] x = v48 at *
  generalize hpl [zero, zero, zero, one] x = v49 at *
  generalize hpl [zero, zero, one, negOne] x = v50 at *
  generalize hpl [zero, zero, one, one] x = v51 at *
  generalize hpl [zero, one, negOne, negOne] x = v52 at *
  generalize hpl [zero, one, negOne, one] x = v53 at *
  generalize hpl [zero, one, one, negOne] x = v54 at *
  generalize hpl [zero, one, one, one] x = v55 at *
  generalize hpl [negOne, negOne, one] x = v56 at *
  generalize hpl [negOne, zero, zero] x = v57 at *
  generalize hpl [negOne, one, one] x = v58 at *
  generalize hpl [zero, negOne, negOne] x = v59 at *
  generalize hpl [zero, negOne, zero] x = v60 at *
  generalize hpl [zero, negOne, one] x = v61 at *
  generalize hpl [zero, zero, negOne] x = v62 at *
  generalize hpl [zero, zero, zero] x = v63 at *
  generalize hpl [zero, zero, one] x = v64 at *
  generalize hpl [zero, one, negOne] x = v65 at *
  generalize hpl [zero, one, one] x = v66 at *
  generalize hpl [negOne, zero] x = v67 at *
  generalize hpl [negOne, one] x = v68 at *
  generalize hpl [zero, negOne] x = v69 at *
  generalize hpl [zero, zero] x = v70 at *
  generalize hpl [zero, one] x = v71 at *
  generalize hpl [negOne] x = v72 at *
  generalize hpl [zero] x = v73 at *
  generalize hpl [one] x = v74 at *
  ring

/-- **`(Ψ₄⁽76⁾)'(ξ) ξ' = p₄⁽76⁾`**, in terms of `ξ`. -/
theorem i8Psi4s76D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s76D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s76 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s76_eq_w hx]
  unfold i8Psi4s76D i8Psi4s76N0 i8Psi4s76N1 i8Psi4s76N2 i8Psi4s76N3 i8Psi4s76N4 i8Psi4s76dN0
    i8Psi4s76dN1 i8Psi4s76dN2 i8Psi4s76dN3 i8Psi4s76dN4 i8Psi4s76dW i8P4w76
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, zero, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, zero] x = v1 at *
  generalize hpl [zero, zero, zero, zero] x = v2 at *
  generalize hpl [negOne, zero, zero] x = v3 at *
  generalize hpl [zero, negOne, zero] x = v4 at *
  generalize hpl [zero, zero, zero] x = v5 at *
  generalize hpl [negOne, zero] x = v6 at *
  generalize hpl [zero, zero] x = v7 at *
  generalize hpl [zero] x = v8 at *
  ring

/-- The part of `ξ² Ψ₄⁽77⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s77N0 (x : ℝ) : ℝ :=
    (-27 / 8 + π ^ 2 / 12) * hpl [negOne] x +
    (-27 / 4 + π ^ 2 / 6) * hpl [negOne, zero] x +
    (-27 / 4 + π ^ 2 / 6) * hpl [zero, negOne] x +
    (2) * hpl [negOne, negOne, zero] x +
    (1) * hpl [negOne, zero, negOne] x +
    (-11 / 2) * hpl [negOne, zero, zero] x +
    (-11 / 2) * hpl [zero, negOne, zero] x +
    (-11 / 2) * hpl [zero, zero, negOne] x +
    (8) * hpl [negOne, negOne, zero, zero] x +
    (6) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [negOne, zero, zero, negOne] x +
    (-3) * hpl [negOne, zero, zero, zero] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (2) * hpl [zero, negOne, zero, negOne] x +
    (-3) * hpl [zero, negOne, zero, zero] x +
    (-3) * hpl [zero, zero, negOne, zero] x +
    (-3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s77N0`. -/
noncomputable def i8Psi4s77dN0 (x : ℝ) : ℝ :=
    (-27 / 8 + π ^ 2 / 12) * (negOne.kernel x * hpl [] x) +
    (-27 / 4 + π ^ 2 / 6) * (negOne.kernel x * hpl [zero] x) +
    (-27 / 4 + π ^ 2 / 6) * (zero.kernel x * hpl [negOne] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-11 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (6) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-3) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-3) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s77N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77N0 (i8Psi4s77dN0 x) x := by
  unfold i8Psi4s77N0 i8Psi4s77dN0
  exact ((((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-27 / 8 + π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-27 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-27 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3)))

/-- Chunk 0 of `i8Psi4s77N1`. -/
noncomputable def i8Psi4s77N1c0 (x : ℝ) : ℝ :=
    (-149 / 8 + π ^ 2 / 4) +
    (-23 + 2 / 3 * π ^ 2) * hpl [negOne] x +
    (-61 / 4 + π ^ 2 / 6) * hpl [zero] x +
    (-20 + 2 / 3 * π ^ 2) * hpl [negOne, zero] x +
    (-23 + 2 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (-17 / 2) * hpl [zero, zero] x +
    (16) * hpl [negOne, negOne, zero] x +
    (8) * hpl [negOne, zero, negOne] x +
    (-20) * hpl [negOne, zero, zero] x +
    (-22) * hpl [zero, negOne, zero] x +
    (-24) * hpl [zero, zero, negOne] x +
    (-3) * hpl [zero, zero, zero] x +
    (32) * hpl [negOne, negOne, zero, zero] x +
    (24) * hpl [negOne, zero, negOne, zero] x +
    (16) * hpl [negOne, zero, zero, negOne] x +
    (-12) * hpl [negOne, zero, zero, zero] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (8) * hpl [zero, negOne, zero, negOne] x +
    (-12) * hpl [zero, negOne, zero, zero] x +
    (-12) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s77N1c0`. -/
noncomputable def i8Psi4s77dN1c0 (x : ℝ) : ℝ :=
    0 +
    (-23 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-61 / 4 + π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (-20 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (-23 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (-17 / 2) * (zero.kernel x * hpl [zero] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-20) * (negOne.kernel x * hpl [zero, zero] x) +
    (-22) * (zero.kernel x * hpl [negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, negOne] x) +
    (-3) * (zero.kernel x * hpl [zero, zero] x) +
    (32) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s77N1c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77N1c0 (i8Psi4s77dN1c0 x) x := by
  unfold i8Psi4s77N1c0 i8Psi4s77dN1c0
  exact ((((((((((((((((((((hasDerivAt_const x (-149 / 8 + π ^ 2 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-23 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-61 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-20 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-23 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-17 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-12)))

/-- Chunk 1 of `i8Psi4s77N1`. -/
noncomputable def i8Psi4s77N1c1 (x : ℝ) : ℝ :=
    (-12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s77N1c1`. -/
noncomputable def i8Psi4s77dN1c1 (x : ℝ) : ℝ :=
    (-12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s77N1c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77N1c1 (i8Psi4s77dN1c1 x) x := by
  unfold i8Psi4s77N1c1 i8Psi4s77dN1c1
  exact ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-12))

/-- The part of `ξ² Ψ₄⁽77⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s77N1 (x : ℝ) : ℝ :=
    i8Psi4s77N1c0 x + i8Psi4s77N1c1 x

/-- The derivative of `i8Psi4s77N1`. -/
noncomputable def i8Psi4s77dN1 (x : ℝ) : ℝ :=
    i8Psi4s77dN1c0 x + i8Psi4s77dN1c1 x

theorem hasDerivAt_i8Psi4s77N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77N1 (i8Psi4s77dN1 x) x := by
  unfold i8Psi4s77N1 i8Psi4s77dN1
  exact ((hasDerivAt_i8Psi4s77N1c0 hx).add (hasDerivAt_i8Psi4s77N1c1 hx))

/-- The part of `ξ² Ψ₄⁽77⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s77N2 (x : ℝ) : ℝ :=
    (-157 / 4) * hpl [negOne] x +
    (157 / 8 - 7 / 12 * π ^ 2) * hpl [zero] x +
    (15 + π ^ 2) * hpl [negOne, zero] x +
    (53 / 4 - π ^ 2 / 2) * hpl [zero, zero] x +
    (-36) * hpl [negOne, zero, zero] x +
    (-30) * hpl [zero, negOne, zero] x +
    (-23) * hpl [zero, zero, negOne] x +
    (29 / 2) * hpl [zero, zero, zero] x +
    (48) * hpl [negOne, negOne, zero, zero] x +
    (36) * hpl [negOne, zero, negOne, zero] x +
    (24) * hpl [negOne, zero, zero, negOne] x +
    (-18) * hpl [negOne, zero, zero, zero] x +
    (-24) * hpl [zero, negOne, zero, zero] x +
    (-18) * hpl [zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s77N2`. -/
noncomputable def i8Psi4s77dN2 (x : ℝ) : ℝ :=
    (-157 / 4) * (negOne.kernel x * hpl [] x) +
    (157 / 8 - 7 / 12 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (15 + π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (53 / 4 - π ^ 2 / 2) * (zero.kernel x * hpl [zero] x) +
    (-36) * (negOne.kernel x * hpl [zero, zero] x) +
    (-30) * (zero.kernel x * hpl [negOne, zero] x) +
    (-23) * (zero.kernel x * hpl [zero, negOne] x) +
    (29 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (48) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (36) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-18) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-18) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s77N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77N2 (i8Psi4s77dN2 x) x := by
  unfold i8Psi4s77N2 i8Psi4s77dN2
  exact ((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-157 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (157 / 8 - 7 / 12 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (15 + π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (53 / 4 - π ^ 2 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-36))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-23))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (29 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-12)))

/-- Chunk 0 of `i8Psi4s77N3`. -/
noncomputable def i8Psi4s77N3c0 (x : ℝ) : ℝ :=
    (483 / 8 + 13 / 12 * π ^ 2) +
    (-23 - 2 / 3 * π ^ 2) * hpl [negOne] x +
    (-163 / 4 - π ^ 2 / 2) * hpl [zero] x +
    (36 + 2 / 3 * π ^ 2) * hpl [negOne, zero] x +
    (23 + 2 / 3 * π ^ 2) * hpl [zero, negOne] x +
    (25 / 2) * hpl [zero, zero] x +
    (-16) * hpl [negOne, negOne, zero] x +
    (-8) * hpl [negOne, zero, negOne] x +
    (-28) * hpl [negOne, zero, zero] x +
    (-22) * hpl [zero, negOne, zero] x +
    (-16) * hpl [zero, zero, negOne] x +
    (9) * hpl [zero, zero, zero] x +
    (32) * hpl [negOne, negOne, zero, zero] x +
    (24) * hpl [negOne, zero, negOne, zero] x +
    (16) * hpl [negOne, zero, zero, negOne] x +
    (-12) * hpl [negOne, zero, zero, zero] x +
    (16) * hpl [zero, negOne, negOne, zero] x +
    (8) * hpl [zero, negOne, zero, negOne] x +
    (-12) * hpl [zero, negOne, zero, zero] x +
    (-12) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s77N3c0`. -/
noncomputable def i8Psi4s77dN3c0 (x : ℝ) : ℝ :=
    0 +
    (-23 - 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-163 / 4 - π ^ 2 / 2) * (zero.kernel x * hpl [] x) +
    (36 + 2 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (23 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x) +
    (25 / 2) * (zero.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-28) * (negOne.kernel x * hpl [zero, zero] x) +
    (-22) * (zero.kernel x * hpl [negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, negOne] x) +
    (9) * (zero.kernel x * hpl [zero, zero] x) +
    (32) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (16) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s77N3c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77N3c0 (i8Psi4s77dN3c0 x) x := by
  unfold i8Psi4s77N3c0 i8Psi4s77dN3c0
  exact ((((((((((((((((((((hasDerivAt_const x (483 / 8 + 13 / 12 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-23 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-163 / 4 - π ^ 2 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (36 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (23 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (25 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-12)))

/-- Chunk 1 of `i8Psi4s77N3`. -/
noncomputable def i8Psi4s77N3c1 (x : ℝ) : ℝ :=
    (-12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s77N3c1`. -/
noncomputable def i8Psi4s77dN3c1 (x : ℝ) : ℝ :=
    (-12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s77N3c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77N3c1 (i8Psi4s77dN3c1 x) x := by
  unfold i8Psi4s77N3c1 i8Psi4s77dN3c1
  exact ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-12))

/-- The part of `ξ² Ψ₄⁽77⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s77N3 (x : ℝ) : ℝ :=
    i8Psi4s77N3c0 x + i8Psi4s77N3c1 x

/-- The derivative of `i8Psi4s77N3`. -/
noncomputable def i8Psi4s77dN3 (x : ℝ) : ℝ :=
    i8Psi4s77dN3c0 x + i8Psi4s77dN3c1 x

theorem hasDerivAt_i8Psi4s77N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77N3 (i8Psi4s77dN3 x) x := by
  unfold i8Psi4s77N3 i8Psi4s77dN3
  exact ((hasDerivAt_i8Psi4s77N3c0 hx).add (hasDerivAt_i8Psi4s77N3c1 hx))

/-- Chunk 0 of `i8Psi4s77N4`. -/
noncomputable def i8Psi4s77N4c0 (x : ℝ) : ℝ :=
    (17 / 4 + π ^ 2 / 12) +
    (-27 / 8 - π ^ 2 / 12) * hpl [negOne] x +
    (-41 / 8 - π ^ 2 / 12) * hpl [zero] x +
    (31 / 4 + π ^ 2 / 6) * hpl [negOne, zero] x +
    (27 / 4 + π ^ 2 / 6) * hpl [zero, negOne] x +
    (5 / 2) * hpl [zero, zero] x +
    (-2) * hpl [negOne, negOne, zero] x +
    (-1) * hpl [negOne, zero, negOne] x +
    (-13 / 2) * hpl [negOne, zero, zero] x +
    (-11 / 2) * hpl [zero, negOne, zero] x +
    (-9 / 2) * hpl [zero, zero, negOne] x +
    (3 / 2) * hpl [zero, zero, zero] x +
    (8) * hpl [negOne, negOne, zero, zero] x +
    (6) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [negOne, zero, zero, negOne] x +
    (-3) * hpl [negOne, zero, zero, zero] x +
    (4) * hpl [zero, negOne, negOne, zero] x +
    (2) * hpl [zero, negOne, zero, negOne] x +
    (-3) * hpl [zero, negOne, zero, zero] x +
    (-3) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s77N4c0`. -/
noncomputable def i8Psi4s77dN4c0 (x : ℝ) : ℝ :=
    0 +
    (-27 / 8 - π ^ 2 / 12) * (negOne.kernel x * hpl [] x) +
    (-41 / 8 - π ^ 2 / 12) * (zero.kernel x * hpl [] x) +
    (31 / 4 + π ^ 2 / 6) * (negOne.kernel x * hpl [zero] x) +
    (27 / 4 + π ^ 2 / 6) * (zero.kernel x * hpl [negOne] x) +
    (5 / 2) * (zero.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne] x) +
    (-13 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-9 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (3 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (6) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-3) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-3) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s77N4c0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77N4c0 (i8Psi4s77dN4c0 x) x := by
  unfold i8Psi4s77N4c0 i8Psi4s77dN4c0
  exact ((((((((((((((((((((hasDerivAt_const x (17 / 4 + π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-27 / 8 - π ^ 2 / 12))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-41 / 8 - π ^ 2 / 12))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (31 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (27 / 4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-13 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-9 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-3)))

/-- Chunk 1 of `i8Psi4s77N4`. -/
noncomputable def i8Psi4s77N4c1 (x : ℝ) : ℝ :=
    (-3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s77N4c1`. -/
noncomputable def i8Psi4s77dN4c1 (x : ℝ) : ℝ :=
    (-3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s77N4c1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77N4c1 (i8Psi4s77dN4c1 x) x := by
  unfold i8Psi4s77N4c1 i8Psi4s77dN4c1
  exact ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3))

/-- The part of `ξ² Ψ₄⁽77⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s77N4 (x : ℝ) : ℝ :=
    i8Psi4s77N4c0 x + i8Psi4s77N4c1 x

/-- The derivative of `i8Psi4s77N4`. -/
noncomputable def i8Psi4s77dN4 (x : ℝ) : ℝ :=
    i8Psi4s77dN4c0 x + i8Psi4s77dN4c1 x

theorem hasDerivAt_i8Psi4s77N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77N4 (i8Psi4s77dN4 x) x := by
  unfold i8Psi4s77N4 i8Psi4s77dN4
  exact ((hasDerivAt_i8Psi4s77N4c0 hx).add (hasDerivAt_i8Psi4s77N4c1 hx))

/-- The part of `Ψ₄⁽77⁾` with constant coefficients. -/
noncomputable def i8Psi4s77W (x : ℝ) : ℝ :=
    (9) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s77W`. -/
noncomputable def i8Psi4s77dW (x : ℝ) : ℝ :=
    (9) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s77W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77W (i8Psi4s77dW x) x := by
  unfold i8Psi4s77W i8Psi4s77dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (9))

/-- The piece `Ψ₄⁽77⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s77 (x : ℝ) : ℝ :=
  (i8Psi4s77N0 x + x * i8Psi4s77N1 x + x ^ 2 * i8Psi4s77N2 x + x ^ 3 * i8Psi4s77N3 x +
    x ^ 4 * i8Psi4s77N4 x) / x ^ 2 + i8Psi4s77W x

/-- The derivative of `Ψ₄⁽77⁾`. -/
noncomputable def i8Psi4s77D (x : ℝ) : ℝ :=
  ((i8Psi4s77dN0 x + (i8Psi4s77N1 x + x * i8Psi4s77dN1 x) + (2 * x * i8Psi4s77N2 x +
    x ^ 2 * i8Psi4s77dN2 x) + (3 * x ^ 2 * i8Psi4s77N3 x + x ^ 3 * i8Psi4s77dN3 x) +
    (4 * x ^ 3 * i8Psi4s77N4 x + x ^ 4 * i8Psi4s77dN4 x)) * x ^ 2 - (i8Psi4s77N0 x +
    x * i8Psi4s77N1 x + x ^ 2 * i8Psi4s77N2 x + x ^ 3 * i8Psi4s77N3 x +
    x ^ 4 * i8Psi4s77N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s77dW x

theorem hasDerivAt_i8Psi4s77 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s77 (i8Psi4s77D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s77N0 hx).add (X.mul (hasDerivAt_i8Psi4s77N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s77N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s77N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s77N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s77W hx)
  unfold i8Psi4s77
  refine e.congr_deriv ?_
  unfold i8Psi4s77D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 77 of `p₄` in `ξ`: from `t B2 A1 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s77 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * i13Be2x x * ((1 + x) / (1 - x) * (-hpl [negOne] x))

/-- `p₄⁽77⁾` written over words. -/
noncomputable def i8P4w77 (x : ℝ) : ℝ :=
    ((-8 + 8 * x ^ 2 + π ^ 2 / 3 + π ^ 2 * x ^ 2 / 3 +
      2 / 3 * π ^ 2 * x) / (x)) * hpl [negOne, zero] x +
    ((-8 + 8 * x ^ 2 + π ^ 2 / 3 + π ^ 2 * x ^ 2 / 3 +
      2 / 3 * π ^ 2 * x) / (x)) * hpl [zero, negOne] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [negOne, zero, zero] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [zero, negOne, zero] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [zero, zero, negOne] x +
    ((16 + 16 * x ^ 2 + 32 * x) / (x)) * hpl [negOne, negOne, zero, zero] x +
    ((12 + 12 * x ^ 2 + 24 * x) / (x)) * hpl [negOne, zero, negOne, zero] x +
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [negOne, zero, zero, negOne] x +
    ((-6 - 12 * x - 6 * x ^ 2) / (x)) * hpl [negOne, zero, zero, zero] x +
    ((8 + 8 * x ^ 2 + 16 * x) / (x)) * hpl [zero, negOne, negOne, zero] x +
    ((4 + 4 * x ^ 2 + 8 * x) / (x)) * hpl [zero, negOne, zero, negOne] x +
    ((-6 - 12 * x - 6 * x ^ 2) / (x)) * hpl [zero, negOne, zero, zero] x +
    ((-6 - 12 * x - 6 * x ^ 2) / (x)) * hpl [zero, zero, negOne, zero] x +
    ((-6 - 12 * x - 6 * x ^ 2) / (x)) * hpl [zero, zero, zero, negOne] x

theorem i8P4s77_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s77 x = i8P4w77 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s77 i8P4w77 i13Be2x
  simp only [i13hw_m0 hx, i13hw_0m0 hx, i13hw_m00 hx, i13hw_00m0 hx, i13hw_0m00 hx, i13hw_0m0m hx,
    i13hw_0mm0 hx, i13hw_m000 hx, i13hw_m00m hx, i13hw_m0m0 hx, i13hw_mm00 hx, i13_Li₂_neg_eq hx,
    i13_log_one_add_eq hx]
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
  generalize hpl [zero, negOne, one, one, negOne] x = v11 at *
  generalize hpl [zero, negOne, one, one, one] x = v12 at *
  generalize hpl [zero, zero, negOne, negOne, negOne] x = v13 at *
  generalize hpl [zero, zero, negOne, negOne, one] x = v14 at *
  generalize hpl [zero, zero, negOne, zero, negOne] x = v15 at *
  generalize hpl [zero, zero, negOne, zero, one] x = v16 at *
  generalize hpl [zero, zero, negOne, one, negOne] x = v17 at *
  generalize hpl [zero, zero, negOne, one, one] x = v18 at *
  generalize hpl [zero, zero, zero, negOne, negOne] x = v19 at *
  generalize hpl [zero, zero, zero, negOne, one] x = v20 at *
  generalize hpl [zero, zero, zero, zero, negOne] x = v21 at *
  generalize hpl [zero, zero, zero, zero, one] x = v22 at *
  generalize hpl [zero, zero, zero, one, negOne] x = v23 at *
  generalize hpl [zero, zero, zero, one, one] x = v24 at *
  generalize hpl [zero, zero, one, negOne, negOne] x = v25 at *
  generalize hpl [zero, zero, one, negOne, one] x = v26 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v27 at *
  generalize hpl [zero, zero, one, one, negOne] x = v28 at *
  generalize hpl [zero, zero, one, one, one] x = v29 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v30 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v31 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v32 at *
  generalize hpl [zero, one, negOne, one, one] x = v33 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v34 at *
  generalize hpl [zero, one, one, negOne, one] x = v35 at *
  generalize hpl [zero, one, one, one, negOne] x = v36 at *
  generalize hpl [zero, one, one, one, one] x = v37 at *
  generalize hpl [negOne, negOne, zero, zero] x = v38 at *
  generalize hpl [negOne, zero, negOne, zero] x = v39 at *
  generalize hpl [negOne, zero, zero, negOne] x = v40 at *
  generalize hpl [negOne, zero, zero, zero] x = v41 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v42 at *
  generalize hpl [zero, negOne, negOne, zero] x = v43 at *
  generalize hpl [zero, negOne, negOne, one] x = v44 at *
  generalize hpl [zero, negOne, zero, negOne] x = v45 at *
  generalize hpl [zero, negOne, zero, zero] x = v46 at *
  generalize hpl [zero, negOne, zero, one] x = v47 at *
  generalize hpl [zero, negOne, one, negOne] x = v48 at *
  generalize hpl [zero, negOne, one, one] x = v49 at *
  generalize hpl [zero, zero, negOne, negOne] x = v50 at *
  generalize hpl [zero, zero, negOne, zero] x = v51 at *
  generalize hpl [zero, zero, negOne, one] x = v52 at *
  generalize hpl [zero, zero, zero, negOne] x = v53 at *
  generalize hpl [zero, zero, zero, zero] x = v54 at *
  generalize hpl [zero, zero, zero, one] x = v55 at *
  generalize hpl [zero, zero, one, negOne] x = v56 at *
  generalize hpl [zero, zero, one, one] x = v57 at *
  generalize hpl [zero, one, negOne, negOne] x = v58 at *
  generalize hpl [zero, one, negOne, one] x = v59 at *
  generalize hpl [zero, one, one, negOne] x = v60 at *
  generalize hpl [zero, one, one, one] x = v61 at *
  generalize hpl [negOne, negOne, zero] x = v62 at *
  generalize hpl [negOne, negOne, one] x = v63 at *
  generalize hpl [negOne, zero, negOne] x = v64 at *
  generalize hpl [negOne, zero, zero] x = v65 at *
  generalize hpl [negOne, one, one] x = v66 at *
  generalize hpl [zero, negOne, negOne] x = v67 at *
  generalize hpl [zero, negOne, zero] x = v68 at *
  generalize hpl [zero, negOne, one] x = v69 at *
  generalize hpl [zero, zero, negOne] x = v70 at *
  generalize hpl [zero, zero, zero] x = v71 at *
  generalize hpl [zero, zero, one] x = v72 at *
  generalize hpl [zero, one, negOne] x = v73 at *
  generalize hpl [zero, one, one] x = v74 at *
  generalize hpl [negOne, zero] x = v75 at *
  generalize hpl [negOne, one] x = v76 at *
  generalize hpl [zero, negOne] x = v77 at *
  generalize hpl [zero, zero] x = v78 at *
  generalize hpl [zero, one] x = v79 at *
  generalize hpl [negOne] x = v80 at *
  generalize hpl [zero] x = v81 at *
  generalize hpl [one] x = v82 at *
  ring

/-- **`(Ψ₄⁽77⁾)'(ξ) ξ' = p₄⁽77⁾`**, in terms of `ξ`. -/
theorem i8Psi4s77D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s77D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s77 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s77_eq_w hx]
  unfold i8Psi4s77D i8Psi4s77N0 i8Psi4s77N1 i8Psi4s77N2 i8Psi4s77N3 i8Psi4s77N4 i8Psi4s77dN0
    i8Psi4s77dN1 i8Psi4s77dN2 i8Psi4s77dN3 i8Psi4s77dN4 i8Psi4s77dW i8Psi4s77N1c0 i8Psi4s77dN1c0
    i8Psi4s77N1c1 i8Psi4s77dN1c1 i8Psi4s77N3c0 i8Psi4s77dN3c0 i8Psi4s77N3c1 i8Psi4s77dN3c1
    i8Psi4s77N4c0 i8Psi4s77dN4c0 i8Psi4s77N4c1 i8Psi4s77dN4c1 i8P4w77
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [negOne, negOne, zero, zero] x = v0 at *
  generalize hpl [negOne, zero, negOne, zero] x = v1 at *
  generalize hpl [negOne, zero, zero, negOne] x = v2 at *
  generalize hpl [negOne, zero, zero, zero] x = v3 at *
  generalize hpl [zero, negOne, negOne, zero] x = v4 at *
  generalize hpl [zero, negOne, zero, negOne] x = v5 at *
  generalize hpl [zero, negOne, zero, zero] x = v6 at *
  generalize hpl [zero, zero, negOne, zero] x = v7 at *
  generalize hpl [zero, zero, zero, negOne] x = v8 at *
  generalize hpl [zero, zero, zero, zero] x = v9 at *
  generalize hpl [negOne, negOne, zero] x = v10 at *
  generalize hpl [negOne, zero, negOne] x = v11 at *
  generalize hpl [negOne, zero, zero] x = v12 at *
  generalize hpl [zero, negOne, zero] x = v13 at *
  generalize hpl [zero, zero, negOne] x = v14 at *
  generalize hpl [zero, zero, zero] x = v15 at *
  generalize hpl [negOne, zero] x = v16 at *
  generalize hpl [zero, negOne] x = v17 at *
  generalize hpl [zero, zero] x = v18 at *
  generalize hpl [negOne] x = v19 at *
  generalize hpl [zero] x = v20 at *
  ring

end QED.ThreeLoopD
