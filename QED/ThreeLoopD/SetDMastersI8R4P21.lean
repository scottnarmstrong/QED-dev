/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P20

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 85 to 87

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s85`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s85D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s85`, `QED.ThreeLoopD.i8Psi4s85D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽85⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s85N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s85N0`. -/
noncomputable def i8Psi4s85dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s85N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s85N0 (i8Psi4s85dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽85⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s85N1 (x : ℝ) : ℝ :=
    (20) * hpl [one] x +
    (12) * hpl [zero, one] x +
    (12) * hpl [one, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (4) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s85N1`. -/
noncomputable def i8Psi4s85dN1 (x : ℝ) : ℝ :=
    (20) * (one.kernel x * hpl [] x) +
    (12) * (zero.kernel x * hpl [one] x) +
    (12) * (one.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s85N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s85N1 (i8Psi4s85dN1 x) x := by
  unfold i8Psi4s85N1 i8Psi4s85dN1
  exact (((((((hasDerivAt_hpl_cons one [] hx).const_mul (20)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽85⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s85N2 (x : ℝ) : ℝ :=
    (-20) * hpl [zero] x +
    (-3 / 2) * hpl [one] x +
    (-12) * hpl [zero, zero] x +
    (8) * hpl [zero, one] x +
    (-37) * hpl [one, zero] x +
    (-8) * hpl [zero, zero, one] x +
    (-8) * hpl [zero, one, zero] x +
    (10) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s85N2`. -/
noncomputable def i8Psi4s85dN2 (x : ℝ) : ℝ :=
    (-20) * (zero.kernel x * hpl [] x) +
    (-3 / 2) * (one.kernel x * hpl [] x) +
    (-12) * (zero.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [one] x) +
    (-37) * (one.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [zero, one] x) +
    (-8) * (zero.kernel x * hpl [one, zero] x) +
    (10) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s85N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s85N2 (i8Psi4s85dN2 x) x := by
  unfold i8Psi4s85N2 i8Psi4s85dN2
  exact (((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-20)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-37))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (10)))

/-- The part of `ξ² Ψ₄⁽85⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s85N3 (x : ℝ) : ℝ :=
    (-115 / 2) +
    (39) * hpl [zero] x +
    (-12) * hpl [one] x +
    (-14) * hpl [zero, zero] x +
    (20) * hpl [zero, one] x +
    (20) * hpl [one, zero] x +
    (-12) * hpl [zero, zero, one] x +
    (-12) * hpl [zero, one, zero] x +
    (-12) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s85N3`. -/
noncomputable def i8Psi4s85dN3 (x : ℝ) : ℝ :=
    0 +
    (39) * (zero.kernel x * hpl [] x) +
    (-12) * (one.kernel x * hpl [] x) +
    (-14) * (zero.kernel x * hpl [zero] x) +
    (20) * (zero.kernel x * hpl [one] x) +
    (20) * (one.kernel x * hpl [zero] x) +
    (-12) * (zero.kernel x * hpl [zero, one] x) +
    (-12) * (zero.kernel x * hpl [one, zero] x) +
    (-12) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s85N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s85N3 (i8Psi4s85dN3 x) x := by
  unfold i8Psi4s85N3 i8Psi4s85dN3
  exact (((((((((hasDerivAt_const x (-115 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (39))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽85⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s85N4 (x : ℝ) : ℝ :=
    (-19 / 4) +
    (3) * hpl [zero] x +
    (-13 / 2) * hpl [one] x +
    (-1) * hpl [zero, zero] x +
    (5) * hpl [zero, one] x +
    (5) * hpl [one, zero] x +
    (-2) * hpl [zero, zero, one] x +
    (-2) * hpl [zero, one, zero] x +
    (-2) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s85N4`. -/
noncomputable def i8Psi4s85dN4 (x : ℝ) : ℝ :=
    0 +
    (3) * (zero.kernel x * hpl [] x) +
    (-13 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [zero] x) +
    (5) * (zero.kernel x * hpl [one] x) +
    (5) * (one.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [zero, one] x) +
    (-2) * (zero.kernel x * hpl [one, zero] x) +
    (-2) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s85N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s85N4 (i8Psi4s85dN4 x) x := by
  unfold i8Psi4s85N4 i8Psi4s85dN4
  exact (((((((((hasDerivAt_const x (-19 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-13 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽85⁾` with constant coefficients. -/
noncomputable def i8Psi4s85W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, zero, zero] x +
    (-12) * hpl [zero, zero, zero, one] x +
    (-12) * hpl [zero, zero, one, zero] x +
    (-12) * hpl [zero, one, zero, zero] x

/-- The derivative of `i8Psi4s85W`. -/
noncomputable def i8Psi4s85dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [zero, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-12) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-12) * (zero.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s85W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s85W (i8Psi4s85dW x) x := by
  unfold i8Psi4s85W i8Psi4s85dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-12)))

/-- The piece `Ψ₄⁽85⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s85 (x : ℝ) : ℝ :=
  (i8Psi4s85N0 x + x * i8Psi4s85N1 x + x ^ 2 * i8Psi4s85N2 x + x ^ 3 * i8Psi4s85N3 x +
    x ^ 4 * i8Psi4s85N4 x) / x ^ 2 + i8Psi4s85W x

/-- The derivative of `Ψ₄⁽85⁾`. -/
noncomputable def i8Psi4s85D (x : ℝ) : ℝ :=
  ((i8Psi4s85dN0 x + (i8Psi4s85N1 x + x * i8Psi4s85dN1 x) + (2 * x * i8Psi4s85N2 x +
    x ^ 2 * i8Psi4s85dN2 x) + (3 * x ^ 2 * i8Psi4s85N3 x + x ^ 3 * i8Psi4s85dN3 x) +
    (4 * x ^ 3 * i8Psi4s85N4 x + x ^ 4 * i8Psi4s85dN4 x)) * x ^ 2 - (i8Psi4s85N0 x +
    x * i8Psi4s85N1 x + x ^ 2 * i8Psi4s85N2 x + x ^ 3 * i8Psi4s85N3 x +
    x ^ 4 * i8Psi4s85N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s85dW x

theorem hasDerivAt_i8Psi4s85 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s85 (i8Psi4s85D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s85N0 hx).add (X.mul (hasDerivAt_i8Psi4s85N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s85N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s85N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s85N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s85W hx)
  unfold i8Psi4s85
  refine e.congr_deriv ?_
  unfold i8Psi4s85D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 85 of `p₄` in `ξ`: from `t B2 A1 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s85 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * (2 + Real.log x * (1 + x) / (1 - x)) * (2 +
    Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 - x) * (x / (1 + x))))

/-- `p₄⁽85⁾` written over words. -/
noncomputable def i8P4w85 (x : ℝ) : ℝ :=
    (8 - 8 * x) * hpl [one] x +
    (8 + 8 * x) * hpl [zero, one] x +
    (8 + 8 * x) * hpl [one, zero] x +
    ((4 + 4 * x ^ 2 + 8 * x) / ((1 - x))) * hpl [zero, zero, one] x +
    ((4 + 4 * x ^ 2 + 8 * x) / ((1 - x))) * hpl [zero, one, zero] x +
    ((4 + 4 * x ^ 2 + 8 * x) / ((1 - x))) * hpl [one, zero, zero] x

theorem i8P4s85_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s85 x = i8P4w85 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s85 i8P4w85
  simp only [i13hw_10 hx, i13hw_010 hx, i13hw_100 hx, i13_log_one_sub_eq hx]
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
  generalize hpl [zero, negOne, one, one] x = v46 at *
  generalize hpl [zero, zero, negOne, negOne] x = v47 at *
  generalize hpl [zero, zero, negOne, one] x = v48 at *
  generalize hpl [zero, zero, zero, negOne] x = v49 at *
  generalize hpl [zero, zero, zero, one] x = v50 at *
  generalize hpl [zero, zero, one, negOne] x = v51 at *
  generalize hpl [zero, zero, one, zero] x = v52 at *
  generalize hpl [zero, zero, one, one] x = v53 at *
  generalize hpl [zero, one, negOne, negOne] x = v54 at *
  generalize hpl [zero, one, negOne, one] x = v55 at *
  generalize hpl [zero, one, zero, zero] x = v56 at *
  generalize hpl [zero, one, one, negOne] x = v57 at *
  generalize hpl [zero, one, one, one] x = v58 at *
  generalize hpl [negOne, negOne, one] x = v59 at *
  generalize hpl [negOne, one, one] x = v60 at *
  generalize hpl [zero, negOne, negOne] x = v61 at *
  generalize hpl [zero, negOne, one] x = v62 at *
  generalize hpl [zero, zero, negOne] x = v63 at *
  generalize hpl [zero, zero, zero] x = v64 at *
  generalize hpl [zero, zero, one] x = v65 at *
  generalize hpl [zero, one, negOne] x = v66 at *
  generalize hpl [zero, one, zero] x = v67 at *
  generalize hpl [zero, one, one] x = v68 at *
  generalize hpl [one, zero, zero] x = v69 at *
  generalize hpl [negOne, one] x = v70 at *
  generalize hpl [zero, negOne] x = v71 at *
  generalize hpl [zero, zero] x = v72 at *
  generalize hpl [zero, one] x = v73 at *
  generalize hpl [one, zero] x = v74 at *
  generalize hpl [negOne] x = v75 at *
  generalize hpl [zero] x = v76 at *
  generalize hpl [one] x = v77 at *
  ring

/-- **`(Ψ₄⁽85⁾)'(ξ) ξ' = p₄⁽85⁾`**, in terms of `ξ`. -/
theorem i8Psi4s85D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s85D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s85 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s85_eq_w hx]
  unfold i8Psi4s85D i8Psi4s85N0 i8Psi4s85N1 i8Psi4s85N2 i8Psi4s85N3 i8Psi4s85N4 i8Psi4s85dN0
    i8Psi4s85dN1 i8Psi4s85dN2 i8Psi4s85dN3 i8Psi4s85dN4 i8Psi4s85dW i8P4w85
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

/-- The part of `ξ² Ψ₄⁽86⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s86N0 (x : ℝ) : ℝ :=
    (-5) * hpl [negOne, one] x +
    (-5) * hpl [one, negOne] x +
    (-2) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, one, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, one, negOne] x +
    (-2) * hpl [one, negOne, zero] x +
    (-2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s86N0`. -/
noncomputable def i8Psi4s86dN0 (x : ℝ) : ℝ :=
    (-5) * (negOne.kernel x * hpl [one] x) +
    (-5) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s86N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s86N0 (i8Psi4s86dN0 x) x := by
  unfold i8Psi4s86N0 i8Psi4s86dN0
  exact (((((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-5)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽86⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s86N1 (x : ℝ) : ℝ :=
    (-7) * hpl [negOne] x +
    (-7) * hpl [one] x +
    (-2) * hpl [negOne, zero] x +
    (-8) * hpl [negOne, one] x +
    (-2) * hpl [zero, negOne] x +
    (-2) * hpl [zero, one] x +
    (-8) * hpl [one, negOne] x +
    (-2) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (-8) * hpl [zero, negOne, one] x +
    (-8) * hpl [zero, one, negOne] x +
    (-8) * hpl [one, negOne, zero] x +
    (-8) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s86N1`. -/
noncomputable def i8Psi4s86dN1 (x : ℝ) : ℝ :=
    (-7) * (negOne.kernel x * hpl [] x) +
    (-7) * (one.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [negOne] x) +
    (-2) * (zero.kernel x * hpl [one] x) +
    (-8) * (one.kernel x * hpl [negOne] x) +
    (-2) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one] x) +
    (-8) * (zero.kernel x * hpl [one, negOne] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s86N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s86N1 (i8Psi4s86dN1 x) x := by
  unfold i8Psi4s86N1 i8Psi4s86dN1
  exact (((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-7)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽86⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s86N2 (x : ℝ) : ℝ :=
    (13) * hpl [negOne] x +
    (14) * hpl [zero] x +
    (19) * hpl [one] x +
    (-11) * hpl [negOne, zero] x +
    (13) * hpl [zero, negOne] x +
    (3) * hpl [zero, one] x +
    (-5) * hpl [one, zero] x +
    (-12) * hpl [negOne, zero, one] x +
    (-12) * hpl [negOne, one, zero] x +
    (-16) * hpl [zero, negOne, one] x +
    (-16) * hpl [zero, one, negOne] x +
    (20) * hpl [one, negOne, zero] x +
    (20) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s86N2`. -/
noncomputable def i8Psi4s86dN2 (x : ℝ) : ℝ :=
    (13) * (negOne.kernel x * hpl [] x) +
    (14) * (zero.kernel x * hpl [] x) +
    (19) * (one.kernel x * hpl [] x) +
    (-11) * (negOne.kernel x * hpl [zero] x) +
    (13) * (zero.kernel x * hpl [negOne] x) +
    (3) * (zero.kernel x * hpl [one] x) +
    (-5) * (one.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, one] x) +
    (-12) * (negOne.kernel x * hpl [one, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, one] x) +
    (-16) * (zero.kernel x * hpl [one, negOne] x) +
    (20) * (one.kernel x * hpl [negOne, zero] x) +
    (20) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s86N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s86N2 (i8Psi4s86dN2 x) x := by
  unfold i8Psi4s86N2 i8Psi4s86dN2
  exact ((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (13)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (19))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (13))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (20)))

/-- The part of `ξ² Ψ₄⁽86⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s86N3 (x : ℝ) : ℝ :=
    (-48) +
    (23) * hpl [negOne] x +
    (16) * hpl [zero] x +
    (-9) * hpl [one] x +
    (-10) * hpl [negOne, zero] x +
    (8) * hpl [negOne, one] x +
    (-10) * hpl [zero, negOne] x +
    (6) * hpl [zero, one] x +
    (8) * hpl [one, negOne] x +
    (6) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (-8) * hpl [zero, negOne, one] x +
    (-8) * hpl [zero, one, negOne] x +
    (-8) * hpl [one, negOne, zero] x +
    (-8) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s86N3`. -/
noncomputable def i8Psi4s86dN3 (x : ℝ) : ℝ :=
    0 +
    (23) * (negOne.kernel x * hpl [] x) +
    (16) * (zero.kernel x * hpl [] x) +
    (-9) * (one.kernel x * hpl [] x) +
    (-10) * (negOne.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [one] x) +
    (-10) * (zero.kernel x * hpl [negOne] x) +
    (6) * (zero.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [negOne] x) +
    (6) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one] x) +
    (-8) * (zero.kernel x * hpl [one, negOne] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s86N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s86N3 (i8Psi4s86dN3 x) x := by
  unfold i8Psi4s86N3 i8Psi4s86dN3
  exact ((((((((((((((((hasDerivAt_const x (-48)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (23))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-9))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽86⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s86N4 (x : ℝ) : ℝ :=
    (-7 / 2) +
    (3) * hpl [negOne] x +
    (1) * hpl [zero] x +
    (-3) * hpl [one] x +
    (-1) * hpl [negOne, zero] x +
    (5) * hpl [negOne, one] x +
    (-1) * hpl [zero, negOne] x +
    (1) * hpl [zero, one] x +
    (5) * hpl [one, negOne] x +
    (1) * hpl [one, zero] x +
    (-2) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, one, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, one, negOne] x +
    (-2) * hpl [one, negOne, zero] x +
    (-2) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s86N4`. -/
noncomputable def i8Psi4s86dN4 (x : ℝ) : ℝ :=
    0 +
    (3) * (negOne.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [] x) +
    (-3) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (5) * (negOne.kernel x * hpl [one] x) +
    (-1) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [one] x) +
    (5) * (one.kernel x * hpl [negOne] x) +
    (1) * (one.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (one.kernel x * hpl [negOne, zero] x) +
    (-2) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s86N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s86N4 (i8Psi4s86dN4 x) x := by
  unfold i8Psi4s86N4 i8Psi4s86dN4
  exact ((((((((((((((((hasDerivAt_const x (-7 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽86⁾` with constant coefficients. -/
noncomputable def i8Psi4s86W (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero] x +
    (10) * hpl [zero, negOne, zero] x +
    (10) * hpl [zero, zero, negOne] x +
    (6) * hpl [zero, zero, one] x +
    (6) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s86W`. -/
noncomputable def i8Psi4s86dW (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero] x) +
    (10) * (zero.kernel x * hpl [negOne, zero] x) +
    (10) * (zero.kernel x * hpl [zero, negOne] x) +
    (6) * (zero.kernel x * hpl [zero, one] x) +
    (6) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s86W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s86W (i8Psi4s86dW x) x := by
  unfold i8Psi4s86W i8Psi4s86dW
  exact ((((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (6)))

/-- The piece `Ψ₄⁽86⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s86 (x : ℝ) : ℝ :=
  (i8Psi4s86N0 x + x * i8Psi4s86N1 x + x ^ 2 * i8Psi4s86N2 x + x ^ 3 * i8Psi4s86N3 x +
    x ^ 4 * i8Psi4s86N4 x) / x ^ 2 + i8Psi4s86W x

/-- The derivative of `Ψ₄⁽86⁾`. -/
noncomputable def i8Psi4s86D (x : ℝ) : ℝ :=
  ((i8Psi4s86dN0 x + (i8Psi4s86N1 x + x * i8Psi4s86dN1 x) + (2 * x * i8Psi4s86N2 x +
    x ^ 2 * i8Psi4s86dN2 x) + (3 * x ^ 2 * i8Psi4s86N3 x + x ^ 3 * i8Psi4s86dN3 x) +
    (4 * x ^ 3 * i8Psi4s86N4 x + x ^ 4 * i8Psi4s86dN4 x)) * x ^ 2 - (i8Psi4s86N0 x +
    x * i8Psi4s86N1 x + x ^ 2 * i8Psi4s86N2 x + x ^ 3 * i8Psi4s86N3 x +
    x ^ 4 * i8Psi4s86N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s86dW x

theorem hasDerivAt_i8Psi4s86 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s86 (i8Psi4s86D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s86N0 hx).add (X.mul (hasDerivAt_i8Psi4s86N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s86N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s86N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s86N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s86W hx)
  unfold i8Psi4s86
  refine e.congr_deriv ?_
  unfold i8Psi4s86D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 86 of `p₄` in `ξ`: from `t B2 A1 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s86 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 +
    x) / (1 - x) * ((2 + ((-2) * x)) / (1 + x))) * ((1 + x) / (1 - x) * (-hpl [negOne] x)))

/-- `p₄⁽86⁾` written over words. -/
noncomputable def i8P4w86 (x : ℝ) : ℝ :=
    ((-8 + 8 * x ^ 2) / (x)) * hpl [negOne, one] x +
    ((-8 + 8 * x ^ 2) / (x)) * hpl [one, negOne] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [negOne, zero, one] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [negOne, one, zero] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [zero, negOne, one] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [zero, one, negOne] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [one, negOne, zero] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [one, zero, negOne] x

theorem i8P4s86_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s86 x = i8P4w86 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s86 i8P4w86
  simp only [i13hw_1m hx, i13hw_10m hx, i13hw_1m0 hx, i13hw_m01 hx, i13hw_m10 hx, i13_log_one_sub_eq
    hx]
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
  generalize hpl [zero, negOne, one, one] x = v46 at *
  generalize hpl [zero, zero, negOne, negOne] x = v47 at *
  generalize hpl [zero, zero, negOne, one] x = v48 at *
  generalize hpl [zero, zero, zero, negOne] x = v49 at *
  generalize hpl [zero, zero, zero, one] x = v50 at *
  generalize hpl [zero, zero, one, negOne] x = v51 at *
  generalize hpl [zero, zero, one, one] x = v52 at *
  generalize hpl [zero, one, negOne, negOne] x = v53 at *
  generalize hpl [zero, one, negOne, one] x = v54 at *
  generalize hpl [zero, one, one, negOne] x = v55 at *
  generalize hpl [zero, one, one, one] x = v56 at *
  generalize hpl [negOne, negOne, one] x = v57 at *
  generalize hpl [negOne, zero, one] x = v58 at *
  generalize hpl [negOne, one, zero] x = v59 at *
  generalize hpl [negOne, one, one] x = v60 at *
  generalize hpl [zero, negOne, negOne] x = v61 at *
  generalize hpl [zero, negOne, zero] x = v62 at *
  generalize hpl [zero, negOne, one] x = v63 at *
  generalize hpl [zero, zero, negOne] x = v64 at *
  generalize hpl [zero, zero, one] x = v65 at *
  generalize hpl [zero, one, negOne] x = v66 at *
  generalize hpl [zero, one, zero] x = v67 at *
  generalize hpl [zero, one, one] x = v68 at *
  generalize hpl [one, negOne, zero] x = v69 at *
  generalize hpl [one, zero, negOne] x = v70 at *
  generalize hpl [negOne, zero] x = v71 at *
  generalize hpl [negOne, one] x = v72 at *
  generalize hpl [zero, negOne] x = v73 at *
  generalize hpl [zero, zero] x = v74 at *
  generalize hpl [zero, one] x = v75 at *
  generalize hpl [one, negOne] x = v76 at *
  generalize hpl [one, zero] x = v77 at *
  generalize hpl [negOne] x = v78 at *
  generalize hpl [zero] x = v79 at *
  generalize hpl [one] x = v80 at *
  ring

/-- **`(Ψ₄⁽86⁾)'(ξ) ξ' = p₄⁽86⁾`**, in terms of `ξ`. -/
theorem i8Psi4s86D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s86D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s86 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s86_eq_w hx]
  unfold i8Psi4s86D i8Psi4s86N0 i8Psi4s86N1 i8Psi4s86N2 i8Psi4s86N3 i8Psi4s86N4 i8Psi4s86dN0
    i8Psi4s86dN1 i8Psi4s86dN2 i8Psi4s86dN3 i8Psi4s86dN4 i8Psi4s86dW i8P4w86
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [negOne, zero, one] x = v0 at *
  generalize hpl [negOne, one, zero] x = v1 at *
  generalize hpl [zero, negOne, zero] x = v2 at *
  generalize hpl [zero, negOne, one] x = v3 at *
  generalize hpl [zero, zero, negOne] x = v4 at *
  generalize hpl [zero, zero, one] x = v5 at *
  generalize hpl [zero, one, negOne] x = v6 at *
  generalize hpl [zero, one, zero] x = v7 at *
  generalize hpl [one, negOne, zero] x = v8 at *
  generalize hpl [one, zero, negOne] x = v9 at *
  generalize hpl [negOne, zero] x = v10 at *
  generalize hpl [negOne, one] x = v11 at *
  generalize hpl [zero, negOne] x = v12 at *
  generalize hpl [zero, zero] x = v13 at *
  generalize hpl [zero, one] x = v14 at *
  generalize hpl [one, negOne] x = v15 at *
  generalize hpl [one, zero] x = v16 at *
  generalize hpl [negOne] x = v17 at *
  generalize hpl [zero] x = v18 at *
  generalize hpl [one] x = v19 at *
  ring

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s87k0N0 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne, one] x +
    (-1) * hpl [one, negOne] x +
    (-2) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, one, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi4s87k0N0`. -/
noncomputable def i8Psi4s87k0dN0 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [negOne] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s87k0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k0N0 (i8Psi4s87k0dN0 x) x := by
  unfold i8Psi4s87k0N0 i8Psi4s87k0dN0
  exact (((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s87k0N1 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne] x +
    (-3) * hpl [one] x +
    (-8) * hpl [negOne, one] x +
    (-2) * hpl [zero, one] x +
    (-8) * hpl [one, negOne] x +
    (-2) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (-8) * hpl [zero, negOne, one] x +
    (-8) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi4s87k0N1`. -/
noncomputable def i8Psi4s87k0dN1 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [] x) +
    (-3) * (one.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [one] x) +
    (-8) * (one.kernel x * hpl [negOne] x) +
    (-2) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one] x) +
    (-8) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s87k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k0N1 (i8Psi4s87k0dN1 x) x := by
  unfold i8Psi4s87k0N1 i8Psi4s87k0dN1
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s87k0N2 (x : ℝ) : ℝ :=
    (15 / 2) * hpl [negOne] x +
    (4) * hpl [zero] x +
    (17) * hpl [one] x +
    (7) * hpl [zero, one] x +
    (-5) * hpl [one, zero] x +
    (-12) * hpl [negOne, zero, one] x +
    (-12) * hpl [negOne, one, zero] x

/-- The derivative of `i8Psi4s87k0N2`. -/
noncomputable def i8Psi4s87k0dN2 (x : ℝ) : ℝ :=
    (15 / 2) * (negOne.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [] x) +
    (17) * (one.kernel x * hpl [] x) +
    (7) * (zero.kernel x * hpl [one] x) +
    (-5) * (one.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, one] x) +
    (-12) * (negOne.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s87k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k0N2 (i8Psi4s87k0dN2 x) x := by
  unfold i8Psi4s87k0N2 i8Psi4s87k0dN2
  exact ((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (15 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (17))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s87k0N3 (x : ℝ) : ℝ :=
    (-59 / 2) +
    (9) * hpl [negOne] x +
    (7) * hpl [zero] x +
    (-13) * hpl [one] x +
    (8) * hpl [negOne, one] x +
    (6) * hpl [zero, one] x +
    (8) * hpl [one, negOne] x +
    (6) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (-8) * hpl [zero, negOne, one] x +
    (-8) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi4s87k0N3`. -/
noncomputable def i8Psi4s87k0dN3 (x : ℝ) : ℝ :=
    0 +
    (9) * (negOne.kernel x * hpl [] x) +
    (7) * (zero.kernel x * hpl [] x) +
    (-13) * (one.kernel x * hpl [] x) +
    (8) * (negOne.kernel x * hpl [one] x) +
    (6) * (zero.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [negOne] x) +
    (6) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, one] x) +
    (-8) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s87k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k0N3 (i8Psi4s87k0dN3 x) x := by
  unfold i8Psi4s87k0N3 i8Psi4s87k0dN3
  exact ((((((((((((hasDerivAt_const x (-59 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-13))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽87⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s87k0N4 (x : ℝ) : ℝ :=
    (-1) +
    (1 / 2) * hpl [negOne] x +
    (1 / 2) * hpl [zero] x +
    (-1) * hpl [one] x +
    (1) * hpl [negOne, one] x +
    (1) * hpl [zero, one] x +
    (1) * hpl [one, negOne] x +
    (1) * hpl [one, zero] x +
    (-2) * hpl [negOne, zero, one] x +
    (-2) * hpl [negOne, one, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (-2) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi4s87k0N4`. -/
noncomputable def i8Psi4s87k0dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-1) * (one.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (1) * (one.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, one] x) +
    (-2) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s87k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k0N4 (i8Psi4s87k0dN4 x) x := by
  unfold i8Psi4s87k0N4 i8Psi4s87k0dN4
  exact ((((((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽87⁾` with constant coefficients. -/
noncomputable def i8Psi4s87k0W (x : ℝ) : ℝ :=
    (9) * hpl [zero, negOne] x +
    (2) * hpl [zero, zero] x +
    (6) * hpl [zero, zero, one] x +
    (6) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s87k0W`. -/
noncomputable def i8Psi4s87k0dW (x : ℝ) : ℝ :=
    (9) * (zero.kernel x * hpl [negOne] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [zero, one] x) +
    (6) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s87k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k0W (i8Psi4s87k0dW x) x := by
  unfold i8Psi4s87k0W i8Psi4s87k0dW
  exact (((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (9)).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (6)))

/-- Chunk 0 of the piece `Ψ₄⁽87⁾`. -/
noncomputable def i8Psi4s87k0 (x : ℝ) : ℝ :=
  (i8Psi4s87k0N0 x + x * i8Psi4s87k0N1 x + x ^ 2 * i8Psi4s87k0N2 x + x ^ 3 * i8Psi4s87k0N3 x +
    x ^ 4 * i8Psi4s87k0N4 x) / x ^ 2 + i8Psi4s87k0W x

/-- The derivative of `i8Psi4s87k0`. -/
noncomputable def i8Psi4s87k0D (x : ℝ) : ℝ :=
  ((i8Psi4s87k0dN0 x + (i8Psi4s87k0N1 x + x * i8Psi4s87k0dN1 x) + (2 * x * i8Psi4s87k0N2 x +
    x ^ 2 * i8Psi4s87k0dN2 x) + (3 * x ^ 2 * i8Psi4s87k0N3 x + x ^ 3 * i8Psi4s87k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s87k0N4 x + x ^ 4 * i8Psi4s87k0dN4 x)) * x ^ 2 - (i8Psi4s87k0N0 x +
    x * i8Psi4s87k0N1 x + x ^ 2 * i8Psi4s87k0N2 x + x ^ 3 * i8Psi4s87k0N3 x +
    x ^ 4 * i8Psi4s87k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s87k0dW x

theorem hasDerivAt_i8Psi4s87k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87k0 (i8Psi4s87k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s87k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s87k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s87k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s87k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s87k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s87k0W hx)
  unfold i8Psi4s87k0
  refine e.congr_deriv ?_
  unfold i8Psi4s87k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽87⁾` over words. -/
noncomputable def i8P4w87k0 (x : ℝ) : ℝ :=
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [negOne, zero, one] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [negOne, one, zero] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [zero, negOne, one] x +
    ((-4 - 8 * x - 4 * x ^ 2) / (x)) * hpl [zero, one, negOne] x

theorem i8Psi4s87k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s87k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w87k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s87k0D i8Psi4s87k0N0 i8Psi4s87k0N1 i8Psi4s87k0N2 i8Psi4s87k0N3 i8Psi4s87k0N4
    i8Psi4s87k0dN0 i8Psi4s87k0dN1 i8Psi4s87k0dN2 i8Psi4s87k0dN3 i8Psi4s87k0dN4 i8Psi4s87k0dW
    i8P4w87k0
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [negOne, zero, one] x = v0 at *
  generalize hpl [negOne, one, zero] x = v1 at *
  generalize hpl [zero, negOne, one] x = v2 at *
  generalize hpl [zero, zero, one] x = v3 at *
  generalize hpl [zero, one, negOne] x = v4 at *
  generalize hpl [zero, one, zero] x = v5 at *
  generalize hpl [negOne, one] x = v6 at *
  generalize hpl [zero, negOne] x = v7 at *
  generalize hpl [zero, zero] x = v8 at *
  generalize hpl [zero, one] x = v9 at *
  generalize hpl [one, negOne] x = v10 at *
  generalize hpl [one, zero] x = v11 at *
  generalize hpl [negOne] x = v12 at *
  generalize hpl [zero] x = v13 at *
  generalize hpl [one] x = v14 at *
  field_simp
  ring

end QED.ThreeLoopD
