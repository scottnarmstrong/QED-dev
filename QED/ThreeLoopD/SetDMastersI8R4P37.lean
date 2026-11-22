/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P36

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 126 to 127

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s126`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s126D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s126`, `QED.ThreeLoopD.i8Psi4s126D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽126⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s126N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s126N0`. -/
noncomputable def i8Psi4s126dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s126N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s126N0 (i8Psi4s126dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽126⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s126N1 (x : ℝ) : ℝ :=
    (24) * hpl [one, one] x +
    (8) * hpl [zero, one, one] x +
    (8) * hpl [one, zero, one] x +
    (8) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s126N1`. -/
noncomputable def i8Psi4s126dN1 (x : ℝ) : ℝ :=
    (24) * (one.kernel x * hpl [one] x) +
    (8) * (zero.kernel x * hpl [one, one] x) +
    (8) * (one.kernel x * hpl [zero, one] x) +
    (8) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s126N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s126N1 (i8Psi4s126dN1 x) x := by
  unfold i8Psi4s126N1 i8Psi4s126dN1
  exact (((((hasDerivAt_hpl_cons one [one] hx).const_mul (24)).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽126⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s126N2 (x : ℝ) : ℝ :=
    (20) * hpl [one] x +
    (-24) * hpl [zero, one] x +
    (-14) * hpl [one, zero] x +
    (-22) * hpl [one, one] x +
    (16) * hpl [zero, one, one] x +
    (-20) * hpl [one, zero, one] x +
    (-20) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s126N2`. -/
noncomputable def i8Psi4s126dN2 (x : ℝ) : ℝ :=
    (20) * (one.kernel x * hpl [] x) +
    (-24) * (zero.kernel x * hpl [one] x) +
    (-14) * (one.kernel x * hpl [zero] x) +
    (-22) * (one.kernel x * hpl [one] x) +
    (16) * (zero.kernel x * hpl [one, one] x) +
    (-20) * (one.kernel x * hpl [zero, one] x) +
    (-20) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s126N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s126N2 (i8Psi4s126dN2 x) x := by
  unfold i8Psi4s126N2 i8Psi4s126dN2
  exact ((((((((hasDerivAt_hpl_cons one [] hx).const_mul (20)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-20)))

/-- The part of `ξ² Ψ₄⁽126⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s126N3 (x : ℝ) : ℝ :=
    (-34) +
    (14) * hpl [zero] x +
    (-14) * hpl [one] x +
    (12) * hpl [zero, one] x +
    (12) * hpl [one, zero] x +
    (8) * hpl [one, one] x +
    (8) * hpl [zero, one, one] x +
    (8) * hpl [one, zero, one] x +
    (8) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s126N3`. -/
noncomputable def i8Psi4s126dN3 (x : ℝ) : ℝ :=
    0 +
    (14) * (zero.kernel x * hpl [] x) +
    (-14) * (one.kernel x * hpl [] x) +
    (12) * (zero.kernel x * hpl [one] x) +
    (12) * (one.kernel x * hpl [zero] x) +
    (8) * (one.kernel x * hpl [one] x) +
    (8) * (zero.kernel x * hpl [one, one] x) +
    (8) * (one.kernel x * hpl [zero, one] x) +
    (8) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s126N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s126N3 (i8Psi4s126dN3 x) x := by
  unfold i8Psi4s126N3 i8Psi4s126dN3
  exact (((((((((hasDerivAt_const x (-34)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽126⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s126N4 (x : ℝ) : ℝ :=
    (-7 / 2) +
    (1) * hpl [zero] x +
    (-6) * hpl [one] x +
    (2) * hpl [zero, one] x +
    (2) * hpl [one, zero] x +
    (-10) * hpl [one, one] x +
    (4) * hpl [zero, one, one] x +
    (4) * hpl [one, zero, one] x +
    (4) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s126N4`. -/
noncomputable def i8Psi4s126dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (-6) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (-10) * (one.kernel x * hpl [one] x) +
    (4) * (zero.kernel x * hpl [one, one] x) +
    (4) * (one.kernel x * hpl [zero, one] x) +
    (4) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s126N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s126N4 (i8Psi4s126dN4 x) x := by
  unfold i8Psi4s126N4 i8Psi4s126dN4
  exact (((((((((hasDerivAt_const x (-7 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽126⁾` with constant coefficients. -/
noncomputable def i8Psi4s126W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, one] x +
    (-8) * hpl [zero, one, zero] x +
    (-8) * hpl [zero, zero, one, one] x +
    (-8) * hpl [zero, one, zero, one] x +
    (-8) * hpl [zero, one, one, zero] x

/-- The derivative of `i8Psi4s126W`. -/
noncomputable def i8Psi4s126dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero, one] x) +
    (-8) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, one, one] x) +
    (-8) * (zero.kernel x * hpl [one, zero, one] x) +
    (-8) * (zero.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s126W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s126W (i8Psi4s126dW x) x := by
  unfold i8Psi4s126W i8Psi4s126dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (-8)))

/-- The piece `Ψ₄⁽126⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s126 (x : ℝ) : ℝ :=
  (i8Psi4s126N0 x + x * i8Psi4s126N1 x + x ^ 2 * i8Psi4s126N2 x + x ^ 3 * i8Psi4s126N3 x +
    x ^ 4 * i8Psi4s126N4 x) / x ^ 2 + i8Psi4s126W x

/-- The derivative of `Ψ₄⁽126⁾`. -/
noncomputable def i8Psi4s126D (x : ℝ) : ℝ :=
  ((i8Psi4s126dN0 x + (i8Psi4s126N1 x + x * i8Psi4s126dN1 x) + (2 * x * i8Psi4s126N2 x +
    x ^ 2 * i8Psi4s126dN2 x) + (3 * x ^ 2 * i8Psi4s126N3 x + x ^ 3 * i8Psi4s126dN3 x) +
    (4 * x ^ 3 * i8Psi4s126N4 x + x ^ 4 * i8Psi4s126dN4 x)) * x ^ 2 - (i8Psi4s126N0 x +
    x * i8Psi4s126N1 x + x ^ 2 * i8Psi4s126N2 x + x ^ 3 * i8Psi4s126N3 x +
    x ^ 4 * i8Psi4s126N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s126dW x

theorem hasDerivAt_i8Psi4s126 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s126 (i8Psi4s126D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s126N0 hx).add (X.mul (hasDerivAt_i8Psi4s126N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s126N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s126N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s126N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s126W hx)
  unfold i8Psi4s126
  refine e.congr_deriv ?_
  unfold i8Psi4s126D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 126 of `p₄` in `ξ`: from `t B1 A1 (-λ)^2/2!`, the term with `log^2 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s126 (x : ℝ) : ℝ :=
  4 * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 2 * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 +
    x) / (1 - x) * (x / (1 + x)))

/-- `p₄⁽126⁾` written over words. -/
noncomputable def i8P4w126 (x : ℝ) : ℝ :=
    (16 - 16 * x) * hpl [one, one] x +
    (8 + 8 * x) * hpl [zero, one, one] x +
    (8 + 8 * x) * hpl [one, zero, one] x +
    (8 + 8 * x) * hpl [one, one, zero] x

theorem i8P4s126_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s126 x = i8P4w126 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s126 i8P4w126
  simp only [i13hw_11 hx, i13hw_101 hx, i13hw_110 hx, i13_log_one_sub_eq hx]
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
  generalize hpl [zero, one, zero, one] x = v55 at *
  generalize hpl [zero, one, one, negOne] x = v56 at *
  generalize hpl [zero, one, one, zero] x = v57 at *
  generalize hpl [zero, one, one, one] x = v58 at *
  generalize hpl [negOne, negOne, one] x = v59 at *
  generalize hpl [negOne, one, one] x = v60 at *
  generalize hpl [zero, negOne, negOne] x = v61 at *
  generalize hpl [zero, negOne, one] x = v62 at *
  generalize hpl [zero, zero, negOne] x = v63 at *
  generalize hpl [zero, zero, one] x = v64 at *
  generalize hpl [zero, one, negOne] x = v65 at *
  generalize hpl [zero, one, zero] x = v66 at *
  generalize hpl [zero, one, one] x = v67 at *
  generalize hpl [one, zero, one] x = v68 at *
  generalize hpl [one, one, zero] x = v69 at *
  generalize hpl [negOne, one] x = v70 at *
  generalize hpl [zero, negOne] x = v71 at *
  generalize hpl [zero, one] x = v72 at *
  generalize hpl [one, zero] x = v73 at *
  generalize hpl [one, one] x = v74 at *
  generalize hpl [negOne] x = v75 at *
  generalize hpl [zero] x = v76 at *
  generalize hpl [one] x = v77 at *
  ring

/-- **`(Ψ₄⁽126⁾)'(ξ) ξ' = p₄⁽126⁾`**, in terms of `ξ`. -/
theorem i8Psi4s126D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s126D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s126 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s126_eq_w hx]
  unfold i8Psi4s126D i8Psi4s126N0 i8Psi4s126N1 i8Psi4s126N2 i8Psi4s126N3 i8Psi4s126N4 i8Psi4s126dN0
    i8Psi4s126dN1 i8Psi4s126dN2 i8Psi4s126dN3 i8Psi4s126dN4 i8Psi4s126dW i8P4w126
  simp only [kernel_zero, kernel_one, hpl_nil]
  field_simp
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
  ring

/-- The part of `ξ² Ψ₄⁽127⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s127N0 (x : ℝ) : ℝ :=
    (-8) * hpl [negOne, one, one] x +
    (-8) * hpl [one, negOne, one] x +
    (-8) * hpl [one, one, negOne] x

/-- The derivative of `i8Psi4s127N0`. -/
noncomputable def i8Psi4s127dN0 (x : ℝ) : ℝ :=
    (-8) * (negOne.kernel x * hpl [one, one] x) +
    (-8) * (one.kernel x * hpl [negOne, one] x) +
    (-8) * (one.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s127N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s127N0 (i8Psi4s127dN0 x) x := by
  unfold i8Psi4s127N0 i8Psi4s127dN0
  exact ((((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽127⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s127N1 (x : ℝ) : ℝ :=
    (-8) * hpl [negOne, one] x +
    (-8) * hpl [one, negOne] x +
    (-8) * hpl [one, one] x

/-- The derivative of `i8Psi4s127N1`. -/
noncomputable def i8Psi4s127dN1 (x : ℝ) : ℝ :=
    (-8) * (negOne.kernel x * hpl [one] x) +
    (-8) * (one.kernel x * hpl [negOne] x) +
    (-8) * (one.kernel x * hpl [one] x)

theorem hasDerivAt_i8Psi4s127N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s127N1 (i8Psi4s127dN1 x) x := by
  unfold i8Psi4s127N1 i8Psi4s127dN1
  exact ((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽127⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s127N2 (x : ℝ) : ℝ :=
    (10) * hpl [negOne] x +
    (4) * hpl [one] x +
    (-4) * hpl [negOne, one] x +
    (-4) * hpl [one, negOne] x +
    (4) * hpl [one, one] x

/-- The derivative of `i8Psi4s127N2`. -/
noncomputable def i8Psi4s127dN2 (x : ℝ) : ℝ :=
    (10) * (negOne.kernel x * hpl [] x) +
    (4) * (one.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [one] x) +
    (-4) * (one.kernel x * hpl [negOne] x) +
    (4) * (one.kernel x * hpl [one] x)

theorem hasDerivAt_i8Psi4s127N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s127N2 (i8Psi4s127dN2 x) x := by
  unfold i8Psi4s127N2 i8Psi4s127dN2
  exact ((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (10)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽127⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s127N3 (x : ℝ) : ℝ :=
    (-14) +
    (12) * hpl [negOne] x +
    (8) * hpl [negOne, one] x +
    (8) * hpl [one, negOne] x +
    (8) * hpl [one, one] x

/-- The derivative of `i8Psi4s127N3`. -/
noncomputable def i8Psi4s127dN3 (x : ℝ) : ℝ :=
    0 +
    (12) * (negOne.kernel x * hpl [] x) +
    (8) * (negOne.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [negOne] x) +
    (8) * (one.kernel x * hpl [one] x)

theorem hasDerivAt_i8Psi4s127N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s127N3 (i8Psi4s127dN3 x) x := by
  unfold i8Psi4s127N3 i8Psi4s127dN3
  exact (((((hasDerivAt_const x (-14)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽127⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s127N4 (x : ℝ) : ℝ :=
    (-3) +
    (2) * hpl [negOne] x +
    (-4) * hpl [one] x +
    (4) * hpl [negOne, one] x +
    (4) * hpl [one, negOne] x +
    (-4) * hpl [one, one] x +
    (8) * hpl [negOne, one, one] x +
    (8) * hpl [one, negOne, one] x +
    (8) * hpl [one, one, negOne] x

/-- The derivative of `i8Psi4s127N4`. -/
noncomputable def i8Psi4s127dN4 (x : ℝ) : ℝ :=
    0 +
    (2) * (negOne.kernel x * hpl [] x) +
    (-4) * (one.kernel x * hpl [] x) +
    (4) * (negOne.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [negOne] x) +
    (-4) * (one.kernel x * hpl [one] x) +
    (8) * (negOne.kernel x * hpl [one, one] x) +
    (8) * (one.kernel x * hpl [negOne, one] x) +
    (8) * (one.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s127N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s127N4 (i8Psi4s127dN4 x) x := by
  unfold i8Psi4s127N4 i8Psi4s127dN4
  exact (((((((((hasDerivAt_const x (-3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [negOne, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, negOne] hx).const_mul (8)))

/-- The part of `Ψ₄⁽127⁾` with constant coefficients. -/
noncomputable def i8Psi4s127W (x : ℝ) : ℝ :=
    (8) * hpl [zero, negOne] x +
    (16) * hpl [zero, one] x +
    (8) * hpl [zero, negOne, one] x +
    (8) * hpl [zero, one, negOne] x +
    (-8) * hpl [zero, one, one] x +
    (-32) * hpl [zero, negOne, one, one] x +
    (-32) * hpl [zero, one, negOne, one] x +
    (-32) * hpl [zero, one, one, negOne] x

/-- The derivative of `i8Psi4s127W`. -/
noncomputable def i8Psi4s127dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [negOne] x) +
    (16) * (zero.kernel x * hpl [one] x) +
    (8) * (zero.kernel x * hpl [negOne, one] x) +
    (8) * (zero.kernel x * hpl [one, negOne] x) +
    (-8) * (zero.kernel x * hpl [one, one] x) +
    (-32) * (zero.kernel x * hpl [negOne, one, one] x) +
    (-32) * (zero.kernel x * hpl [one, negOne, one] x) +
    (-32) * (zero.kernel x * hpl [one, one, negOne] x)

theorem hasDerivAt_i8Psi4s127W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s127W (i8Psi4s127dW x) x := by
  unfold i8Psi4s127W i8Psi4s127dW
  exact (((((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, one] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, one] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons zero [one, one, negOne] hx).const_mul (-32)))

/-- The piece `Ψ₄⁽127⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s127 (x : ℝ) : ℝ :=
  (i8Psi4s127N0 x + x * i8Psi4s127N1 x + x ^ 2 * i8Psi4s127N2 x + x ^ 3 * i8Psi4s127N3 x +
    x ^ 4 * i8Psi4s127N4 x) / x ^ 2 + i8Psi4s127W x

/-- The derivative of `Ψ₄⁽127⁾`. -/
noncomputable def i8Psi4s127D (x : ℝ) : ℝ :=
  ((i8Psi4s127dN0 x + (i8Psi4s127N1 x + x * i8Psi4s127dN1 x) + (2 * x * i8Psi4s127N2 x +
    x ^ 2 * i8Psi4s127dN2 x) + (3 * x ^ 2 * i8Psi4s127N3 x + x ^ 3 * i8Psi4s127dN3 x) +
    (4 * x ^ 3 * i8Psi4s127N4 x + x ^ 4 * i8Psi4s127dN4 x)) * x ^ 2 - (i8Psi4s127N0 x +
    x * i8Psi4s127N1 x + x ^ 2 * i8Psi4s127N2 x + x ^ 3 * i8Psi4s127N3 x +
    x ^ 4 * i8Psi4s127N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s127dW x

theorem hasDerivAt_i8Psi4s127 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s127 (i8Psi4s127D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s127N0 hx).add (X.mul (hasDerivAt_i8Psi4s127N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s127N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s127N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s127N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s127W hx)
  unfold i8Psi4s127
  refine e.congr_deriv ?_
  unfold i8Psi4s127D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 127 of `p₄` in `ξ`: from `t B1 A1 (-λ)^2/2!`, the term with `log^2 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s127 (x : ℝ) : ℝ :=
  4 * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 2 * ((1 + x) / (1 - x) * ((2 + ((-2) * x)) / (1 +
    x))) * ((1 + x) / (1 - x) * (-hpl [negOne] x))

/-- `p₄⁽127⁾` written over words. -/
noncomputable def i8P4w127 (x : ℝ) : ℝ :=
    ((-16 + 16 * x ^ 2) / (x)) * hpl [negOne, one, one] x +
    ((-16 + 16 * x ^ 2) / (x)) * hpl [one, negOne, one] x +
    ((-16 + 16 * x ^ 2) / (x)) * hpl [one, one, negOne] x

theorem i8P4s127_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s127 x = i8P4w127 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s127 i8P4w127
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [one] [one] hx
  have e1 := hpl_mul_hpl [negOne] [one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  linear_combination (norm := skip) (((-8 + 8 * x ^ 2) / (x)) * hpl [negOne] x) * e0 + (((-16 +
    16 * x ^ 2) / (x))) * e1
  field_simp
  generalize hpl [negOne, one, one] x = v0 at *
  generalize hpl [one, negOne, one] x = v1 at *
  generalize hpl [one, one, negOne] x = v2 at *
  generalize hpl [one, one] x = v3 at *
  generalize hpl [negOne] x = v4 at *
  generalize hpl [one] x = v5 at *
  ring

/-- **`(Ψ₄⁽127⁾)'(ξ) ξ' = p₄⁽127⁾`**, in terms of `ξ`. -/
theorem i8Psi4s127D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s127D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s127 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s127_eq_w hx]
  unfold i8Psi4s127D i8Psi4s127N0 i8Psi4s127N1 i8Psi4s127N2 i8Psi4s127N3 i8Psi4s127N4 i8Psi4s127dN0
    i8Psi4s127dN1 i8Psi4s127dN2 i8Psi4s127dN3 i8Psi4s127dN4 i8Psi4s127dW i8P4w127
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, one, one] x = v0 at *
  generalize hpl [zero, one, negOne, one] x = v1 at *
  generalize hpl [zero, one, one, negOne] x = v2 at *
  generalize hpl [negOne, one, one] x = v3 at *
  generalize hpl [zero, negOne, one] x = v4 at *
  generalize hpl [zero, one, negOne] x = v5 at *
  generalize hpl [zero, one, one] x = v6 at *
  generalize hpl [one, negOne, one] x = v7 at *
  generalize hpl [one, one, negOne] x = v8 at *
  generalize hpl [negOne, one] x = v9 at *
  generalize hpl [zero, negOne] x = v10 at *
  generalize hpl [zero, one] x = v11 at *
  generalize hpl [one, negOne] x = v12 at *
  generalize hpl [one, one] x = v13 at *
  generalize hpl [negOne] x = v14 at *
  generalize hpl [one] x = v15 at *
  ring

end QED.ThreeLoopD
