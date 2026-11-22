/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P33

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 121 to 123

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s121`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s121D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s121`, `QED.ThreeLoopD.i8Psi4s121D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽121⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s121N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s121N0`. -/
noncomputable def i8Psi4s121dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s121N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s121N0 (i8Psi4s121dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽121⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s121N1 (x : ℝ) : ℝ :=
    (10) +
    (10) * hpl [zero] x +
    (10) * hpl [zero, zero] x +
    (6) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s121N1`. -/
noncomputable def i8Psi4s121dN1 (x : ℝ) : ℝ :=
    0 +
    (10) * (zero.kernel x * hpl [] x) +
    (10) * (zero.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s121N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s121N1 (i8Psi4s121dN1 x) x := by
  unfold i8Psi4s121N1 i8Psi4s121dN1
  exact ((((hasDerivAt_const x (10)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6)))

/-- The part of `ξ² Ψ₄⁽121⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s121N2 (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s121N2`. -/
noncomputable def i8Psi4s121dN2 (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s121N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s121N2 (i8Psi4s121dN2 x) x := by
  unfold i8Psi4s121N2 i8Psi4s121dN2
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (4))

/-- The part of `ξ² Ψ₄⁽121⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s121N3 (x : ℝ) : ℝ :=
    (-2) +
    (2) * hpl [zero] x +
    (-2) * hpl [zero, zero] x +
    (6) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s121N3`. -/
noncomputable def i8Psi4s121dN3 (x : ℝ) : ℝ :=
    0 +
    (2) * (zero.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s121N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s121N3 (i8Psi4s121dN3 x) x := by
  unfold i8Psi4s121N3 i8Psi4s121dN3
  exact ((((hasDerivAt_const x (-2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6)))

/-- The part of `ξ² Ψ₄⁽121⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s121N4 (x : ℝ) : ℝ :=
    (-7 / 8) +
    (7 / 4) * hpl [zero] x +
    (-7 / 2) * hpl [zero, zero] x +
    (3) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s121N4`. -/
noncomputable def i8Psi4s121dN4 (x : ℝ) : ℝ :=
    0 +
    (7 / 4) * (zero.kernel x * hpl [] x) +
    (-7 / 2) * (zero.kernel x * hpl [zero] x) +
    (3) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s121N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s121N4 (i8Psi4s121dN4 x) x := by
  unfold i8Psi4s121N4 i8Psi4s121dN4
  exact ((((hasDerivAt_const x (-7 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (7 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (3)))

/-- The part of `Ψ₄⁽121⁾` with constant coefficients. -/
noncomputable def i8Psi4s121W (x : ℝ) : ℝ :=
    (-6) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s121W`. -/
noncomputable def i8Psi4s121dW (x : ℝ) : ℝ :=
    (-6) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s121W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s121W (i8Psi4s121dW x) x := by
  unfold i8Psi4s121W i8Psi4s121dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-6))

/-- The piece `Ψ₄⁽121⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s121 (x : ℝ) : ℝ :=
  (i8Psi4s121N0 x + x * i8Psi4s121N1 x + x ^ 2 * i8Psi4s121N2 x + x ^ 3 * i8Psi4s121N3 x +
    x ^ 4 * i8Psi4s121N4 x) / x ^ 2 + i8Psi4s121W x

/-- The derivative of `Ψ₄⁽121⁾`. -/
noncomputable def i8Psi4s121D (x : ℝ) : ℝ :=
  ((i8Psi4s121dN0 x + (i8Psi4s121N1 x + x * i8Psi4s121dN1 x) + (2 * x * i8Psi4s121N2 x +
    x ^ 2 * i8Psi4s121dN2 x) + (3 * x ^ 2 * i8Psi4s121N3 x + x ^ 3 * i8Psi4s121dN3 x) +
    (4 * x ^ 3 * i8Psi4s121N4 x + x ^ 4 * i8Psi4s121dN4 x)) * x ^ 2 - (i8Psi4s121N0 x +
    x * i8Psi4s121N1 x + x ^ 2 * i8Psi4s121N2 x + x ^ 3 * i8Psi4s121N3 x +
    x ^ 4 * i8Psi4s121N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s121dW x

theorem hasDerivAt_i8Psi4s121 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s121 (i8Psi4s121D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s121N0 hx).add (X.mul (hasDerivAt_i8Psi4s121N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s121N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s121N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s121N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s121W hx)
  unfold i8Psi4s121
  refine e.congr_deriv ?_
  unfold i8Psi4s121D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 121 of `p₄` in `ξ`: from `t B1 A1 (-λ)^2/2!`, the term with `log^0 (1 -
  ξ) log^2 ξ`. -/
noncomputable def i8P4s121 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x ^ 2 * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * (x / (1 + x)))

/-- `p₄⁽121⁾` written over words. -/
noncomputable def i8P4w121 (x : ℝ) : ℝ :=
    (4 - 4 * x) * hpl [zero, zero] x +
    (6 + 6 * x) * hpl [zero, zero, zero] x

theorem i8P4s121_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s121 x = i8P4w121 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s121 i8P4w121
  simp only [i13hw_00, i13hw_000]
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
  generalize hpl [zero, zero, zero, zero] x = v50 at *
  generalize hpl [zero, zero, zero, one] x = v51 at *
  generalize hpl [zero, zero, one, negOne] x = v52 at *
  generalize hpl [zero, zero, one, one] x = v53 at *
  generalize hpl [zero, one, negOne, negOne] x = v54 at *
  generalize hpl [zero, one, negOne, one] x = v55 at *
  generalize hpl [zero, one, one, negOne] x = v56 at *
  generalize hpl [zero, one, one, one] x = v57 at *
  generalize hpl [negOne, negOne, one] x = v58 at *
  generalize hpl [negOne, one, one] x = v59 at *
  generalize hpl [zero, negOne, negOne] x = v60 at *
  generalize hpl [zero, negOne, one] x = v61 at *
  generalize hpl [zero, zero, negOne] x = v62 at *
  generalize hpl [zero, zero, zero] x = v63 at *
  generalize hpl [zero, zero, one] x = v64 at *
  generalize hpl [zero, one, negOne] x = v65 at *
  generalize hpl [zero, one, one] x = v66 at *
  generalize hpl [negOne, one] x = v67 at *
  generalize hpl [zero, negOne] x = v68 at *
  generalize hpl [zero, zero] x = v69 at *
  generalize hpl [zero, one] x = v70 at *
  generalize hpl [negOne] x = v71 at *
  generalize hpl [zero] x = v72 at *
  generalize hpl [one] x = v73 at *
  ring

/-- **`(Ψ₄⁽121⁾)'(ξ) ξ' = p₄⁽121⁾`**, in terms of `ξ`. -/
theorem i8Psi4s121D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s121D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s121 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s121_eq_w hx]
  unfold i8Psi4s121D i8Psi4s121N0 i8Psi4s121N1 i8Psi4s121N2 i8Psi4s121N3 i8Psi4s121N4 i8Psi4s121dN0
    i8Psi4s121dN1 i8Psi4s121dN2 i8Psi4s121dN3 i8Psi4s121dN4 i8Psi4s121dW i8P4w121
  simp only [kernel_zero, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero] x = v1 at *
  generalize hpl [zero, zero] x = v2 at *
  generalize hpl [zero] x = v3 at *
  ring

/-- The part of `ξ² Ψ₄⁽122⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s122N0 (x : ℝ) : ℝ :=
    (-7 / 8) * hpl [negOne] x +
    (-7 / 4) * hpl [negOne, zero] x +
    (-7 / 4) * hpl [zero, negOne] x +
    (-7 / 2) * hpl [negOne, zero, zero] x +
    (-7 / 2) * hpl [zero, negOne, zero] x +
    (-7 / 2) * hpl [zero, zero, negOne] x +
    (-3) * hpl [negOne, zero, zero, zero] x +
    (-3) * hpl [zero, negOne, zero, zero] x +
    (-3) * hpl [zero, zero, negOne, zero] x +
    (-3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s122N0`. -/
noncomputable def i8Psi4s122dN0 (x : ℝ) : ℝ :=
    (-7 / 8) * (negOne.kernel x * hpl [] x) +
    (-7 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-7 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-7 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-7 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-7 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-3) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-3) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s122N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s122N0 (i8Psi4s122dN0 x) x := by
  unfold i8Psi4s122N0 i8Psi4s122dN0
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-7 / 8)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-7 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-7 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3)))

/-- The part of `ξ² Ψ₄⁽122⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s122N1 (x : ℝ) : ℝ :=
    (-73 / 8) +
    (-12) * hpl [negOne] x +
    (-33 / 4) * hpl [zero] x +
    (-12) * hpl [negOne, zero] x +
    (-12) * hpl [zero, negOne] x +
    (-13 / 2) * hpl [zero, zero] x +
    (-12) * hpl [negOne, zero, zero] x +
    (-12) * hpl [zero, negOne, zero] x +
    (-12) * hpl [zero, zero, negOne] x +
    (-3) * hpl [zero, zero, zero] x +
    (-12) * hpl [negOne, zero, zero, zero] x +
    (-12) * hpl [zero, negOne, zero, zero] x +
    (-12) * hpl [zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s122N1`. -/
noncomputable def i8Psi4s122dN1 (x : ℝ) : ℝ :=
    0 +
    (-12) * (negOne.kernel x * hpl [] x) +
    (-33 / 4) * (zero.kernel x * hpl [] x) +
    (-12) * (negOne.kernel x * hpl [zero] x) +
    (-12) * (zero.kernel x * hpl [negOne] x) +
    (-13 / 2) * (zero.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, negOne] x) +
    (-3) * (zero.kernel x * hpl [zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s122N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s122N1 (i8Psi4s122dN1 x) x := by
  unfold i8Psi4s122N1 i8Psi4s122dN1
  exact ((((((((((((((hasDerivAt_const x (-73 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-33 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-13 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽122⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s122N2 (x : ℝ) : ℝ :=
    (89 / 8) * hpl [zero] x +
    (-41 / 2) * hpl [negOne, zero] x +
    (41 / 4) * hpl [zero, zero] x +
    (17 / 2) * hpl [zero, zero, zero] x +
    (-18) * hpl [negOne, zero, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x +
    (-8) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s122N2`. -/
noncomputable def i8Psi4s122dN2 (x : ℝ) : ℝ :=
    (89 / 8) * (zero.kernel x * hpl [] x) +
    (-41 / 2) * (negOne.kernel x * hpl [zero] x) +
    (41 / 4) * (zero.kernel x * hpl [zero] x) +
    (17 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (-18) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s122N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s122N2 (i8Psi4s122dN2 x) x := by
  unfold i8Psi4s122N2 i8Psi4s122dN2
  exact (((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (89 / 8)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-41 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (41 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (17 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽122⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s122N3 (x : ℝ) : ℝ :=
    (-311 / 8) +
    (12) * hpl [negOne] x +
    (111 / 4) * hpl [zero] x +
    (-12) * hpl [negOne, zero] x +
    (-12) * hpl [zero, negOne] x +
    (-35 / 2) * hpl [zero, zero] x +
    (12) * hpl [negOne, zero, zero] x +
    (12) * hpl [zero, negOne, zero] x +
    (12) * hpl [zero, zero, negOne] x +
    (9) * hpl [zero, zero, zero] x +
    (-12) * hpl [negOne, zero, zero, zero] x +
    (-12) * hpl [zero, negOne, zero, zero] x +
    (-12) * hpl [zero, zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s122N3`. -/
noncomputable def i8Psi4s122dN3 (x : ℝ) : ℝ :=
    0 +
    (12) * (negOne.kernel x * hpl [] x) +
    (111 / 4) * (zero.kernel x * hpl [] x) +
    (-12) * (negOne.kernel x * hpl [zero] x) +
    (-12) * (zero.kernel x * hpl [negOne] x) +
    (-35 / 2) * (zero.kernel x * hpl [zero] x) +
    (12) * (negOne.kernel x * hpl [zero, zero] x) +
    (12) * (zero.kernel x * hpl [negOne, zero] x) +
    (12) * (zero.kernel x * hpl [zero, negOne] x) +
    (9) * (zero.kernel x * hpl [zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-12) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s122N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s122N3 (i8Psi4s122dN3 x) x := by
  unfold i8Psi4s122N3 i8Psi4s122dN3
  exact ((((((((((((((hasDerivAt_const x (-311 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (111 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-35 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽122⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s122N4 (x : ℝ) : ℝ :=
    (-3 / 2) +
    (7 / 8) * hpl [negOne] x +
    (17 / 8) * hpl [zero] x +
    (-7 / 4) * hpl [negOne, zero] x +
    (-7 / 4) * hpl [zero, negOne] x +
    (-5 / 2) * hpl [zero, zero] x +
    (7 / 2) * hpl [negOne, zero, zero] x +
    (7 / 2) * hpl [zero, negOne, zero] x +
    (7 / 2) * hpl [zero, zero, negOne] x +
    (3 / 2) * hpl [zero, zero, zero] x +
    (-3) * hpl [negOne, zero, zero, zero] x +
    (-3) * hpl [zero, negOne, zero, zero] x +
    (-3) * hpl [zero, zero, negOne, zero] x +
    (-3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s122N4`. -/
noncomputable def i8Psi4s122dN4 (x : ℝ) : ℝ :=
    0 +
    (7 / 8) * (negOne.kernel x * hpl [] x) +
    (17 / 8) * (zero.kernel x * hpl [] x) +
    (-7 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-7 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-5 / 2) * (zero.kernel x * hpl [zero] x) +
    (7 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (7 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (7 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (3 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (-3) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-3) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s122N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s122N4 (i8Psi4s122dN4 x) x := by
  unfold i8Psi4s122N4 i8Psi4s122dN4
  exact ((((((((((((((hasDerivAt_const x (-3 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (7 / 8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (17 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-7 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-7 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3)))

/-- The part of `Ψ₄⁽122⁾` with constant coefficients. -/
noncomputable def i8Psi4s122W (x : ℝ) : ℝ :=
    (9) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s122W`. -/
noncomputable def i8Psi4s122dW (x : ℝ) : ℝ :=
    (9) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s122W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s122W (i8Psi4s122dW x) x := by
  unfold i8Psi4s122W i8Psi4s122dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (9))

/-- The piece `Ψ₄⁽122⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s122 (x : ℝ) : ℝ :=
  (i8Psi4s122N0 x + x * i8Psi4s122N1 x + x ^ 2 * i8Psi4s122N2 x + x ^ 3 * i8Psi4s122N3 x +
    x ^ 4 * i8Psi4s122N4 x) / x ^ 2 + i8Psi4s122W x

/-- The derivative of `Ψ₄⁽122⁾`. -/
noncomputable def i8Psi4s122D (x : ℝ) : ℝ :=
  ((i8Psi4s122dN0 x + (i8Psi4s122N1 x + x * i8Psi4s122dN1 x) + (2 * x * i8Psi4s122N2 x +
    x ^ 2 * i8Psi4s122dN2 x) + (3 * x ^ 2 * i8Psi4s122N3 x + x ^ 3 * i8Psi4s122dN3 x) +
    (4 * x ^ 3 * i8Psi4s122N4 x + x ^ 4 * i8Psi4s122dN4 x)) * x ^ 2 - (i8Psi4s122N0 x +
    x * i8Psi4s122N1 x + x ^ 2 * i8Psi4s122N2 x + x ^ 3 * i8Psi4s122N3 x +
    x ^ 4 * i8Psi4s122N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s122dW x

theorem hasDerivAt_i8Psi4s122 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s122 (i8Psi4s122D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s122N0 hx).add (X.mul (hasDerivAt_i8Psi4s122N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s122N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s122N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s122N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s122W hx)
  unfold i8Psi4s122
  refine e.congr_deriv ?_
  unfold i8Psi4s122D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 122 of `p₄` in `ξ`: from `t B1 A1 (-λ)^2/2!`, the term with `log^0 (1 -
  ξ) log^2 ξ`. -/
noncomputable def i8P4s122 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x ^ 2 * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 + x) / (1 -
    x) * (-hpl [negOne] x))

/-- `p₄⁽122⁾` written over words. -/
noncomputable def i8P4w122 (x : ℝ) : ℝ :=
    ((-4 + 4 * x ^ 2) / (x)) * hpl [negOne, zero, zero] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [zero, negOne, zero] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [zero, zero, negOne] x +
    ((-6 - 12 * x - 6 * x ^ 2) / (x)) * hpl [negOne, zero, zero, zero] x +
    ((-6 - 12 * x - 6 * x ^ 2) / (x)) * hpl [zero, negOne, zero, zero] x +
    ((-6 - 12 * x - 6 * x ^ 2) / (x)) * hpl [zero, zero, negOne, zero] x +
    ((-6 - 12 * x - 6 * x ^ 2) / (x)) * hpl [zero, zero, zero, negOne] x

theorem i8P4s122_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s122 x = i8P4w122 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s122 i8P4w122
  simp only [i13hw_0m0 hx, i13hw_m00 hx, i13hw_00m0 hx, i13hw_0m00 hx, i13hw_m000 hx]
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
  generalize hpl [negOne, zero, zero, zero] x = v42 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v43 at *
  generalize hpl [zero, negOne, negOne, one] x = v44 at *
  generalize hpl [zero, negOne, zero, zero] x = v45 at *
  generalize hpl [zero, negOne, zero, one] x = v46 at *
  generalize hpl [zero, negOne, one, negOne] x = v47 at *
  generalize hpl [zero, negOne, one, one] x = v48 at *
  generalize hpl [zero, zero, negOne, negOne] x = v49 at *
  generalize hpl [zero, zero, negOne, zero] x = v50 at *
  generalize hpl [zero, zero, negOne, one] x = v51 at *
  generalize hpl [zero, zero, zero, negOne] x = v52 at *
  generalize hpl [zero, zero, zero, zero] x = v53 at *
  generalize hpl [zero, zero, zero, one] x = v54 at *
  generalize hpl [zero, zero, one, negOne] x = v55 at *
  generalize hpl [zero, zero, one, one] x = v56 at *
  generalize hpl [zero, one, negOne, negOne] x = v57 at *
  generalize hpl [zero, one, negOne, one] x = v58 at *
  generalize hpl [zero, one, one, negOne] x = v59 at *
  generalize hpl [zero, one, one, one] x = v60 at *
  generalize hpl [negOne, negOne, one] x = v61 at *
  generalize hpl [negOne, zero, zero] x = v62 at *
  generalize hpl [negOne, one, one] x = v63 at *
  generalize hpl [zero, negOne, negOne] x = v64 at *
  generalize hpl [zero, negOne, zero] x = v65 at *
  generalize hpl [zero, negOne, one] x = v66 at *
  generalize hpl [zero, zero, negOne] x = v67 at *
  generalize hpl [zero, zero, zero] x = v68 at *
  generalize hpl [zero, zero, one] x = v69 at *
  generalize hpl [zero, one, negOne] x = v70 at *
  generalize hpl [zero, one, one] x = v71 at *
  generalize hpl [negOne, zero] x = v72 at *
  generalize hpl [negOne, one] x = v73 at *
  generalize hpl [zero, negOne] x = v74 at *
  generalize hpl [zero, zero] x = v75 at *
  generalize hpl [zero, one] x = v76 at *
  generalize hpl [negOne] x = v77 at *
  generalize hpl [zero] x = v78 at *
  generalize hpl [one] x = v79 at *
  ring

/-- **`(Ψ₄⁽122⁾)'(ξ) ξ' = p₄⁽122⁾`**, in terms of `ξ`. -/
theorem i8Psi4s122D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s122D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s122 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s122_eq_w hx]
  unfold i8Psi4s122D i8Psi4s122N0 i8Psi4s122N1 i8Psi4s122N2 i8Psi4s122N3 i8Psi4s122N4 i8Psi4s122dN0
    i8Psi4s122dN1 i8Psi4s122dN2 i8Psi4s122dN3 i8Psi4s122dN4 i8Psi4s122dW i8P4w122
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [negOne, zero, zero, zero] x = v0 at *
  generalize hpl [zero, negOne, zero, zero] x = v1 at *
  generalize hpl [zero, zero, negOne, zero] x = v2 at *
  generalize hpl [zero, zero, zero, negOne] x = v3 at *
  generalize hpl [zero, zero, zero, zero] x = v4 at *
  generalize hpl [negOne, zero, zero] x = v5 at *
  generalize hpl [zero, negOne, zero] x = v6 at *
  generalize hpl [zero, zero, negOne] x = v7 at *
  generalize hpl [zero, zero, zero] x = v8 at *
  generalize hpl [negOne, zero] x = v9 at *
  generalize hpl [zero, negOne] x = v10 at *
  generalize hpl [zero, zero] x = v11 at *
  generalize hpl [negOne] x = v12 at *
  generalize hpl [zero] x = v13 at *
  ring

/-- The part of `ξ² Ψ₄⁽123⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s123N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s123N0`. -/
noncomputable def i8Psi4s123dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s123N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s123N0 (i8Psi4s123dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽123⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s123N1 (x : ℝ) : ℝ :=
    (16) * hpl [one] x +
    (16) * hpl [zero, one] x +
    (16) * hpl [one, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (8) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s123N1`. -/
noncomputable def i8Psi4s123dN1 (x : ℝ) : ℝ :=
    (16) * (one.kernel x * hpl [] x) +
    (16) * (zero.kernel x * hpl [one] x) +
    (16) * (one.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s123N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s123N1 (i8Psi4s123dN1 x) x := by
  unfold i8Psi4s123N1 i8Psi4s123dN1
  exact (((((((hasDerivAt_hpl_cons one [] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽123⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s123N2 (x : ℝ) : ℝ :=
    (-16) * hpl [zero] x +
    (-19) * hpl [one] x +
    (-16) * hpl [zero, zero] x +
    (-10) * hpl [one, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (-20) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s123N2`. -/
noncomputable def i8Psi4s123dN2 (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [] x) +
    (-19) * (one.kernel x * hpl [] x) +
    (-16) * (zero.kernel x * hpl [zero] x) +
    (-10) * (one.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (-20) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s123N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s123N2 (i8Psi4s123dN2 x) x := by
  unfold i8Psi4s123N2 i8Psi4s123dN2
  exact ((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-19))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-20)))

/-- The part of `ξ² Ψ₄⁽123⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s123N3 (x : ℝ) : ℝ :=
    (21) +
    (-18) * hpl [zero] x +
    (12) * hpl [zero, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (8) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s123N3`. -/
noncomputable def i8Psi4s123dN3 (x : ℝ) : ℝ :=
    0 +
    (-18) * (zero.kernel x * hpl [] x) +
    (12) * (zero.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s123N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s123N3 (i8Psi4s123dN3 x) x := by
  unfold i8Psi4s123N3 i8Psi4s123dN3
  exact ((((((hasDerivAt_const x (21)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-18))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽123⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s123N4 (x : ℝ) : ℝ :=
    (7 / 2) +
    (-4) * hpl [zero] x +
    (3) * hpl [one] x +
    (2) * hpl [zero, zero] x +
    (-6) * hpl [zero, one] x +
    (-6) * hpl [one, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (4) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi4s123N4`. -/
noncomputable def i8Psi4s123dN4 (x : ℝ) : ℝ :=
    0 +
    (-4) * (zero.kernel x * hpl [] x) +
    (3) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (-6) * (zero.kernel x * hpl [one] x) +
    (-6) * (one.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s123N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s123N4 (i8Psi4s123dN4 x) x := by
  unfold i8Psi4s123N4 i8Psi4s123dN4
  exact (((((((((hasDerivAt_const x (7 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽123⁾` with constant coefficients. -/
noncomputable def i8Psi4s123W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, zero] x +
    (-8) * hpl [zero, zero, zero, one] x +
    (-8) * hpl [zero, zero, one, zero] x +
    (-8) * hpl [zero, one, zero, zero] x

/-- The derivative of `i8Psi4s123W`. -/
noncomputable def i8Psi4s123dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-8) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s123W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s123W (i8Psi4s123dW x) x := by
  unfold i8Psi4s123W i8Psi4s123dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-8)))

/-- The piece `Ψ₄⁽123⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s123 (x : ℝ) : ℝ :=
  (i8Psi4s123N0 x + x * i8Psi4s123N1 x + x ^ 2 * i8Psi4s123N2 x + x ^ 3 * i8Psi4s123N3 x +
    x ^ 4 * i8Psi4s123N4 x) / x ^ 2 + i8Psi4s123W x

/-- The derivative of `Ψ₄⁽123⁾`. -/
noncomputable def i8Psi4s123D (x : ℝ) : ℝ :=
  ((i8Psi4s123dN0 x + (i8Psi4s123N1 x + x * i8Psi4s123dN1 x) + (2 * x * i8Psi4s123N2 x +
    x ^ 2 * i8Psi4s123dN2 x) + (3 * x ^ 2 * i8Psi4s123N3 x + x ^ 3 * i8Psi4s123dN3 x) +
    (4 * x ^ 3 * i8Psi4s123N4 x + x ^ 4 * i8Psi4s123dN4 x)) * x ^ 2 - (i8Psi4s123N0 x +
    x * i8Psi4s123N1 x + x ^ 2 * i8Psi4s123N2 x + x ^ 3 * i8Psi4s123N3 x +
    x ^ 4 * i8Psi4s123N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s123dW x

theorem hasDerivAt_i8Psi4s123 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s123 (i8Psi4s123D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s123N0 hx).add (X.mul (hasDerivAt_i8Psi4s123N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s123N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s123N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s123N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s123W hx)
  unfold i8Psi4s123
  refine e.congr_deriv ?_
  unfold i8Psi4s123D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 123 of `p₄` in `ξ`: from `t B1 A1 (-λ)^2/2!`, the term with `log^1 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s123 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * Real.log x * (2 + Real.log x * (1 + x) / (1 -
    x)) * ((1 + x) / (1 - x) * (x / (1 + x))))

/-- `p₄⁽123⁾` written over words. -/
noncomputable def i8P4w123 (x : ℝ) : ℝ :=
    (8 - 8 * x) * hpl [zero, one] x +
    (8 - 8 * x) * hpl [one, zero] x +
    (8 + 8 * x) * hpl [zero, zero, one] x +
    (8 + 8 * x) * hpl [zero, one, zero] x +
    (8 + 8 * x) * hpl [one, zero, zero] x

theorem i8P4s123_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s123 x = i8P4w123 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s123 i8P4w123
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

/-- **`(Ψ₄⁽123⁾)'(ξ) ξ' = p₄⁽123⁾`**, in terms of `ξ`. -/
theorem i8Psi4s123D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s123D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s123 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s123_eq_w hx]
  unfold i8Psi4s123D i8Psi4s123N0 i8Psi4s123N1 i8Psi4s123N2 i8Psi4s123N3 i8Psi4s123N4 i8Psi4s123dN0
    i8Psi4s123dN1 i8Psi4s123dN2 i8Psi4s123dN3 i8Psi4s123dN4 i8Psi4s123dW i8P4w123
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

end QED.ThreeLoopD
