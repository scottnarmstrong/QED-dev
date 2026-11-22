/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P22

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 87 to 92

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s87`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s87D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s87`, `QED.ThreeLoopD.i8Psi4s87D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The piece `Ψ₄⁽87⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s87 (x : ℝ) : ℝ :=
  i8Psi4s87k0 x + i8Psi4s87k1 x + i8Psi4s87k2 x + i8Psi4s87k3 x + i8Psi4s87k4 x

/-- The derivative of `Ψ₄⁽87⁾`. -/
noncomputable def i8Psi4s87D (x : ℝ) : ℝ :=
  i8Psi4s87k0D x + i8Psi4s87k1D x + i8Psi4s87k2D x + i8Psi4s87k3D x + i8Psi4s87k4D x

theorem hasDerivAt_i8Psi4s87 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s87 (i8Psi4s87D x) x := by
  unfold i8Psi4s87 i8Psi4s87D
  exact (((((hasDerivAt_i8Psi4s87k0 hx).add (hasDerivAt_i8Psi4s87k1 hx)).add (hasDerivAt_i8Psi4s87k2
    hx)).add (hasDerivAt_i8Psi4s87k3 hx)).add (hasDerivAt_i8Psi4s87k4 hx))

/-- The sub-piece 87 of `p₄` in `ξ`: from `t B2 A1 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s87 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * (2 + Real.log x * (1 + x) / (1 - x)) * ((1 +
    x) / (1 - x) * (1 * hpl [zero] x)) * ((1 + x) / (1 - x) * (-hpl [negOne] x)))

/-- `p₄⁽87⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w87 (x : ℝ) : ℝ :=
  i8P4w87k0 x + i8P4w87k1 x + i8P4w87k2 x + i8P4w87k3 x + i8P4w87k4 x

theorem i8P4s87_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s87 x = i8P4w87 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s87 i8P4w87 i8P4w87k0 i8P4w87k1 i8P4w87k2 i8P4w87k3 i8P4w87k4
  simp only [hpl_zero, i13hw_10m hx, i13hw_1m0 hx, i13hw_m01 hx, i13hw_m10 hx, i13hw_010m hx,
    i13hw_01m0 hx, i13hw_0m10 hx, i13hw_100m hx, i13hw_10m0 hx, i13hw_1m00 hx, i13hw_m001 hx,
    i13hw_m010 hx, i13hw_m100 hx, i13_log_one_sub_eq hx]
  field_simp
  generalize hpl [zero, negOne, negOne, negOne, negOne] x = v0 at *
  generalize hpl [zero, negOne, negOne, negOne, one] x = v1 at *
  generalize hpl [zero, negOne, negOne, zero, one] x = v2 at *
  generalize hpl [zero, negOne, negOne, one, negOne] x = v3 at *
  generalize hpl [zero, negOne, negOne, one, one] x = v4 at *
  generalize hpl [zero, negOne, zero, negOne, negOne] x = v5 at *
  generalize hpl [zero, negOne, zero, negOne, one] x = v6 at *
  generalize hpl [zero, negOne, zero, zero, one] x = v7 at *
  generalize hpl [zero, negOne, zero, one, negOne] x = v8 at *
  generalize hpl [zero, negOne, zero, one, zero] x = v9 at *
  generalize hpl [zero, negOne, zero, one, one] x = v10 at *
  generalize hpl [zero, negOne, one, negOne, negOne] x = v11 at *
  generalize hpl [zero, negOne, one, negOne, one] x = v12 at *
  generalize hpl [zero, negOne, one, zero, zero] x = v13 at *
  generalize hpl [zero, negOne, one, zero, one] x = v14 at *
  generalize hpl [zero, negOne, one, one, negOne] x = v15 at *
  generalize hpl [zero, negOne, one, one, one] x = v16 at *
  generalize hpl [zero, zero, negOne, negOne, negOne] x = v17 at *
  generalize hpl [zero, zero, negOne, negOne, one] x = v18 at *
  generalize hpl [zero, zero, negOne, zero, negOne] x = v19 at *
  generalize hpl [zero, zero, negOne, zero, one] x = v20 at *
  generalize hpl [zero, zero, negOne, one, negOne] x = v21 at *
  generalize hpl [zero, zero, negOne, one, zero] x = v22 at *
  generalize hpl [zero, zero, negOne, one, one] x = v23 at *
  generalize hpl [zero, zero, zero, negOne, negOne] x = v24 at *
  generalize hpl [zero, zero, zero, negOne, one] x = v25 at *
  generalize hpl [zero, zero, zero, zero, negOne] x = v26 at *
  generalize hpl [zero, zero, zero, zero, one] x = v27 at *
  generalize hpl [zero, zero, zero, one, negOne] x = v28 at *
  generalize hpl [zero, zero, zero, one, one] x = v29 at *
  generalize hpl [zero, zero, one, negOne, negOne] x = v30 at *
  generalize hpl [zero, zero, one, negOne, zero] x = v31 at *
  generalize hpl [zero, zero, one, negOne, one] x = v32 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v33 at *
  generalize hpl [zero, zero, one, zero, one] x = v34 at *
  generalize hpl [zero, zero, one, one, negOne] x = v35 at *
  generalize hpl [zero, zero, one, one, one] x = v36 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v37 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v38 at *
  generalize hpl [zero, one, negOne, zero, zero] x = v39 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v40 at *
  generalize hpl [zero, one, negOne, one, one] x = v41 at *
  generalize hpl [zero, one, zero, negOne, zero] x = v42 at *
  generalize hpl [zero, one, zero, zero, negOne] x = v43 at *
  generalize hpl [zero, one, zero, one, negOne] x = v44 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v45 at *
  generalize hpl [zero, one, one, negOne, one] x = v46 at *
  generalize hpl [zero, one, one, one, negOne] x = v47 at *
  generalize hpl [zero, one, one, one, one] x = v48 at *
  generalize hpl [negOne, negOne, one, one] x = v49 at *
  generalize hpl [negOne, zero, zero, one] x = v50 at *
  generalize hpl [negOne, zero, one, zero] x = v51 at *
  generalize hpl [negOne, one, zero, zero] x = v52 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v53 at *
  generalize hpl [zero, negOne, negOne, one] x = v54 at *
  generalize hpl [zero, negOne, zero, zero] x = v55 at *
  generalize hpl [zero, negOne, zero, one] x = v56 at *
  generalize hpl [zero, negOne, one, negOne] x = v57 at *
  generalize hpl [zero, negOne, one, zero] x = v58 at *
  generalize hpl [zero, negOne, one, one] x = v59 at *
  generalize hpl [zero, zero, negOne, negOne] x = v60 at *
  generalize hpl [zero, zero, negOne, zero] x = v61 at *
  generalize hpl [zero, zero, negOne, one] x = v62 at *
  generalize hpl [zero, zero, zero, negOne] x = v63 at *
  generalize hpl [zero, zero, zero, one] x = v64 at *
  generalize hpl [zero, zero, one, negOne] x = v65 at *
  generalize hpl [zero, zero, one, zero] x = v66 at *
  generalize hpl [zero, zero, one, one] x = v67 at *
  generalize hpl [zero, one, negOne, negOne] x = v68 at *
  generalize hpl [zero, one, negOne, zero] x = v69 at *
  generalize hpl [zero, one, negOne, one] x = v70 at *
  generalize hpl [zero, one, zero, negOne] x = v71 at *
  generalize hpl [zero, one, zero, zero] x = v72 at *
  generalize hpl [zero, one, one, negOne] x = v73 at *
  generalize hpl [zero, one, one, one] x = v74 at *
  generalize hpl [one, negOne, zero, zero] x = v75 at *
  generalize hpl [one, zero, negOne, zero] x = v76 at *
  generalize hpl [one, zero, zero, negOne] x = v77 at *
  generalize hpl [negOne, negOne, one] x = v78 at *
  generalize hpl [negOne, zero, zero] x = v79 at *
  generalize hpl [negOne, zero, one] x = v80 at *
  generalize hpl [negOne, one, zero] x = v81 at *
  generalize hpl [negOne, one, one] x = v82 at *
  generalize hpl [zero, negOne, negOne] x = v83 at *
  generalize hpl [zero, negOne, zero] x = v84 at *
  generalize hpl [zero, negOne, one] x = v85 at *
  generalize hpl [zero, zero, negOne] x = v86 at *
  generalize hpl [zero, zero, zero] x = v87 at *
  generalize hpl [zero, zero, one] x = v88 at *
  generalize hpl [zero, one, negOne] x = v89 at *
  generalize hpl [zero, one, zero] x = v90 at *
  generalize hpl [zero, one, one] x = v91 at *
  generalize hpl [one, negOne, zero] x = v92 at *
  generalize hpl [one, zero, negOne] x = v93 at *
  generalize hpl [one, zero, zero] x = v94 at *
  generalize hpl [negOne, zero] x = v95 at *
  generalize hpl [negOne, one] x = v96 at *
  generalize hpl [zero, negOne] x = v97 at *
  generalize hpl [zero, zero] x = v98 at *
  generalize hpl [zero, one] x = v99 at *
  generalize hpl [one, negOne] x = v100 at *
  generalize hpl [one, zero] x = v101 at *
  generalize hpl [negOne] x = v102 at *
  generalize hpl [zero] x = v103 at *
  generalize hpl [one] x = v104 at *
  ring

/-- **`(Ψ₄⁽87⁾)'(ξ) ξ' = p₄⁽87⁾`**, in terms of `ξ`. -/
theorem i8Psi4s87D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s87D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s87 x := by
  rw [i8P4s87_eq_w hx]
  unfold i8Psi4s87D i8P4w87
  rw [← i8Psi4s87k0D_mul hx, ← i8Psi4s87k1D_mul hx, ← i8Psi4s87k2D_mul hx, ← i8Psi4s87k3D_mul hx, ←
    i8Psi4s87k4D_mul hx]
  ring

/-- The part of `ξ² Ψ₄⁽88⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s88N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s88N0`. -/
noncomputable def i8Psi4s88dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s88N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s88N0 (i8Psi4s88dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽88⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s88N1 (x : ℝ) : ℝ :=
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) +
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) * hpl [zero] x

/-- The derivative of `i8Psi4s88N1`. -/
noncomputable def i8Psi4s88dN1 (x : ℝ) : ℝ :=
    0 +
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s88N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s88N1 (i8Psi4s88dN1 x) x := by
  unfold i8Psi4s88N1 i8Psi4s88dN1
  exact ((hasDerivAt_const x (16 - 4 * zeta3 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (16 - 4 * zeta3 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽88⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s88N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s88N2`. -/
noncomputable def i8Psi4s88dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s88N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s88N2 (i8Psi4s88dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽88⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s88N3 (x : ℝ) : ℝ :=
    (-16 + 4 * zeta3 + 2 / 3 * π ^ 2) +
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) * hpl [zero] x

/-- The derivative of `i8Psi4s88N3`. -/
noncomputable def i8Psi4s88dN3 (x : ℝ) : ℝ :=
    0 +
    (16 - 4 * zeta3 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s88N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s88N3 (i8Psi4s88dN3 x) x := by
  unfold i8Psi4s88N3 i8Psi4s88dN3
  exact ((hasDerivAt_const x (-16 + 4 * zeta3 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (16 - 4 * zeta3 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽88⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s88N4 (x : ℝ) : ℝ :=
    (4 + zeta3 + π ^ 2 / 6) +
    (-8 - 2 * zeta3 - π ^ 2 / 3) * hpl [zero] x

/-- The derivative of `i8Psi4s88N4`. -/
noncomputable def i8Psi4s88dN4 (x : ℝ) : ℝ :=
    0 +
    (-8 - 2 * zeta3 - π ^ 2 / 3) * (zero.kernel x * hpl [] x)

theorem hasDerivAt_i8Psi4s88N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s88N4 (i8Psi4s88dN4 x) x := by
  unfold i8Psi4s88N4 i8Psi4s88dN4
  exact ((hasDerivAt_const x (4 + zeta3 + π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-8 - 2 * zeta3 - π ^ 2 / 3)))

/-- The part of `Ψ₄⁽88⁾` with constant coefficients. -/
noncomputable def i8Psi4s88W (x : ℝ) : ℝ :=
    (16 + 4 * zeta3 + 2 / 3 * π ^ 2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s88W`. -/
noncomputable def i8Psi4s88dW (x : ℝ) : ℝ :=
    (16 + 4 * zeta3 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s88W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s88W (i8Psi4s88dW x) x := by
  unfold i8Psi4s88W i8Psi4s88dW
  exact ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (16 + 4 * zeta3 + 2 / 3 * π ^ 2))

/-- The piece `Ψ₄⁽88⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s88 (x : ℝ) : ℝ :=
  (i8Psi4s88N0 x + x * i8Psi4s88N1 x + x ^ 2 * i8Psi4s88N2 x + x ^ 3 * i8Psi4s88N3 x +
    x ^ 4 * i8Psi4s88N4 x) / x ^ 2 + i8Psi4s88W x

/-- The derivative of `Ψ₄⁽88⁾`. -/
noncomputable def i8Psi4s88D (x : ℝ) : ℝ :=
  ((i8Psi4s88dN0 x + (i8Psi4s88N1 x + x * i8Psi4s88dN1 x) + (2 * x * i8Psi4s88N2 x +
    x ^ 2 * i8Psi4s88dN2 x) + (3 * x ^ 2 * i8Psi4s88N3 x + x ^ 3 * i8Psi4s88dN3 x) +
    (4 * x ^ 3 * i8Psi4s88N4 x + x ^ 4 * i8Psi4s88dN4 x)) * x ^ 2 - (i8Psi4s88N0 x +
    x * i8Psi4s88N1 x + x ^ 2 * i8Psi4s88N2 x + x ^ 3 * i8Psi4s88N3 x +
    x ^ 4 * i8Psi4s88N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s88dW x

theorem hasDerivAt_i8Psi4s88 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s88 (i8Psi4s88D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s88N0 hx).add (X.mul (hasDerivAt_i8Psi4s88N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s88N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s88N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s88N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s88W hx)
  unfold i8Psi4s88
  refine e.congr_deriv ?_
  unfold i8Psi4s88D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 88 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s88 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 - x) * ((24 + ((-1) * π ^ 2) +
    ((-24) * x) + ((-6) * zeta3) + ((-1) * π ^ 2 * x) + ((-6) * x * zeta3)) / (3 +
    (3 * x)))) * (x / (1 - x))

/-- `p₄⁽88⁾` written over words. -/
noncomputable def i8P4w88 (x : ℝ) : ℝ :=
    (16 - 16 * x - 4 * zeta3 - 2 / 3 * π ^ 2 - 4 * x * zeta3 - 2 / 3 * π ^ 2 * x) * hpl [zero] x

theorem i8P4s88_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s88 x = i8P4w88 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s88 i8P4w88
  simp only [← hpl_zero]
  field_simp
  generalize hpl [zero] x = v0 at *
  ring

/-- **`(Ψ₄⁽88⁾)'(ξ) ξ' = p₄⁽88⁾`**, in terms of `ξ`. -/
theorem i8Psi4s88D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s88D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s88 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s88_eq_w hx]
  unfold i8Psi4s88D i8Psi4s88N0 i8Psi4s88N1 i8Psi4s88N2 i8Psi4s88N3 i8Psi4s88N4 i8Psi4s88dN0
    i8Psi4s88dN1 i8Psi4s88dN2 i8Psi4s88dN3 i8Psi4s88dN4 i8Psi4s88dW i8P4w88
  simp only [kernel_zero, hpl_nil]
  field_simp
  generalize hpl [zero, zero] x = v0 at *
  generalize hpl [zero] x = v1 at *
  ring

/-- The part of `ξ² Ψ₄⁽89⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s89N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s89N0`. -/
noncomputable def i8Psi4s89dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s89N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s89N0 (i8Psi4s89dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽89⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s89N1 (x : ℝ) : ℝ :=
    (16 - 2 / 3 * π ^ 2) +
    (16 - 2 / 3 * π ^ 2) * hpl [zero] x +
    (16 - 2 / 3 * π ^ 2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s89N1`. -/
noncomputable def i8Psi4s89dN1 (x : ℝ) : ℝ :=
    0 +
    (16 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (16 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s89N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s89N1 (i8Psi4s89dN1 x) x := by
  unfold i8Psi4s89N1 i8Psi4s89dN1
  exact (((hasDerivAt_const x (16 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (16 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (16 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽89⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s89N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s89N2`. -/
noncomputable def i8Psi4s89dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s89N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s89N2 (i8Psi4s89dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽89⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s89N3 (x : ℝ) : ℝ :=
    (16 - 2 / 3 * π ^ 2) +
    (-16 + 2 / 3 * π ^ 2) * hpl [zero] x +
    (16 - 2 / 3 * π ^ 2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s89N3`. -/
noncomputable def i8Psi4s89dN3 (x : ℝ) : ℝ :=
    0 +
    (-16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (16 - 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s89N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s89N3 (i8Psi4s89dN3 x) x := by
  unfold i8Psi4s89N3 i8Psi4s89dN3
  exact (((hasDerivAt_const x (16 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-16 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (16 - 2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽89⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s89N4 (x : ℝ) : ℝ :=
    (2 - π ^ 2 / 12) +
    (-4 + π ^ 2 / 6) * hpl [zero] x +
    (8 - π ^ 2 / 3) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s89N4`. -/
noncomputable def i8Psi4s89dN4 (x : ℝ) : ℝ :=
    0 +
    (-4 + π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (8 - π ^ 2 / 3) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s89N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s89N4 (i8Psi4s89dN4 x) x := by
  unfold i8Psi4s89N4 i8Psi4s89dN4
  exact (((hasDerivAt_const x (2 - π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-4 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8 - π ^ 2 / 3)))

/-- The part of `Ψ₄⁽89⁾` with constant coefficients. -/
noncomputable def i8Psi4s89W (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s89W`. -/
noncomputable def i8Psi4s89dW (x : ℝ) : ℝ :=
    (-16 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s89W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s89W (i8Psi4s89dW x) x := by
  unfold i8Psi4s89W i8Psi4s89dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-16 + 2 / 3 * π ^ 2))

/-- The piece `Ψ₄⁽89⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s89 (x : ℝ) : ℝ :=
  (i8Psi4s89N0 x + x * i8Psi4s89N1 x + x ^ 2 * i8Psi4s89N2 x + x ^ 3 * i8Psi4s89N3 x +
    x ^ 4 * i8Psi4s89N4 x) / x ^ 2 + i8Psi4s89W x

/-- The derivative of `Ψ₄⁽89⁾`. -/
noncomputable def i8Psi4s89D (x : ℝ) : ℝ :=
  ((i8Psi4s89dN0 x + (i8Psi4s89N1 x + x * i8Psi4s89dN1 x) + (2 * x * i8Psi4s89N2 x +
    x ^ 2 * i8Psi4s89dN2 x) + (3 * x ^ 2 * i8Psi4s89N3 x + x ^ 3 * i8Psi4s89dN3 x) +
    (4 * x ^ 3 * i8Psi4s89N4 x + x ^ 4 * i8Psi4s89dN4 x)) * x ^ 2 - (i8Psi4s89N0 x +
    x * i8Psi4s89N1 x + x ^ 2 * i8Psi4s89N2 x + x ^ 3 * i8Psi4s89N3 x +
    x ^ 4 * i8Psi4s89N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s89dW x

theorem hasDerivAt_i8Psi4s89 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s89 (i8Psi4s89D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s89N0 hx).add (X.mul (hasDerivAt_i8Psi4s89N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s89N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s89N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s89N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s89W hx)
  unfold i8Psi4s89
  refine e.congr_deriv ?_
  unfold i8Psi4s89D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 89 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s89 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 - x) * (((24 +
    ((-1) * π ^ 2)) / 6) * hpl [zero] x)) * (x / (1 - x))

/-- `p₄⁽89⁾` written over words. -/
noncomputable def i8P4w89 (x : ℝ) : ℝ :=
    (16 + 16 * x - 2 / 3 * π ^ 2 - 2 / 3 * π ^ 2 * x) * hpl [zero, zero] x

theorem i8P4s89_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s89 x = i8P4w89 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s89 i8P4w89
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((8 + 8 * x - π ^ 2 / 3 - π ^ 2 * x / 3)) * e0
  field_simp
  generalize hpl [zero, zero] x = v0 at *
  generalize hpl [zero] x = v1 at *
  ring

/-- **`(Ψ₄⁽89⁾)'(ξ) ξ' = p₄⁽89⁾`**, in terms of `ξ`. -/
theorem i8Psi4s89D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s89D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s89 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s89_eq_w hx]
  unfold i8Psi4s89D i8Psi4s89N0 i8Psi4s89N1 i8Psi4s89N2 i8Psi4s89N3 i8Psi4s89N4 i8Psi4s89dN0
    i8Psi4s89dN1 i8Psi4s89dN2 i8Psi4s89dN3 i8Psi4s89dN4 i8Psi4s89dW i8P4w89
  simp only [kernel_zero, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero] x = v1 at *
  generalize hpl [zero] x = v2 at *
  ring

/-- The part of `ξ² Ψ₄⁽90⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s90N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s90N0`. -/
noncomputable def i8Psi4s90dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s90N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s90N0 (i8Psi4s90dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽90⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s90N1 (x : ℝ) : ℝ :=
    (2 / 3 * π ^ 2) * hpl [negOne] x +
    (2 / 3 * π ^ 2) * hpl [negOne, zero] x +
    (2 / 3 * π ^ 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s90N1`. -/
noncomputable def i8Psi4s90dN1 (x : ℝ) : ℝ :=
    (2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (2 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s90N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s90N1 (i8Psi4s90dN1 x) x := by
  unfold i8Psi4s90N1 i8Psi4s90dN1
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽90⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s90N2 (x : ℝ) : ℝ :=
    (π ^ 2 / 6) * hpl [negOne] x +
    (-2 / 3 * π ^ 2) * hpl [zero] x +
    (π ^ 2) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s90N2`. -/
noncomputable def i8Psi4s90dN2 (x : ℝ) : ℝ :=
    (π ^ 2 / 6) * (negOne.kernel x * hpl [] x) +
    (-2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (π ^ 2) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s90N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s90N2 (i8Psi4s90dN2 x) x := by
  unfold i8Psi4s90N2 i8Psi4s90dN2
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (π ^ 2)))

/-- The part of `ξ² Ψ₄⁽90⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s90N3 (x : ℝ) : ℝ :=
    (5 / 6 * π ^ 2) +
    (-2 / 3 * π ^ 2) * hpl [negOne] x +
    (-π ^ 2 / 3) * hpl [zero] x +
    (2 / 3 * π ^ 2) * hpl [negOne, zero] x +
    (2 / 3 * π ^ 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s90N3`. -/
noncomputable def i8Psi4s90dN3 (x : ℝ) : ℝ :=
    0 +
    (-2 / 3 * π ^ 2) * (negOne.kernel x * hpl [] x) +
    (-π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (2 / 3 * π ^ 2) * (negOne.kernel x * hpl [zero] x) +
    (2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s90N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s90N3 (i8Psi4s90dN3 x) x := by
  unfold i8Psi4s90N3 i8Psi4s90dN3
  exact (((((hasDerivAt_const x (5 / 6 * π ^ 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2 / 3 * π ^ 2)))

/-- The part of `ξ² Ψ₄⁽90⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s90N4 (x : ℝ) : ℝ :=
    (π ^ 2 / 6) +
    (-π ^ 2 / 6) * hpl [negOne] x +
    (-π ^ 2 / 6) * hpl [zero] x +
    (π ^ 2 / 3) * hpl [negOne, zero] x +
    (π ^ 2 / 3) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s90N4`. -/
noncomputable def i8Psi4s90dN4 (x : ℝ) : ℝ :=
    0 +
    (-π ^ 2 / 6) * (negOne.kernel x * hpl [] x) +
    (-π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (π ^ 2 / 3) * (negOne.kernel x * hpl [zero] x) +
    (π ^ 2 / 3) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s90N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s90N4 (i8Psi4s90dN4 x) x := by
  unfold i8Psi4s90N4 i8Psi4s90dN4
  exact (((((hasDerivAt_const x (π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (π ^ 2 / 3)))

/-- The part of `Ψ₄⁽90⁾` with constant coefficients. -/
noncomputable def i8Psi4s90W (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * hpl [zero, zero] x +
    (-2 / 3 * π ^ 2) * hpl [zero, negOne, zero] x +
    (-2 / 3 * π ^ 2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s90W`. -/
noncomputable def i8Psi4s90dW (x : ℝ) : ℝ :=
    (-2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero] x) +
    (-2 / 3 * π ^ 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2 / 3 * π ^ 2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s90W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s90W (i8Psi4s90dW x) x := by
  unfold i8Psi4s90W i8Psi4s90dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-2 / 3 * π ^ 2)))

/-- The piece `Ψ₄⁽90⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s90 (x : ℝ) : ℝ :=
  (i8Psi4s90N0 x + x * i8Psi4s90N1 x + x ^ 2 * i8Psi4s90N2 x + x ^ 3 * i8Psi4s90N3 x +
    x ^ 4 * i8Psi4s90N4 x) / x ^ 2 + i8Psi4s90W x

/-- The derivative of `Ψ₄⁽90⁾`. -/
noncomputable def i8Psi4s90D (x : ℝ) : ℝ :=
  ((i8Psi4s90dN0 x + (i8Psi4s90N1 x + x * i8Psi4s90dN1 x) + (2 * x * i8Psi4s90N2 x +
    x ^ 2 * i8Psi4s90dN2 x) + (3 * x ^ 2 * i8Psi4s90N3 x + x ^ 3 * i8Psi4s90dN3 x) +
    (4 * x ^ 3 * i8Psi4s90N4 x + x ^ 4 * i8Psi4s90dN4 x)) * x ^ 2 - (i8Psi4s90N0 x +
    x * i8Psi4s90N1 x + x ^ 2 * i8Psi4s90N2 x + x ^ 3 * i8Psi4s90N3 x +
    x ^ 4 * i8Psi4s90N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s90dW x

theorem hasDerivAt_i8Psi4s90 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s90 (i8Psi4s90D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s90N0 hx).add (X.mul (hasDerivAt_i8Psi4s90N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s90N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s90N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s90N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s90W hx)
  unfold i8Psi4s90
  refine e.congr_deriv ?_
  unfold i8Psi4s90D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 90 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s90 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 -
    x) * ((π ^ 2 / 3) * hpl [negOne] x)) * (x / (1 - x))

/-- `p₄⁽90⁾` written over words. -/
noncomputable def i8P4w90 (x : ℝ) : ℝ :=
    (2 / 3 * π ^ 2 + 2 / 3 * π ^ 2 * x) * hpl [negOne, zero] x +
    (2 / 3 * π ^ 2 + 2 / 3 * π ^ 2 * x) * hpl [zero, negOne] x

theorem i8P4s90_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s90 x = i8P4w90 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s90 i8P4w90
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [negOne] [zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((2 / 3 * π ^ 2 + 2 / 3 * π ^ 2 * x)) * e0
  field_simp
  generalize hpl [negOne, zero] x = v0 at *
  generalize hpl [zero, negOne] x = v1 at *
  generalize hpl [negOne] x = v2 at *
  generalize hpl [zero] x = v3 at *
  ring

/-- **`(Ψ₄⁽90⁾)'(ξ) ξ' = p₄⁽90⁾`**, in terms of `ξ`. -/
theorem i8Psi4s90D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s90D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s90 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s90_eq_w hx]
  unfold i8Psi4s90D i8Psi4s90N0 i8Psi4s90N1 i8Psi4s90N2 i8Psi4s90N3 i8Psi4s90N4 i8Psi4s90dN0
    i8Psi4s90dN1 i8Psi4s90dN2 i8Psi4s90dN3 i8Psi4s90dN4 i8Psi4s90dW i8P4w90
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, zero] x = v0 at *
  generalize hpl [zero, zero, negOne] x = v1 at *
  generalize hpl [negOne, zero] x = v2 at *
  generalize hpl [zero, negOne] x = v3 at *
  generalize hpl [zero, zero] x = v4 at *
  generalize hpl [negOne] x = v5 at *
  generalize hpl [zero] x = v6 at *
  ring

/-- The part of `ξ² Ψ₄⁽91⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s91N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s91N0`. -/
noncomputable def i8Psi4s91dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s91N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s91N0 (i8Psi4s91dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽91⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s91N1 (x : ℝ) : ℝ :=
    (-8) * hpl [negOne, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s91N1`. -/
noncomputable def i8Psi4s91dN1 (x : ℝ) : ℝ :=
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s91N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s91N1 (i8Psi4s91dN1 x) x := by
  unfold i8Psi4s91N1 i8Psi4s91dN1
  exact ((((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽91⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s91N2 (x : ℝ) : ℝ :=
    (-15) * hpl [negOne, zero] x +
    (8) * hpl [zero, zero] x +
    (-2) * hpl [negOne, zero, zero] x

/-- The derivative of `i8Psi4s91N2`. -/
noncomputable def i8Psi4s91dN2 (x : ℝ) : ℝ :=
    (-15) * (negOne.kernel x * hpl [zero] x) +
    (8) * (zero.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s91N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s91N2 (i8Psi4s91dN2 x) x := by
  unfold i8Psi4s91N2 i8Psi4s91dN2
  exact ((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-15)).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-2)))

/-- The part of `ξ² Ψ₄⁽91⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s91N3 (x : ℝ) : ℝ :=
    (-13) +
    (13) * hpl [zero] x +
    (-8) * hpl [negOne, zero] x +
    (-6) * hpl [zero, zero] x +
    (8) * hpl [negOne, zero, zero] x +
    (8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s91N3`. -/
noncomputable def i8Psi4s91dN3 (x : ℝ) : ℝ :=
    0 +
    (13) * (zero.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (-6) * (zero.kernel x * hpl [zero] x) +
    (8) * (negOne.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s91N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s91N3 (i8Psi4s91dN3 x) x := by
  unfold i8Psi4s91N3 i8Psi4s91dN3
  exact ((((((((hasDerivAt_const x (-13)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (13))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽91⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s91N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (1) * hpl [zero] x +
    (-1) * hpl [negOne, zero] x +
    (-1) * hpl [zero, zero] x +
    (2) * hpl [negOne, zero, zero] x +
    (2) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, negOne, zero, zero] x +
    (-4) * hpl [zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s91N4`. -/
noncomputable def i8Psi4s91dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [zero] x) +
    (2) * (negOne.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s91N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s91N4 (i8Psi4s91dN4 x) x := by
  unfold i8Psi4s91N4 i8Psi4s91dN4
  exact ((((((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽91⁾` with constant coefficients. -/
noncomputable def i8Psi4s91W (x : ℝ) : ℝ :=
    (8) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, zero, negOne, zero, zero] x +
    (8) * hpl [zero, zero, zero, negOne, zero] x

/-- The derivative of `i8Psi4s91W`. -/
noncomputable def i8Psi4s91dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, negOne, zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s91W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s91W (i8Psi4s91dW x) x := by
  unfold i8Psi4s91W i8Psi4s91dW
  exact ((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (8)))

/-- The piece `Ψ₄⁽91⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s91 (x : ℝ) : ℝ :=
  (i8Psi4s91N0 x + x * i8Psi4s91N1 x + x ^ 2 * i8Psi4s91N2 x + x ^ 3 * i8Psi4s91N3 x +
    x ^ 4 * i8Psi4s91N4 x) / x ^ 2 + i8Psi4s91W x

/-- The derivative of `Ψ₄⁽91⁾`. -/
noncomputable def i8Psi4s91D (x : ℝ) : ℝ :=
  ((i8Psi4s91dN0 x + (i8Psi4s91N1 x + x * i8Psi4s91dN1 x) + (2 * x * i8Psi4s91N2 x +
    x ^ 2 * i8Psi4s91dN2 x) + (3 * x ^ 2 * i8Psi4s91N3 x + x ^ 3 * i8Psi4s91dN3 x) +
    (4 * x ^ 3 * i8Psi4s91N4 x + x ^ 4 * i8Psi4s91dN4 x)) * x ^ 2 - (i8Psi4s91N0 x +
    x * i8Psi4s91N1 x + x ^ 2 * i8Psi4s91N2 x + x ^ 3 * i8Psi4s91N3 x +
    x ^ 4 * i8Psi4s91N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s91dW x

theorem hasDerivAt_i8Psi4s91 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s91 (i8Psi4s91D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s91N0 hx).add (X.mul (hasDerivAt_i8Psi4s91N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s91N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s91N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s91N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s91W hx)
  unfold i8Psi4s91
  refine e.congr_deriv ?_
  unfold i8Psi4s91D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 91 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s91 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 -
    x) * ((-2) * hpl [zero, negOne, zero] x)) * (x / (1 - x))

/-- `p₄⁽91⁾` written over words. -/
noncomputable def i8P4w91 (x : ℝ) : ℝ :=
    (-8 - 8 * x) * hpl [zero, negOne, zero, zero] x +
    (-8 - 8 * x) * hpl [zero, zero, negOne, zero] x

theorem i8P4s91_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s91 x = i8P4w91 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s91 i8P4w91
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero, negOne, zero] [zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((-4 - 4 * x)) * e0
  field_simp
  generalize hpl [zero, negOne, zero, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, zero] x = v1 at *
  generalize hpl [zero, negOne, zero] x = v2 at *
  generalize hpl [zero] x = v3 at *
  ring

/-- **`(Ψ₄⁽91⁾)'(ξ) ξ' = p₄⁽91⁾`**, in terms of `ξ`. -/
theorem i8Psi4s91D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s91D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s91 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s91_eq_w hx]
  unfold i8Psi4s91D i8Psi4s91N0 i8Psi4s91N1 i8Psi4s91N2 i8Psi4s91N3 i8Psi4s91N4 i8Psi4s91dN0
    i8Psi4s91dN1 i8Psi4s91dN2 i8Psi4s91dN3 i8Psi4s91dN4 i8Psi4s91dW i8P4w91
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, zero, negOne, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero, negOne, zero] x = v1 at *
  generalize hpl [zero, negOne, zero, zero] x = v2 at *
  generalize hpl [zero, zero, negOne, zero] x = v3 at *
  generalize hpl [negOne, zero, zero] x = v4 at *
  generalize hpl [zero, negOne, zero] x = v5 at *
  generalize hpl [zero, zero, zero] x = v6 at *
  generalize hpl [negOne, zero] x = v7 at *
  generalize hpl [zero, zero] x = v8 at *
  generalize hpl [zero] x = v9 at *
  ring

/-- The part of `ξ² Ψ₄⁽92⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s92N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s92N0`. -/
noncomputable def i8Psi4s92dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s92N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s92N0 (i8Psi4s92dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽92⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s92N1 (x : ℝ) : ℝ :=
    (8) * hpl [negOne, negOne, zero] x +
    (16) * hpl [negOne, negOne, zero, zero] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (8) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s92N1`. -/
noncomputable def i8Psi4s92dN1 (x : ℝ) : ℝ :=
    (8) * (negOne.kernel x * hpl [negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s92N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s92N1 (i8Psi4s92dN1 x) x := by
  unfold i8Psi4s92N1 i8Psi4s92dN1
  exact (((((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽92⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s92N2 (x : ℝ) : ℝ :=
    (8) * hpl [negOne, zero] x +
    (2) * hpl [negOne, negOne, zero] x +
    (-4) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (24) * hpl [negOne, negOne, zero, zero] x +
    (12) * hpl [negOne, zero, negOne, zero] x

/-- The derivative of `i8Psi4s92N2`. -/
noncomputable def i8Psi4s92dN2 (x : ℝ) : ℝ :=
    (8) * (negOne.kernel x * hpl [zero] x) +
    (2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (24) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (12) * (negOne.kernel x * hpl [zero, negOne, zero] x)

theorem hasDerivAt_i8Psi4s92N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s92N2 (i8Psi4s92dN2 x) x := by
  unfold i8Psi4s92N2 i8Psi4s92dN2
  exact (((((((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽92⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s92N3 (x : ℝ) : ℝ :=
    (12) +
    (-12) * hpl [zero] x +
    (10) * hpl [negOne, zero] x +
    (4) * hpl [zero, zero] x +
    (-8) * hpl [negOne, negOne, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (16) * hpl [negOne, negOne, zero, zero] x +
    (8) * hpl [negOne, zero, negOne, zero] x +
    (8) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s92N3`. -/
noncomputable def i8Psi4s92dN3 (x : ℝ) : ℝ :=
    0 +
    (-12) * (zero.kernel x * hpl [] x) +
    (10) * (negOne.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (16) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s92N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s92N3 (i8Psi4s92dN3 x) x := by
  unfold i8Psi4s92N3 i8Psi4s92dN3
  exact ((((((((((hasDerivAt_const x (12)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽92⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s92N4 (x : ℝ) : ℝ :=
    (1) +
    (-2) * hpl [zero] x +
    (2) * hpl [negOne, zero] x +
    (2) * hpl [zero, zero] x +
    (-2) * hpl [negOne, negOne, zero] x +
    (-4) * hpl [negOne, zero, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (8) * hpl [negOne, negOne, zero, zero] x +
    (4) * hpl [negOne, zero, negOne, zero] x +
    (4) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s92N4`. -/
noncomputable def i8Psi4s92dN4 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x) +
    (2) * (negOne.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (8) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (4) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s92N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s92N4 (i8Psi4s92dN4 x) x := by
  unfold i8Psi4s92N4 i8Psi4s92dN4
  exact ((((((((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽92⁾` with constant coefficients. -/
noncomputable def i8Psi4s92W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, negOne, zero, zero] x +
    (-8) * hpl [zero, zero, negOne, zero] x +
    (-16) * hpl [zero, negOne, negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s92W`. -/
noncomputable def i8Psi4s92dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, negOne, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero, negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s92W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s92W (i8Psi4s92dW x) x := by
  unfold i8Psi4s92W i8Psi4s92dW
  exact ((((((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne, zero] hx).const_mul (-8)))

/-- The piece `Ψ₄⁽92⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s92 (x : ℝ) : ℝ :=
  (i8Psi4s92N0 x + x * i8Psi4s92N1 x + x ^ 2 * i8Psi4s92N2 x + x ^ 3 * i8Psi4s92N3 x +
    x ^ 4 * i8Psi4s92N4 x) / x ^ 2 + i8Psi4s92W x

/-- The derivative of `Ψ₄⁽92⁾`. -/
noncomputable def i8Psi4s92D (x : ℝ) : ℝ :=
  ((i8Psi4s92dN0 x + (i8Psi4s92N1 x + x * i8Psi4s92dN1 x) + (2 * x * i8Psi4s92N2 x +
    x ^ 2 * i8Psi4s92dN2 x) + (3 * x ^ 2 * i8Psi4s92N3 x + x ^ 3 * i8Psi4s92dN3 x) +
    (4 * x ^ 3 * i8Psi4s92N4 x + x ^ 4 * i8Psi4s92dN4 x)) * x ^ 2 - (i8Psi4s92N0 x +
    x * i8Psi4s92N1 x + x ^ 2 * i8Psi4s92N2 x + x ^ 3 * i8Psi4s92N3 x +
    x ^ 4 * i8Psi4s92N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s92dW x

theorem hasDerivAt_i8Psi4s92 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s92 (i8Psi4s92D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s92N0 hx).add (X.mul (hasDerivAt_i8Psi4s92N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s92N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s92N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s92N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s92W hx)
  unfold i8Psi4s92
  refine e.congr_deriv ?_
  unfold i8Psi4s92D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 92 of `p₄` in `ξ`: from `t B3 A0 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s92 (x : ℝ) : ℝ :=
  2 * (1 - x) ^ 2 / x * Real.log x * ((1 + x) / (1 -
    x) * (4 * hpl [negOne, negOne, zero] x)) * (x / (1 - x))

/-- `p₄⁽92⁾` written over words. -/
noncomputable def i8P4w92 (x : ℝ) : ℝ :=
    (16 + 16 * x) * hpl [negOne, negOne, zero, zero] x +
    (8 + 8 * x) * hpl [negOne, zero, negOne, zero] x +
    (8 + 8 * x) * hpl [zero, negOne, negOne, zero] x

theorem i8P4s92_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s92 x = i8P4w92 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s92 i8P4w92
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [negOne, negOne, zero] [zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((8 + 8 * x)) * e0
  field_simp
  generalize hpl [negOne, negOne, zero, zero] x = v0 at *
  generalize hpl [negOne, zero, negOne, zero] x = v1 at *
  generalize hpl [zero, negOne, negOne, zero] x = v2 at *
  generalize hpl [negOne, negOne, zero] x = v3 at *
  generalize hpl [zero] x = v4 at *
  ring

/-- **`(Ψ₄⁽92⁾)'(ξ) ξ' = p₄⁽92⁾`**, in terms of `ξ`. -/
theorem i8Psi4s92D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s92D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s92 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s92_eq_w hx]
  unfold i8Psi4s92D i8Psi4s92N0 i8Psi4s92N1 i8Psi4s92N2 i8Psi4s92N3 i8Psi4s92N4 i8Psi4s92dN0
    i8Psi4s92dN1 i8Psi4s92dN2 i8Psi4s92dN3 i8Psi4s92dN4 i8Psi4s92dW i8P4w92
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, negOne, zero, zero] x = v0 at *
  generalize hpl [zero, negOne, zero, negOne, zero] x = v1 at *
  generalize hpl [zero, zero, negOne, negOne, zero] x = v2 at *
  generalize hpl [negOne, negOne, zero, zero] x = v3 at *
  generalize hpl [negOne, zero, negOne, zero] x = v4 at *
  generalize hpl [zero, negOne, negOne, zero] x = v5 at *
  generalize hpl [zero, negOne, zero, zero] x = v6 at *
  generalize hpl [zero, zero, negOne, zero] x = v7 at *
  generalize hpl [negOne, negOne, zero] x = v8 at *
  generalize hpl [negOne, zero, zero] x = v9 at *
  generalize hpl [zero, negOne, zero] x = v10 at *
  generalize hpl [negOne, zero] x = v11 at *
  generalize hpl [zero, zero] x = v12 at *
  generalize hpl [zero] x = v13 at *
  ring

end QED.ThreeLoopD
