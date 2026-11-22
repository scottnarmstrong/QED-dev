/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P29

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 113 to 114

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s113`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s113D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s113`, `QED.ThreeLoopD.i8Psi4s113D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽113⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s113N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s113N0`. -/
noncomputable def i8Psi4s113dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s113N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s113N0 (i8Psi4s113dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽113⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s113N1 (x : ℝ) : ℝ :=
    (4) * hpl [one] x +
    (4) * hpl [zero, one] x +
    (4) * hpl [one, zero] x

/-- The derivative of `i8Psi4s113N1`. -/
noncomputable def i8Psi4s113dN1 (x : ℝ) : ℝ :=
    (4) * (one.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s113N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s113N1 (i8Psi4s113dN1 x) x := by
  unfold i8Psi4s113N1 i8Psi4s113dN1
  exact ((((hasDerivAt_hpl_cons one [] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽113⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s113N2 (x : ℝ) : ℝ :=
    (-4) * hpl [zero] x +
    (-1) * hpl [one] x +
    (-6) * hpl [one, zero] x

/-- The derivative of `i8Psi4s113N2`. -/
noncomputable def i8Psi4s113dN2 (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [] x) +
    (-1) * (one.kernel x * hpl [] x) +
    (-6) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s113N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s113N2 (i8Psi4s113dN2 x) x := by
  unfold i8Psi4s113N2 i8Psi4s113dN2
  exact ((((hasDerivAt_hpl_cons zero [] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-6)))

/-- The part of `ξ² Ψ₄⁽113⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s113N3 (x : ℝ) : ℝ :=
    (-5) +
    (2) * hpl [zero] x +
    (-4) * hpl [one] x +
    (4) * hpl [zero, one] x +
    (4) * hpl [one, zero] x

/-- The derivative of `i8Psi4s113N3`. -/
noncomputable def i8Psi4s113dN3 (x : ℝ) : ℝ :=
    0 +
    (2) * (zero.kernel x * hpl [] x) +
    (-4) * (one.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s113N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s113N3 (i8Psi4s113dN3 x) x := by
  unfold i8Psi4s113N3 i8Psi4s113dN3
  exact (((((hasDerivAt_const x (-5)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽113⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s113N4 (x : ℝ) : ℝ :=
    (1) +
    (-1) * hpl [zero] x +
    (1) * hpl [one] x +
    (-2) * hpl [zero, one] x +
    (-2) * hpl [one, zero] x

/-- The derivative of `i8Psi4s113N4`. -/
noncomputable def i8Psi4s113dN4 (x : ℝ) : ℝ :=
    0 +
    (-1) * (zero.kernel x * hpl [] x) +
    (1) * (one.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s113N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s113N4 (i8Psi4s113dN4 x) x := by
  unfold i8Psi4s113N4 i8Psi4s113dN4
  exact (((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽113⁾` with constant coefficients. -/
noncomputable def i8Psi4s113W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s113W`. -/
noncomputable def i8Psi4s113dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s113W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s113W (i8Psi4s113dW x) x := by
  unfold i8Psi4s113W i8Psi4s113dW
  exact ((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4)))

/-- The piece `Ψ₄⁽113⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s113 (x : ℝ) : ℝ :=
  (i8Psi4s113N0 x + x * i8Psi4s113N1 x + x ^ 2 * i8Psi4s113N2 x + x ^ 3 * i8Psi4s113N3 x +
    x ^ 4 * i8Psi4s113N4 x) / x ^ 2 + i8Psi4s113W x

/-- The derivative of `Ψ₄⁽113⁾`. -/
noncomputable def i8Psi4s113D (x : ℝ) : ℝ :=
  ((i8Psi4s113dN0 x + (i8Psi4s113N1 x + x * i8Psi4s113dN1 x) + (2 * x * i8Psi4s113N2 x +
    x ^ 2 * i8Psi4s113dN2 x) + (3 * x ^ 2 * i8Psi4s113N3 x + x ^ 3 * i8Psi4s113dN3 x) +
    (4 * x ^ 3 * i8Psi4s113N4 x + x ^ 4 * i8Psi4s113dN4 x)) * x ^ 2 - (i8Psi4s113N0 x +
    x * i8Psi4s113N1 x + x ^ 2 * i8Psi4s113N2 x + x ^ 3 * i8Psi4s113N3 x +
    x ^ 4 * i8Psi4s113N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s113dW x

theorem hasDerivAt_i8Psi4s113 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s113 (i8Psi4s113D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s113N0 hx).add (X.mul (hasDerivAt_i8Psi4s113N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s113N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s113N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s113N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s113W hx)
  unfold i8Psi4s113
  refine e.congr_deriv ?_
  unfold i8Psi4s113D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 113 of `p₄` in `ξ`: from `t B0 A2 (-λ)^2/2!`, the term with `log^1 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s113 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * Real.log x * ((1 + x) / (1 - x) * (2 * x / (1 + x))))

/-- `p₄⁽113⁾` written over words. -/
noncomputable def i8P4w113 (x : ℝ) : ℝ :=
    (4 - 4 * x) * hpl [zero, one] x +
    (4 - 4 * x) * hpl [one, zero] x

theorem i8P4s113_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s113 x = i8P4w113 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s113 i8P4w113
  rw [i13_log_one_sub_eq hx]
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((4 - 4 * x)) * e0
  field_simp
  generalize hpl [zero, one] x = v0 at *
  generalize hpl [one, zero] x = v1 at *
  generalize hpl [zero] x = v2 at *
  generalize hpl [one] x = v3 at *
  ring

/-- **`(Ψ₄⁽113⁾)'(ξ) ξ' = p₄⁽113⁾`**, in terms of `ξ`. -/
theorem i8Psi4s113D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s113D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s113 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s113_eq_w hx]
  unfold i8Psi4s113D i8Psi4s113N0 i8Psi4s113N1 i8Psi4s113N2 i8Psi4s113N3 i8Psi4s113N4 i8Psi4s113dN0
    i8Psi4s113dN1 i8Psi4s113dN2 i8Psi4s113dN3 i8Psi4s113dN4 i8Psi4s113dW i8P4w113
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

/-- The part of `ξ² Ψ₄⁽114⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s114k0N0 (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [negOne, one] x +
    (-1 / 2) * hpl [one, negOne] x +
    (-1) * hpl [negOne, zero, one] x +
    (-1) * hpl [negOne, one, zero] x +
    (-1) * hpl [zero, negOne, one] x +
    (-1) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi4s114k0N0`. -/
noncomputable def i8Psi4s114k0dN0 (x : ℝ) : ℝ :=
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero, one] x) +
    (-1) * (negOne.kernel x * hpl [one, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, one] x) +
    (-1) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s114k0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k0N0 (i8Psi4s114k0dN0 x) x := by
  unfold i8Psi4s114k0N0 i8Psi4s114k0dN0
  exact (((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽114⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s114k0N1 (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [negOne] x +
    (-3 / 2) * hpl [one] x +
    (-1) * hpl [zero, one] x +
    (-1) * hpl [one, zero] x

/-- The derivative of `i8Psi4s114k0N1`. -/
noncomputable def i8Psi4s114k0dN1 (x : ℝ) : ℝ :=
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (-3 / 2) * (one.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s114k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k0N1 (i8Psi4s114k0dN1 x) x := by
  unfold i8Psi4s114k0N1 i8Psi4s114k0dN1
  exact (((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽114⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s114k0N2 (x : ℝ) : ℝ :=
    (-3 / 4) * hpl [negOne] x +
    (2) * hpl [zero] x +
    (5 / 2) * hpl [one] x +
    (1) * hpl [negOne, one] x +
    (-1 / 2) * hpl [zero, one] x +
    (1) * hpl [one, negOne] x +
    (1 / 2) * hpl [one, zero] x

/-- The derivative of `i8Psi4s114k0N2`. -/
noncomputable def i8Psi4s114k0dN2 (x : ℝ) : ℝ :=
    (-3 / 4) * (negOne.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [] x) +
    (5 / 2) * (one.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (-1 / 2) * (zero.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (1 / 2) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s114k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k0N2 (i8Psi4s114k0dN2 x) x := by
  unfold i8Psi4s114k0N2 i8Psi4s114k0dN2
  exact ((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽114⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s114k0N3 (x : ℝ) : ℝ :=
    (-5 / 4) +
    (-1 / 2) * hpl [negOne] x +
    (1 / 2) * hpl [zero] x +
    (-3 / 2) * hpl [one] x +
    (1) * hpl [zero, one] x +
    (1) * hpl [one, zero] x

/-- The derivative of `i8Psi4s114k0N3`. -/
noncomputable def i8Psi4s114k0dN3 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-3 / 2) * (one.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s114k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k0N3 (i8Psi4s114k0dN3 x) x := by
  unfold i8Psi4s114k0N3 i8Psi4s114k0dN3
  exact ((((((hasDerivAt_const x (-5 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽114⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s114k0N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1 / 4) * hpl [negOne] x +
    (-1 / 4) * hpl [zero] x +
    (1 / 2) * hpl [one] x +
    (-1 / 2) * hpl [negOne, one] x +
    (-1 / 2) * hpl [zero, one] x +
    (-1 / 2) * hpl [one, negOne] x +
    (-1 / 2) * hpl [one, zero] x +
    (1) * hpl [negOne, zero, one] x +
    (1) * hpl [negOne, one, zero] x +
    (1) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, negOne] x

/-- The derivative of `i8Psi4s114k0N4`. -/
noncomputable def i8Psi4s114k0dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 4) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (one.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [one] x) +
    (-1 / 2) * (zero.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [negOne] x) +
    (-1 / 2) * (one.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [zero, one] x) +
    (1) * (negOne.kernel x * hpl [one, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, one] x) +
    (1) * (zero.kernel x * hpl [one, negOne] x)

theorem hasDerivAt_i8Psi4s114k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k0N4 (i8Psi4s114k0dN4 x) x := by
  unfold i8Psi4s114k0N4 i8Psi4s114k0dN4
  exact ((((((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (1)))

/-- The part of `Ψ₄⁽114⁾` with constant coefficients. -/
noncomputable def i8Psi4s114k0W (x : ℝ) : ℝ :=
    (1 / 2) * hpl [zero, negOne] x +
    (1) * hpl [zero, zero] x +
    (-1) * hpl [zero, zero, one] x +
    (-1) * hpl [zero, one, zero] x +
    (-4) * hpl [zero, negOne, zero, one] x +
    (-4) * hpl [zero, negOne, one, zero] x +
    (-4) * hpl [zero, zero, negOne, one] x +
    (-4) * hpl [zero, zero, one, negOne] x

/-- The derivative of `i8Psi4s114k0W`. -/
noncomputable def i8Psi4s114k0dW (x : ℝ) : ℝ :=
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [zero, one] x) +
    (-1) * (zero.kernel x * hpl [one, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (-4) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne, one] x) +
    (-4) * (zero.kernel x * hpl [zero, one, negOne] x)

theorem hasDerivAt_i8Psi4s114k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k0W (i8Psi4s114k0dW x) x := by
  unfold i8Psi4s114k0W i8Psi4s114k0dW
  exact (((((((((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2)).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, negOne] hx).const_mul (-4)))

/-- Chunk 0 of the piece `Ψ₄⁽114⁾`. -/
noncomputable def i8Psi4s114k0 (x : ℝ) : ℝ :=
  (i8Psi4s114k0N0 x + x * i8Psi4s114k0N1 x + x ^ 2 * i8Psi4s114k0N2 x + x ^ 3 * i8Psi4s114k0N3 x +
    x ^ 4 * i8Psi4s114k0N4 x) / x ^ 2 + i8Psi4s114k0W x

/-- The derivative of `i8Psi4s114k0`. -/
noncomputable def i8Psi4s114k0D (x : ℝ) : ℝ :=
  ((i8Psi4s114k0dN0 x + (i8Psi4s114k0N1 x + x * i8Psi4s114k0dN1 x) + (2 * x * i8Psi4s114k0N2 x +
    x ^ 2 * i8Psi4s114k0dN2 x) + (3 * x ^ 2 * i8Psi4s114k0N3 x + x ^ 3 * i8Psi4s114k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s114k0N4 x + x ^ 4 * i8Psi4s114k0dN4 x)) * x ^ 2 - (i8Psi4s114k0N0 x +
    x * i8Psi4s114k0N1 x + x ^ 2 * i8Psi4s114k0N2 x + x ^ 3 * i8Psi4s114k0N3 x +
    x ^ 4 * i8Psi4s114k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s114k0dW x

theorem hasDerivAt_i8Psi4s114k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k0 (i8Psi4s114k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s114k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s114k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s114k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s114k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s114k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s114k0W hx)
  unfold i8Psi4s114k0
  refine e.congr_deriv ?_
  unfold i8Psi4s114k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽114⁾` over words. -/
noncomputable def i8P4w114k0 (x : ℝ) : ℝ :=
    ((-2 + 2 * x ^ 2) / (x)) * hpl [negOne, zero, one] x +
    ((-2 + 2 * x ^ 2) / (x)) * hpl [negOne, one, zero] x +
    ((-2 + 2 * x ^ 2) / (x)) * hpl [zero, negOne, one] x +
    ((-2 + 2 * x ^ 2) / (x)) * hpl [zero, one, negOne] x

theorem i8Psi4s114k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s114k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w114k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s114k0D i8Psi4s114k0N0 i8Psi4s114k0N1 i8Psi4s114k0N2 i8Psi4s114k0N3 i8Psi4s114k0N4
    i8Psi4s114k0dN0 i8Psi4s114k0dN1 i8Psi4s114k0dN2 i8Psi4s114k0dN3 i8Psi4s114k0dN4 i8Psi4s114k0dW
    i8P4w114k0
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, zero, one] x = v0 at *
  generalize hpl [zero, negOne, one, zero] x = v1 at *
  generalize hpl [zero, zero, negOne, one] x = v2 at *
  generalize hpl [zero, zero, one, negOne] x = v3 at *
  generalize hpl [negOne, zero, one] x = v4 at *
  generalize hpl [negOne, one, zero] x = v5 at *
  generalize hpl [zero, negOne, one] x = v6 at *
  generalize hpl [zero, zero, one] x = v7 at *
  generalize hpl [zero, one, negOne] x = v8 at *
  generalize hpl [zero, one, zero] x = v9 at *
  generalize hpl [negOne, one] x = v10 at *
  generalize hpl [zero, negOne] x = v11 at *
  generalize hpl [zero, zero] x = v12 at *
  generalize hpl [zero, one] x = v13 at *
  generalize hpl [one, negOne] x = v14 at *
  generalize hpl [one, zero] x = v15 at *
  generalize hpl [negOne] x = v16 at *
  generalize hpl [zero] x = v17 at *
  generalize hpl [one] x = v18 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽114⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s114k1N0 (x : ℝ) : ℝ :=
    (-1) * hpl [one, negOne, zero] x +
    (-1) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s114k1N0`. -/
noncomputable def i8Psi4s114k1dN0 (x : ℝ) : ℝ :=
    (-1) * (one.kernel x * hpl [negOne, zero] x) +
    (-1) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s114k1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k1N0 (i8Psi4s114k1dN0 x) x := by
  unfold i8Psi4s114k1N0 i8Psi4s114k1dN0
  exact (((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽114⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s114k1N1 (x : ℝ) : ℝ :=
    (-1) * hpl [negOne] x +
    (-1) * hpl [negOne, zero] x +
    (-1) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s114k1N1`. -/
noncomputable def i8Psi4s114k1dN1 (x : ℝ) : ℝ :=
    (-1) * (negOne.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s114k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k1N1 (i8Psi4s114k1dN1 x) x := by
  unfold i8Psi4s114k1N1 i8Psi4s114k1dN1
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽114⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s114k1N2 (x : ℝ) : ℝ :=
    (-7 / 4) * hpl [negOne] x +
    (1) * hpl [zero] x +
    (-1 / 2) * hpl [negOne, zero] x

/-- The derivative of `i8Psi4s114k1N2`. -/
noncomputable def i8Psi4s114k1dN2 (x : ℝ) : ℝ :=
    (-7 / 4) * (negOne.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s114k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k1N2 (i8Psi4s114k1dN2 x) x := by
  unfold i8Psi4s114k1N2 i8Psi4s114k1dN2
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-7 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 2)))

/-- The part of `ξ² Ψ₄⁽114⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s114k1N3 (x : ℝ) : ℝ :=
    (5 / 4) +
    (-1) * hpl [negOne] x +
    (-1 / 2) * hpl [zero] x +
    (1) * hpl [negOne, zero] x +
    (1) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s114k1N3`. -/
noncomputable def i8Psi4s114k1dN3 (x : ℝ) : ℝ :=
    0 +
    (-1) * (negOne.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s114k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k1N3 (i8Psi4s114k1dN3 x) x := by
  unfold i8Psi4s114k1N3 i8Psi4s114k1dN3
  exact (((((hasDerivAt_const x (5 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽114⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s114k1N4 (x : ℝ) : ℝ :=
    (1 / 4) +
    (-1 / 4) * hpl [negOne] x +
    (-1 / 4) * hpl [zero] x +
    (1 / 2) * hpl [negOne, zero] x +
    (1 / 2) * hpl [zero, negOne] x +
    (1) * hpl [one, negOne, zero] x +
    (1) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s114k1N4`. -/
noncomputable def i8Psi4s114k1dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 4) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x) +
    (1) * (one.kernel x * hpl [negOne, zero] x) +
    (1) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s114k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k1N4 (i8Psi4s114k1dN4 x) x := by
  unfold i8Psi4s114k1N4 i8Psi4s114k1dN4
  exact (((((((hasDerivAt_const x (1 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (1)))

/-- The part of `Ψ₄⁽114⁾` with constant coefficients. -/
noncomputable def i8Psi4s114k1W (x : ℝ) : ℝ :=
    (1) * hpl [zero, zero] x +
    (1) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, negOne] x +
    (-4) * hpl [zero, one, negOne, zero] x +
    (-4) * hpl [zero, one, zero, negOne] x

/-- The derivative of `i8Psi4s114k1W`. -/
noncomputable def i8Psi4s114k1dW (x : ℝ) : ℝ :=
    (1) * (zero.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x) +
    (-4) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [one, zero, negOne] x)

theorem hasDerivAt_i8Psi4s114k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k1W (i8Psi4s114k1dW x) x := by
  unfold i8Psi4s114k1W i8Psi4s114k1dW
  exact ((((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, negOne] hx).const_mul (-4)))

/-- Chunk 1 of the piece `Ψ₄⁽114⁾`. -/
noncomputable def i8Psi4s114k1 (x : ℝ) : ℝ :=
  (i8Psi4s114k1N0 x + x * i8Psi4s114k1N1 x + x ^ 2 * i8Psi4s114k1N2 x + x ^ 3 * i8Psi4s114k1N3 x +
    x ^ 4 * i8Psi4s114k1N4 x) / x ^ 2 + i8Psi4s114k1W x

/-- The derivative of `i8Psi4s114k1`. -/
noncomputable def i8Psi4s114k1D (x : ℝ) : ℝ :=
  ((i8Psi4s114k1dN0 x + (i8Psi4s114k1N1 x + x * i8Psi4s114k1dN1 x) + (2 * x * i8Psi4s114k1N2 x +
    x ^ 2 * i8Psi4s114k1dN2 x) + (3 * x ^ 2 * i8Psi4s114k1N3 x + x ^ 3 * i8Psi4s114k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s114k1N4 x + x ^ 4 * i8Psi4s114k1dN4 x)) * x ^ 2 - (i8Psi4s114k1N0 x +
    x * i8Psi4s114k1N1 x + x ^ 2 * i8Psi4s114k1N2 x + x ^ 3 * i8Psi4s114k1N3 x +
    x ^ 4 * i8Psi4s114k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s114k1dW x

theorem hasDerivAt_i8Psi4s114k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114k1 (i8Psi4s114k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s114k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s114k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s114k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s114k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s114k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s114k1W hx)
  unfold i8Psi4s114k1
  refine e.congr_deriv ?_
  unfold i8Psi4s114k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽114⁾` over words. -/
noncomputable def i8P4w114k1 (x : ℝ) : ℝ :=
    ((-2 + 2 * x ^ 2) / (x)) * hpl [one, negOne, zero] x +
    ((-2 + 2 * x ^ 2) / (x)) * hpl [one, zero, negOne] x

theorem i8Psi4s114k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s114k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w114k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s114k1D i8Psi4s114k1N0 i8Psi4s114k1N1 i8Psi4s114k1N2 i8Psi4s114k1N3 i8Psi4s114k1N4
    i8Psi4s114k1dN0 i8Psi4s114k1dN1 i8Psi4s114k1dN2 i8Psi4s114k1dN3 i8Psi4s114k1dN4 i8Psi4s114k1dW
    i8P4w114k1
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil]
  generalize hpl [zero, one, negOne, zero] x = v0 at *
  generalize hpl [zero, one, zero, negOne] x = v1 at *
  generalize hpl [zero, negOne, zero] x = v2 at *
  generalize hpl [zero, zero, negOne] x = v3 at *
  generalize hpl [one, negOne, zero] x = v4 at *
  generalize hpl [one, zero, negOne] x = v5 at *
  generalize hpl [negOne, zero] x = v6 at *
  generalize hpl [zero, negOne] x = v7 at *
  generalize hpl [zero, zero] x = v8 at *
  generalize hpl [negOne] x = v9 at *
  generalize hpl [zero] x = v10 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽114⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s114 (x : ℝ) : ℝ :=
  i8Psi4s114k0 x + i8Psi4s114k1 x

/-- The derivative of `Ψ₄⁽114⁾`. -/
noncomputable def i8Psi4s114D (x : ℝ) : ℝ :=
  i8Psi4s114k0D x + i8Psi4s114k1D x

theorem hasDerivAt_i8Psi4s114 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s114 (i8Psi4s114D x) x := by
  unfold i8Psi4s114 i8Psi4s114D
  exact ((hasDerivAt_i8Psi4s114k0 hx).add (hasDerivAt_i8Psi4s114k1 hx))

/-- The sub-piece 114 of `p₄` in `ξ`: from `t B0 A2 (-λ)^2/2!`, the term with `log^1 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s114 (x : ℝ) : ℝ :=
  -(2 * (1 - x) ^ 2 / x * Real.log (1 - x) * Real.log x * ((1 + x) / (1 - x) * (-hpl [negOne] x)))

/-- `p₄⁽114⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w114 (x : ℝ) : ℝ :=
  i8P4w114k0 x + i8P4w114k1 x

theorem i8P4s114_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s114 x = i8P4w114 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s114 i8P4w114 i8P4w114k0 i8P4w114k1
  rw [i13_log_one_sub_eq hx]
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [one] hx
  have e1 := hpl_mul_hpl [negOne] [zero, one] hx
  have e2 := hpl_mul_hpl [negOne] [one, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  linear_combination (norm := skip) (((-2 + 2 * x ^ 2) / (x)) * hpl [negOne] x) * e0 + (((-2 +
    2 * x ^ 2) / (x))) * e1 + (((-2 + 2 * x ^ 2) / (x))) * e2
  field_simp
  generalize hpl [negOne, zero, one] x = v0 at *
  generalize hpl [negOne, one, zero] x = v1 at *
  generalize hpl [zero, negOne, one] x = v2 at *
  generalize hpl [zero, one, negOne] x = v3 at *
  generalize hpl [one, negOne, zero] x = v4 at *
  generalize hpl [one, zero, negOne] x = v5 at *
  generalize hpl [zero, one] x = v6 at *
  generalize hpl [one, zero] x = v7 at *
  generalize hpl [negOne] x = v8 at *
  generalize hpl [zero] x = v9 at *
  generalize hpl [one] x = v10 at *
  ring

/-- **`(Ψ₄⁽114⁾)'(ξ) ξ' = p₄⁽114⁾`**, in terms of `ξ`. -/
theorem i8Psi4s114D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s114D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s114 x := by
  rw [i8P4s114_eq_w hx]
  unfold i8Psi4s114D i8P4w114
  rw [← i8Psi4s114k0D_mul hx, ← i8Psi4s114k1D_mul hx]
  ring

end QED.ThreeLoopD
