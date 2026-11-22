/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P47

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 153 to 155

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s153`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s153D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s153`, `QED.ThreeLoopD.i8Psi4s153D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽153⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s153N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s153N0`. -/
noncomputable def i8Psi4s153dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s153N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s153N0 (i8Psi4s153dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽153⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s153N1 (x : ℝ) : ℝ :=
    (1) +
    (1) * hpl [zero] x +
    (1) * hpl [zero, zero] x +
    (1) * hpl [zero, zero, zero] x +
    (1) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s153N1`. -/
noncomputable def i8Psi4s153dN1 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [zero, zero] x) +
    (1) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s153N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s153N1 (i8Psi4s153dN1 x) x := by
  unfold i8Psi4s153N1 i8Psi4s153dN1
  exact (((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽153⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s153N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s153N2`. -/
noncomputable def i8Psi4s153dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s153N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s153N2 (i8Psi4s153dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽153⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s153N3 (x : ℝ) : ℝ :=
    (1) +
    (-1) * hpl [zero] x +
    (1) * hpl [zero, zero] x +
    (-1) * hpl [zero, zero, zero] x +
    (1) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s153N3`. -/
noncomputable def i8Psi4s153dN3 (x : ℝ) : ℝ :=
    0 +
    (-1) * (zero.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [zero, zero] x) +
    (1) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s153N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s153N3 (i8Psi4s153dN3 x) x := by
  unfold i8Psi4s153N3 i8Psi4s153dN3
  exact (((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽153⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s153N4 (x : ℝ) : ℝ :=
    (-1 / 32) +
    (1 / 16) * hpl [zero] x +
    (-1 / 8) * hpl [zero, zero] x +
    (1 / 4) * hpl [zero, zero, zero] x +
    (-1 / 2) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s153N4`. -/
noncomputable def i8Psi4s153dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 16) * (zero.kernel x * hpl [] x) +
    (-1 / 8) * (zero.kernel x * hpl [zero] x) +
    (1 / 4) * (zero.kernel x * hpl [zero, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s153N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s153N4 (i8Psi4s153dN4 x) x := by
  unfold i8Psi4s153N4 i8Psi4s153dN4
  exact (((((hasDerivAt_const x (-1 / 32)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 16))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-1 / 2)))

/-- The part of `Ψ₄⁽153⁾` with constant coefficients. -/
noncomputable def i8Psi4s153W (x : ℝ) : ℝ :=
    (1) * hpl [zero, zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s153W`. -/
noncomputable def i8Psi4s153dW (x : ℝ) : ℝ :=
    (1) * (zero.kernel x * hpl [zero, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s153W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s153W (i8Psi4s153dW x) x := by
  unfold i8Psi4s153W i8Psi4s153dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero, zero] hx).const_mul (1))

/-- The piece `Ψ₄⁽153⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s153 (x : ℝ) : ℝ :=
  (i8Psi4s153N0 x + x * i8Psi4s153N1 x + x ^ 2 * i8Psi4s153N2 x + x ^ 3 * i8Psi4s153N3 x +
    x ^ 4 * i8Psi4s153N4 x) / x ^ 2 + i8Psi4s153W x

/-- The derivative of `Ψ₄⁽153⁾`. -/
noncomputable def i8Psi4s153D (x : ℝ) : ℝ :=
  ((i8Psi4s153dN0 x + (i8Psi4s153N1 x + x * i8Psi4s153dN1 x) + (2 * x * i8Psi4s153N2 x +
    x ^ 2 * i8Psi4s153dN2 x) + (3 * x ^ 2 * i8Psi4s153N3 x + x ^ 3 * i8Psi4s153dN3 x) +
    (4 * x ^ 3 * i8Psi4s153N4 x + x ^ 4 * i8Psi4s153dN4 x)) * x ^ 2 - (i8Psi4s153N0 x +
    x * i8Psi4s153N1 x + x ^ 2 * i8Psi4s153N2 x + x ^ 3 * i8Psi4s153N3 x +
    x ^ 4 * i8Psi4s153N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s153dW x

theorem hasDerivAt_i8Psi4s153 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s153 (i8Psi4s153D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s153N0 hx).add (X.mul (hasDerivAt_i8Psi4s153N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s153N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s153N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s153N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s153W hx)
  unfold i8Psi4s153
  refine e.congr_deriv ?_
  unfold i8Psi4s153D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 153 of `p₄` in `ξ`: from `t B0 A0 (-λ)^4/4!`, the term with `log^0 (1 -
  ξ) log^4 ξ`. -/
noncomputable def i8P4s153 (x : ℝ) : ℝ :=
  (1 / 24) * (1 - x) ^ 2 / x * Real.log x ^ 4 * (x / (1 - x))

/-- `p₄⁽153⁾` written over words. -/
noncomputable def i8P4w153 (x : ℝ) : ℝ :=
    (1 - x) * hpl [zero, zero, zero, zero] x

theorem i8P4s153_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s153 x = i8P4w153 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s153 i8P4w153
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [zero] hx
  have e1 := hpl_mul_hpl [zero] [zero, zero] hx
  have e2 := hpl_mul_hpl [zero] [zero, zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  linear_combination (norm := skip) ((1 / 24 - x / 24) * hpl [zero] x * hpl [zero] x) * e0 +
    ((1 / 12 - x / 12) * hpl [zero] x) * e1 + ((1 / 4 - x / 4)) * e2
  field_simp
  generalize hpl [zero, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero] x = v1 at *
  generalize hpl [zero, zero] x = v2 at *
  generalize hpl [zero] x = v3 at *
  ring

/-- **`(Ψ₄⁽153⁾)'(ξ) ξ' = p₄⁽153⁾`**, in terms of `ξ`. -/
theorem i8Psi4s153D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s153D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s153 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s153_eq_w hx]
  unfold i8Psi4s153D i8Psi4s153N0 i8Psi4s153N1 i8Psi4s153N2 i8Psi4s153N3 i8Psi4s153N4 i8Psi4s153dN0
    i8Psi4s153dN1 i8Psi4s153dN2 i8Psi4s153dN3 i8Psi4s153dN4 i8Psi4s153dW i8P4w153
  simp only [kernel_zero, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero, zero] x = v1 at *
  generalize hpl [zero, zero, zero] x = v2 at *
  generalize hpl [zero, zero] x = v3 at *
  generalize hpl [zero] x = v4 at *
  ring

/-- The part of `ξ² Ψ₄⁽154⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s154N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s154N0`. -/
noncomputable def i8Psi4s154dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s154N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s154N0 (i8Psi4s154dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽154⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s154N1 (x : ℝ) : ℝ :=
    (2) * hpl [one] x +
    (2) * hpl [zero, one] x +
    (2) * hpl [one, zero] x +
    (2) * hpl [zero, zero, one] x +
    (2) * hpl [zero, one, zero] x +
    (2) * hpl [one, zero, zero] x +
    (2) * hpl [zero, zero, zero, one] x +
    (2) * hpl [zero, zero, one, zero] x +
    (2) * hpl [zero, one, zero, zero] x +
    (2) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s154N1`. -/
noncomputable def i8Psi4s154dN1 (x : ℝ) : ℝ :=
    (2) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (2) * (zero.kernel x * hpl [one, zero] x) +
    (2) * (one.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero, one] x) +
    (2) * (zero.kernel x * hpl [zero, one, zero] x) +
    (2) * (zero.kernel x * hpl [one, zero, zero] x) +
    (2) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s154N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s154N1 (i8Psi4s154dN1 x) x := by
  unfold i8Psi4s154N1 i8Psi4s154dN1
  exact (((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽154⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s154N2 (x : ℝ) : ℝ :=
    (-2) * hpl [zero] x +
    (-1 / 8) * hpl [one] x +
    (-2) * hpl [zero, zero] x +
    (-15 / 4) * hpl [one, zero] x +
    (-2) * hpl [zero, zero, zero] x +
    (-1 / 2) * hpl [one, zero, zero] x +
    (-3) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s154N2`. -/
noncomputable def i8Psi4s154dN2 (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [] x) +
    (-1 / 8) * (one.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [zero] x) +
    (-15 / 4) * (one.kernel x * hpl [zero] x) +
    (-2) * (zero.kernel x * hpl [zero, zero] x) +
    (-1 / 2) * (one.kernel x * hpl [zero, zero] x) +
    (-3) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s154N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s154N2 (i8Psi4s154dN2 x) x := by
  unfold i8Psi4s154N2 i8Psi4s154dN2
  exact ((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-15 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (-3)))

/-- The part of `ξ² Ψ₄⁽154⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s154N3 (x : ℝ) : ℝ :=
    (-49 / 8) +
    (17 / 4) * hpl [zero] x +
    (-2) * hpl [one] x +
    (-5 / 2) * hpl [zero, zero] x +
    (2) * hpl [zero, one] x +
    (2) * hpl [one, zero] x +
    (1) * hpl [zero, zero, zero] x +
    (-2) * hpl [zero, zero, one] x +
    (-2) * hpl [zero, one, zero] x +
    (-2) * hpl [one, zero, zero] x +
    (2) * hpl [zero, zero, zero, one] x +
    (2) * hpl [zero, zero, one, zero] x +
    (2) * hpl [zero, one, zero, zero] x +
    (2) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s154N3`. -/
noncomputable def i8Psi4s154dN3 (x : ℝ) : ℝ :=
    0 +
    (17 / 4) * (zero.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [] x) +
    (-5 / 2) * (zero.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, one] x) +
    (-2) * (zero.kernel x * hpl [one, zero] x) +
    (-2) * (one.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero, one] x) +
    (2) * (zero.kernel x * hpl [zero, one, zero] x) +
    (2) * (zero.kernel x * hpl [one, zero, zero] x) +
    (2) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s154N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s154N3 (i8Psi4s154dN3 x) x := by
  unfold i8Psi4s154N3 i8Psi4s154dN3
  exact ((((((((((((((hasDerivAt_const x (-49 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (17 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽154⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s154N4 (x : ℝ) : ℝ :=
    (1 / 4) +
    (-3 / 8) * hpl [zero] x +
    (1 / 8) * hpl [one] x +
    (1 / 2) * hpl [zero, zero] x +
    (-1 / 4) * hpl [zero, one] x +
    (-1 / 4) * hpl [one, zero] x +
    (-1 / 2) * hpl [zero, zero, zero] x +
    (1 / 2) * hpl [zero, zero, one] x +
    (1 / 2) * hpl [zero, one, zero] x +
    (1 / 2) * hpl [one, zero, zero] x +
    (-1) * hpl [zero, zero, zero, one] x +
    (-1) * hpl [zero, zero, one, zero] x +
    (-1) * hpl [zero, one, zero, zero] x +
    (-1) * hpl [one, zero, zero, zero] x

/-- The derivative of `i8Psi4s154N4`. -/
noncomputable def i8Psi4s154dN4 (x : ℝ) : ℝ :=
    0 +
    (-3 / 8) * (zero.kernel x * hpl [] x) +
    (1 / 8) * (one.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [one] x) +
    (-1 / 4) * (one.kernel x * hpl [zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, one] x) +
    (1 / 2) * (zero.kernel x * hpl [one, zero] x) +
    (1 / 2) * (one.kernel x * hpl [zero, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-1) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-1) * (zero.kernel x * hpl [one, zero, zero] x) +
    (-1) * (one.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s154N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s154N4 (i8Psi4s154dN4 x) x := by
  unfold i8Psi4s154N4 i8Psi4s154dN4
  exact ((((((((((((((hasDerivAt_const x (1 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 8))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, zero, zero] hx).const_mul (-1)))

/-- The part of `Ψ₄⁽154⁾` with constant coefficients. -/
noncomputable def i8Psi4s154W (x : ℝ) : ℝ :=
    (-2) * hpl [zero, zero, zero, zero] x +
    (2) * hpl [zero, zero, zero, zero, one] x +
    (2) * hpl [zero, zero, zero, one, zero] x +
    (2) * hpl [zero, zero, one, zero, zero] x +
    (2) * hpl [zero, one, zero, zero, zero] x

/-- The derivative of `i8Psi4s154W`. -/
noncomputable def i8Psi4s154dW (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero, zero, one] x) +
    (2) * (zero.kernel x * hpl [zero, zero, one, zero] x) +
    (2) * (zero.kernel x * hpl [zero, one, zero, zero] x) +
    (2) * (zero.kernel x * hpl [one, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s154W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s154W (i8Psi4s154dW x) x := by
  unfold i8Psi4s154W i8Psi4s154dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero, zero] hx).const_mul (2)))

/-- The piece `Ψ₄⁽154⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s154 (x : ℝ) : ℝ :=
  (i8Psi4s154N0 x + x * i8Psi4s154N1 x + x ^ 2 * i8Psi4s154N2 x + x ^ 3 * i8Psi4s154N3 x +
    x ^ 4 * i8Psi4s154N4 x) / x ^ 2 + i8Psi4s154W x

/-- The derivative of `Ψ₄⁽154⁾`. -/
noncomputable def i8Psi4s154D (x : ℝ) : ℝ :=
  ((i8Psi4s154dN0 x + (i8Psi4s154N1 x + x * i8Psi4s154dN1 x) + (2 * x * i8Psi4s154N2 x +
    x ^ 2 * i8Psi4s154dN2 x) + (3 * x ^ 2 * i8Psi4s154N3 x + x ^ 3 * i8Psi4s154dN3 x) +
    (4 * x ^ 3 * i8Psi4s154N4 x + x ^ 4 * i8Psi4s154dN4 x)) * x ^ 2 - (i8Psi4s154N0 x +
    x * i8Psi4s154N1 x + x ^ 2 * i8Psi4s154N2 x + x ^ 3 * i8Psi4s154N3 x +
    x ^ 4 * i8Psi4s154N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s154dW x

theorem hasDerivAt_i8Psi4s154 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s154 (i8Psi4s154D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s154N0 hx).add (X.mul (hasDerivAt_i8Psi4s154N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s154N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s154N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s154N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s154W hx)
  unfold i8Psi4s154
  refine e.congr_deriv ?_
  unfold i8Psi4s154D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 154 of `p₄` in `ξ`: from `t B0 A0 (-λ)^4/4!`, the term with `log^1 (1 -
  ξ) log^3 ξ`. -/
noncomputable def i8P4s154 (x : ℝ) : ℝ :=
  -((1 / 3) * (1 - x) ^ 2 / x * Real.log (1 - x) * Real.log x ^ 3 * (x / (1 - x)))

/-- `p₄⁽154⁾` written over words. -/
noncomputable def i8P4w154 (x : ℝ) : ℝ :=
    (2 - 2 * x) * hpl [zero, zero, zero, one] x +
    (2 - 2 * x) * hpl [zero, zero, one, zero] x +
    (2 - 2 * x) * hpl [zero, one, zero, zero] x +
    (2 - 2 * x) * hpl [one, zero, zero, zero] x

theorem i8P4s154_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s154 x = i8P4w154 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s154 i8P4w154
  rw [i13_log_one_sub_eq hx]
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [one] hx
  have e1 := hpl_mul_hpl [zero] [zero, one] hx
  have e2 := hpl_mul_hpl [zero] [one, zero] hx
  have e3 := hpl_mul_hpl [zero] [zero, zero, one] hx
  have e4 := hpl_mul_hpl [zero] [zero, one, zero] hx
  have e5 := hpl_mul_hpl [zero] [one, zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e3
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e4
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e5
  linear_combination (norm := skip) ((1 / 3 - x / 3) * hpl [zero] x * hpl [zero] x) * e0 +
    ((1 / 3 - x / 3) * hpl [zero] x) * e1 + ((1 / 3 - x / 3) * hpl [zero] x) * e2 + ((2 / 3 -
    2 / 3 * x)) * e3 + ((2 / 3 - 2 / 3 * x)) * e4 + ((2 / 3 - 2 / 3 * x)) * e5
  field_simp
  generalize hpl [zero, zero, zero, one] x = v0 at *
  generalize hpl [zero, zero, one, zero] x = v1 at *
  generalize hpl [zero, one, zero, zero] x = v2 at *
  generalize hpl [one, zero, zero, zero] x = v3 at *
  generalize hpl [zero, zero, one] x = v4 at *
  generalize hpl [zero, one, zero] x = v5 at *
  generalize hpl [one, zero, zero] x = v6 at *
  generalize hpl [zero, one] x = v7 at *
  generalize hpl [one, zero] x = v8 at *
  generalize hpl [zero] x = v9 at *
  generalize hpl [one] x = v10 at *
  ring

/-- **`(Ψ₄⁽154⁾)'(ξ) ξ' = p₄⁽154⁾`**, in terms of `ξ`. -/
theorem i8Psi4s154D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s154D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s154 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s154_eq_w hx]
  unfold i8Psi4s154D i8Psi4s154N0 i8Psi4s154N1 i8Psi4s154N2 i8Psi4s154N3 i8Psi4s154N4 i8Psi4s154dN0
    i8Psi4s154dN1 i8Psi4s154dN2 i8Psi4s154dN3 i8Psi4s154dN4 i8Psi4s154dW i8P4w154
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

/-- The part of `ξ² Ψ₄⁽155⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s155k0N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s155k0N0`. -/
noncomputable def i8Psi4s155k0dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s155k0N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k0N0 (i8Psi4s155k0dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽155⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s155k0N1 (x : ℝ) : ℝ :=
    (4) * hpl [one, one] x +
    (4) * hpl [zero, one, one] x +
    (4) * hpl [one, zero, one] x +
    (4) * hpl [one, one, zero] x +
    (4) * hpl [zero, zero, one, one] x +
    (4) * hpl [zero, one, zero, one] x +
    (4) * hpl [zero, one, one, zero] x +
    (4) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s155k0N1`. -/
noncomputable def i8Psi4s155k0dN1 (x : ℝ) : ℝ :=
    (4) * (one.kernel x * hpl [one] x) +
    (4) * (zero.kernel x * hpl [one, one] x) +
    (4) * (one.kernel x * hpl [zero, one] x) +
    (4) * (one.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [zero, one, one] x) +
    (4) * (zero.kernel x * hpl [one, zero, one] x) +
    (4) * (zero.kernel x * hpl [one, one, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s155k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k0N1 (i8Psi4s155k0dN1 x) x := by
  unfold i8Psi4s155k0N1 i8Psi4s155k0dN1
  exact (((((((((hasDerivAt_hpl_cons one [one] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽155⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s155k0N2 (x : ℝ) : ℝ :=
    (-31 / 4) * hpl [one] x +
    (-4) * hpl [zero, one] x +
    (5 / 2) * hpl [one, zero] x +
    (-15 / 2) * hpl [one, one] x +
    (-4) * hpl [zero, zero, one] x +
    (-1) * hpl [one, zero, one] x +
    (-1) * hpl [one, one, zero] x +
    (-6) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s155k0N2`. -/
noncomputable def i8Psi4s155k0dN2 (x : ℝ) : ℝ :=
    (-31 / 4) * (one.kernel x * hpl [] x) +
    (-4) * (zero.kernel x * hpl [one] x) +
    (5 / 2) * (one.kernel x * hpl [zero] x) +
    (-15 / 2) * (one.kernel x * hpl [one] x) +
    (-4) * (zero.kernel x * hpl [zero, one] x) +
    (-1) * (one.kernel x * hpl [zero, one] x) +
    (-1) * (one.kernel x * hpl [one, zero] x) +
    (-6) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s155k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k0N2 (i8Psi4s155k0dN2 x) x := by
  unfold i8Psi4s155k0N2 i8Psi4s155k0dN2
  exact (((((((((hasDerivAt_hpl_cons one [] hx).const_mul (-31 / 4)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (5 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-15 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (-6)))

/-- The part of `ξ² Ψ₄⁽155⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s155k0N3 (x : ℝ) : ℝ :=
    (41 / 4) +
    (-5 / 2) * hpl [zero] x +
    (17 / 2) * hpl [one] x +
    (-5) * hpl [zero, one] x +
    (-3) * hpl [one, zero] x +
    (4) * hpl [one, one] x +
    (2) * hpl [zero, zero, one] x +
    (-4) * hpl [zero, one, one] x +
    (-4) * hpl [one, zero, one] x +
    (-4) * hpl [one, one, zero] x +
    (4) * hpl [zero, zero, one, one] x +
    (4) * hpl [zero, one, zero, one] x +
    (4) * hpl [zero, one, one, zero] x +
    (4) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s155k0N3`. -/
noncomputable def i8Psi4s155k0dN3 (x : ℝ) : ℝ :=
    0 +
    (-5 / 2) * (zero.kernel x * hpl [] x) +
    (17 / 2) * (one.kernel x * hpl [] x) +
    (-5) * (zero.kernel x * hpl [one] x) +
    (-3) * (one.kernel x * hpl [zero] x) +
    (4) * (one.kernel x * hpl [one] x) +
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (-4) * (zero.kernel x * hpl [one, one] x) +
    (-4) * (one.kernel x * hpl [zero, one] x) +
    (-4) * (one.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [zero, one, one] x) +
    (4) * (zero.kernel x * hpl [one, zero, one] x) +
    (4) * (zero.kernel x * hpl [one, one, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s155k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k0N3 (i8Psi4s155k0dN3 x) x := by
  unfold i8Psi4s155k0N3 i8Psi4s155k0dN3
  exact ((((((((((((((hasDerivAt_const x (41 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (17 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽155⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s155k0N4 (x : ℝ) : ℝ :=
    (-1 / 2) +
    (1 / 4) * hpl [zero] x +
    (-3 / 4) * hpl [one] x +
    (1) * hpl [zero, one] x +
    (1 / 2) * hpl [one, zero] x +
    (-1 / 2) * hpl [one, one] x +
    (-1) * hpl [zero, zero, one] x +
    (1) * hpl [zero, one, one] x +
    (1) * hpl [one, zero, one] x +
    (1) * hpl [one, one, zero] x +
    (-2) * hpl [zero, zero, one, one] x +
    (-2) * hpl [zero, one, zero, one] x +
    (-2) * hpl [zero, one, one, zero] x +
    (-2) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s155k0N4`. -/
noncomputable def i8Psi4s155k0dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 4) * (zero.kernel x * hpl [] x) +
    (-3 / 4) * (one.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [one] x) +
    (1 / 2) * (one.kernel x * hpl [zero] x) +
    (-1 / 2) * (one.kernel x * hpl [one] x) +
    (-1) * (zero.kernel x * hpl [zero, one] x) +
    (1) * (zero.kernel x * hpl [one, one] x) +
    (1) * (one.kernel x * hpl [zero, one] x) +
    (1) * (one.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, one, one] x) +
    (-2) * (zero.kernel x * hpl [one, zero, one] x) +
    (-2) * (zero.kernel x * hpl [one, one, zero] x) +
    (-2) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s155k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k0N4 (i8Psi4s155k0dN4 x) x := by
  unfold i8Psi4s155k0N4 i8Psi4s155k0dN4
  exact ((((((((((((((hasDerivAt_const x (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽155⁾` with constant coefficients. -/
noncomputable def i8Psi4s155k0W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, one, zero] x +
    (-4) * hpl [zero, zero, zero, one] x +
    (4) * hpl [zero, zero, zero, one, one] x +
    (4) * hpl [zero, zero, one, zero, one] x +
    (4) * hpl [zero, zero, one, one, zero] x +
    (4) * hpl [zero, one, zero, zero, one] x

/-- The derivative of `i8Psi4s155k0W`. -/
noncomputable def i8Psi4s155k0dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [one, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, one] x) +
    (4) * (zero.kernel x * hpl [zero, zero, one, one] x) +
    (4) * (zero.kernel x * hpl [zero, one, zero, one] x) +
    (4) * (zero.kernel x * hpl [zero, one, one, zero] x) +
    (4) * (zero.kernel x * hpl [one, zero, zero, one] x)

theorem hasDerivAt_i8Psi4s155k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k0W (i8Psi4s155k0dW x) x := by
  unfold i8Psi4s155k0W i8Psi4s155k0dW
  exact (((((((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero, one] hx).const_mul (4)))

/-- Chunk 0 of the piece `Ψ₄⁽155⁾`. -/
noncomputable def i8Psi4s155k0 (x : ℝ) : ℝ :=
  (i8Psi4s155k0N0 x + x * i8Psi4s155k0N1 x + x ^ 2 * i8Psi4s155k0N2 x + x ^ 3 * i8Psi4s155k0N3 x +
    x ^ 4 * i8Psi4s155k0N4 x) / x ^ 2 + i8Psi4s155k0W x

/-- The derivative of `i8Psi4s155k0`. -/
noncomputable def i8Psi4s155k0D (x : ℝ) : ℝ :=
  ((i8Psi4s155k0dN0 x + (i8Psi4s155k0N1 x + x * i8Psi4s155k0dN1 x) + (2 * x * i8Psi4s155k0N2 x +
    x ^ 2 * i8Psi4s155k0dN2 x) + (3 * x ^ 2 * i8Psi4s155k0N3 x + x ^ 3 * i8Psi4s155k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s155k0N4 x + x ^ 4 * i8Psi4s155k0dN4 x)) * x ^ 2 - (i8Psi4s155k0N0 x +
    x * i8Psi4s155k0N1 x + x ^ 2 * i8Psi4s155k0N2 x + x ^ 3 * i8Psi4s155k0N3 x +
    x ^ 4 * i8Psi4s155k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s155k0dW x

theorem hasDerivAt_i8Psi4s155k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k0 (i8Psi4s155k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s155k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s155k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s155k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s155k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s155k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s155k0W hx)
  unfold i8Psi4s155k0
  refine e.congr_deriv ?_
  unfold i8Psi4s155k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽155⁾` over words. -/
noncomputable def i8P4w155k0 (x : ℝ) : ℝ :=
    (4 - 4 * x) * hpl [zero, zero, one, one] x +
    (4 - 4 * x) * hpl [zero, one, zero, one] x +
    (4 - 4 * x) * hpl [zero, one, one, zero] x +
    (4 - 4 * x) * hpl [one, zero, zero, one] x

theorem i8Psi4s155k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s155k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w155k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s155k0D i8Psi4s155k0N0 i8Psi4s155k0N1 i8Psi4s155k0N2 i8Psi4s155k0N3 i8Psi4s155k0N4
    i8Psi4s155k0dN0 i8Psi4s155k0dN1 i8Psi4s155k0dN2 i8Psi4s155k0dN3 i8Psi4s155k0dN4 i8Psi4s155k0dW
    i8P4w155k0
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

/-- The part of `ξ² Ψ₄⁽155⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s155k1N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s155k1N0`. -/
noncomputable def i8Psi4s155k1dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s155k1N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k1N0 (i8Psi4s155k1dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽155⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s155k1N1 (x : ℝ) : ℝ :=
    (4) * hpl [one, zero, one, zero] x +
    (4) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s155k1N1`. -/
noncomputable def i8Psi4s155k1dN1 (x : ℝ) : ℝ :=
    (4) * (one.kernel x * hpl [zero, one, zero] x) +
    (4) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s155k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k1N1 (i8Psi4s155k1dN1 x) x := by
  unfold i8Psi4s155k1N1 i8Psi4s155k1dN1
  exact (((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽155⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s155k1N2 (x : ℝ) : ℝ :=
    (3 / 2) * hpl [one, zero] x +
    (-1) * hpl [one, zero, zero] x +
    (-6) * hpl [one, zero, one, zero] x +
    (-6) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s155k1N2`. -/
noncomputable def i8Psi4s155k1dN2 (x : ℝ) : ℝ :=
    (3 / 2) * (one.kernel x * hpl [zero] x) +
    (-1) * (one.kernel x * hpl [zero, zero] x) +
    (-6) * (one.kernel x * hpl [zero, one, zero] x) +
    (-6) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s155k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k1N2 (i8Psi4s155k1dN2 x) x := by
  unfold i8Psi4s155k1N2 i8Psi4s155k1dN2
  exact (((((hasDerivAt_hpl_cons one [zero] hx).const_mul (3 / 2)).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (-6)))

/-- The part of `ξ² Ψ₄⁽155⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s155k1N3 (x : ℝ) : ℝ :=
    (5 / 2) +
    (-5 / 2) * hpl [zero] x +
    (1) * hpl [zero, zero] x +
    (-2) * hpl [one, zero] x +
    (2) * hpl [zero, one, zero] x +
    (2) * hpl [one, zero, zero] x +
    (4) * hpl [one, zero, one, zero] x +
    (4) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s155k1N3`. -/
noncomputable def i8Psi4s155k1dN3 (x : ℝ) : ℝ :=
    0 +
    (-5 / 2) * (zero.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-2) * (one.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [one, zero] x) +
    (2) * (one.kernel x * hpl [zero, zero] x) +
    (4) * (one.kernel x * hpl [zero, one, zero] x) +
    (4) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s155k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k1N3 (i8Psi4s155k1dN3 x) x := by
  unfold i8Psi4s155k1N3 i8Psi4s155k1dN3
  exact ((((((((hasDerivAt_const x (5 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (4)))

/-- The part of `ξ² Ψ₄⁽155⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s155k1N4 (x : ℝ) : ℝ :=
    (-1 / 4) +
    (1 / 2) * hpl [zero] x +
    (-1 / 2) * hpl [zero, zero] x +
    (1 / 2) * hpl [one, zero] x +
    (-1) * hpl [zero, one, zero] x +
    (-1) * hpl [one, zero, zero] x +
    (-2) * hpl [one, zero, one, zero] x +
    (-2) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s155k1N4`. -/
noncomputable def i8Psi4s155k1dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (one.kernel x * hpl [zero] x) +
    (-1) * (zero.kernel x * hpl [one, zero] x) +
    (-1) * (one.kernel x * hpl [zero, zero] x) +
    (-2) * (one.kernel x * hpl [zero, one, zero] x) +
    (-2) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s155k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k1N4 (i8Psi4s155k1dN4 x) x := by
  unfold i8Psi4s155k1N4 i8Psi4s155k1dN4
  exact ((((((((hasDerivAt_const x (-1 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (-2)))

/-- The part of `Ψ₄⁽155⁾` with constant coefficients. -/
noncomputable def i8Psi4s155k1W (x : ℝ) : ℝ :=
    (-4) * hpl [zero, zero, one, zero] x +
    (-4) * hpl [zero, one, zero, zero] x +
    (4) * hpl [zero, one, zero, one, zero] x +
    (4) * hpl [zero, one, one, zero, zero] x

/-- The derivative of `i8Psi4s155k1W`. -/
noncomputable def i8Psi4s155k1dW (x : ℝ) : ℝ :=
    (-4) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-4) * (zero.kernel x * hpl [one, zero, zero] x) +
    (4) * (zero.kernel x * hpl [one, zero, one, zero] x) +
    (4) * (zero.kernel x * hpl [one, one, zero, zero] x)

theorem hasDerivAt_i8Psi4s155k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k1W (i8Psi4s155k1dW x) x := by
  unfold i8Psi4s155k1W i8Psi4s155k1dW
  exact (((((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-4)).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero, zero] hx).const_mul (4)))

/-- Chunk 1 of the piece `Ψ₄⁽155⁾`. -/
noncomputable def i8Psi4s155k1 (x : ℝ) : ℝ :=
  (i8Psi4s155k1N0 x + x * i8Psi4s155k1N1 x + x ^ 2 * i8Psi4s155k1N2 x + x ^ 3 * i8Psi4s155k1N3 x +
    x ^ 4 * i8Psi4s155k1N4 x) / x ^ 2 + i8Psi4s155k1W x

/-- The derivative of `i8Psi4s155k1`. -/
noncomputable def i8Psi4s155k1D (x : ℝ) : ℝ :=
  ((i8Psi4s155k1dN0 x + (i8Psi4s155k1N1 x + x * i8Psi4s155k1dN1 x) + (2 * x * i8Psi4s155k1N2 x +
    x ^ 2 * i8Psi4s155k1dN2 x) + (3 * x ^ 2 * i8Psi4s155k1N3 x + x ^ 3 * i8Psi4s155k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s155k1N4 x + x ^ 4 * i8Psi4s155k1dN4 x)) * x ^ 2 - (i8Psi4s155k1N0 x +
    x * i8Psi4s155k1N1 x + x ^ 2 * i8Psi4s155k1N2 x + x ^ 3 * i8Psi4s155k1N3 x +
    x ^ 4 * i8Psi4s155k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s155k1dW x

theorem hasDerivAt_i8Psi4s155k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155k1 (i8Psi4s155k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s155k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s155k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s155k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s155k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s155k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s155k1W hx)
  unfold i8Psi4s155k1
  refine e.congr_deriv ?_
  unfold i8Psi4s155k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽155⁾` over words. -/
noncomputable def i8P4w155k1 (x : ℝ) : ℝ :=
    (4 - 4 * x) * hpl [one, zero, one, zero] x +
    (4 - 4 * x) * hpl [one, one, zero, zero] x

theorem i8Psi4s155k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s155k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w155k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s155k1D i8Psi4s155k1N0 i8Psi4s155k1N1 i8Psi4s155k1N2 i8Psi4s155k1N3 i8Psi4s155k1N4
    i8Psi4s155k1dN0 i8Psi4s155k1dN1 i8Psi4s155k1dN2 i8Psi4s155k1dN3 i8Psi4s155k1dN4 i8Psi4s155k1dW
    i8P4w155k1
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

/-- The piece `Ψ₄⁽155⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s155 (x : ℝ) : ℝ :=
  i8Psi4s155k0 x + i8Psi4s155k1 x

/-- The derivative of `Ψ₄⁽155⁾`. -/
noncomputable def i8Psi4s155D (x : ℝ) : ℝ :=
  i8Psi4s155k0D x + i8Psi4s155k1D x

theorem hasDerivAt_i8Psi4s155 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s155 (i8Psi4s155D x) x := by
  unfold i8Psi4s155 i8Psi4s155D
  exact ((hasDerivAt_i8Psi4s155k0 hx).add (hasDerivAt_i8Psi4s155k1 hx))

/-- The sub-piece 155 of `p₄` in `ξ`: from `t B0 A0 (-λ)^4/4!`, the term with `log^2 (1 -
  ξ) log^2 ξ`. -/
noncomputable def i8P4s155 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log (1 - x) ^ 2 * Real.log x ^ 2 * (x / (1 - x))

/-- `p₄⁽155⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w155 (x : ℝ) : ℝ :=
  i8P4w155k0 x + i8P4w155k1 x

theorem i8P4s155_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s155 x = i8P4w155 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s155 i8P4w155 i8P4w155k0 i8P4w155k1
  rw [i13_log_one_sub_eq hx]
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [one] [one] hx
  have e1 := hpl_mul_hpl [zero] [one, one] hx
  have e2 := hpl_mul_hpl [zero] [zero, one, one] hx
  have e3 := hpl_mul_hpl [zero] [one, zero, one] hx
  have e4 := hpl_mul_hpl [zero] [one, one, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e3
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e4
  linear_combination (norm := skip) ((1 - x) * hpl [zero] x * hpl [zero] x) * e0 + ((2 -
    2 * x) * hpl [zero] x) * e1 + ((2 - 2 * x)) * e2 + ((2 - 2 * x)) * e3 + ((2 - 2 * x)) * e4
  field_simp
  generalize hpl [zero, zero, one, one] x = v0 at *
  generalize hpl [zero, one, zero, one] x = v1 at *
  generalize hpl [zero, one, one, zero] x = v2 at *
  generalize hpl [one, zero, zero, one] x = v3 at *
  generalize hpl [one, zero, one, zero] x = v4 at *
  generalize hpl [one, one, zero, zero] x = v5 at *
  generalize hpl [zero, one, one] x = v6 at *
  generalize hpl [one, zero, one] x = v7 at *
  generalize hpl [one, one, zero] x = v8 at *
  generalize hpl [one, one] x = v9 at *
  generalize hpl [zero] x = v10 at *
  generalize hpl [one] x = v11 at *
  ring

/-- **`(Ψ₄⁽155⁾)'(ξ) ξ' = p₄⁽155⁾`**, in terms of `ξ`. -/
theorem i8Psi4s155D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s155D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s155 x := by
  rw [i8P4s155_eq_w hx]
  unfold i8Psi4s155D i8P4w155
  rw [← i8Psi4s155k0D_mul hx, ← i8Psi4s155k1D_mul hx]
  ring

end QED.ThreeLoopD
