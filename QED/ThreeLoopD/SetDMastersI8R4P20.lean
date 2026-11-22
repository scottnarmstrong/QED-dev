/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P19

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 82 to 84

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s82`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s82D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s82`, `QED.ThreeLoopD.i8Psi4s82D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽82⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s82N0 (x : ℝ) : ℝ :=
    (-2) * hpl [negOne, one] x +
    (-2) * hpl [one, negOne] x +
    (-4) * hpl [negOne, zero, one] x +
    (-4) * hpl [negOne, one, zero] x +
    (-4) * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, one, negOne] x +
    (-4) * hpl [one, negOne, zero] x +
    (-4) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s82N0`. -/
noncomputable def i8Psi4s82dN0 (x : ℝ) : ℝ :=
    (-2) * (negOne.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [negOne] x) +
    (-4) * (negOne.kernel x * hpl [zero, one] x) +
    (-4) * (negOne.kernel x * hpl [one, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, one] x) +
    (-4) * (zero.kernel x * hpl [one, negOne] x) +
    (-4) * (one.kernel x * hpl [negOne, zero] x) +
    (-4) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s82N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s82N0 (i8Psi4s82dN0 x) x := by
  unfold i8Psi4s82N0 i8Psi4s82dN0
  exact (((((((((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-4)))

/-- The part of `ξ² Ψ₄⁽82⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s82N1 (x : ℝ) : ℝ :=
    (-6) * hpl [negOne] x +
    (-6) * hpl [one] x +
    (-4) * hpl [negOne, zero] x +
    (-16) * hpl [negOne, one] x +
    (-4) * hpl [zero, negOne] x +
    (-4) * hpl [zero, one] x +
    (-16) * hpl [one, negOne] x +
    (-4) * hpl [one, zero] x +
    (-16) * hpl [negOne, zero, one] x +
    (-16) * hpl [negOne, one, zero] x +
    (-16) * hpl [zero, negOne, one] x +
    (-16) * hpl [zero, one, negOne] x +
    (-16) * hpl [one, negOne, zero] x +
    (-16) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s82N1`. -/
noncomputable def i8Psi4s82dN1 (x : ℝ) : ℝ :=
    (-6) * (negOne.kernel x * hpl [] x) +
    (-6) * (one.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [one] x) +
    (-4) * (zero.kernel x * hpl [negOne] x) +
    (-4) * (zero.kernel x * hpl [one] x) +
    (-16) * (one.kernel x * hpl [negOne] x) +
    (-4) * (one.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, one] x) +
    (-16) * (negOne.kernel x * hpl [one, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, one] x) +
    (-16) * (zero.kernel x * hpl [one, negOne] x) +
    (-16) * (one.kernel x * hpl [negOne, zero] x) +
    (-16) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s82N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s82N1 (i8Psi4s82dN1 x) x := by
  unfold i8Psi4s82N1 i8Psi4s82dN1
  exact (((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-6)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽82⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s82N2 (x : ℝ) : ℝ :=
    (30) * hpl [negOne] x +
    (12) * hpl [zero] x +
    (34) * hpl [one] x +
    (-22) * hpl [negOne, zero] x +
    (18) * hpl [zero, negOne] x +
    (14) * hpl [zero, one] x +
    (-10) * hpl [one, zero] x +
    (-24) * hpl [negOne, zero, one] x +
    (-24) * hpl [negOne, one, zero] x +
    (40) * hpl [one, negOne, zero] x +
    (40) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s82N2`. -/
noncomputable def i8Psi4s82dN2 (x : ℝ) : ℝ :=
    (30) * (negOne.kernel x * hpl [] x) +
    (12) * (zero.kernel x * hpl [] x) +
    (34) * (one.kernel x * hpl [] x) +
    (-22) * (negOne.kernel x * hpl [zero] x) +
    (18) * (zero.kernel x * hpl [negOne] x) +
    (14) * (zero.kernel x * hpl [one] x) +
    (-10) * (one.kernel x * hpl [zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, one] x) +
    (-24) * (negOne.kernel x * hpl [one, zero] x) +
    (40) * (one.kernel x * hpl [negOne, zero] x) +
    (40) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s82N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s82N2 (i8Psi4s82dN2 x) x := by
  unfold i8Psi4s82N2 i8Psi4s82dN2
  exact ((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (30)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (34))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (40)))

/-- The part of `ξ² Ψ₄⁽82⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s82N3 (x : ℝ) : ℝ :=
    (-96) +
    (38) * hpl [negOne] x +
    (32) * hpl [zero] x +
    (-26) * hpl [one] x +
    (-20) * hpl [negOne, zero] x +
    (16) * hpl [negOne, one] x +
    (-20) * hpl [zero, negOne] x +
    (12) * hpl [zero, one] x +
    (16) * hpl [one, negOne] x +
    (12) * hpl [one, zero] x +
    (-16) * hpl [negOne, zero, one] x +
    (-16) * hpl [negOne, one, zero] x +
    (-16) * hpl [zero, negOne, one] x +
    (-16) * hpl [zero, one, negOne] x +
    (-16) * hpl [one, negOne, zero] x +
    (-16) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s82N3`. -/
noncomputable def i8Psi4s82dN3 (x : ℝ) : ℝ :=
    0 +
    (38) * (negOne.kernel x * hpl [] x) +
    (32) * (zero.kernel x * hpl [] x) +
    (-26) * (one.kernel x * hpl [] x) +
    (-20) * (negOne.kernel x * hpl [zero] x) +
    (16) * (negOne.kernel x * hpl [one] x) +
    (-20) * (zero.kernel x * hpl [negOne] x) +
    (12) * (zero.kernel x * hpl [one] x) +
    (16) * (one.kernel x * hpl [negOne] x) +
    (12) * (one.kernel x * hpl [zero] x) +
    (-16) * (negOne.kernel x * hpl [zero, one] x) +
    (-16) * (negOne.kernel x * hpl [one, zero] x) +
    (-16) * (zero.kernel x * hpl [negOne, one] x) +
    (-16) * (zero.kernel x * hpl [one, negOne] x) +
    (-16) * (one.kernel x * hpl [negOne, zero] x) +
    (-16) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s82N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s82N3 (i8Psi4s82dN3 x) x := by
  unfold i8Psi4s82N3 i8Psi4s82dN3
  exact ((((((((((((((((hasDerivAt_const x (-96)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (38))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-26))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-16)))

/-- The part of `ξ² Ψ₄⁽82⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s82N4 (x : ℝ) : ℝ :=
    (-3) +
    (2) * hpl [negOne] x +
    (2) * hpl [zero] x +
    (-2) * hpl [one] x +
    (-2) * hpl [negOne, zero] x +
    (2) * hpl [negOne, one] x +
    (-2) * hpl [zero, negOne] x +
    (2) * hpl [zero, one] x +
    (2) * hpl [one, negOne] x +
    (2) * hpl [one, zero] x +
    (-4) * hpl [negOne, zero, one] x +
    (-4) * hpl [negOne, one, zero] x +
    (-4) * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, one, negOne] x +
    (-4) * hpl [one, negOne, zero] x +
    (-4) * hpl [one, zero, negOne] x

/-- The derivative of `i8Psi4s82N4`. -/
noncomputable def i8Psi4s82dN4 (x : ℝ) : ℝ :=
    0 +
    (2) * (negOne.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [zero] x) +
    (2) * (negOne.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [negOne] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [negOne] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, one] x) +
    (-4) * (negOne.kernel x * hpl [one, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, one] x) +
    (-4) * (zero.kernel x * hpl [one, negOne] x) +
    (-4) * (one.kernel x * hpl [negOne, zero] x) +
    (-4) * (one.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s82N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s82N4 (i8Psi4s82dN4 x) x := by
  unfold i8Psi4s82N4 i8Psi4s82dN4
  exact ((((((((((((((((hasDerivAt_const x (-3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-4)))

/-- The part of `Ψ₄⁽82⁾` with constant coefficients. -/
noncomputable def i8Psi4s82W (x : ℝ) : ℝ :=
    (8) * hpl [zero, zero] x +
    (20) * hpl [zero, negOne, zero] x +
    (20) * hpl [zero, zero, negOne] x +
    (12) * hpl [zero, zero, one] x +
    (12) * hpl [zero, one, zero] x

/-- The derivative of `i8Psi4s82W`. -/
noncomputable def i8Psi4s82dW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [zero] x) +
    (20) * (zero.kernel x * hpl [negOne, zero] x) +
    (20) * (zero.kernel x * hpl [zero, negOne] x) +
    (12) * (zero.kernel x * hpl [zero, one] x) +
    (12) * (zero.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s82W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s82W (i8Psi4s82dW x) x := by
  unfold i8Psi4s82W i8Psi4s82dW
  exact ((((((hasDerivAt_hpl_cons zero [zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (20))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (12)))

/-- The piece `Ψ₄⁽82⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s82 (x : ℝ) : ℝ :=
  (i8Psi4s82N0 x + x * i8Psi4s82N1 x + x ^ 2 * i8Psi4s82N2 x + x ^ 3 * i8Psi4s82N3 x +
    x ^ 4 * i8Psi4s82N4 x) / x ^ 2 + i8Psi4s82W x

/-- The derivative of `Ψ₄⁽82⁾`. -/
noncomputable def i8Psi4s82D (x : ℝ) : ℝ :=
  ((i8Psi4s82dN0 x + (i8Psi4s82N1 x + x * i8Psi4s82dN1 x) + (2 * x * i8Psi4s82N2 x +
    x ^ 2 * i8Psi4s82dN2 x) + (3 * x ^ 2 * i8Psi4s82N3 x + x ^ 3 * i8Psi4s82dN3 x) +
    (4 * x ^ 3 * i8Psi4s82N4 x + x ^ 4 * i8Psi4s82dN4 x)) * x ^ 2 - (i8Psi4s82N0 x +
    x * i8Psi4s82N1 x + x ^ 2 * i8Psi4s82N2 x + x ^ 3 * i8Psi4s82N3 x +
    x ^ 4 * i8Psi4s82N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s82dW x

theorem hasDerivAt_i8Psi4s82 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s82 (i8Psi4s82D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s82N0 hx).add (X.mul (hasDerivAt_i8Psi4s82N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s82N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s82N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s82N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s82W hx)
  unfold i8Psi4s82
  refine e.congr_deriv ?_
  unfold i8Psi4s82D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 82 of `p₄` in `ξ`: from `t B2 A1 (-λ)^1/1!`, the term with `log^1 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s82 (x : ℝ) : ℝ :=
  -(4 * (1 - x) ^ 2 / x * Real.log (1 - x) * ((1 + x) / (1 - x) * (2 * hpl [zero] x)) * ((1 +
    x) / (1 - x) * (-hpl [negOne] x)))

/-- `p₄⁽82⁾` written over words. -/
noncomputable def i8P4w82 (x : ℝ) : ℝ :=
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [negOne, zero, one] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [negOne, one, zero] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [zero, negOne, one] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [zero, one, negOne] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [one, negOne, zero] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [one, zero, negOne] x

theorem i8P4s82_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s82 x = i8P4w82 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s82 i8P4w82
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [zero] [one] hx
  have e1 := hpl_mul_hpl [negOne] [zero, one] hx
  have e2 := hpl_mul_hpl [negOne] [one, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e2
  linear_combination (norm := skip) (((-8 - 16 * x -
    8 * x ^ 2) / (x)) * hpl [negOne] x) * e0 + (((-8 - 16 * x - 8 * x ^ 2) / (x))) * e1 + (((-8 -
    16 * x - 8 * x ^ 2) / (x))) * e2
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

/-- **`(Ψ₄⁽82⁾)'(ξ) ξ' = p₄⁽82⁾`**, in terms of `ξ`. -/
theorem i8Psi4s82D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s82D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s82 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s82_eq_w hx]
  unfold i8Psi4s82D i8Psi4s82N0 i8Psi4s82N1 i8Psi4s82N2 i8Psi4s82N3 i8Psi4s82N4 i8Psi4s82dN0
    i8Psi4s82dN1 i8Psi4s82dN2 i8Psi4s82dN3 i8Psi4s82dN4 i8Psi4s82dW i8P4w82
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

/-- The part of `ξ² Ψ₄⁽83⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s83N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s83N0`. -/
noncomputable def i8Psi4s83dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s83N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s83N0 (i8Psi4s83dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽83⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s83N1 (x : ℝ) : ℝ :=
    (18) +
    (18) * hpl [zero] x +
    (14) * hpl [zero, zero] x +
    (6) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s83N1`. -/
noncomputable def i8Psi4s83dN1 (x : ℝ) : ℝ :=
    0 +
    (18) * (zero.kernel x * hpl [] x) +
    (14) * (zero.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s83N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s83N1 (i8Psi4s83dN1 x) x := by
  unfold i8Psi4s83N1 i8Psi4s83dN1
  exact ((((hasDerivAt_const x (18)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (18))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6)))

/-- The part of `ξ² Ψ₄⁽83⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s83N2 (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero] x +
    (-8) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s83N2`. -/
noncomputable def i8Psi4s83dN2 (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s83N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s83N2 (i8Psi4s83dN2 x) x := by
  unfold i8Psi4s83N2 i8Psi4s83dN2
  exact (((hasDerivAt_hpl_cons zero [zero] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₄⁽83⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s83N3 (x : ℝ) : ℝ :=
    (22) +
    (-22) * hpl [zero] x +
    (26) * hpl [zero, zero] x +
    (-18) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s83N3`. -/
noncomputable def i8Psi4s83dN3 (x : ℝ) : ℝ :=
    0 +
    (-22) * (zero.kernel x * hpl [] x) +
    (26) * (zero.kernel x * hpl [zero] x) +
    (-18) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s83N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s83N3 (i8Psi4s83dN3 x) x := by
  unfold i8Psi4s83N3 i8Psi4s83dN3
  exact ((((hasDerivAt_const x (22)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (26))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-18)))

/-- The part of `ξ² Ψ₄⁽83⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s83N4 (x : ℝ) : ℝ :=
    (19 / 8) +
    (-19 / 4) * hpl [zero] x +
    (11 / 2) * hpl [zero, zero] x +
    (-3) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s83N4`. -/
noncomputable def i8Psi4s83dN4 (x : ℝ) : ℝ :=
    0 +
    (-19 / 4) * (zero.kernel x * hpl [] x) +
    (11 / 2) * (zero.kernel x * hpl [zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s83N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s83N4 (i8Psi4s83dN4 x) x := by
  unfold i8Psi4s83N4 i8Psi4s83dN4
  exact ((((hasDerivAt_const x (19 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-19 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (11 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-3)))

/-- The part of `Ψ₄⁽83⁾` with constant coefficients. -/
noncomputable def i8Psi4s83W (x : ℝ) : ℝ :=
    (-18) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s83W`. -/
noncomputable def i8Psi4s83dW (x : ℝ) : ℝ :=
    (-18) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s83W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s83W (i8Psi4s83dW x) x := by
  unfold i8Psi4s83W i8Psi4s83dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-18))

/-- The piece `Ψ₄⁽83⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s83 (x : ℝ) : ℝ :=
  (i8Psi4s83N0 x + x * i8Psi4s83N1 x + x ^ 2 * i8Psi4s83N2 x + x ^ 3 * i8Psi4s83N3 x +
    x ^ 4 * i8Psi4s83N4 x) / x ^ 2 + i8Psi4s83W x

/-- The derivative of `Ψ₄⁽83⁾`. -/
noncomputable def i8Psi4s83D (x : ℝ) : ℝ :=
  ((i8Psi4s83dN0 x + (i8Psi4s83N1 x + x * i8Psi4s83dN1 x) + (2 * x * i8Psi4s83N2 x +
    x ^ 2 * i8Psi4s83dN2 x) + (3 * x ^ 2 * i8Psi4s83N3 x + x ^ 3 * i8Psi4s83dN3 x) +
    (4 * x ^ 3 * i8Psi4s83N4 x + x ^ 4 * i8Psi4s83dN4 x)) * x ^ 2 - (i8Psi4s83N0 x +
    x * i8Psi4s83N1 x + x ^ 2 * i8Psi4s83N2 x + x ^ 3 * i8Psi4s83N3 x +
    x ^ 4 * i8Psi4s83N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s83dW x

theorem hasDerivAt_i8Psi4s83 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s83 (i8Psi4s83D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s83N0 hx).add (X.mul (hasDerivAt_i8Psi4s83N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s83N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s83N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s83N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s83W hx)
  unfold i8Psi4s83
  refine e.congr_deriv ?_
  unfold i8Psi4s83D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 83 of `p₄` in `ξ`: from `t B2 A1 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s83 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x * (2 + Real.log x * (1 + x) / (1 - x)) * (2 + Real.log x * (1 +
    x) / (1 - x)) * ((1 + x) / (1 - x) * (x / (1 + x)))

/-- `p₄⁽83⁾` written over words. -/
noncomputable def i8P4w83 (x : ℝ) : ℝ :=
    (4 - 4 * x) * hpl [zero] x +
    (8 + 8 * x) * hpl [zero, zero] x +
    ((6 + 6 * x ^ 2 + 12 * x) / ((1 - x))) * hpl [zero, zero, zero] x

theorem i8P4s83_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s83 x = i8P4w83 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s83 i8P4w83
  simp only [hpl_zero, i13hw_00, i13hw_000]
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

/-- **`(Ψ₄⁽83⁾)'(ξ) ξ' = p₄⁽83⁾`**, in terms of `ξ`. -/
theorem i8Psi4s83D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s83D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s83 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s83_eq_w hx]
  unfold i8Psi4s83D i8Psi4s83N0 i8Psi4s83N1 i8Psi4s83N2 i8Psi4s83N3 i8Psi4s83N4 i8Psi4s83dN0
    i8Psi4s83dN1 i8Psi4s83dN2 i8Psi4s83dN3 i8Psi4s83dN4 i8Psi4s83dW i8P4w83
  simp only [kernel_zero, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero] x = v1 at *
  generalize hpl [zero, zero] x = v2 at *
  generalize hpl [zero] x = v3 at *
  ring

/-- The part of `ξ² Ψ₄⁽84⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s84N0 (x : ℝ) : ℝ :=
    (-19 / 8) * hpl [negOne] x +
    (-19 / 4) * hpl [negOne, zero] x +
    (-19 / 4) * hpl [zero, negOne] x +
    (-11 / 2) * hpl [negOne, zero, zero] x +
    (-11 / 2) * hpl [zero, negOne, zero] x +
    (-11 / 2) * hpl [zero, zero, negOne] x +
    (-3) * hpl [negOne, zero, zero, zero] x +
    (-3) * hpl [zero, negOne, zero, zero] x +
    (-3) * hpl [zero, zero, negOne, zero] x +
    (-3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s84N0`. -/
noncomputable def i8Psi4s84dN0 (x : ℝ) : ℝ :=
    (-19 / 8) * (negOne.kernel x * hpl [] x) +
    (-19 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-19 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-11 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-3) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-3) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s84N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s84N0 (i8Psi4s84dN0 x) x := by
  unfold i8Psi4s84N0 i8Psi4s84dN0
  exact (((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-19 / 8)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-19 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-19 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3)))

/-- The part of `ξ² Ψ₄⁽84⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s84N1 (x : ℝ) : ℝ :=
    (-125 / 8) +
    (-40) * hpl [negOne] x +
    (-53 / 4) * hpl [zero] x +
    (-40) * hpl [negOne, zero] x +
    (-40) * hpl [zero, negOne] x +
    (-17 / 2) * hpl [zero, zero] x +
    (-40) * hpl [negOne, zero, zero] x +
    (-40) * hpl [zero, negOne, zero] x +
    (-40) * hpl [zero, zero, negOne] x +
    (-3) * hpl [zero, zero, zero] x +
    (-24) * hpl [negOne, zero, zero, zero] x +
    (-24) * hpl [zero, negOne, zero, zero] x +
    (-24) * hpl [zero, zero, negOne, zero] x +
    (-24) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s84N1`. -/
noncomputable def i8Psi4s84dN1 (x : ℝ) : ℝ :=
    0 +
    (-40) * (negOne.kernel x * hpl [] x) +
    (-53 / 4) * (zero.kernel x * hpl [] x) +
    (-40) * (negOne.kernel x * hpl [zero] x) +
    (-40) * (zero.kernel x * hpl [negOne] x) +
    (-17 / 2) * (zero.kernel x * hpl [zero] x) +
    (-40) * (negOne.kernel x * hpl [zero, zero] x) +
    (-40) * (zero.kernel x * hpl [negOne, zero] x) +
    (-40) * (zero.kernel x * hpl [zero, negOne] x) +
    (-3) * (zero.kernel x * hpl [zero, zero] x) +
    (-24) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (-24) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s84N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s84N1 (i8Psi4s84dN1 x) x := by
  unfold i8Psi4s84N1 i8Psi4s84dN1
  exact ((((((((((((((hasDerivAt_const x (-125 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-53 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-17 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-24)))

/-- The part of `ξ² Ψ₄⁽84⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s84N2 (x : ℝ) : ℝ :=
    (-301 / 4) * hpl [negOne] x +
    (301 / 8) * hpl [zero] x +
    (141 / 4) * hpl [zero, zero] x +
    (-69) * hpl [negOne, zero, zero] x +
    (-8) * hpl [zero, negOne, zero] x +
    (-8) * hpl [zero, zero, negOne] x +
    (69 / 2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s84N2`. -/
noncomputable def i8Psi4s84dN2 (x : ℝ) : ℝ :=
    (-301 / 4) * (negOne.kernel x * hpl [] x) +
    (301 / 8) * (zero.kernel x * hpl [] x) +
    (141 / 4) * (zero.kernel x * hpl [zero] x) +
    (-69) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, negOne] x) +
    (69 / 2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s84N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s84N2 (i8Psi4s84dN2 x) x := by
  unfold i8Psi4s84N2 i8Psi4s84dN2
  exact ((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-301 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (301 / 8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (141 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-69))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (69 / 2)))

/-- The part of `ξ² Ψ₄⁽84⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s84N3 (x : ℝ) : ℝ :=
    (1027 / 8) +
    (-40) * hpl [negOne] x +
    (-363 / 4) * hpl [zero] x +
    (40) * hpl [negOne, zero] x +
    (40) * hpl [zero, negOne] x +
    (111 / 2) * hpl [zero, zero] x +
    (-40) * hpl [negOne, zero, zero] x +
    (-40) * hpl [zero, negOne, zero] x +
    (-40) * hpl [zero, zero, negOne] x +
    (-21) * hpl [zero, zero, zero] x +
    (24) * hpl [negOne, zero, zero, zero] x +
    (24) * hpl [zero, negOne, zero, zero] x +
    (24) * hpl [zero, zero, negOne, zero] x +
    (24) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s84N3`. -/
noncomputable def i8Psi4s84dN3 (x : ℝ) : ℝ :=
    0 +
    (-40) * (negOne.kernel x * hpl [] x) +
    (-363 / 4) * (zero.kernel x * hpl [] x) +
    (40) * (negOne.kernel x * hpl [zero] x) +
    (40) * (zero.kernel x * hpl [negOne] x) +
    (111 / 2) * (zero.kernel x * hpl [zero] x) +
    (-40) * (negOne.kernel x * hpl [zero, zero] x) +
    (-40) * (zero.kernel x * hpl [negOne, zero] x) +
    (-40) * (zero.kernel x * hpl [zero, negOne] x) +
    (-21) * (zero.kernel x * hpl [zero, zero] x) +
    (24) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (24) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (24) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (24) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s84N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s84N3 (i8Psi4s84dN3 x) x := by
  unfold i8Psi4s84N3 i8Psi4s84dN3
  exact ((((((((((((((hasDerivAt_const x (1027 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-363 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (111 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-21))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (24)))

/-- The part of `ξ² Ψ₄⁽84⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s84N4 (x : ℝ) : ℝ :=
    (13 / 4) +
    (-19 / 8) * hpl [negOne] x +
    (-33 / 8) * hpl [zero] x +
    (19 / 4) * hpl [negOne, zero] x +
    (19 / 4) * hpl [zero, negOne] x +
    (7 / 2) * hpl [zero, zero] x +
    (-11 / 2) * hpl [negOne, zero, zero] x +
    (-11 / 2) * hpl [zero, negOne, zero] x +
    (-11 / 2) * hpl [zero, zero, negOne] x +
    (-3 / 2) * hpl [zero, zero, zero] x +
    (3) * hpl [negOne, zero, zero, zero] x +
    (3) * hpl [zero, negOne, zero, zero] x +
    (3) * hpl [zero, zero, negOne, zero] x +
    (3) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s84N4`. -/
noncomputable def i8Psi4s84dN4 (x : ℝ) : ℝ :=
    0 +
    (-19 / 8) * (negOne.kernel x * hpl [] x) +
    (-33 / 8) * (zero.kernel x * hpl [] x) +
    (19 / 4) * (negOne.kernel x * hpl [zero] x) +
    (19 / 4) * (zero.kernel x * hpl [negOne] x) +
    (7 / 2) * (zero.kernel x * hpl [zero] x) +
    (-11 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-11 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-3 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (3) * (negOne.kernel x * hpl [zero, zero, zero] x) +
    (3) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (3) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (3) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s84N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s84N4 (i8Psi4s84dN4 x) x := by
  unfold i8Psi4s84N4 i8Psi4s84dN4
  exact ((((((((((((((hasDerivAt_const x (13 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-19 / 8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-33 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (19 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (19 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-11 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (3)))

/-- The part of `Ψ₄⁽84⁾` with constant coefficients. -/
noncomputable def i8Psi4s84W (x : ℝ) : ℝ :=
    (21) * hpl [zero, zero, zero, zero] x +
    (36) * hpl [zero, negOne, zero, zero, zero] x +
    (36) * hpl [zero, zero, negOne, zero, zero] x +
    (36) * hpl [zero, zero, zero, negOne, zero] x +
    (36) * hpl [zero, zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s84W`. -/
noncomputable def i8Psi4s84dW (x : ℝ) : ℝ :=
    (21) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (36) * (zero.kernel x * hpl [negOne, zero, zero, zero] x) +
    (36) * (zero.kernel x * hpl [zero, negOne, zero, zero] x) +
    (36) * (zero.kernel x * hpl [zero, zero, negOne, zero] x) +
    (36) * (zero.kernel x * hpl [zero, zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s84W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s84W (i8Psi4s84dW x) x := by
  unfold i8Psi4s84W i8Psi4s84dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (21)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (36))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, negOne] hx).const_mul (36)))

/-- The piece `Ψ₄⁽84⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s84 (x : ℝ) : ℝ :=
  (i8Psi4s84N0 x + x * i8Psi4s84N1 x + x ^ 2 * i8Psi4s84N2 x + x ^ 3 * i8Psi4s84N3 x +
    x ^ 4 * i8Psi4s84N4 x) / x ^ 2 + i8Psi4s84W x

/-- The derivative of `Ψ₄⁽84⁾`. -/
noncomputable def i8Psi4s84D (x : ℝ) : ℝ :=
  ((i8Psi4s84dN0 x + (i8Psi4s84N1 x + x * i8Psi4s84dN1 x) + (2 * x * i8Psi4s84N2 x +
    x ^ 2 * i8Psi4s84dN2 x) + (3 * x ^ 2 * i8Psi4s84N3 x + x ^ 3 * i8Psi4s84dN3 x) +
    (4 * x ^ 3 * i8Psi4s84N4 x + x ^ 4 * i8Psi4s84dN4 x)) * x ^ 2 - (i8Psi4s84N0 x +
    x * i8Psi4s84N1 x + x ^ 2 * i8Psi4s84N2 x + x ^ 3 * i8Psi4s84N3 x +
    x ^ 4 * i8Psi4s84N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s84dW x

theorem hasDerivAt_i8Psi4s84 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s84 (i8Psi4s84D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s84N0 hx).add (X.mul (hasDerivAt_i8Psi4s84N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s84N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s84N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s84N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s84W hx)
  unfold i8Psi4s84
  refine e.congr_deriv ?_
  unfold i8Psi4s84D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 84 of `p₄` in `ξ`: from `t B2 A1 (-λ)^1/1!`, the term with `log^0 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s84 (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * Real.log x * (2 + Real.log x * (1 + x) / (1 - x)) * (2 + Real.log x * (1 +
    x) / (1 - x)) * ((1 + x) / (1 - x) * (-hpl [negOne] x))

/-- `p₄⁽84⁾` written over words. -/
noncomputable def i8P4w84 (x : ℝ) : ℝ :=
    ((-4 + 4 * x ^ 2) / (x)) * hpl [negOne, zero] x +
    ((-4 + 4 * x ^ 2) / (x)) * hpl [zero, negOne] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [negOne, zero, zero] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [zero, negOne, zero] x +
    ((-8 - 16 * x - 8 * x ^ 2) / (x)) * hpl [zero, zero, negOne] x +
    ((-6 - 18 * x - 18 * x ^ 2 - 6 * x ^ 3) / (x * (1 - x))) * hpl [negOne, zero, zero, zero] x +
    ((-6 - 18 * x - 18 * x ^ 2 - 6 * x ^ 3) / (x * (1 - x))) * hpl [zero, negOne, zero, zero] x +
    ((-6 - 18 * x - 18 * x ^ 2 - 6 * x ^ 3) / (x * (1 - x))) * hpl [zero, zero, negOne, zero] x +
    ((-6 - 18 * x - 18 * x ^ 2 - 6 * x ^ 3) / (x * (1 - x))) * hpl [zero, zero, zero, negOne] x

theorem i8P4s84_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s84 x = i8P4w84 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s84 i8P4w84
  simp only [i13hw_m0 hx, i13hw_0m0 hx, i13hw_m00 hx, i13hw_00m0 hx, i13hw_0m00 hx, i13hw_m000 hx]
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
  generalize hpl [zero, zero, zero, zero, one] x = v26 at *
  generalize hpl [zero, zero, zero, one, negOne] x = v27 at *
  generalize hpl [zero, zero, zero, one, one] x = v28 at *
  generalize hpl [zero, zero, one, negOne, negOne] x = v29 at *
  generalize hpl [zero, zero, one, negOne, one] x = v30 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v31 at *
  generalize hpl [zero, zero, one, zero, one] x = v32 at *
  generalize hpl [zero, zero, one, one, negOne] x = v33 at *
  generalize hpl [zero, zero, one, one, one] x = v34 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v35 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v36 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v37 at *
  generalize hpl [zero, one, negOne, one, one] x = v38 at *
  generalize hpl [zero, one, zero, one, negOne] x = v39 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v40 at *
  generalize hpl [zero, one, one, negOne, one] x = v41 at *
  generalize hpl [zero, one, one, one, negOne] x = v42 at *
  generalize hpl [zero, one, one, one, one] x = v43 at *
  generalize hpl [negOne, negOne, one, one] x = v44 at *
  generalize hpl [negOne, zero, zero, zero] x = v45 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v46 at *
  generalize hpl [zero, negOne, negOne, one] x = v47 at *
  generalize hpl [zero, negOne, zero, zero] x = v48 at *
  generalize hpl [zero, negOne, zero, one] x = v49 at *
  generalize hpl [zero, negOne, one, negOne] x = v50 at *
  generalize hpl [zero, negOne, one, one] x = v51 at *
  generalize hpl [zero, zero, negOne, negOne] x = v52 at *
  generalize hpl [zero, zero, negOne, zero] x = v53 at *
  generalize hpl [zero, zero, negOne, one] x = v54 at *
  generalize hpl [zero, zero, zero, negOne] x = v55 at *
  generalize hpl [zero, zero, zero, zero] x = v56 at *
  generalize hpl [zero, zero, zero, one] x = v57 at *
  generalize hpl [zero, zero, one, negOne] x = v58 at *
  generalize hpl [zero, zero, one, one] x = v59 at *
  generalize hpl [zero, one, negOne, negOne] x = v60 at *
  generalize hpl [zero, one, negOne, one] x = v61 at *
  generalize hpl [zero, one, one, negOne] x = v62 at *
  generalize hpl [zero, one, one, one] x = v63 at *
  generalize hpl [negOne, negOne, one] x = v64 at *
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

/-- **`(Ψ₄⁽84⁾)'(ξ) ξ' = p₄⁽84⁾`**, in terms of `ξ`. -/
theorem i8Psi4s84D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s84D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s84 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s84_eq_w hx]
  unfold i8Psi4s84D i8Psi4s84N0 i8Psi4s84N1 i8Psi4s84N2 i8Psi4s84N3 i8Psi4s84N4 i8Psi4s84dN0
    i8Psi4s84dN1 i8Psi4s84dN2 i8Psi4s84dN3 i8Psi4s84dN4 i8Psi4s84dW i8P4w84
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, zero, zero] x = v1 at *
  generalize hpl [zero, zero, zero, negOne, zero] x = v2 at *
  generalize hpl [zero, zero, zero, zero, negOne] x = v3 at *
  generalize hpl [negOne, zero, zero, zero] x = v4 at *
  generalize hpl [zero, negOne, zero, zero] x = v5 at *
  generalize hpl [zero, zero, negOne, zero] x = v6 at *
  generalize hpl [zero, zero, zero, negOne] x = v7 at *
  generalize hpl [zero, zero, zero, zero] x = v8 at *
  generalize hpl [negOne, zero, zero] x = v9 at *
  generalize hpl [zero, negOne, zero] x = v10 at *
  generalize hpl [zero, zero, negOne] x = v11 at *
  generalize hpl [zero, zero, zero] x = v12 at *
  generalize hpl [negOne, zero] x = v13 at *
  generalize hpl [zero, negOne] x = v14 at *
  generalize hpl [zero, zero] x = v15 at *
  generalize hpl [negOne] x = v16 at *
  generalize hpl [zero] x = v17 at *
  ring

end QED.ThreeLoopD
