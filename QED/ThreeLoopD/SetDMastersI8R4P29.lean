/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P28

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 109 to 112

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s109`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s109D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s109`, `QED.ThreeLoopD.i8Psi4s109D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽109⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s109N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s109N0`. -/
noncomputable def i8Psi4s109dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s109N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s109N0 (i8Psi4s109dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽109⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s109N1 (x : ℝ) : ℝ :=
    (2) +
    (2) * hpl [zero] x +
    (2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s109N1`. -/
noncomputable def i8Psi4s109dN1 (x : ℝ) : ℝ :=
    0 +
    (2) * (zero.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s109N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s109N1 (i8Psi4s109dN1 x) x := by
  unfold i8Psi4s109N1 i8Psi4s109dN1
  exact (((hasDerivAt_const x (2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽109⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s109N2 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s109N2`. -/
noncomputable def i8Psi4s109dN2 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s109N2 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s109N2 (i8Psi4s109dN2 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽109⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s109N3 (x : ℝ) : ℝ :=
    (2) +
    (-2) * hpl [zero] x +
    (2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s109N3`. -/
noncomputable def i8Psi4s109dN3 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s109N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s109N3 (i8Psi4s109dN3 x) x := by
  unfold i8Psi4s109N3 i8Psi4s109dN3
  exact (((hasDerivAt_const x (2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2)))

/-- The part of `ξ² Ψ₄⁽109⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s109N4 (x : ℝ) : ℝ :=
    (-1 / 4) +
    (1 / 2) * hpl [zero] x +
    (-1) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s109N4`. -/
noncomputable def i8Psi4s109dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s109N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s109N4 (i8Psi4s109dN4 x) x := by
  unfold i8Psi4s109N4 i8Psi4s109dN4
  exact (((hasDerivAt_const x (-1 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1)))

/-- The part of `Ψ₄⁽109⁾` with constant coefficients. -/
noncomputable def i8Psi4s109W (x : ℝ) : ℝ :=
    (2) * hpl [zero, zero, zero] x

/-- The derivative of `i8Psi4s109W`. -/
noncomputable def i8Psi4s109dW (x : ℝ) : ℝ :=
    (2) * (zero.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s109W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s109W (i8Psi4s109dW x) x := by
  unfold i8Psi4s109W i8Psi4s109dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (2))

/-- The piece `Ψ₄⁽109⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s109 (x : ℝ) : ℝ :=
  (i8Psi4s109N0 x + x * i8Psi4s109N1 x + x ^ 2 * i8Psi4s109N2 x + x ^ 3 * i8Psi4s109N3 x +
    x ^ 4 * i8Psi4s109N4 x) / x ^ 2 + i8Psi4s109W x

/-- The derivative of `Ψ₄⁽109⁾`. -/
noncomputable def i8Psi4s109D (x : ℝ) : ℝ :=
  ((i8Psi4s109dN0 x + (i8Psi4s109N1 x + x * i8Psi4s109dN1 x) + (2 * x * i8Psi4s109N2 x +
    x ^ 2 * i8Psi4s109dN2 x) + (3 * x ^ 2 * i8Psi4s109N3 x + x ^ 3 * i8Psi4s109dN3 x) +
    (4 * x ^ 3 * i8Psi4s109N4 x + x ^ 4 * i8Psi4s109dN4 x)) * x ^ 2 - (i8Psi4s109N0 x +
    x * i8Psi4s109N1 x + x ^ 2 * i8Psi4s109N2 x + x ^ 3 * i8Psi4s109N3 x +
    x ^ 4 * i8Psi4s109N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s109dW x

theorem hasDerivAt_i8Psi4s109 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s109 (i8Psi4s109D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s109N0 hx).add (X.mul (hasDerivAt_i8Psi4s109N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s109N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s109N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s109N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s109W hx)
  unfold i8Psi4s109
  refine e.congr_deriv ?_
  unfold i8Psi4s109D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 109 of `p₄` in `ξ`: from `t B0 A2 (-λ)^2/2!`, the term with `log^0 (1 -
  ξ) log^2 ξ`. -/
noncomputable def i8P4s109 (x : ℝ) : ℝ :=
  (1 / 2) * (1 - x) ^ 2 / x * Real.log x ^ 2 * ((1 + x) / (1 - x) * (2 * x / (1 + x)))

/-- `p₄⁽109⁾` written over words. -/
noncomputable def i8P4w109 (x : ℝ) : ℝ :=
    (2 - 2 * x) * hpl [zero, zero] x

theorem i8P4s109_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s109 x = i8P4w109 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s109 i8P4w109
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  linear_combination (norm := skip) ((1 - x)) * e0
  field_simp
  generalize hpl [zero, zero] x = v0 at *
  generalize hpl [zero] x = v1 at *
  ring

/-- **`(Ψ₄⁽109⁾)'(ξ) ξ' = p₄⁽109⁾`**, in terms of `ξ`. -/
theorem i8Psi4s109D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s109D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s109 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s109_eq_w hx]
  unfold i8Psi4s109D i8Psi4s109N0 i8Psi4s109N1 i8Psi4s109N2 i8Psi4s109N3 i8Psi4s109N4 i8Psi4s109dN0
    i8Psi4s109dN1 i8Psi4s109dN2 i8Psi4s109dN3 i8Psi4s109dN4 i8Psi4s109dW i8P4w109
  simp only [kernel_zero, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero] x = v1 at *
  generalize hpl [zero] x = v2 at *
  ring

/-- The part of `ξ² Ψ₄⁽110⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s110N0 (x : ℝ) : ℝ :=
    (-1 / 8) * hpl [negOne] x +
    (-1 / 4) * hpl [negOne, zero] x +
    (-1 / 4) * hpl [zero, negOne] x +
    (-1 / 2) * hpl [negOne, zero, zero] x +
    (-1 / 2) * hpl [zero, negOne, zero] x +
    (-1 / 2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s110N0`. -/
noncomputable def i8Psi4s110dN0 (x : ℝ) : ℝ :=
    (-1 / 8) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s110N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s110N0 (i8Psi4s110dN0 x) x := by
  unfold i8Psi4s110N0 i8Psi4s110dN0
  exact (((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 8)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1 / 2)))

/-- The part of `ξ² Ψ₄⁽110⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s110N1 (x : ℝ) : ℝ :=
    (-7 / 8) +
    (-3 / 4) * hpl [zero] x +
    (-1 / 2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s110N1`. -/
noncomputable def i8Psi4s110dN1 (x : ℝ) : ℝ :=
    0 +
    (-3 / 4) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s110N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s110N1 (i8Psi4s110dN1 x) x := by
  unfold i8Psi4s110N1 i8Psi4s110dN1
  exact (((hasDerivAt_const x (-7 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 2)))

/-- The part of `ξ² Ψ₄⁽110⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s110N2 (x : ℝ) : ℝ :=
    (-1 / 8) * hpl [zero] x +
    (1 / 2) * hpl [negOne, zero] x +
    (-1 / 4) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s110N2`. -/
noncomputable def i8Psi4s110dN2 (x : ℝ) : ℝ :=
    (-1 / 8) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s110N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s110N2 (i8Psi4s110dN2 x) x := by
  unfold i8Psi4s110N2 i8Psi4s110dN2
  exact ((((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 8)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 4)))

/-- The part of `ξ² Ψ₄⁽110⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s110N3 (x : ℝ) : ℝ :=
    (7 / 8) +
    (-3 / 4) * hpl [zero] x +
    (1 / 2) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s110N3`. -/
noncomputable def i8Psi4s110dN3 (x : ℝ) : ℝ :=
    0 +
    (-3 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s110N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s110N3 (i8Psi4s110dN3 x) x := by
  unfold i8Psi4s110N3 i8Psi4s110dN3
  exact (((hasDerivAt_const x (7 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽110⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s110N4 (x : ℝ) : ℝ :=
    (-3 / 16) +
    (1 / 8) * hpl [negOne] x +
    (1 / 4) * hpl [zero] x +
    (-1 / 4) * hpl [negOne, zero] x +
    (-1 / 4) * hpl [zero, negOne] x +
    (-1 / 4) * hpl [zero, zero] x +
    (1 / 2) * hpl [negOne, zero, zero] x +
    (1 / 2) * hpl [zero, negOne, zero] x +
    (1 / 2) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s110N4`. -/
noncomputable def i8Psi4s110dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 8) * (negOne.kernel x * hpl [] x) +
    (1 / 4) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s110N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s110N4 (i8Psi4s110dN4 x) x := by
  unfold i8Psi4s110N4 i8Psi4s110dN4
  exact (((((((((hasDerivAt_const x (-3 / 16)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1 / 2)))

/-- The part of `Ψ₄⁽110⁾` with constant coefficients. -/
noncomputable def i8Psi4s110W (x : ℝ) : ℝ :=
    (-1 / 2) * hpl [zero, zero, zero] x +
    (-2) * hpl [zero, negOne, zero, zero] x +
    (-2) * hpl [zero, zero, negOne, zero] x +
    (-2) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s110W`. -/
noncomputable def i8Psi4s110dW (x : ℝ) : ℝ :=
    (-1 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s110W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s110W (i8Psi4s110dW x) x := by
  unfold i8Psi4s110W i8Psi4s110dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1 / 2)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-2)))

/-- The piece `Ψ₄⁽110⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s110 (x : ℝ) : ℝ :=
  (i8Psi4s110N0 x + x * i8Psi4s110N1 x + x ^ 2 * i8Psi4s110N2 x + x ^ 3 * i8Psi4s110N3 x +
    x ^ 4 * i8Psi4s110N4 x) / x ^ 2 + i8Psi4s110W x

/-- The derivative of `Ψ₄⁽110⁾`. -/
noncomputable def i8Psi4s110D (x : ℝ) : ℝ :=
  ((i8Psi4s110dN0 x + (i8Psi4s110N1 x + x * i8Psi4s110dN1 x) + (2 * x * i8Psi4s110N2 x +
    x ^ 2 * i8Psi4s110dN2 x) + (3 * x ^ 2 * i8Psi4s110N3 x + x ^ 3 * i8Psi4s110dN3 x) +
    (4 * x ^ 3 * i8Psi4s110N4 x + x ^ 4 * i8Psi4s110dN4 x)) * x ^ 2 - (i8Psi4s110N0 x +
    x * i8Psi4s110N1 x + x ^ 2 * i8Psi4s110N2 x + x ^ 3 * i8Psi4s110N3 x +
    x ^ 4 * i8Psi4s110N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s110dW x

theorem hasDerivAt_i8Psi4s110 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s110 (i8Psi4s110D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s110N0 hx).add (X.mul (hasDerivAt_i8Psi4s110N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s110N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s110N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s110N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s110W hx)
  unfold i8Psi4s110
  refine e.congr_deriv ?_
  unfold i8Psi4s110D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 110 of `p₄` in `ξ`: from `t B0 A2 (-λ)^2/2!`, the term with `log^0 (1 -
  ξ) log^2 ξ`. -/
noncomputable def i8P4s110 (x : ℝ) : ℝ :=
  (1 / 2) * (1 - x) ^ 2 / x * Real.log x ^ 2 * ((1 + x) / (1 - x) * (-hpl [negOne] x))

/-- `p₄⁽110⁾` written over words. -/
noncomputable def i8P4w110 (x : ℝ) : ℝ :=
    ((-1 + x ^ 2) / (x)) * hpl [negOne, zero, zero] x +
    ((-1 + x ^ 2) / (x)) * hpl [zero, negOne, zero] x +
    ((-1 + x ^ 2) / (x)) * hpl [zero, zero, negOne] x

theorem i8P4s110_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s110 x = i8P4w110 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s110 i8P4w110
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [zero] hx
  have e1 := hpl_mul_hpl [negOne] [zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  linear_combination (norm := skip) (((-1 / 2 + x ^ 2 / 2) / (x)) * hpl [negOne] x) * e0 + (((-1 +
    x ^ 2) / (x))) * e1
  field_simp
  generalize hpl [negOne, zero, zero] x = v0 at *
  generalize hpl [zero, negOne, zero] x = v1 at *
  generalize hpl [zero, zero, negOne] x = v2 at *
  generalize hpl [zero, zero] x = v3 at *
  generalize hpl [negOne] x = v4 at *
  generalize hpl [zero] x = v5 at *
  ring

/-- **`(Ψ₄⁽110⁾)'(ξ) ξ' = p₄⁽110⁾`**, in terms of `ξ`. -/
theorem i8Psi4s110D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s110D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s110 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s110_eq_w hx]
  unfold i8Psi4s110D i8Psi4s110N0 i8Psi4s110N1 i8Psi4s110N2 i8Psi4s110N3 i8Psi4s110N4 i8Psi4s110dN0
    i8Psi4s110dN1 i8Psi4s110dN2 i8Psi4s110dN3 i8Psi4s110dN4 i8Psi4s110dW i8P4w110
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, negOne, zero, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, zero] x = v1 at *
  generalize hpl [zero, zero, zero, negOne] x = v2 at *
  generalize hpl [negOne, zero, zero] x = v3 at *
  generalize hpl [zero, negOne, zero] x = v4 at *
  generalize hpl [zero, zero, negOne] x = v5 at *
  generalize hpl [zero, zero, zero] x = v6 at *
  generalize hpl [negOne, zero] x = v7 at *
  generalize hpl [zero, negOne] x = v8 at *
  generalize hpl [zero, zero] x = v9 at *
  generalize hpl [negOne] x = v10 at *
  generalize hpl [zero] x = v11 at *
  ring

/-- The part of `ξ² Ψ₄⁽111⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s111k0N0 (x : ℝ) : ℝ :=
    (1 / 2) * hpl [negOne, negOne, zero] x +
    (1) * hpl [negOne, negOne, zero, zero] x +
    (1) * hpl [negOne, zero, negOne, zero] x +
    (1) * hpl [negOne, zero, zero, negOne] x +
    (1) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s111k0N0`. -/
noncomputable def i8Psi4s111k0dN0 (x : ℝ) : ℝ :=
    (1 / 2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (1) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (1) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (1) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s111k0N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k0N0 (i8Psi4s111k0dN0 x) x := by
  unfold i8Psi4s111k0N0 i8Psi4s111k0dN0
  exact ((((((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (1 / 2)).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽111⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s111k0N1 (x : ℝ) : ℝ :=
    (1) * hpl [negOne] x +
    (3 / 2) * hpl [negOne, zero] x +
    (1) * hpl [zero, negOne] x +
    (1) * hpl [negOne, zero, zero] x +
    (1) * hpl [zero, negOne, zero] x +
    (1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s111k0N1`. -/
noncomputable def i8Psi4s111k0dN1 (x : ℝ) : ℝ :=
    (1) * (negOne.kernel x * hpl [] x) +
    (3 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne] x) +
    (1) * (negOne.kernel x * hpl [zero, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, zero] x) +
    (1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s111k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k0N1 (i8Psi4s111k0dN1 x) x := by
  unfold i8Psi4s111k0N1 i8Psi4s111k0dN1
  exact (((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽111⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s111k0N2 (x : ℝ) : ℝ :=
    (-1 / 8) * hpl [negOne] x +
    (-1) * hpl [zero] x +
    (7 / 2) * hpl [negOne, zero] x +
    (-3 / 2) * hpl [zero, zero] x +
    (-1) * hpl [negOne, negOne, zero] x +
    (-1 / 2) * hpl [negOne, zero, zero] x +
    (1 / 2) * hpl [zero, negOne, zero] x

/-- The derivative of `i8Psi4s111k0N2`. -/
noncomputable def i8Psi4s111k0dN2 (x : ℝ) : ℝ :=
    (-1 / 8) * (negOne.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [] x) +
    (7 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-3 / 2) * (zero.kernel x * hpl [zero] x) +
    (-1) * (negOne.kernel x * hpl [negOne, zero] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi4s111k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k0N2 (i8Psi4s111k0dN2 x) x := by
  unfold i8Psi4s111k0N2 i8Psi4s111k0dN2
  exact ((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽111⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s111k0N3 (x : ℝ) : ℝ :=
    (37 / 8) +
    (-1) * hpl [negOne] x +
    (-7 / 2) * hpl [zero] x +
    (3 / 2) * hpl [negOne, zero] x +
    (1) * hpl [zero, negOne] x +
    (3 / 2) * hpl [zero, zero] x +
    (-1) * hpl [negOne, zero, zero] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-1) * hpl [zero, zero, negOne] x

/-- The derivative of `i8Psi4s111k0N3`. -/
noncomputable def i8Psi4s111k0dN3 (x : ℝ) : ℝ :=
    0 +
    (-1) * (negOne.kernel x * hpl [] x) +
    (-7 / 2) * (zero.kernel x * hpl [] x) +
    (3 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [negOne] x) +
    (3 / 2) * (zero.kernel x * hpl [zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s111k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k0N3 (i8Psi4s111k0dN3 x) x := by
  unfold i8Psi4s111k0N3 i8Psi4s111k0dN3
  exact (((((((((hasDerivAt_const x (37 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-7 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽111⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s111k0N4 (x : ℝ) : ℝ :=
    (-1 / 4) +
    (1 / 8) * hpl [negOne] x +
    (3 / 8) * hpl [zero] x +
    (-1 / 2) * hpl [negOne, zero] x +
    (-1 / 4) * hpl [zero, negOne] x +
    (-1 / 4) * hpl [zero, zero] x +
    (1 / 2) * hpl [negOne, negOne, zero] x +
    (1 / 2) * hpl [negOne, zero, zero] x +
    (1 / 2) * hpl [zero, negOne, zero] x +
    (1 / 2) * hpl [zero, zero, negOne] x +
    (-1) * hpl [negOne, negOne, zero, zero] x +
    (-1) * hpl [negOne, zero, negOne, zero] x +
    (-1) * hpl [negOne, zero, zero, negOne] x +
    (-1) * hpl [zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s111k0N4`. -/
noncomputable def i8Psi4s111k0dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 8) * (negOne.kernel x * hpl [] x) +
    (3 / 8) * (zero.kernel x * hpl [] x) +
    (-1 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (negOne.kernel x * hpl [negOne, zero] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1) * (negOne.kernel x * hpl [negOne, zero, zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne, zero] x) +
    (-1) * (negOne.kernel x * hpl [zero, zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s111k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k0N4 (i8Psi4s111k0dN4 x) x := by
  unfold i8Psi4s111k0N4 i8Psi4s111k0dN4
  exact ((((((((((((((hasDerivAt_const x (-1 / 4)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (3 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons negOne [negOne, zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero] hx).const_mul (-1)))

/-- The part of `Ψ₄⁽111⁾` with constant coefficients. -/
noncomputable def i8Psi4s111k0W (x : ℝ) : ℝ :=
    (-1) * hpl [zero, zero, zero] x +
    (1) * hpl [zero, negOne, zero, zero] x +
    (1) * hpl [zero, zero, negOne, zero] x +
    (1) * hpl [zero, zero, zero, negOne] x +
    (4) * hpl [zero, negOne, negOne, zero, zero] x +
    (4) * hpl [zero, negOne, zero, negOne, zero] x +
    (4) * hpl [zero, negOne, zero, zero, negOne] x +
    (4) * hpl [zero, zero, negOne, negOne, zero] x

/-- The derivative of `i8Psi4s111k0W`. -/
noncomputable def i8Psi4s111k0dW (x : ℝ) : ℝ :=
    (-1) * (zero.kernel x * hpl [zero, zero] x) +
    (1) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (1) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (1) * (zero.kernel x * hpl [zero, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [negOne, negOne, zero, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, negOne, zero] x) +
    (4) * (zero.kernel x * hpl [negOne, zero, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, negOne, zero] x)

theorem hasDerivAt_i8Psi4s111k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k0W (i8Psi4s111k0dW x) x := by
  unfold i8Psi4s111k0W i8Psi4s111k0dW
  exact (((((((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne, zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne, zero] hx).const_mul (4)))

/-- Chunk 0 of the piece `Ψ₄⁽111⁾`. -/
noncomputable def i8Psi4s111k0 (x : ℝ) : ℝ :=
  (i8Psi4s111k0N0 x + x * i8Psi4s111k0N1 x + x ^ 2 * i8Psi4s111k0N2 x + x ^ 3 * i8Psi4s111k0N3 x +
    x ^ 4 * i8Psi4s111k0N4 x) / x ^ 2 + i8Psi4s111k0W x

/-- The derivative of `i8Psi4s111k0`. -/
noncomputable def i8Psi4s111k0D (x : ℝ) : ℝ :=
  ((i8Psi4s111k0dN0 x + (i8Psi4s111k0N1 x + x * i8Psi4s111k0dN1 x) + (2 * x * i8Psi4s111k0N2 x +
    x ^ 2 * i8Psi4s111k0dN2 x) + (3 * x ^ 2 * i8Psi4s111k0N3 x + x ^ 3 * i8Psi4s111k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s111k0N4 x + x ^ 4 * i8Psi4s111k0dN4 x)) * x ^ 2 - (i8Psi4s111k0N0 x +
    x * i8Psi4s111k0N1 x + x ^ 2 * i8Psi4s111k0N2 x + x ^ 3 * i8Psi4s111k0N3 x +
    x ^ 4 * i8Psi4s111k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s111k0dW x

theorem hasDerivAt_i8Psi4s111k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k0 (i8Psi4s111k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s111k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s111k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s111k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s111k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s111k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s111k0W hx)
  unfold i8Psi4s111k0
  refine e.congr_deriv ?_
  unfold i8Psi4s111k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽111⁾` over words. -/
noncomputable def i8P4w111k0 (x : ℝ) : ℝ :=
    ((2 - 2 * x ^ 2) / (x)) * hpl [negOne, negOne, zero, zero] x +
    ((2 - 2 * x ^ 2) / (x)) * hpl [negOne, zero, negOne, zero] x +
    ((2 - 2 * x ^ 2) / (x)) * hpl [negOne, zero, zero, negOne] x +
    ((2 - 2 * x ^ 2) / (x)) * hpl [zero, negOne, negOne, zero] x

theorem i8Psi4s111k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s111k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w111k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s111k0D i8Psi4s111k0N0 i8Psi4s111k0N1 i8Psi4s111k0N2 i8Psi4s111k0N3 i8Psi4s111k0N4
    i8Psi4s111k0dN0 i8Psi4s111k0dN1 i8Psi4s111k0dN2 i8Psi4s111k0dN3 i8Psi4s111k0dN4 i8Psi4s111k0dW
    i8P4w111k0
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  generalize hpl [zero, negOne, negOne, zero, zero] x = v0 at *
  generalize hpl [zero, negOne, zero, negOne, zero] x = v1 at *
  generalize hpl [zero, negOne, zero, zero, negOne] x = v2 at *
  generalize hpl [zero, zero, negOne, negOne, zero] x = v3 at *
  generalize hpl [negOne, negOne, zero, zero] x = v4 at *
  generalize hpl [negOne, zero, negOne, zero] x = v5 at *
  generalize hpl [negOne, zero, zero, negOne] x = v6 at *
  generalize hpl [zero, negOne, negOne, zero] x = v7 at *
  generalize hpl [zero, negOne, zero, zero] x = v8 at *
  generalize hpl [zero, zero, negOne, zero] x = v9 at *
  generalize hpl [zero, zero, zero, negOne] x = v10 at *
  generalize hpl [negOne, negOne, zero] x = v11 at *
  generalize hpl [negOne, zero, zero] x = v12 at *
  generalize hpl [zero, negOne, zero] x = v13 at *
  generalize hpl [zero, zero, negOne] x = v14 at *
  generalize hpl [zero, zero, zero] x = v15 at *
  generalize hpl [negOne, zero] x = v16 at *
  generalize hpl [zero, negOne] x = v17 at *
  generalize hpl [zero, zero] x = v18 at *
  generalize hpl [negOne] x = v19 at *
  generalize hpl [zero] x = v20 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽111⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s111k1N0 (x : ℝ) : ℝ :=
    (1 / 4) * hpl [negOne, negOne] x +
    (1 / 2) * hpl [negOne, zero, negOne] x +
    (1 / 2) * hpl [zero, negOne, negOne] x +
    (1) * hpl [zero, negOne, zero, negOne] x +
    (1) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s111k1N0`. -/
noncomputable def i8Psi4s111k1dN0 (x : ℝ) : ℝ :=
    (1 / 4) * (negOne.kernel x * hpl [negOne] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, negOne] x) +
    (1) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (1) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s111k1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k1N0 (i8Psi4s111k1dN0 x) x := by
  unfold i8Psi4s111k1N0 i8Psi4s111k1dN0
  exact ((((((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (1 / 4)).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (1)))

/-- The part of `ξ² Ψ₄⁽111⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s111k1N1 (x : ℝ) : ℝ :=
    (3 / 4) * hpl [negOne] x +
    (1 / 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s111k1N1`. -/
noncomputable def i8Psi4s111k1dN1 (x : ℝ) : ℝ :=
    (3 / 4) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s111k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k1N1 (i8Psi4s111k1dN1 x) x := by
  unfold i8Psi4s111k1N1 i8Psi4s111k1dN1
  exact (((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 4)).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽111⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s111k1N2 (x : ℝ) : ℝ :=
    (-1 / 4) * hpl [negOne] x +
    (1 / 4) * hpl [zero, negOne] x +
    (-1) * hpl [negOne, zero, negOne] x

/-- The derivative of `i8Psi4s111k1N2`. -/
noncomputable def i8Psi4s111k1dN2 (x : ℝ) : ℝ :=
    (-1 / 4) * (negOne.kernel x * hpl [] x) +
    (1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (negOne.kernel x * hpl [zero, negOne] x)

theorem hasDerivAt_i8Psi4s111k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k1N2 (i8Psi4s111k1dN2 x) x := by
  unfold i8Psi4s111k1N2 i8Psi4s111k1dN2
  exact ((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-1 / 4)).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₄⁽111⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s111k1N3 (x : ℝ) : ℝ :=
    (1) +
    (-3 / 4) * hpl [negOne] x +
    (1 / 2) * hpl [zero, negOne] x

/-- The derivative of `i8Psi4s111k1N3`. -/
noncomputable def i8Psi4s111k1dN3 (x : ℝ) : ℝ :=
    0 +
    (-3 / 4) * (negOne.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi4s111k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k1N3 (i8Psi4s111k1dN3 x) x := by
  unfold i8Psi4s111k1N3 i8Psi4s111k1dN3
  exact (((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽111⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s111k1N4 (x : ℝ) : ℝ :=
    (-1 / 8) +
    (1 / 4) * hpl [negOne] x +
    (-1 / 4) * hpl [negOne, negOne] x +
    (-1 / 4) * hpl [zero, negOne] x +
    (1 / 2) * hpl [negOne, zero, negOne] x +
    (1 / 2) * hpl [zero, negOne, negOne] x +
    (-1) * hpl [zero, negOne, zero, negOne] x +
    (-1) * hpl [zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s111k1N4`. -/
noncomputable def i8Psi4s111k1dN4 (x : ℝ) : ℝ :=
    0 +
    (1 / 4) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (negOne.kernel x * hpl [negOne] x) +
    (-1 / 4) * (zero.kernel x * hpl [negOne] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, negOne] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero, negOne] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s111k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k1N4 (i8Psi4s111k1dN4 x) x := by
  unfold i8Psi4s111k1N4 i8Psi4s111k1dN4
  exact ((((((((hasDerivAt_const x (-1 / 8)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, negOne] hx).const_mul (-1)))

/-- The part of `Ψ₄⁽111⁾` with constant coefficients. -/
noncomputable def i8Psi4s111k1W (x : ℝ) : ℝ :=
    (-3 / 4) * hpl [zero] x +
    (1 / 2) * hpl [zero, zero, negOne] x +
    (4) * hpl [zero, zero, negOne, zero, negOne] x +
    (4) * hpl [zero, zero, zero, negOne, negOne] x

/-- The derivative of `i8Psi4s111k1W`. -/
noncomputable def i8Psi4s111k1dW (x : ℝ) : ℝ :=
    (-3 / 4) * (zero.kernel x * hpl [] x) +
    (1 / 2) * (zero.kernel x * hpl [zero, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, zero, negOne] x) +
    (4) * (zero.kernel x * hpl [zero, zero, negOne, negOne] x)

theorem hasDerivAt_i8Psi4s111k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k1W (i8Psi4s111k1dW x) x := by
  unfold i8Psi4s111k1W i8Psi4s111k1dW
  exact (((((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 4)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, negOne] hx).const_mul (4)))

/-- Chunk 1 of the piece `Ψ₄⁽111⁾`. -/
noncomputable def i8Psi4s111k1 (x : ℝ) : ℝ :=
  (i8Psi4s111k1N0 x + x * i8Psi4s111k1N1 x + x ^ 2 * i8Psi4s111k1N2 x + x ^ 3 * i8Psi4s111k1N3 x +
    x ^ 4 * i8Psi4s111k1N4 x) / x ^ 2 + i8Psi4s111k1W x

/-- The derivative of `i8Psi4s111k1`. -/
noncomputable def i8Psi4s111k1D (x : ℝ) : ℝ :=
  ((i8Psi4s111k1dN0 x + (i8Psi4s111k1N1 x + x * i8Psi4s111k1dN1 x) + (2 * x * i8Psi4s111k1N2 x +
    x ^ 2 * i8Psi4s111k1dN2 x) + (3 * x ^ 2 * i8Psi4s111k1N3 x + x ^ 3 * i8Psi4s111k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s111k1N4 x + x ^ 4 * i8Psi4s111k1dN4 x)) * x ^ 2 - (i8Psi4s111k1N0 x +
    x * i8Psi4s111k1N1 x + x ^ 2 * i8Psi4s111k1N2 x + x ^ 3 * i8Psi4s111k1N3 x +
    x ^ 4 * i8Psi4s111k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s111k1dW x

theorem hasDerivAt_i8Psi4s111k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111k1 (i8Psi4s111k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s111k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s111k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s111k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s111k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s111k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s111k1W hx)
  unfold i8Psi4s111k1
  refine e.congr_deriv ?_
  unfold i8Psi4s111k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽111⁾` over words. -/
noncomputable def i8P4w111k1 (x : ℝ) : ℝ :=
    ((2 - 2 * x ^ 2) / (x)) * hpl [zero, negOne, zero, negOne] x +
    ((2 - 2 * x ^ 2) / (x)) * hpl [zero, zero, negOne, negOne] x

theorem i8Psi4s111k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s111k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w111k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s111k1D i8Psi4s111k1N0 i8Psi4s111k1N1 i8Psi4s111k1N2 i8Psi4s111k1N3 i8Psi4s111k1N4
    i8Psi4s111k1dN0 i8Psi4s111k1dN1 i8Psi4s111k1dN2 i8Psi4s111k1dN3 i8Psi4s111k1dN4 i8Psi4s111k1dW
    i8P4w111k1
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  generalize hpl [zero, zero, negOne, zero, negOne] x = v0 at *
  generalize hpl [zero, zero, zero, negOne, negOne] x = v1 at *
  generalize hpl [zero, negOne, zero, negOne] x = v2 at *
  generalize hpl [zero, zero, negOne, negOne] x = v3 at *
  generalize hpl [negOne, zero, negOne] x = v4 at *
  generalize hpl [zero, negOne, negOne] x = v5 at *
  generalize hpl [zero, zero, negOne] x = v6 at *
  generalize hpl [negOne, negOne] x = v7 at *
  generalize hpl [zero, negOne] x = v8 at *
  generalize hpl [negOne] x = v9 at *
  generalize hpl [zero] x = v10 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽111⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s111 (x : ℝ) : ℝ :=
  i8Psi4s111k0 x + i8Psi4s111k1 x

/-- The derivative of `Ψ₄⁽111⁾`. -/
noncomputable def i8Psi4s111D (x : ℝ) : ℝ :=
  i8Psi4s111k0D x + i8Psi4s111k1D x

theorem hasDerivAt_i8Psi4s111 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s111 (i8Psi4s111D x) x := by
  unfold i8Psi4s111 i8Psi4s111D
  exact ((hasDerivAt_i8Psi4s111k0 hx).add (hasDerivAt_i8Psi4s111k1 hx))

/-- The sub-piece 111 of `p₄` in `ξ`: from `t B0 A2 (-λ)^2/2!`, the term with `log^0 (1 -
  ξ) log^2 ξ`. -/
noncomputable def i8P4s111 (x : ℝ) : ℝ :=
  (1 / 2) * (1 - x) ^ 2 / x * Real.log x ^ 2 * ((1 + x) / (1 - x) * (2 * hpl [negOne, negOne] x))

/-- `p₄⁽111⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w111 (x : ℝ) : ℝ :=
  i8P4w111k0 x + i8P4w111k1 x

theorem i8P4s111_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s111 x = i8P4w111 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s111 i8P4w111 i8P4w111k0 i8P4w111k1
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [zero] hx
  have e1 := hpl_mul_hpl [negOne, negOne] [zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  linear_combination (norm := skip) (((1 - x ^ 2) / (x)) * hpl [negOne, negOne] x) * e0 + (((2 -
    2 * x ^ 2) / (x))) * e1
  field_simp
  generalize hpl [negOne, negOne, zero, zero] x = v0 at *
  generalize hpl [negOne, zero, negOne, zero] x = v1 at *
  generalize hpl [negOne, zero, zero, negOne] x = v2 at *
  generalize hpl [zero, negOne, negOne, zero] x = v3 at *
  generalize hpl [zero, negOne, zero, negOne] x = v4 at *
  generalize hpl [zero, zero, negOne, negOne] x = v5 at *
  generalize hpl [negOne, negOne] x = v6 at *
  generalize hpl [zero, zero] x = v7 at *
  generalize hpl [zero] x = v8 at *
  ring

/-- **`(Ψ₄⁽111⁾)'(ξ) ξ' = p₄⁽111⁾`**, in terms of `ξ`. -/
theorem i8Psi4s111D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s111D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s111 x := by
  rw [i8P4s111_eq_w hx]
  unfold i8Psi4s111D i8P4w111
  rw [← i8Psi4s111k0D_mul hx, ← i8Psi4s111k1D_mul hx]
  ring

/-- The part of `ξ² Ψ₄⁽112⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s112N0 (x : ℝ) : ℝ :=
    (-3 / 16) * hpl [negOne] x +
    (-1 / 4) * hpl [negOne, zero] x +
    (-3 / 8) * hpl [zero, negOne] x +
    (-1 / 4) * hpl [negOne, zero, zero] x +
    (-1 / 2) * hpl [zero, negOne, zero] x +
    (-3 / 4) * hpl [zero, zero, negOne] x +
    (-1 / 2) * hpl [zero, negOne, zero, zero] x +
    (-1) * hpl [zero, zero, negOne, zero] x +
    (-3 / 2) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s112N0`. -/
noncomputable def i8Psi4s112dN0 (x : ℝ) : ℝ :=
    (-3 / 16) * (negOne.kernel x * hpl [] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (-3 / 8) * (zero.kernel x * hpl [negOne] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-3 / 4) * (zero.kernel x * hpl [zero, negOne] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-3 / 2) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s112N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s112N0 (i8Psi4s112dN0 x) x := by
  unfold i8Psi4s112N0 i8Psi4s112dN0
  exact ((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 16)).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-3 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (-3 / 2)))

/-- The part of `ξ² Ψ₄⁽112⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s112N1 (x : ℝ) : ℝ :=
    (-11 / 16) +
    (-1 / 2) * hpl [zero] x +
    (-1 / 4) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s112N1`. -/
noncomputable def i8Psi4s112dN1 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s112N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s112N1 (i8Psi4s112dN1 x) x := by
  unfold i8Psi4s112N1 i8Psi4s112dN1
  exact (((hasDerivAt_const x (-11 / 16)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 4)))

/-- The part of `ξ² Ψ₄⁽112⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s112N2 (x : ℝ) : ℝ :=
    (3 / 8) * hpl [negOne] x +
    (-3 / 16) * hpl [zero] x +
    (-1 / 4) * hpl [zero, zero] x +
    (1 / 2) * hpl [negOne, zero, zero] x

/-- The derivative of `i8Psi4s112N2`. -/
noncomputable def i8Psi4s112dN2 (x : ℝ) : ℝ :=
    (3 / 8) * (negOne.kernel x * hpl [] x) +
    (-3 / 16) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero] x) +
    (1 / 2) * (negOne.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi4s112N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s112N2 (i8Psi4s112dN2 x) x := by
  unfold i8Psi4s112N2 i8Psi4s112dN2
  exact (((((hasDerivAt_hpl_cons negOne [] hx).const_mul (3 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 16))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (1 / 2)))

/-- The part of `ξ² Ψ₄⁽112⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s112N3 (x : ℝ) : ℝ :=
    (-11 / 16) +
    (1 / 2) * hpl [zero] x +
    (-1 / 4) * hpl [zero, zero] x

/-- The derivative of `i8Psi4s112N3`. -/
noncomputable def i8Psi4s112dN3 (x : ℝ) : ℝ :=
    0 +
    (1 / 2) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero] x)

theorem hasDerivAt_i8Psi4s112N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s112N3 (i8Psi4s112dN3 x) x := by
  unfold i8Psi4s112N3 i8Psi4s112dN3
  exact (((hasDerivAt_const x (-11 / 16)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 4)))

/-- The part of `ξ² Ψ₄⁽112⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s112N4 (x : ℝ) : ℝ :=
    (3 / 16) +
    (-3 / 16) * hpl [negOne] x +
    (-3 / 16) * hpl [zero] x +
    (1 / 4) * hpl [negOne, zero] x +
    (3 / 8) * hpl [zero, negOne] x +
    (1 / 8) * hpl [zero, zero] x +
    (-1 / 4) * hpl [negOne, zero, zero] x +
    (-1 / 2) * hpl [zero, negOne, zero] x +
    (-3 / 4) * hpl [zero, zero, negOne] x +
    (1 / 2) * hpl [zero, negOne, zero, zero] x +
    (1) * hpl [zero, zero, negOne, zero] x +
    (3 / 2) * hpl [zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s112N4`. -/
noncomputable def i8Psi4s112dN4 (x : ℝ) : ℝ :=
    0 +
    (-3 / 16) * (negOne.kernel x * hpl [] x) +
    (-3 / 16) * (zero.kernel x * hpl [] x) +
    (1 / 4) * (negOne.kernel x * hpl [zero] x) +
    (3 / 8) * (zero.kernel x * hpl [negOne] x) +
    (1 / 8) * (zero.kernel x * hpl [zero] x) +
    (-1 / 4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-3 / 4) * (zero.kernel x * hpl [zero, negOne] x) +
    (1 / 2) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (1) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (3 / 2) * (zero.kernel x * hpl [zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s112N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s112N4 (i8Psi4s112dN4 x) x := by
  unfold i8Psi4s112N4 i8Psi4s112dN4
  exact ((((((((((((hasDerivAt_const x (3 / 16)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-3 / 16))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-3 / 16))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (3 / 8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1 / 8))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne] hx).const_mul (3 / 2)))

/-- The part of `Ψ₄⁽112⁾` with constant coefficients. -/
noncomputable def i8Psi4s112W (x : ℝ) : ℝ :=
    (-1 / 4) * hpl [zero, zero, zero] x +
    (-2) * hpl [zero, zero, negOne, zero, zero] x +
    (-4) * hpl [zero, zero, zero, negOne, zero] x +
    (-6) * hpl [zero, zero, zero, zero, negOne] x

/-- The derivative of `i8Psi4s112W`. -/
noncomputable def i8Psi4s112dW (x : ℝ) : ℝ :=
    (-1 / 4) * (zero.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, negOne, zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, negOne, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero, zero, negOne] x)

theorem hasDerivAt_i8Psi4s112W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s112W (i8Psi4s112dW x) x := by
  unfold i8Psi4s112W i8Psi4s112dW
  exact (((((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1 / 4)).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero, negOne] hx).const_mul (-6)))

/-- The piece `Ψ₄⁽112⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s112 (x : ℝ) : ℝ :=
  (i8Psi4s112N0 x + x * i8Psi4s112N1 x + x ^ 2 * i8Psi4s112N2 x + x ^ 3 * i8Psi4s112N3 x +
    x ^ 4 * i8Psi4s112N4 x) / x ^ 2 + i8Psi4s112W x

/-- The derivative of `Ψ₄⁽112⁾`. -/
noncomputable def i8Psi4s112D (x : ℝ) : ℝ :=
  ((i8Psi4s112dN0 x + (i8Psi4s112N1 x + x * i8Psi4s112dN1 x) + (2 * x * i8Psi4s112N2 x +
    x ^ 2 * i8Psi4s112dN2 x) + (3 * x ^ 2 * i8Psi4s112N3 x + x ^ 3 * i8Psi4s112dN3 x) +
    (4 * x ^ 3 * i8Psi4s112N4 x + x ^ 4 * i8Psi4s112dN4 x)) * x ^ 2 - (i8Psi4s112N0 x +
    x * i8Psi4s112N1 x + x ^ 2 * i8Psi4s112N2 x + x ^ 3 * i8Psi4s112N3 x +
    x ^ 4 * i8Psi4s112N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s112dW x

theorem hasDerivAt_i8Psi4s112 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s112 (i8Psi4s112D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s112N0 hx).add (X.mul (hasDerivAt_i8Psi4s112N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s112N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s112N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s112N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s112W hx)
  unfold i8Psi4s112
  refine e.congr_deriv ?_
  unfold i8Psi4s112D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 112 of `p₄` in `ξ`: from `t B0 A2 (-λ)^2/2!`, the term with `log^0 (1 -
  ξ) log^2 ξ`. -/
noncomputable def i8P4s112 (x : ℝ) : ℝ :=
  (1 / 2) * (1 - x) ^ 2 / x * Real.log x ^ 2 * ((1 + x) / (1 - x) * (-hpl [zero, negOne] x))

/-- `p₄⁽112⁾` written over words. -/
noncomputable def i8P4w112 (x : ℝ) : ℝ :=
    ((-1 + x ^ 2) / (x)) * hpl [zero, negOne, zero, zero] x +
    ((-2 + 2 * x ^ 2) / (x)) * hpl [zero, zero, negOne, zero] x +
    ((-3 + 3 * x ^ 2) / (x)) * hpl [zero, zero, zero, negOne] x

theorem i8P4s112_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s112 x = i8P4w112 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s112 i8P4w112
  simp only [← hpl_zero]
  have e0 := hpl_mul_hpl [zero] [zero] hx
  have e1 := hpl_mul_hpl [zero, negOne] [zero, zero] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  linear_combination (norm := skip) (((-1 / 2 +
    x ^ 2 / 2) / (x)) * hpl [zero, negOne] x) * e0 + (((-1 + x ^ 2) / (x))) * e1
  field_simp
  generalize hpl [zero, negOne, zero, zero] x = v0 at *
  generalize hpl [zero, zero, negOne, zero] x = v1 at *
  generalize hpl [zero, zero, zero, negOne] x = v2 at *
  generalize hpl [zero, negOne] x = v3 at *
  generalize hpl [zero, zero] x = v4 at *
  generalize hpl [zero] x = v5 at *
  ring

/-- **`(Ψ₄⁽112⁾)'(ξ) ξ' = p₄⁽112⁾`**, in terms of `ξ`. -/
theorem i8Psi4s112D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s112D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s112 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s112_eq_w hx]
  unfold i8Psi4s112D i8Psi4s112N0 i8Psi4s112N1 i8Psi4s112N2 i8Psi4s112N3 i8Psi4s112N4 i8Psi4s112dN0
    i8Psi4s112dN1 i8Psi4s112dN2 i8Psi4s112dN3 i8Psi4s112dN4 i8Psi4s112dW i8P4w112
  simp only [kernel_zero, kernel_negOne, hpl_nil]
  field_simp
  generalize hpl [zero, zero, negOne, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero, negOne, zero] x = v1 at *
  generalize hpl [zero, zero, zero, zero, negOne] x = v2 at *
  generalize hpl [zero, negOne, zero, zero] x = v3 at *
  generalize hpl [zero, zero, negOne, zero] x = v4 at *
  generalize hpl [zero, zero, zero, negOne] x = v5 at *
  generalize hpl [negOne, zero, zero] x = v6 at *
  generalize hpl [zero, negOne, zero] x = v7 at *
  generalize hpl [zero, zero, negOne] x = v8 at *
  generalize hpl [zero, zero, zero] x = v9 at *
  generalize hpl [negOne, zero] x = v10 at *
  generalize hpl [zero, negOne] x = v11 at *
  generalize hpl [zero, zero] x = v12 at *
  generalize hpl [negOne] x = v13 at *
  generalize hpl [zero] x = v14 at *
  ring

end QED.ThreeLoopD
