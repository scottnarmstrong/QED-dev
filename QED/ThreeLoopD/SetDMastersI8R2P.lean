/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R2C

/-!
# Set (d), master `I₈`: a primitive of `p₂`

In the variable `ξ` (`t = (1 - ξ)²/ξ`, `dt/dξ = -(1 - ξ²)/ξ²`), `p₂ dt/dξ` has the primitive

  `Ψ₂(ξ) = ∑_w c_w(ξ) H(w; ξ)`,

a combination of 22 harmonic polylogarithms of weight at most three with coefficients in
`ℚ[π², ξ, 1/ξ]` (`QED.ThreeLoopD.i8Psi2`; computed and checked symbolically by the shuffle-algebra
engine of the campaign). `F₂(t) = Ψ₂(ξ(t))` is then a primitive of `p₂` on `t > 0`
(`QED.ThreeLoopD.hasDerivAt_i8F2`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi2`, `QED.ThreeLoopD.i8Psi2D_mul`.
* `QED.ThreeLoopD.hasDerivAt_i8F2`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₂` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi2N0 (x : ℝ) : ℝ :=
    (-7 / 2) * hpl [negOne] x +
    (1) * hpl [negOne, negOne] x +
    (-3 / 2) * hpl [negOne, zero] x +
    (-1) * hpl [negOne, one] x +
    (-2) * hpl [zero, negOne] x +
    (-1) * hpl [one, negOne] x

/-- The derivative of `i8Psi2N0`. -/
noncomputable def i8Psi2dN0 (x : ℝ) : ℝ :=
    (-7 / 2) * (negOne.kernel x * hpl [] x) +
    (1) * (negOne.kernel x * hpl [negOne] x) +
    (-3 / 2) * (negOne.kernel x * hpl [zero] x) +
    (-1) * (negOne.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [negOne] x) +
    (-1) * (one.kernel x * hpl [negOne] x)

theorem hasDerivAt_i8Psi2N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi2N0 (i8Psi2dN0 x) x := by
  unfold i8Psi2N0 i8Psi2dN0
  exact (((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (-7 / 2)).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-1)))

/-- The part of `ξ² Ψ₂` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi2N1 (x : ℝ) : ℝ :=
    (37 - π ^ 2 / 3) +
    (-4) * hpl [negOne] x +
    (45 / 2) * hpl [zero] x +
    (15) * hpl [one] x +
    (-8) * hpl [negOne, zero] x +
    (-4) * hpl [zero, negOne] x +
    (9) * hpl [zero, zero] x +
    (6) * hpl [zero, one] x +
    (6) * hpl [one, zero] x +
    (4) * hpl [one, one] x

/-- The derivative of `i8Psi2N1`. -/
noncomputable def i8Psi2dN1 (x : ℝ) : ℝ :=
    0 +
    (-4) * (negOne.kernel x * hpl [] x) +
    (45 / 2) * (zero.kernel x * hpl [] x) +
    (15) * (one.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [negOne] x) +
    (9) * (zero.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [one] x) +
    (6) * (one.kernel x * hpl [zero] x) +
    (4) * (one.kernel x * hpl [one] x)

theorem hasDerivAt_i8Psi2N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi2N1 (i8Psi2dN1 x) x := by
  unfold i8Psi2N1 i8Psi2dN1
  exact ((((((((((hasDerivAt_const x (37 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (45 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (15))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (4)))

/-- The part of `ξ² Ψ₂` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi2N2 (x : ℝ) : ℝ :=
    (7 / 2 + π ^ 2 / 3) * hpl [zero] x +
    (-15) * hpl [one] x +
    (-12) * hpl [negOne, zero] x +
    (-8) * hpl [zero, negOne] x +
    (-9 / 2) * hpl [zero, zero] x +
    (5) * hpl [zero, one] x +
    (-13) * hpl [one, zero] x +
    (-6) * hpl [one, one] x

/-- The derivative of `i8Psi2N2`. -/
noncomputable def i8Psi2dN2 (x : ℝ) : ℝ :=
    (7 / 2 + π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (-15) * (one.kernel x * hpl [] x) +
    (-12) * (negOne.kernel x * hpl [zero] x) +
    (-8) * (zero.kernel x * hpl [negOne] x) +
    (-9 / 2) * (zero.kernel x * hpl [zero] x) +
    (5) * (zero.kernel x * hpl [one] x) +
    (-13) * (one.kernel x * hpl [zero] x) +
    (-6) * (one.kernel x * hpl [one] x)

theorem hasDerivAt_i8Psi2N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi2N2 (i8Psi2dN2 x) x := by
  unfold i8Psi2N2 i8Psi2dN2
  exact (((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (7 / 2 + π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-15))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-9 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-13))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-6)))

/-- The part of `ξ² Ψ₂` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi2N3 (x : ℝ) : ℝ :=
    (-9 - π ^ 2 / 3) +
    (4) * hpl [negOne] x +
    (53 / 2) * hpl [zero] x +
    (7) * hpl [one] x +
    (-8) * hpl [negOne, zero] x +
    (-4) * hpl [zero, negOne] x +
    (1) * hpl [zero, zero] x +
    (6) * hpl [zero, one] x +
    (6) * hpl [one, zero] x +
    (4) * hpl [one, one] x

/-- The derivative of `i8Psi2N3`. -/
noncomputable def i8Psi2dN3 (x : ℝ) : ℝ :=
    0 +
    (4) * (negOne.kernel x * hpl [] x) +
    (53 / 2) * (zero.kernel x * hpl [] x) +
    (7) * (one.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [negOne] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (6) * (zero.kernel x * hpl [one] x) +
    (6) * (one.kernel x * hpl [zero] x) +
    (4) * (one.kernel x * hpl [one] x)

theorem hasDerivAt_i8Psi2N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi2N3 (i8Psi2dN3 x) x := by
  unfold i8Psi2N3 i8Psi2dN3
  exact ((((((((((hasDerivAt_const x (-9 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (53 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (7))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (4)))

/-- The part of `ξ² Ψ₂` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi2N4 (x : ℝ) : ℝ :=
    (-16 - π ^ 2 / 6) +
    (7 / 2) * hpl [negOne] x +
    (7 / 2) * hpl [zero] x +
    (-7) * hpl [one] x +
    (-1) * hpl [negOne, negOne] x +
    (-5 / 2) * hpl [negOne, zero] x +
    (1) * hpl [negOne, one] x +
    (3 / 2) * hpl [zero, zero] x +
    (1) * hpl [zero, one] x +
    (1) * hpl [one, negOne] x +
    (1) * hpl [one, zero] x +
    (-2) * hpl [one, one] x

/-- The derivative of `i8Psi2N4`. -/
noncomputable def i8Psi2dN4 (x : ℝ) : ℝ :=
    0 +
    (7 / 2) * (negOne.kernel x * hpl [] x) +
    (7 / 2) * (zero.kernel x * hpl [] x) +
    (-7) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [negOne] x) +
    (-5 / 2) * (negOne.kernel x * hpl [zero] x) +
    (1) * (negOne.kernel x * hpl [one] x) +
    (3 / 2) * (zero.kernel x * hpl [zero] x) +
    (1) * (zero.kernel x * hpl [one] x) +
    (1) * (one.kernel x * hpl [negOne] x) +
    (1) * (one.kernel x * hpl [zero] x) +
    (-2) * (one.kernel x * hpl [one] x)

theorem hasDerivAt_i8Psi2N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi2N4 (i8Psi2dN4 x) x := by
  unfold i8Psi2N4 i8Psi2dN4
  exact ((((((((((((hasDerivAt_const x (-16 - π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (7 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons negOne [negOne] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-5 / 2))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-2)))

/-- The part of `Ψ₂` with constant coefficients. -/
noncomputable def i8Psi2W (x : ℝ) : ℝ :=
    (4) * hpl [zero, negOne, negOne] x +
    (2) * hpl [zero, negOne, zero] x +
    (-4) * hpl [zero, negOne, one] x +
    (-4) * hpl [zero, zero, negOne] x +
    (-11) * hpl [zero, zero, zero] x +
    (-2) * hpl [zero, zero, one] x +
    (-4) * hpl [zero, one, negOne] x +
    (-2) * hpl [zero, one, zero] x +
    (4) * hpl [zero, one, one] x

/-- The derivative of `i8Psi2W`. -/
noncomputable def i8Psi2dW (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [negOne, negOne] x) +
    (2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, one] x) +
    (-4) * (zero.kernel x * hpl [zero, negOne] x) +
    (-11) * (zero.kernel x * hpl [zero, zero] x) +
    (-2) * (zero.kernel x * hpl [zero, one] x) +
    (-4) * (zero.kernel x * hpl [one, negOne] x) +
    (-2) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi2W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi2W (i8Psi2dW x) x := by
  unfold i8Psi2W i8Psi2dW
  exact ((((((((((hasDerivAt_hpl_cons zero [negOne, negOne] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (4)))

/-! ### `Ψ₂` and its derivative -/

/-- The primitive `Ψ₂` of `p₂ dt/dξ`, as a function of `ξ`. -/
noncomputable def i8Psi2 (x : ℝ) : ℝ :=
  (i8Psi2N0 x + x * i8Psi2N1 x + x ^ 2 * i8Psi2N2 x + x ^ 3 * i8Psi2N3 x +
    x ^ 4 * i8Psi2N4 x) / x ^ 2 + i8Psi2W x

/-- The derivative of `Ψ₂`. -/
noncomputable def i8Psi2D (x : ℝ) : ℝ :=
  ((i8Psi2dN0 x + (i8Psi2N1 x + x * i8Psi2dN1 x) +
      (2 * x * i8Psi2N2 x + x ^ 2 * i8Psi2dN2 x) +
      (3 * x ^ 2 * i8Psi2N3 x + x ^ 3 * i8Psi2dN3 x) +
      (4 * x ^ 3 * i8Psi2N4 x + x ^ 4 * i8Psi2dN4 x)) * x ^ 2 -
    (i8Psi2N0 x + x * i8Psi2N1 x + x ^ 2 * i8Psi2N2 x + x ^ 3 * i8Psi2N3 x +
      x ^ 4 * i8Psi2N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi2dW x

theorem hasDerivAt_i8Psi2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi2 (i8Psi2D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := (((((hasDerivAt_i8Psi2N0 hx).add (X.mul (hasDerivAt_i8Psi2N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi2N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi2N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi2N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0) |>.add
    (hasDerivAt_i8Psi2W hx)
  unfold i8Psi2
  refine e.congr_deriv ?_
  unfold i8Psi2D
  simp only [Pi.pow_apply]
  norm_num

/-- `p₂` in the variable `ξ`. -/
noncomputable def i8P2x (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * ((2 * i13Be2x x + (2 + Real.log x * (1 + x) / (1 - x)) ^ 2) *
      (x / (1 - x)) + 2 * (2 + Real.log x * (1 + x) / (1 - x)) * i8A1x x + i8A2x x) -
    (1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) *
      (2 * (2 + Real.log x * (1 + x) / (1 - x)) * (x / (1 - x)) + i8A1x x) +
    (1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 2 / 2 * (x / (1 - x))

theorem i8P2_eq {t : ℝ} (ht : 0 < t) : i8P2 t = i8P2x (i13Xi t) := by
  have hT := (i13Xi_t ht.le).symm
  have hlog := (i8_log_eq ht).symm
  unfold i8P2 i8P2x i13Be1r
  rw [i13Be2r_eq, hT, hlog]

/-- **`Ψ₂'(ξ) ξ' = p₂`**, in terms of `ξ`. -/
theorem i8Psi2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P2x x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi2D i8Psi2N0 i8Psi2N1 i8Psi2N2 i8Psi2N3 i8Psi2N4 i8Psi2dN0 i8Psi2dN1
    i8Psi2dN2 i8Psi2dN3 i8Psi2dN4 i8Psi2dW i8P2x i13Be2x i8A1x i8A2x
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx,
    i13hw_mm hx, i13hw_10 hx, i13hw_1m hx, i13hw_11 hx,
    i13_Li₂_neg_eq hx, i13_log_one_add_eq hx, i13_log_one_sub_eq hx]
  field_simp
  ring

/-! ### The primitive `F₂` -/

/-- `F₂(t) = Ψ₂(ξ(t))`. -/
noncomputable def i8F2 (t : ℝ) : ℝ := i8Psi2 (i13Xi t)

theorem hasDerivAt_i8F2 {t : ℝ} (ht : 0 < t) : HasDerivAt i8F2 (i8P2 t) t := by
  have e := (hasDerivAt_i8Psi2 (i8_xi_mem ht)).comp t (hasDerivAt_i13Xi ht)
  rw [i8Psi2D_mul (i8_xi_mem ht), ← i8P2_eq ht] at e
  exact e

end QED.ThreeLoopD
