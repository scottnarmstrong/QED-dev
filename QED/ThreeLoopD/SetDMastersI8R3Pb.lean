/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3Pa

/-!
# Set (d), master `I₈`: a primitive of `p₃`, piece `b`

`p₃` splits as `p₃⁽ᵃ⁾ + p₃⁽ᵇ⁾ + p₃⁽ᶜ⁾` by the power of `λ = log t` (`QED.ThreeLoopD.i8P3xb`).
The piece `Ψ₃⁽b⁾` (`QED.ThreeLoopD.i8Psi3b`), a combination of harmonic polylogarithms of weight
at most four with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the shuffle-algebra engine of
the campaign, is a primitive of `p₃⁽b⁾ dt/dξ` (`QED.ThreeLoopD.i8Psi3bD_mul`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi3b`, `QED.ThreeLoopD.i8Psi3bD_mul`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₃⁽b⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi3bN0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi3bN0`. -/
noncomputable def i8Psi3bdN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi3bN0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3bN0 (i8Psi3bdN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₃⁽b⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi3bN1 (x : ℝ) : ℝ :=
    (40 - π ^ 2 / 3) +
    (40 - π ^ 2 / 3) * hpl [zero] x +
    (48 - 2 / 3 * π ^ 2) * hpl [one] x +
    (-4) * hpl [negOne, zero] x +
    (28) * hpl [zero, zero] x +
    (24) * hpl [zero, one] x +
    (24) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (12) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (-8) * hpl [one, negOne, zero] x +
    (8) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi3bN1`. -/
noncomputable def i8Psi3bdN1 (x : ℝ) : ℝ :=
    0 +
    (40 - π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (48 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (-4) * (negOne.kernel x * hpl [zero] x) +
    (28) * (zero.kernel x * hpl [zero] x) +
    (24) * (zero.kernel x * hpl [one] x) +
    (24) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi3bN1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3bN1 (i8Psi3bdN1 x) x := by
  unfold i8Psi3bN1 i8Psi3bdN1
  exact ((((((((((((((((hasDerivAt_const x (40 - π ^ 2 / 3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (40 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (48 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₃⁽b⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi3bN2 (x : ℝ) : ℝ :=
    (-48 + 2 / 3 * π ^ 2) * hpl [zero] x +
    (-27 + 5 / 3 * π ^ 2) * hpl [one] x +
    (-11) * hpl [negOne, zero] x +
    (-8 + π ^ 2 / 3) * hpl [zero, zero] x +
    (24 + 2 / 3 * π ^ 2) * hpl [zero, one] x +
    (-62) * hpl [one, zero] x +
    (-12) * hpl [negOne, zero, zero] x +
    (-12) * hpl [negOne, zero, one] x +
    (-12) * hpl [negOne, one, zero] x +
    (8) * hpl [zero, negOne, zero] x +
    (-16) * hpl [zero, zero, zero] x +
    (-8) * hpl [zero, zero, one] x +
    (-8) * hpl [zero, one, zero] x +
    (20) * hpl [one, negOne, zero] x

/-- The derivative of `i8Psi3bN2`. -/
noncomputable def i8Psi3bdN2 (x : ℝ) : ℝ :=
    (-48 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [] x) +
    (-27 + 5 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (-11) * (negOne.kernel x * hpl [zero] x) +
    (-8 + π ^ 2 / 3) * (zero.kernel x * hpl [zero] x) +
    (24 + 2 / 3 * π ^ 2) * (zero.kernel x * hpl [one] x) +
    (-62) * (one.kernel x * hpl [zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, zero] x) +
    (-12) * (negOne.kernel x * hpl [zero, one] x) +
    (-12) * (negOne.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, one] x) +
    (-8) * (zero.kernel x * hpl [one, zero] x) +
    (20) * (one.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi3bN2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3bN2 (i8Psi3bdN2 x) x := by
  unfold i8Psi3bN2 i8Psi3bdN2
  exact (((((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-48 + 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-27 + 5 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-8 + π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (24 + 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-62))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (20)))

/-- The part of `ξ² Ψ₃⁽b⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi3bN3 (x : ℝ) : ℝ :=
    (-54 - 2 / 3 * π ^ 2) +
    (33 - π ^ 2 / 3) * hpl [zero] x +
    (-4 - 2 / 3 * π ^ 2) * hpl [one] x +
    (-8) * hpl [negOne, zero] x +
    (24) * hpl [zero, zero] x +
    (28) * hpl [zero, one] x +
    (28) * hpl [one, zero] x +
    (-8) * hpl [negOne, zero, zero] x +
    (-8) * hpl [negOne, zero, one] x +
    (-8) * hpl [negOne, one, zero] x +
    (-4) * hpl [zero, negOne, zero] x +
    (-12) * hpl [zero, zero, zero] x +
    (-8) * hpl [zero, zero, one] x +
    (-8) * hpl [zero, one, zero] x +
    (-8) * hpl [one, negOne, zero] x +
    (-8) * hpl [one, zero, zero] x

/-- The derivative of `i8Psi3bN3`. -/
noncomputable def i8Psi3bdN3 (x : ℝ) : ℝ :=
    0 +
    (33 - π ^ 2 / 3) * (zero.kernel x * hpl [] x) +
    (-4 - 2 / 3 * π ^ 2) * (one.kernel x * hpl [] x) +
    (-8) * (negOne.kernel x * hpl [zero] x) +
    (24) * (zero.kernel x * hpl [zero] x) +
    (28) * (zero.kernel x * hpl [one] x) +
    (28) * (one.kernel x * hpl [zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, zero] x) +
    (-8) * (negOne.kernel x * hpl [zero, one] x) +
    (-8) * (negOne.kernel x * hpl [one, zero] x) +
    (-4) * (zero.kernel x * hpl [negOne, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, one] x) +
    (-8) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (one.kernel x * hpl [negOne, zero] x) +
    (-8) * (one.kernel x * hpl [zero, zero] x)

theorem hasDerivAt_i8Psi3bN3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3bN3 (i8Psi3bdN3 x) x := by
  unfold i8Psi3bN3 i8Psi3bdN3
  exact ((((((((((((((((hasDerivAt_const x (-54 - 2 / 3 * π ^ 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (33 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-4 - 2 / 3 * π ^ 2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-8)))

/-- The part of `ξ² Ψ₃⁽b⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi3bN4 (x : ℝ) : ℝ :=
    (-23 / 4 - π ^ 2 / 12) +
    (-11 / 2 - π ^ 2 / 6) * hpl [zero] x +
    (-17 - π ^ 2 / 3) * hpl [one] x +
    (-1) * hpl [negOne, zero] x +
    (10) * hpl [zero, zero] x +
    (10) * hpl [zero, one] x +
    (10) * hpl [one, zero] x +
    (-4) * hpl [negOne, zero, zero] x +
    (-4) * hpl [negOne, zero, one] x +
    (-4) * hpl [negOne, one, zero] x +
    (-2) * hpl [zero, negOne, zero] x +
    (-4) * hpl [one, negOne, zero] x

/-- The derivative of `i8Psi3bN4`. -/
noncomputable def i8Psi3bdN4 (x : ℝ) : ℝ :=
    0 +
    (-11 / 2 - π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (-17 - π ^ 2 / 3) * (one.kernel x * hpl [] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (10) * (zero.kernel x * hpl [zero] x) +
    (10) * (zero.kernel x * hpl [one] x) +
    (10) * (one.kernel x * hpl [zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, zero] x) +
    (-4) * (negOne.kernel x * hpl [zero, one] x) +
    (-4) * (negOne.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, zero] x) +
    (-4) * (one.kernel x * hpl [negOne, zero] x)

theorem hasDerivAt_i8Psi3bN4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3bN4 (i8Psi3bdN4 x) x := by
  unfold i8Psi3bN4 i8Psi3bdN4
  exact ((((((((((((hasDerivAt_const x (-23 / 4 - π ^ 2 / 12)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-11 / 2 - π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-17 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons negOne [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons negOne [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne, zero] hx).const_mul (-4)))

/-- The part of `Ψ₃⁽b⁾` with constant coefficients. -/
noncomputable def i8Psi3bW (x : ℝ) : ℝ :=
    (8) * hpl [zero, negOne, zero, zero] x +
    (8) * hpl [zero, negOne, zero, one] x +
    (8) * hpl [zero, negOne, one, zero] x +
    (4) * hpl [zero, zero, negOne, zero] x +
    (-24) * hpl [zero, zero, zero, zero] x +
    (-16) * hpl [zero, zero, zero, one] x +
    (-16) * hpl [zero, zero, one, zero] x +
    (8) * hpl [zero, one, negOne, zero] x +
    (-16) * hpl [zero, one, zero, zero] x

/-- The derivative of `i8Psi3bW`. -/
noncomputable def i8Psi3bdW (x : ℝ) : ℝ :=
    (8) * (zero.kernel x * hpl [negOne, zero, zero] x) +
    (8) * (zero.kernel x * hpl [negOne, zero, one] x) +
    (8) * (zero.kernel x * hpl [negOne, one, zero] x) +
    (4) * (zero.kernel x * hpl [zero, negOne, zero] x) +
    (-24) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-16) * (zero.kernel x * hpl [zero, one, zero] x) +
    (8) * (zero.kernel x * hpl [one, negOne, zero] x) +
    (-16) * (zero.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi3bW {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3bW (i8Psi3bdW x) x := by
  unfold i8Psi3bW i8Psi3bdW
  exact ((((((((((hasDerivAt_hpl_cons zero [negOne, zero, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [negOne, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [negOne, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, negOne, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-16)))

/-- The piece `Ψ₃⁽b⁾` of the primitive of `p₃ dt/dξ`. -/
noncomputable def i8Psi3b (x : ℝ) : ℝ :=
  (i8Psi3bN0 x + x * i8Psi3bN1 x + x ^ 2 * i8Psi3bN2 x + x ^ 3 * i8Psi3bN3 x +
    x ^ 4 * i8Psi3bN4 x) / x ^ 2 + i8Psi3bW x

/-- The derivative of `Ψ₃⁽b⁾`. -/
noncomputable def i8Psi3bD (x : ℝ) : ℝ :=
  ((i8Psi3bdN0 x + (i8Psi3bN1 x + x * i8Psi3bdN1 x) +
      (2 * x * i8Psi3bN2 x + x ^ 2 * i8Psi3bdN2 x) +
      (3 * x ^ 2 * i8Psi3bN3 x + x ^ 3 * i8Psi3bdN3 x) +
      (4 * x ^ 3 * i8Psi3bN4 x + x ^ 4 * i8Psi3bdN4 x)) * x ^ 2 -
    (i8Psi3bN0 x + x * i8Psi3bN1 x + x ^ 2 * i8Psi3bN2 x + x ^ 3 * i8Psi3bN3 x +
      x ^ 4 * i8Psi3bN4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi3bdW x

theorem hasDerivAt_i8Psi3b {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3b (i8Psi3bD x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := (((((hasDerivAt_i8Psi3bN0 hx).add (X.mul (hasDerivAt_i8Psi3bN1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi3bN2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi3bN3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi3bN4 hx))).div (X.pow 2) (pow_ne_zero 2 h0) |>.add
    (hasDerivAt_i8Psi3bW hx)
  unfold i8Psi3b
  refine e.congr_deriv ?_
  unfold i8Psi3bD
  simp only [Pi.pow_apply]
  norm_num

/-- The part `-t λ (2β₂ + β₁²) A₀` of `p₃` in `ξ`. -/
noncomputable def i8P3xb (x : ℝ) : ℝ :=
  -((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) *
    ((2 * i13Be2x x + (2 + Real.log x * (1 + x) / (1 - x)) ^ 2) * (x / (1 - x))))

/-- **`(Ψ₃⁽b⁾)'(ξ) ξ' = p₃⁽b⁾`**, in terms of `ξ`. -/
theorem i8Psi3bD_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3bD x * (-x ^ 2 / (1 - x ^ 2)) = i8P3xb x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi3bD i8Psi3bN0 i8Psi3bN1 i8Psi3bN2 i8Psi3bN3 i8Psi3bN4 i8Psi3bdN0 i8Psi3bdN1
    i8Psi3bdN2 i8Psi3bdN3 i8Psi3bdN4 i8Psi3bdW i8P3xb i13Be2x
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx,
    i13hw_10 hx, i13hw_000, i13hw_0m0 hx, i13hw_010 hx, i13hw_m00 hx, i13hw_m01 hx, i13hw_m10 hx,
    i13hw_100 hx, i13hw_1m0 hx, i13_Li₂_neg_eq hx, i13_log_one_add_eq hx, i13_log_one_sub_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
