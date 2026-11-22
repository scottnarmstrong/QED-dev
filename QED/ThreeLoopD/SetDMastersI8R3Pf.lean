/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3Pe

/-!
# Set (d), master `I₈`: a primitive of `p₃`, piece `f`

`p₃` splits as `p₃⁽ᵃ⁾ + p₃⁽ᵇ⁾ + p₃⁽ᶜ⁾` by the power of `λ = log t` (`QED.ThreeLoopD.i8P3xf`).
The piece `Ψ₃⁽f⁾` (`QED.ThreeLoopD.i8Psi3f`), a combination of harmonic polylogarithms of weight
at most four with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the shuffle-algebra engine of
the campaign, is a primitive of `p₃⁽f⁾ dt/dξ` (`QED.ThreeLoopD.i8Psi3fD_mul`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi3f`, `QED.ThreeLoopD.i8Psi3fD_mul`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₃⁽f⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi3fN0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi3fN0`. -/
noncomputable def i8Psi3fdN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi3fN0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3fN0 (i8Psi3fdN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₃⁽f⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi3fN1 (x : ℝ) : ℝ :=
    (10) +
    (10) * hpl [zero] x +
    (16) * hpl [one] x +
    (10) * hpl [zero, zero] x +
    (16) * hpl [zero, one] x +
    (16) * hpl [one, zero] x +
    (24) * hpl [one, one] x +
    (6) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (8) * hpl [zero, one, one] x +
    (8) * hpl [one, zero, zero] x +
    (8) * hpl [one, zero, one] x +
    (8) * hpl [one, one, zero] x

/-- The derivative of `i8Psi3fN1`. -/
noncomputable def i8Psi3fdN1 (x : ℝ) : ℝ :=
    0 +
    (10) * (zero.kernel x * hpl [] x) +
    (16) * (one.kernel x * hpl [] x) +
    (10) * (zero.kernel x * hpl [zero] x) +
    (16) * (zero.kernel x * hpl [one] x) +
    (16) * (one.kernel x * hpl [zero] x) +
    (24) * (one.kernel x * hpl [one] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [one, one] x) +
    (8) * (one.kernel x * hpl [zero, zero] x) +
    (8) * (one.kernel x * hpl [zero, one] x) +
    (8) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi3fN1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3fN1 (i8Psi3fdN1 x) x := by
  unfold i8Psi3fN1 i8Psi3fdN1
  exact ((((((((((((((hasDerivAt_const x (10)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₃⁽f⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi3fN2 (x : ℝ) : ℝ :=
    (-16) * hpl [zero] x +
    (1) * hpl [one] x +
    (-16) * hpl [zero, zero] x +
    (-24) * hpl [zero, one] x +
    (-24) * hpl [one, zero] x +
    (-22) * hpl [one, one] x +
    (-4) * hpl [zero, zero, zero] x +
    (16) * hpl [zero, one, one] x +
    (-20) * hpl [one, zero, zero] x +
    (-20) * hpl [one, zero, one] x +
    (-20) * hpl [one, one, zero] x

/-- The derivative of `i8Psi3fN2`. -/
noncomputable def i8Psi3fdN2 (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [] x) +
    (1) * (one.kernel x * hpl [] x) +
    (-16) * (zero.kernel x * hpl [zero] x) +
    (-24) * (zero.kernel x * hpl [one] x) +
    (-24) * (one.kernel x * hpl [zero] x) +
    (-22) * (one.kernel x * hpl [one] x) +
    (-4) * (zero.kernel x * hpl [zero, zero] x) +
    (16) * (zero.kernel x * hpl [one, one] x) +
    (-20) * (one.kernel x * hpl [zero, zero] x) +
    (-20) * (one.kernel x * hpl [zero, one] x) +
    (-20) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi3fN2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3fN2 (i8Psi3fdN2 x) x := by
  unfold i8Psi3fN2 i8Psi3fdN2
  exact ((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-20)))

/-- The part of `ξ² Ψ₃⁽f⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi3fN3 (x : ℝ) : ℝ :=
    (-15) +
    (-2) * hpl [zero] x +
    (-14) * hpl [one] x +
    (10) * hpl [zero, zero] x +
    (12) * hpl [zero, one] x +
    (12) * hpl [one, zero] x +
    (8) * hpl [one, one] x +
    (6) * hpl [zero, zero, zero] x +
    (8) * hpl [zero, zero, one] x +
    (8) * hpl [zero, one, zero] x +
    (8) * hpl [zero, one, one] x +
    (8) * hpl [one, zero, zero] x +
    (8) * hpl [one, zero, one] x +
    (8) * hpl [one, one, zero] x

/-- The derivative of `i8Psi3fN3`. -/
noncomputable def i8Psi3fdN3 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x) +
    (-14) * (one.kernel x * hpl [] x) +
    (10) * (zero.kernel x * hpl [zero] x) +
    (12) * (zero.kernel x * hpl [one] x) +
    (12) * (one.kernel x * hpl [zero] x) +
    (8) * (one.kernel x * hpl [one] x) +
    (6) * (zero.kernel x * hpl [zero, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one] x) +
    (8) * (zero.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [one, one] x) +
    (8) * (one.kernel x * hpl [zero, zero] x) +
    (8) * (one.kernel x * hpl [zero, one] x) +
    (8) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi3fN3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3fN3 (i8Psi3fdN3 x) x := by
  unfold i8Psi3fN3 i8Psi3fdN3
  exact ((((((((((((((hasDerivAt_const x (-15)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₃⁽f⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi3fN4 (x : ℝ) : ℝ :=
    (-7 / 8) +
    (-5 / 4) * hpl [zero] x +
    (-3) * hpl [one] x +
    (-3 / 2) * hpl [zero, zero] x +
    (-4) * hpl [zero, one] x +
    (-4) * hpl [one, zero] x +
    (-10) * hpl [one, one] x +
    (3) * hpl [zero, zero, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (4) * hpl [zero, one, one] x +
    (4) * hpl [one, zero, zero] x +
    (4) * hpl [one, zero, one] x +
    (4) * hpl [one, one, zero] x

/-- The derivative of `i8Psi3fN4`. -/
noncomputable def i8Psi3fdN4 (x : ℝ) : ℝ :=
    0 +
    (-5 / 4) * (zero.kernel x * hpl [] x) +
    (-3) * (one.kernel x * hpl [] x) +
    (-3 / 2) * (zero.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [one] x) +
    (-4) * (one.kernel x * hpl [zero] x) +
    (-10) * (one.kernel x * hpl [one] x) +
    (3) * (zero.kernel x * hpl [zero, zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [one, one] x) +
    (4) * (one.kernel x * hpl [zero, zero] x) +
    (4) * (one.kernel x * hpl [zero, one] x) +
    (4) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi3fN4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3fN4 (i8Psi3fdN4 x) x := by
  unfold i8Psi3fN4 i8Psi3fdN4
  exact ((((((((((((((hasDerivAt_const x (-7 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-5 / 4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (4)))

/-- The part of `Ψ₃⁽f⁾` with constant coefficients. -/
noncomputable def i8Psi3fW (x : ℝ) : ℝ :=
    (-6) * hpl [zero, zero, zero, zero] x +
    (-8) * hpl [zero, zero, zero, one] x +
    (-8) * hpl [zero, zero, one, zero] x +
    (-8) * hpl [zero, zero, one, one] x +
    (-8) * hpl [zero, one, zero, zero] x +
    (-8) * hpl [zero, one, zero, one] x +
    (-8) * hpl [zero, one, one, zero] x

/-- The derivative of `i8Psi3fW`. -/
noncomputable def i8Psi3fdW (x : ℝ) : ℝ :=
    (-6) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-8) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, one, one] x) +
    (-8) * (zero.kernel x * hpl [one, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [one, zero, one] x) +
    (-8) * (zero.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi3fW {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3fW (i8Psi3fdW x) x := by
  unfold i8Psi3fW i8Psi3fdW
  exact ((((((((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-6)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (-8)))

/-- The piece `Ψ₃⁽f⁾` of the primitive of `p₃ dt/dξ`. -/
noncomputable def i8Psi3f (x : ℝ) : ℝ :=
  (i8Psi3fN0 x + x * i8Psi3fN1 x + x ^ 2 * i8Psi3fN2 x + x ^ 3 * i8Psi3fN3 x +
    x ^ 4 * i8Psi3fN4 x) / x ^ 2 + i8Psi3fW x

/-- The derivative of `Ψ₃⁽f⁾`. -/
noncomputable def i8Psi3fD (x : ℝ) : ℝ :=
  ((i8Psi3fdN0 x + (i8Psi3fN1 x + x * i8Psi3fdN1 x) +
      (2 * x * i8Psi3fN2 x + x ^ 2 * i8Psi3fdN2 x) +
      (3 * x ^ 2 * i8Psi3fN3 x + x ^ 3 * i8Psi3fdN3 x) +
      (4 * x ^ 3 * i8Psi3fN4 x + x ^ 4 * i8Psi3fdN4 x)) * x ^ 2 -
    (i8Psi3fN0 x + x * i8Psi3fN1 x + x ^ 2 * i8Psi3fN2 x + x ^ 3 * i8Psi3fN3 x +
      x ^ 4 * i8Psi3fN4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi3fdW x

theorem hasDerivAt_i8Psi3f {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3f (i8Psi3fD x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := (((((hasDerivAt_i8Psi3fN0 hx).add (X.mul (hasDerivAt_i8Psi3fN1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi3fN2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi3fN3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi3fN4 hx))).div (X.pow 2) (pow_ne_zero 2 h0) |>.add
    (hasDerivAt_i8Psi3fW hx)
  unfold i8Psi3f
  refine e.congr_deriv ?_
  unfold i8Psi3fD
  simp only [Pi.pow_apply]
  norm_num

/-- The part `t λ² β₁ A₀` of `p₃` in `ξ`. -/
noncomputable def i8P3xf (x : ℝ) : ℝ :=
  (1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 2 / 2 *
    (2 * (2 + Real.log x * (1 + x) / (1 - x)) * (x / (1 - x)))

/-- **`(Ψ₃⁽f⁾)'(ξ) ξ' = p₃⁽f⁾`**, in terms of `ξ`. -/
theorem i8Psi3fD_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3fD x * (-x ^ 2 / (1 - x ^ 2)) = i8P3xf x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi3fD i8Psi3fN0 i8Psi3fN1 i8Psi3fN2 i8Psi3fN3 i8Psi3fN4 i8Psi3fdN0 i8Psi3fdN1
    i8Psi3fdN2 i8Psi3fdN3 i8Psi3fdN4 i8Psi3fdW i8P3xf
  simp only [kernel_zero, kernel_one, hpl_nil, hpl_zero, i13hw_00, i13hw_10 hx, i13hw_11 hx,
    i13hw_000, i13hw_010 hx, i13hw_100 hx, i13hw_101 hx, i13hw_110 hx, i13_log_one_sub_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
