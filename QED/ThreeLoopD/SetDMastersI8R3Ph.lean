/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R3Pg

/-!
# Set (d), master `I₈`: a primitive of `p₃`, piece `h`

`p₃` splits as `p₃⁽ᵃ⁾ + p₃⁽ᵇ⁾ + p₃⁽ᶜ⁾` by the power of `λ = log t` (`QED.ThreeLoopD.i8P3xh`).
The piece `Ψ₃⁽h⁾` (`QED.ThreeLoopD.i8Psi3h`), a combination of harmonic polylogarithms of weight
at most four with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the shuffle-algebra engine of
the campaign, is a primitive of `p₃⁽h⁾ dt/dξ` (`QED.ThreeLoopD.i8Psi3hD_mul`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi3h`, `QED.ThreeLoopD.i8Psi3hD_mul`.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₃⁽h⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi3hN0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi3hN0`. -/
noncomputable def i8Psi3hdN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi3hN0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3hN0 (i8Psi3hdN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₃⁽h⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi3hN1 (x : ℝ) : ℝ :=
    (1) +
    (1) * hpl [zero] x +
    (2) * hpl [one] x +
    (1) * hpl [zero, zero] x +
    (2) * hpl [zero, one] x +
    (2) * hpl [one, zero] x +
    (4) * hpl [one, one] x +
    (1) * hpl [zero, zero, zero] x +
    (2) * hpl [zero, zero, one] x +
    (2) * hpl [zero, one, zero] x +
    (4) * hpl [zero, one, one] x +
    (2) * hpl [one, zero, zero] x +
    (4) * hpl [one, zero, one] x +
    (4) * hpl [one, one, zero] x +
    (8) * hpl [one, one, one] x

/-- The derivative of `i8Psi3hN1`. -/
noncomputable def i8Psi3hdN1 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (2) * (one.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (4) * (one.kernel x * hpl [one] x) +
    (1) * (zero.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (2) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [one, one] x) +
    (2) * (one.kernel x * hpl [zero, zero] x) +
    (4) * (one.kernel x * hpl [zero, one] x) +
    (4) * (one.kernel x * hpl [one, zero] x) +
    (8) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi3hN1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3hN1 (i8Psi3hdN1 x) x := by
  unfold i8Psi3hN1 i8Psi3hdN1
  exact (((((((((((((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (8)))

/-- The part of `ξ² Ψ₃⁽h⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi3hN2 (x : ℝ) : ℝ :=
    (-2) * hpl [zero] x +
    (-3 / 4) * hpl [one] x +
    (-2) * hpl [zero, zero] x +
    (-4) * hpl [zero, one] x +
    (-3 / 2) * hpl [one, zero] x +
    (-3) * hpl [one, one] x +
    (-2) * hpl [zero, zero, zero] x +
    (-4) * hpl [zero, zero, one] x +
    (-4) * hpl [zero, one, zero] x +
    (-8) * hpl [zero, one, one] x +
    (-3) * hpl [one, zero, zero] x +
    (-6) * hpl [one, zero, one] x +
    (-6) * hpl [one, one, zero] x +
    (-12) * hpl [one, one, one] x

/-- The derivative of `i8Psi3hN2`. -/
noncomputable def i8Psi3hdN2 (x : ℝ) : ℝ :=
    (-2) * (zero.kernel x * hpl [] x) +
    (-3 / 4) * (one.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [zero] x) +
    (-4) * (zero.kernel x * hpl [one] x) +
    (-3 / 2) * (one.kernel x * hpl [zero] x) +
    (-3) * (one.kernel x * hpl [one] x) +
    (-2) * (zero.kernel x * hpl [zero, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, one] x) +
    (-4) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, one] x) +
    (-3) * (one.kernel x * hpl [zero, zero] x) +
    (-6) * (one.kernel x * hpl [zero, one] x) +
    (-6) * (one.kernel x * hpl [one, zero] x) +
    (-12) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi3hN2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3hN2 (i8Psi3hdN2 x) x := by
  unfold i8Psi3hN2 i8Psi3hdN2
  exact (((((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-3 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-3 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-3))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₃⁽h⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi3hN3 (x : ℝ) : ℝ :=
    (-3 / 4) +
    (-1 / 2) * hpl [zero] x +
    (-1) * hpl [one] x +
    (1) * hpl [zero, zero, zero] x +
    (2) * hpl [zero, zero, one] x +
    (2) * hpl [zero, one, zero] x +
    (4) * hpl [zero, one, one] x +
    (2) * hpl [one, zero, zero] x +
    (4) * hpl [one, zero, one] x +
    (4) * hpl [one, one, zero] x +
    (8) * hpl [one, one, one] x

/-- The derivative of `i8Psi3hN3`. -/
noncomputable def i8Psi3hdN3 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (-1) * (one.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (2) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [one, one] x) +
    (2) * (one.kernel x * hpl [zero, zero] x) +
    (4) * (one.kernel x * hpl [zero, one] x) +
    (4) * (one.kernel x * hpl [one, zero] x) +
    (8) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi3hN3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3hN3 (i8Psi3hdN3 x) x := by
  unfold i8Psi3hN3 i8Psi3hdN3
  exact (((((((((((hasDerivAt_const x (-3 / 4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (8)))

/-- The part of `ξ² Ψ₃⁽h⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi3hN4 (x : ℝ) : ℝ :=
    (-1 / 16) +
    (-1 / 8) * hpl [zero] x +
    (-1 / 4) * hpl [one] x +
    (-1 / 4) * hpl [zero, zero] x +
    (-1 / 2) * hpl [zero, one] x +
    (-1 / 2) * hpl [one, zero] x +
    (-1) * hpl [one, one] x +
    (-1 / 2) * hpl [zero, zero, zero] x +
    (-1) * hpl [zero, zero, one] x +
    (-1) * hpl [zero, one, zero] x +
    (-2) * hpl [zero, one, one] x +
    (-1) * hpl [one, zero, zero] x +
    (-2) * hpl [one, zero, one] x +
    (-2) * hpl [one, one, zero] x +
    (-4) * hpl [one, one, one] x

/-- The derivative of `i8Psi3hN4`. -/
noncomputable def i8Psi3hdN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 8) * (zero.kernel x * hpl [] x) +
    (-1 / 4) * (one.kernel x * hpl [] x) +
    (-1 / 4) * (zero.kernel x * hpl [zero] x) +
    (-1 / 2) * (zero.kernel x * hpl [one] x) +
    (-1 / 2) * (one.kernel x * hpl [zero] x) +
    (-1) * (one.kernel x * hpl [one] x) +
    (-1 / 2) * (zero.kernel x * hpl [zero, zero] x) +
    (-1) * (zero.kernel x * hpl [zero, one] x) +
    (-1) * (zero.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [one, one] x) +
    (-1) * (one.kernel x * hpl [zero, zero] x) +
    (-2) * (one.kernel x * hpl [zero, one] x) +
    (-2) * (one.kernel x * hpl [one, zero] x) +
    (-4) * (one.kernel x * hpl [one, one] x)

theorem hasDerivAt_i8Psi3hN4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3hN4 (i8Psi3hdN4 x) x := by
  unfold i8Psi3hN4 i8Psi3hdN4
  exact (((((((((((((((hasDerivAt_const x (-1 / 16)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 8))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1 / 4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-4)))

/-- The part of `Ψ₃⁽h⁾` with constant coefficients. -/
noncomputable def i8Psi3hW (x : ℝ) : ℝ :=
    (1) * hpl [zero, zero, zero, zero] x +
    (2) * hpl [zero, zero, zero, one] x +
    (2) * hpl [zero, zero, one, zero] x +
    (4) * hpl [zero, zero, one, one] x +
    (2) * hpl [zero, one, zero, zero] x +
    (4) * hpl [zero, one, zero, one] x +
    (4) * hpl [zero, one, one, zero] x +
    (8) * hpl [zero, one, one, one] x

/-- The derivative of `i8Psi3hW`. -/
noncomputable def i8Psi3hdW (x : ℝ) : ℝ :=
    (1) * (zero.kernel x * hpl [zero, zero, zero] x) +
    (2) * (zero.kernel x * hpl [zero, zero, one] x) +
    (2) * (zero.kernel x * hpl [zero, one, zero] x) +
    (4) * (zero.kernel x * hpl [zero, one, one] x) +
    (2) * (zero.kernel x * hpl [one, zero, zero] x) +
    (4) * (zero.kernel x * hpl [one, zero, one] x) +
    (4) * (zero.kernel x * hpl [one, one, zero] x) +
    (8) * (zero.kernel x * hpl [one, one, one] x)

theorem hasDerivAt_i8Psi3hW {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3hW (i8Psi3hdW x) x := by
  unfold i8Psi3hW i8Psi3hdW
  exact (((((((((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (1)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (8)))

/-- The piece `Ψ₃⁽h⁾` of the primitive of `p₃ dt/dξ`. -/
noncomputable def i8Psi3h (x : ℝ) : ℝ :=
  (i8Psi3hN0 x + x * i8Psi3hN1 x + x ^ 2 * i8Psi3hN2 x + x ^ 3 * i8Psi3hN3 x +
    x ^ 4 * i8Psi3hN4 x) / x ^ 2 + i8Psi3hW x

/-- The derivative of `Ψ₃⁽h⁾`. -/
noncomputable def i8Psi3hD (x : ℝ) : ℝ :=
  ((i8Psi3hdN0 x + (i8Psi3hN1 x + x * i8Psi3hdN1 x) +
      (2 * x * i8Psi3hN2 x + x ^ 2 * i8Psi3hdN2 x) +
      (3 * x ^ 2 * i8Psi3hN3 x + x ^ 3 * i8Psi3hdN3 x) +
      (4 * x ^ 3 * i8Psi3hN4 x + x ^ 4 * i8Psi3hdN4 x)) * x ^ 2 -
    (i8Psi3hN0 x + x * i8Psi3hN1 x + x ^ 2 * i8Psi3hN2 x + x ^ 3 * i8Psi3hN3 x +
      x ^ 4 * i8Psi3hN4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi3hdW x

theorem hasDerivAt_i8Psi3h {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi3h (i8Psi3hD x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := (((((hasDerivAt_i8Psi3hN0 hx).add (X.mul (hasDerivAt_i8Psi3hN1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi3hN2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi3hN3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi3hN4 hx))).div (X.pow 2) (pow_ne_zero 2 h0) |>.add
    (hasDerivAt_i8Psi3hW hx)
  unfold i8Psi3h
  refine e.congr_deriv ?_
  unfold i8Psi3hD
  simp only [Pi.pow_apply]
  norm_num

/-- The part `-t λ³/6 A₀` of `p₃` in `ξ`. -/
noncomputable def i8P3xh (x : ℝ) : ℝ :=
  -((1 - x) ^ 2 / x * (2 * Real.log (1 - x) - Real.log x) ^ 3 / 6 * (x / (1 - x)))

/-- **`(Ψ₃⁽h⁾)'(ξ) ξ' = p₃⁽h⁾`**, in terms of `ξ`. -/
theorem i8Psi3hD_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi3hD x * (-x ^ 2 / (1 - x ^ 2)) = i8P3xh x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi3hD i8Psi3hN0 i8Psi3hN1 i8Psi3hN2 i8Psi3hN3 i8Psi3hN4 i8Psi3hdN0 i8Psi3hdN1
    i8Psi3hdN2 i8Psi3hdN3 i8Psi3hdN4 i8Psi3hdW i8P3xh
  simp only [kernel_zero, kernel_one, hpl_nil, hpl_zero, i13hw_00, i13hw_10 hx, i13hw_11 hx,
    i13hw_000, i13hw_010 hx, i13hw_100 hx, i13hw_101 hx, i13hw_110 hx, i13hw_111 hx,
    i13_log_one_sub_eq hx]
  field_simp
  ring

end QED.ThreeLoopD
