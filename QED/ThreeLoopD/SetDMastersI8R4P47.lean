/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P46

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 151 to 152

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s151`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s151D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s151`, `QED.ThreeLoopD.i8Psi4s151D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s151k0N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s151k0N0`. -/
noncomputable def i8Psi4s151k0dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s151k0N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k0N0 (i8Psi4s151k0dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s151k0N1 (x : ℝ) : ℝ :=
    (32) * hpl [one, one] x +
    (32) * hpl [zero, one, one] x +
    (16) * hpl [one, zero, one] x +
    (16) * hpl [one, one, zero] x +
    (16) * hpl [zero, zero, one, one] x

/-- The derivative of `i8Psi4s151k0N1`. -/
noncomputable def i8Psi4s151k0dN1 (x : ℝ) : ℝ :=
    (32) * (one.kernel x * hpl [one] x) +
    (32) * (zero.kernel x * hpl [one, one] x) +
    (16) * (one.kernel x * hpl [zero, one] x) +
    (16) * (one.kernel x * hpl [one, zero] x) +
    (16) * (zero.kernel x * hpl [zero, one, one] x)

theorem hasDerivAt_i8Psi4s151k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k0N1 (i8Psi4s151k0dN1 x) x := by
  unfold i8Psi4s151k0N1 i8Psi4s151k0dN1
  exact ((((((hasDerivAt_hpl_cons one [one] hx).const_mul (32)).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s151k0N2 (x : ℝ) : ℝ :=
    (-3) * hpl [one] x +
    (-32) * hpl [zero, one] x +
    (-4) * hpl [one, zero] x +
    (-38) * hpl [one, one] x +
    (-24) * hpl [one, zero, one] x +
    (-24) * hpl [one, one, zero] x +
    (16) * hpl [zero, zero, one, one] x

/-- The derivative of `i8Psi4s151k0N2`. -/
noncomputable def i8Psi4s151k0dN2 (x : ℝ) : ℝ :=
    (-3) * (one.kernel x * hpl [] x) +
    (-32) * (zero.kernel x * hpl [one] x) +
    (-4) * (one.kernel x * hpl [zero] x) +
    (-38) * (one.kernel x * hpl [one] x) +
    (-24) * (one.kernel x * hpl [zero, one] x) +
    (-24) * (one.kernel x * hpl [one, zero] x) +
    (16) * (zero.kernel x * hpl [zero, one, one] x)

theorem hasDerivAt_i8Psi4s151k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k0N2 (i8Psi4s151k0dN2 x) x := by
  unfold i8Psi4s151k0N2 i8Psi4s151k0dN2
  exact ((((((((hasDerivAt_hpl_cons one [] hx).const_mul (-3)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-32))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-38))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-24))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s151k0N3 (x : ℝ) : ℝ :=
    (-1) +
    (4) * hpl [zero] x +
    (-2) * hpl [one] x +
    (8) * hpl [zero, one] x +
    (8) * hpl [one, zero] x +
    (16) * hpl [one, zero, one] x +
    (16) * hpl [one, one, zero] x +
    (16) * hpl [zero, zero, one, one] x

/-- The derivative of `i8Psi4s151k0N3`. -/
noncomputable def i8Psi4s151k0dN3 (x : ℝ) : ℝ :=
    0 +
    (4) * (zero.kernel x * hpl [] x) +
    (-2) * (one.kernel x * hpl [] x) +
    (8) * (zero.kernel x * hpl [one] x) +
    (8) * (one.kernel x * hpl [zero] x) +
    (16) * (one.kernel x * hpl [zero, one] x) +
    (16) * (one.kernel x * hpl [one, zero] x) +
    (16) * (zero.kernel x * hpl [zero, one, one] x)

theorem hasDerivAt_i8Psi4s151k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k0N3 (i8Psi4s151k0dN3 x) x := by
  unfold i8Psi4s151k0N3 i8Psi4s151k0dN3
  exact ((((((((hasDerivAt_const x (-1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s151k0N4 (x : ℝ) : ℝ :=
    (7 / 2) +
    (-2) * hpl [zero] x +
    (5) * hpl [one] x +
    (-4) * hpl [zero, one] x +
    (-4) * hpl [one, zero] x +
    (6) * hpl [one, one] x +
    (-12) * hpl [zero, one, one] x +
    (-8) * hpl [one, zero, one] x +
    (-8) * hpl [one, one, zero] x +
    (8) * hpl [zero, zero, one, one] x

/-- The derivative of `i8Psi4s151k0N4`. -/
noncomputable def i8Psi4s151k0dN4 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x) +
    (5) * (one.kernel x * hpl [] x) +
    (-4) * (zero.kernel x * hpl [one] x) +
    (-4) * (one.kernel x * hpl [zero] x) +
    (6) * (one.kernel x * hpl [one] x) +
    (-12) * (zero.kernel x * hpl [one, one] x) +
    (-8) * (one.kernel x * hpl [zero, one] x) +
    (-8) * (one.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one, one] x)

theorem hasDerivAt_i8Psi4s151k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k0N4 (i8Psi4s151k0dN4 x) x := by
  unfold i8Psi4s151k0N4 i8Psi4s151k0dN4
  exact ((((((((((hasDerivAt_const x (7 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (8)))

/-- The part of `Ψ₄⁽151⁾` with constant coefficients. -/
noncomputable def i8Psi4s151k0W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, zero, one] x +
    (-16) * hpl [zero, one, zero] x +
    (16) * hpl [zero, one, zero, one] x +
    (16) * hpl [zero, one, one, zero] x +
    (-16) * hpl [zero, zero, zero, one, one] x

/-- The derivative of `i8Psi4s151k0W`. -/
noncomputable def i8Psi4s151k0dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [zero, one] x) +
    (-16) * (zero.kernel x * hpl [one, zero] x) +
    (16) * (zero.kernel x * hpl [one, zero, one] x) +
    (16) * (zero.kernel x * hpl [one, one, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, zero, one, one] x)

theorem hasDerivAt_i8Psi4s151k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k0W (i8Psi4s151k0dW x) x := by
  unfold i8Psi4s151k0W i8Psi4s151k0dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one, one] hx).const_mul (-16)))

/-- Chunk 0 of the piece `Ψ₄⁽151⁾`. -/
noncomputable def i8Psi4s151k0 (x : ℝ) : ℝ :=
  (i8Psi4s151k0N0 x + x * i8Psi4s151k0N1 x + x ^ 2 * i8Psi4s151k0N2 x + x ^ 3 * i8Psi4s151k0N3 x +
    x ^ 4 * i8Psi4s151k0N4 x) / x ^ 2 + i8Psi4s151k0W x

/-- The derivative of `i8Psi4s151k0`. -/
noncomputable def i8Psi4s151k0D (x : ℝ) : ℝ :=
  ((i8Psi4s151k0dN0 x + (i8Psi4s151k0N1 x + x * i8Psi4s151k0dN1 x) + (2 * x * i8Psi4s151k0N2 x +
    x ^ 2 * i8Psi4s151k0dN2 x) + (3 * x ^ 2 * i8Psi4s151k0N3 x + x ^ 3 * i8Psi4s151k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s151k0N4 x + x ^ 4 * i8Psi4s151k0dN4 x)) * x ^ 2 - (i8Psi4s151k0N0 x +
    x * i8Psi4s151k0N1 x + x ^ 2 * i8Psi4s151k0N2 x + x ^ 3 * i8Psi4s151k0N3 x +
    x ^ 4 * i8Psi4s151k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s151k0dW x

theorem hasDerivAt_i8Psi4s151k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k0 (i8Psi4s151k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s151k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s151k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s151k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s151k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s151k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s151k0W hx)
  unfold i8Psi4s151k0
  refine e.congr_deriv ?_
  unfold i8Psi4s151k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽151⁾` over words. -/
noncomputable def i8P4w151k0 (x : ℝ) : ℝ :=
    (16 - 16 * x) * hpl [zero, one, one] x +
    (16 - 16 * x) * hpl [one, zero, one] x +
    (16 - 16 * x) * hpl [one, one, zero] x +
    (16 + 16 * x) * hpl [zero, zero, one, one] x

theorem i8Psi4s151k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s151k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w151k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s151k0D i8Psi4s151k0N0 i8Psi4s151k0N1 i8Psi4s151k0N2 i8Psi4s151k0N3 i8Psi4s151k0N4
    i8Psi4s151k0dN0 i8Psi4s151k0dN1 i8Psi4s151k0dN2 i8Psi4s151k0dN3 i8Psi4s151k0dN4 i8Psi4s151k0dW
    i8P4w151k0
  simp only [kernel_zero, kernel_one, hpl_nil]
  generalize hpl [zero, zero, zero, one, one] x = v0 at *
  generalize hpl [zero, zero, one, one] x = v1 at *
  generalize hpl [zero, one, zero, one] x = v2 at *
  generalize hpl [zero, one, one, zero] x = v3 at *
  generalize hpl [zero, zero, one] x = v4 at *
  generalize hpl [zero, one, zero] x = v5 at *
  generalize hpl [zero, one, one] x = v6 at *
  generalize hpl [one, zero, one] x = v7 at *
  generalize hpl [one, one, zero] x = v8 at *
  generalize hpl [zero, one] x = v9 at *
  generalize hpl [one, zero] x = v10 at *
  generalize hpl [one, one] x = v11 at *
  generalize hpl [zero] x = v12 at *
  generalize hpl [one] x = v13 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s151k1N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s151k1N0`. -/
noncomputable def i8Psi4s151k1dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s151k1N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k1N0 (i8Psi4s151k1dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s151k1N1 (x : ℝ) : ℝ :=
    (16) * hpl [one, zero, one] x +
    (16) * hpl [one, one, zero] x +
    (16) * hpl [zero, one, zero, one] x +
    (16) * hpl [zero, one, one, zero] x +
    (16) * hpl [one, zero, zero, one] x +
    (16) * hpl [one, zero, one, zero] x

/-- The derivative of `i8Psi4s151k1N1`. -/
noncomputable def i8Psi4s151k1dN1 (x : ℝ) : ℝ :=
    (16) * (one.kernel x * hpl [zero, one] x) +
    (16) * (one.kernel x * hpl [one, zero] x) +
    (16) * (zero.kernel x * hpl [one, zero, one] x) +
    (16) * (zero.kernel x * hpl [one, one, zero] x) +
    (16) * (one.kernel x * hpl [zero, zero, one] x) +
    (16) * (one.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s151k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k1N1 (i8Psi4s151k1dN1 x) x := by
  unfold i8Psi4s151k1N1 i8Psi4s151k1dN1
  exact (((((((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s151k1N2 (x : ℝ) : ℝ :=
    (-46) * hpl [one] x +
    (48) * hpl [one, zero] x +
    (-16) * hpl [zero, zero, one] x +
    (-16) * hpl [zero, one, zero] x +
    (4) * hpl [one, zero, one] x +
    (4) * hpl [one, one, zero] x +
    (-40) * hpl [one, zero, zero, one] x +
    (-40) * hpl [one, zero, one, zero] x

/-- The derivative of `i8Psi4s151k1N2`. -/
noncomputable def i8Psi4s151k1dN2 (x : ℝ) : ℝ :=
    (-46) * (one.kernel x * hpl [] x) +
    (48) * (one.kernel x * hpl [zero] x) +
    (-16) * (zero.kernel x * hpl [zero, one] x) +
    (-16) * (zero.kernel x * hpl [one, zero] x) +
    (4) * (one.kernel x * hpl [zero, one] x) +
    (4) * (one.kernel x * hpl [one, zero] x) +
    (-40) * (one.kernel x * hpl [zero, zero, one] x) +
    (-40) * (one.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s151k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k1N2 (i8Psi4s151k1dN2 x) x := by
  unfold i8Psi4s151k1N2 i8Psi4s151k1dN2
  exact (((((((((hasDerivAt_hpl_cons one [] hx).const_mul (-46)).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (-40)))

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s151k1N3 (x : ℝ) : ℝ :=
    (94) +
    (-48) * hpl [zero] x +
    (44) * hpl [one] x +
    (-44) * hpl [zero, one] x +
    (-44) * hpl [one, zero] x +
    (24) * hpl [zero, zero, one] x +
    (24) * hpl [zero, one, zero] x +
    (-16) * hpl [one, zero, one] x +
    (-16) * hpl [one, one, zero] x +
    (16) * hpl [zero, one, zero, one] x +
    (16) * hpl [zero, one, one, zero] x +
    (16) * hpl [one, zero, zero, one] x +
    (16) * hpl [one, zero, one, zero] x

/-- The derivative of `i8Psi4s151k1N3`. -/
noncomputable def i8Psi4s151k1dN3 (x : ℝ) : ℝ :=
    0 +
    (-48) * (zero.kernel x * hpl [] x) +
    (44) * (one.kernel x * hpl [] x) +
    (-44) * (zero.kernel x * hpl [one] x) +
    (-44) * (one.kernel x * hpl [zero] x) +
    (24) * (zero.kernel x * hpl [zero, one] x) +
    (24) * (zero.kernel x * hpl [one, zero] x) +
    (-16) * (one.kernel x * hpl [zero, one] x) +
    (-16) * (one.kernel x * hpl [one, zero] x) +
    (16) * (zero.kernel x * hpl [one, zero, one] x) +
    (16) * (zero.kernel x * hpl [one, one, zero] x) +
    (16) * (one.kernel x * hpl [zero, zero, one] x) +
    (16) * (one.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s151k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k1N3 (i8Psi4s151k1dN3 x) x := by
  unfold i8Psi4s151k1N3 i8Psi4s151k1dN3
  exact (((((((((((((hasDerivAt_const x (94)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (44))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-44))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-44))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s151k1N4 (x : ℝ) : ℝ :=
    (2) +
    (-2) * hpl [zero] x +
    (2) * hpl [one] x +
    (-4) * hpl [zero, one] x +
    (-4) * hpl [one, zero] x +
    (4) * hpl [zero, zero, one] x +
    (4) * hpl [zero, one, zero] x +
    (-4) * hpl [one, zero, one] x +
    (-4) * hpl [one, one, zero] x +
    (8) * hpl [zero, one, zero, one] x +
    (8) * hpl [zero, one, one, zero] x +
    (8) * hpl [one, zero, zero, one] x +
    (8) * hpl [one, zero, one, zero] x

/-- The derivative of `i8Psi4s151k1N4`. -/
noncomputable def i8Psi4s151k1dN4 (x : ℝ) : ℝ :=
    0 +
    (-2) * (zero.kernel x * hpl [] x) +
    (2) * (one.kernel x * hpl [] x) +
    (-4) * (zero.kernel x * hpl [one] x) +
    (-4) * (one.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (-4) * (one.kernel x * hpl [zero, one] x) +
    (-4) * (one.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [one, zero, one] x) +
    (8) * (zero.kernel x * hpl [one, one, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero, one] x) +
    (8) * (one.kernel x * hpl [zero, one, zero] x)

theorem hasDerivAt_i8Psi4s151k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k1N4 (i8Psi4s151k1dN4 x) x := by
  unfold i8Psi4s151k1N4 i8Psi4s151k1dN4
  exact (((((((((((((hasDerivAt_const x (2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (8)))

/-- The part of `Ψ₄⁽151⁾` with constant coefficients. -/
noncomputable def i8Psi4s151k1W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, zero, zero, one] x +
    (-16) * hpl [zero, zero, one, zero] x +
    (-16) * hpl [zero, zero, one, zero, one] x +
    (-16) * hpl [zero, zero, one, one, zero] x +
    (-16) * hpl [zero, one, zero, zero, one] x +
    (-16) * hpl [zero, one, zero, one, zero] x

/-- The derivative of `i8Psi4s151k1W`. -/
noncomputable def i8Psi4s151k1dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-16) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, one, zero, one] x) +
    (-16) * (zero.kernel x * hpl [zero, one, one, zero] x) +
    (-16) * (zero.kernel x * hpl [one, zero, zero, one] x) +
    (-16) * (zero.kernel x * hpl [one, zero, one, zero] x)

theorem hasDerivAt_i8Psi4s151k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k1W (i8Psi4s151k1dW x) x := by
  unfold i8Psi4s151k1W i8Psi4s151k1dW
  exact (((((((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one, zero] hx).const_mul (-16)))

/-- Chunk 1 of the piece `Ψ₄⁽151⁾`. -/
noncomputable def i8Psi4s151k1 (x : ℝ) : ℝ :=
  (i8Psi4s151k1N0 x + x * i8Psi4s151k1N1 x + x ^ 2 * i8Psi4s151k1N2 x + x ^ 3 * i8Psi4s151k1N3 x +
    x ^ 4 * i8Psi4s151k1N4 x) / x ^ 2 + i8Psi4s151k1W x

/-- The derivative of `i8Psi4s151k1`. -/
noncomputable def i8Psi4s151k1D (x : ℝ) : ℝ :=
  ((i8Psi4s151k1dN0 x + (i8Psi4s151k1N1 x + x * i8Psi4s151k1dN1 x) + (2 * x * i8Psi4s151k1N2 x +
    x ^ 2 * i8Psi4s151k1dN2 x) + (3 * x ^ 2 * i8Psi4s151k1N3 x + x ^ 3 * i8Psi4s151k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s151k1N4 x + x ^ 4 * i8Psi4s151k1dN4 x)) * x ^ 2 - (i8Psi4s151k1N0 x +
    x * i8Psi4s151k1N1 x + x ^ 2 * i8Psi4s151k1N2 x + x ^ 3 * i8Psi4s151k1N3 x +
    x ^ 4 * i8Psi4s151k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s151k1dW x

theorem hasDerivAt_i8Psi4s151k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k1 (i8Psi4s151k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s151k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s151k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s151k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s151k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s151k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s151k1W hx)
  unfold i8Psi4s151k1
  refine e.congr_deriv ?_
  unfold i8Psi4s151k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽151⁾` over words. -/
noncomputable def i8P4w151k1 (x : ℝ) : ℝ :=
    (16 + 16 * x) * hpl [zero, one, zero, one] x +
    (16 + 16 * x) * hpl [zero, one, one, zero] x +
    (16 + 16 * x) * hpl [one, zero, zero, one] x +
    (16 + 16 * x) * hpl [one, zero, one, zero] x

theorem i8Psi4s151k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s151k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w151k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s151k1D i8Psi4s151k1N0 i8Psi4s151k1N1 i8Psi4s151k1N2 i8Psi4s151k1N3 i8Psi4s151k1N4
    i8Psi4s151k1dN0 i8Psi4s151k1dN1 i8Psi4s151k1dN2 i8Psi4s151k1dN3 i8Psi4s151k1dN4 i8Psi4s151k1dW
    i8P4w151k1
  simp only [kernel_zero, kernel_one, hpl_nil]
  generalize hpl [zero, zero, one, zero, one] x = v0 at *
  generalize hpl [zero, zero, one, one, zero] x = v1 at *
  generalize hpl [zero, one, zero, zero, one] x = v2 at *
  generalize hpl [zero, one, zero, one, zero] x = v3 at *
  generalize hpl [zero, zero, zero, one] x = v4 at *
  generalize hpl [zero, zero, one, zero] x = v5 at *
  generalize hpl [zero, one, zero, one] x = v6 at *
  generalize hpl [zero, one, one, zero] x = v7 at *
  generalize hpl [one, zero, zero, one] x = v8 at *
  generalize hpl [one, zero, one, zero] x = v9 at *
  generalize hpl [zero, zero, one] x = v10 at *
  generalize hpl [zero, one, zero] x = v11 at *
  generalize hpl [one, zero, one] x = v12 at *
  generalize hpl [one, one, zero] x = v13 at *
  generalize hpl [zero, one] x = v14 at *
  generalize hpl [one, zero] x = v15 at *
  generalize hpl [zero] x = v16 at *
  generalize hpl [one] x = v17 at *
  field_simp
  ring

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s151k2N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s151k2N0`. -/
noncomputable def i8Psi4s151k2dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s151k2N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k2N0 (i8Psi4s151k2dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s151k2N1 (x : ℝ) : ℝ :=
    (16) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s151k2N1`. -/
noncomputable def i8Psi4s151k2dN1 (x : ℝ) : ℝ :=
    (16) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s151k2N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k2N1 (i8Psi4s151k2dN1 x) x := by
  unfold i8Psi4s151k2N1 i8Psi4s151k2dN1
  exact ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (16))

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s151k2N2 (x : ℝ) : ℝ :=
    (-28) * hpl [one, zero, zero] x +
    (-40) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s151k2N2`. -/
noncomputable def i8Psi4s151k2dN2 (x : ℝ) : ℝ :=
    (-28) * (one.kernel x * hpl [zero, zero] x) +
    (-40) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s151k2N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k2N2 (i8Psi4s151k2dN2 x) x := by
  unfold i8Psi4s151k2N2 i8Psi4s151k2dN2
  exact (((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-28)).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (-40)))

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s151k2N3 (x : ℝ) : ℝ :=
    (28) +
    (-28) * hpl [zero] x +
    (28) * hpl [zero, zero] x +
    (24) * hpl [one, zero, zero] x +
    (16) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s151k2N3`. -/
noncomputable def i8Psi4s151k2dN3 (x : ℝ) : ℝ :=
    0 +
    (-28) * (zero.kernel x * hpl [] x) +
    (28) * (zero.kernel x * hpl [zero] x) +
    (24) * (one.kernel x * hpl [zero, zero] x) +
    (16) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s151k2N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k2N3 (i8Psi4s151k2dN3 x) x := by
  unfold i8Psi4s151k2N3 i8Psi4s151k2dN3
  exact (((((hasDerivAt_const x (28)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽151⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s151k2N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1) * hpl [zero] x +
    (2) * hpl [zero, zero] x +
    (4) * hpl [one, zero, zero] x +
    (8) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s151k2N4`. -/
noncomputable def i8Psi4s151k2dN4 (x : ℝ) : ℝ :=
    0 +
    (-1) * (zero.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [zero] x) +
    (4) * (one.kernel x * hpl [zero, zero] x) +
    (8) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s151k2N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k2N4 (i8Psi4s151k2dN4 x) x := by
  unfold i8Psi4s151k2N4 i8Psi4s151k2dN4
  exact (((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (8)))

/-- The part of `Ψ₄⁽151⁾` with constant coefficients. -/
noncomputable def i8Psi4s151k2W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, one, zero, zero] x +
    (-16) * hpl [zero, one, one, zero, zero] x

/-- The derivative of `i8Psi4s151k2W`. -/
noncomputable def i8Psi4s151k2dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [one, zero, zero] x) +
    (-16) * (zero.kernel x * hpl [one, one, zero, zero] x)

theorem hasDerivAt_i8Psi4s151k2W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k2W (i8Psi4s151k2dW x) x := by
  unfold i8Psi4s151k2W i8Psi4s151k2dW
  exact (((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [one, one, zero, zero] hx).const_mul (-16)))

/-- Chunk 2 of the piece `Ψ₄⁽151⁾`. -/
noncomputable def i8Psi4s151k2 (x : ℝ) : ℝ :=
  (i8Psi4s151k2N0 x + x * i8Psi4s151k2N1 x + x ^ 2 * i8Psi4s151k2N2 x + x ^ 3 * i8Psi4s151k2N3 x +
    x ^ 4 * i8Psi4s151k2N4 x) / x ^ 2 + i8Psi4s151k2W x

/-- The derivative of `i8Psi4s151k2`. -/
noncomputable def i8Psi4s151k2D (x : ℝ) : ℝ :=
  ((i8Psi4s151k2dN0 x + (i8Psi4s151k2N1 x + x * i8Psi4s151k2dN1 x) + (2 * x * i8Psi4s151k2N2 x +
    x ^ 2 * i8Psi4s151k2dN2 x) + (3 * x ^ 2 * i8Psi4s151k2N3 x + x ^ 3 * i8Psi4s151k2dN3 x) +
    (4 * x ^ 3 * i8Psi4s151k2N4 x + x ^ 4 * i8Psi4s151k2dN4 x)) * x ^ 2 - (i8Psi4s151k2N0 x +
    x * i8Psi4s151k2N1 x + x ^ 2 * i8Psi4s151k2N2 x + x ^ 3 * i8Psi4s151k2N3 x +
    x ^ 4 * i8Psi4s151k2N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s151k2dW x

theorem hasDerivAt_i8Psi4s151k2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151k2 (i8Psi4s151k2D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s151k2N0 hx).add (X.mul (hasDerivAt_i8Psi4s151k2N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s151k2N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s151k2N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s151k2N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s151k2W hx)
  unfold i8Psi4s151k2
  refine e.congr_deriv ?_
  unfold i8Psi4s151k2D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 2 of `p₄⁽151⁾` over words. -/
noncomputable def i8P4w151k2 (x : ℝ) : ℝ :=
    (16 + 16 * x) * hpl [one, one, zero, zero] x

theorem i8Psi4s151k2D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s151k2D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w151k2 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s151k2D i8Psi4s151k2N0 i8Psi4s151k2N1 i8Psi4s151k2N2 i8Psi4s151k2N3 i8Psi4s151k2N4
    i8Psi4s151k2dN0 i8Psi4s151k2dN1 i8Psi4s151k2dN2 i8Psi4s151k2dN3 i8Psi4s151k2dN4 i8Psi4s151k2dW
    i8P4w151k2
  simp only [kernel_zero, kernel_one, hpl_nil]
  generalize hpl [zero, one, one, zero, zero] x = v0 at *
  generalize hpl [zero, one, zero, zero] x = v1 at *
  generalize hpl [one, one, zero, zero] x = v2 at *
  generalize hpl [one, zero, zero] x = v3 at *
  generalize hpl [zero, zero] x = v4 at *
  generalize hpl [zero] x = v5 at *
  field_simp
  ring

/-- The piece `Ψ₄⁽151⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s151 (x : ℝ) : ℝ :=
  i8Psi4s151k0 x + i8Psi4s151k1 x + i8Psi4s151k2 x

/-- The derivative of `Ψ₄⁽151⁾`. -/
noncomputable def i8Psi4s151D (x : ℝ) : ℝ :=
  i8Psi4s151k0D x + i8Psi4s151k1D x + i8Psi4s151k2D x

theorem hasDerivAt_i8Psi4s151 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s151 (i8Psi4s151D x) x := by
  unfold i8Psi4s151 i8Psi4s151D
  exact (((hasDerivAt_i8Psi4s151k0 hx).add (hasDerivAt_i8Psi4s151k1 hx)).add
    (hasDerivAt_i8Psi4s151k2 hx))

/-- The sub-piece 151 of `p₄` in `ξ`: from `t B1 A0 (-λ)^3/3!`, the term with `log^2 (1 -
  ξ) log^1 ξ`. -/
noncomputable def i8P4s151 (x : ℝ) : ℝ :=
  4 * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 2 * Real.log x * (2 + Real.log x * (1 + x) / (1 -
    x)) * (x / (1 - x))

/-- `p₄⁽151⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w151 (x : ℝ) : ℝ :=
  i8P4w151k0 x + i8P4w151k1 x + i8P4w151k2 x

theorem i8P4s151_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s151 x = i8P4w151 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s151 i8P4w151 i8P4w151k0 i8P4w151k1 i8P4w151k2
  simp only [i13hw_101 hx, i13hw_110 hx, i13hw_0101 hx, i13hw_0110 hx, i13hw_1001 hx, i13hw_1010 hx,
    i13hw_1100 hx, i13_log_one_sub_eq hx]
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
  generalize hpl [zero, zero, one, one, zero] x = v31 at *
  generalize hpl [zero, zero, one, one, one] x = v32 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v33 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v34 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v35 at *
  generalize hpl [zero, one, negOne, one, one] x = v36 at *
  generalize hpl [zero, one, zero, zero, one] x = v37 at *
  generalize hpl [zero, one, zero, one, negOne] x = v38 at *
  generalize hpl [zero, one, zero, one, zero] x = v39 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v40 at *
  generalize hpl [zero, one, one, negOne, one] x = v41 at *
  generalize hpl [zero, one, one, zero, zero] x = v42 at *
  generalize hpl [zero, one, one, one, negOne] x = v43 at *
  generalize hpl [zero, one, one, one, one] x = v44 at *
  generalize hpl [negOne, negOne, one, one] x = v45 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v46 at *
  generalize hpl [zero, negOne, negOne, one] x = v47 at *
  generalize hpl [zero, negOne, zero, one] x = v48 at *
  generalize hpl [zero, negOne, one, negOne] x = v49 at *
  generalize hpl [zero, negOne, one, one] x = v50 at *
  generalize hpl [zero, zero, negOne, negOne] x = v51 at *
  generalize hpl [zero, zero, negOne, one] x = v52 at *
  generalize hpl [zero, zero, zero, negOne] x = v53 at *
  generalize hpl [zero, zero, zero, one] x = v54 at *
  generalize hpl [zero, zero, one, negOne] x = v55 at *
  generalize hpl [zero, zero, one, zero] x = v56 at *
  generalize hpl [zero, zero, one, one] x = v57 at *
  generalize hpl [zero, one, negOne, negOne] x = v58 at *
  generalize hpl [zero, one, negOne, one] x = v59 at *
  generalize hpl [zero, one, zero, zero] x = v60 at *
  generalize hpl [zero, one, zero, one] x = v61 at *
  generalize hpl [zero, one, one, negOne] x = v62 at *
  generalize hpl [zero, one, one, zero] x = v63 at *
  generalize hpl [zero, one, one, one] x = v64 at *
  generalize hpl [one, zero, zero, one] x = v65 at *
  generalize hpl [one, zero, one, zero] x = v66 at *
  generalize hpl [one, one, zero, zero] x = v67 at *
  generalize hpl [negOne, negOne, one] x = v68 at *
  generalize hpl [negOne, one, one] x = v69 at *
  generalize hpl [zero, negOne, negOne] x = v70 at *
  generalize hpl [zero, negOne, one] x = v71 at *
  generalize hpl [zero, zero, negOne] x = v72 at *
  generalize hpl [zero, zero, one] x = v73 at *
  generalize hpl [zero, one, negOne] x = v74 at *
  generalize hpl [zero, one, zero] x = v75 at *
  generalize hpl [zero, one, one] x = v76 at *
  generalize hpl [one, zero, zero] x = v77 at *
  generalize hpl [one, zero, one] x = v78 at *
  generalize hpl [one, one, zero] x = v79 at *
  generalize hpl [negOne, one] x = v80 at *
  generalize hpl [zero, negOne] x = v81 at *
  generalize hpl [zero, zero] x = v82 at *
  generalize hpl [zero, one] x = v83 at *
  generalize hpl [one, zero] x = v84 at *
  generalize hpl [one, one] x = v85 at *
  generalize hpl [negOne] x = v86 at *
  generalize hpl [zero] x = v87 at *
  generalize hpl [one] x = v88 at *
  ring

/-- **`(Ψ₄⁽151⁾)'(ξ) ξ' = p₄⁽151⁾`**, in terms of `ξ`. -/
theorem i8Psi4s151D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s151D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s151 x := by
  rw [i8P4s151_eq_w hx]
  unfold i8Psi4s151D i8P4w151
  rw [← i8Psi4s151k0D_mul hx, ← i8Psi4s151k1D_mul hx, ← i8Psi4s151k2D_mul hx]
  ring

/-- The part of `ξ² Ψ₄⁽152⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s152N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s152N0`. -/
noncomputable def i8Psi4s152dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s152N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s152N0 (i8Psi4s152dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽152⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s152N1 (x : ℝ) : ℝ :=
    (48) * hpl [one, one, one] x +
    (16) * hpl [zero, one, one, one] x +
    (16) * hpl [one, zero, one, one] x +
    (16) * hpl [one, one, zero, one] x +
    (16) * hpl [one, one, one, zero] x

/-- The derivative of `i8Psi4s152N1`. -/
noncomputable def i8Psi4s152dN1 (x : ℝ) : ℝ :=
    (48) * (one.kernel x * hpl [one, one] x) +
    (16) * (zero.kernel x * hpl [one, one, one] x) +
    (16) * (one.kernel x * hpl [zero, one, one] x) +
    (16) * (one.kernel x * hpl [one, zero, one] x) +
    (16) * (one.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s152N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s152N1 (i8Psi4s152dN1 x) x := by
  unfold i8Psi4s152N1 i8Psi4s152dN1
  exact ((((((hasDerivAt_hpl_cons one [one, one] hx).const_mul (48)).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one, one, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽152⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s152N2 (x : ℝ) : ℝ :=
    (75) * hpl [one] x +
    (-30) * hpl [one, zero] x +
    (40) * hpl [one, one] x +
    (-48) * hpl [zero, one, one] x +
    (-28) * hpl [one, zero, one] x +
    (-28) * hpl [one, one, zero] x +
    (-44) * hpl [one, one, one] x +
    (32) * hpl [zero, one, one, one] x +
    (-40) * hpl [one, zero, one, one] x +
    (-40) * hpl [one, one, zero, one] x +
    (-40) * hpl [one, one, one, zero] x

/-- The derivative of `i8Psi4s152N2`. -/
noncomputable def i8Psi4s152dN2 (x : ℝ) : ℝ :=
    (75) * (one.kernel x * hpl [] x) +
    (-30) * (one.kernel x * hpl [zero] x) +
    (40) * (one.kernel x * hpl [one] x) +
    (-48) * (zero.kernel x * hpl [one, one] x) +
    (-28) * (one.kernel x * hpl [zero, one] x) +
    (-28) * (one.kernel x * hpl [one, zero] x) +
    (-44) * (one.kernel x * hpl [one, one] x) +
    (32) * (zero.kernel x * hpl [one, one, one] x) +
    (-40) * (one.kernel x * hpl [zero, one, one] x) +
    (-40) * (one.kernel x * hpl [one, zero, one] x) +
    (-40) * (one.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s152N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s152N2 (i8Psi4s152dN2 x) x := by
  unfold i8Psi4s152N2 i8Psi4s152dN2
  exact ((((((((((((hasDerivAt_hpl_cons one [] hx).const_mul (75)).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-30))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (40))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-48))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-44))).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (32))).add
      ((hasDerivAt_hpl_cons one [zero, one, one] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons one [one, zero, one] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons one [one, one, zero] hx).const_mul (-40)))

/-- The part of `ξ² Ψ₄⁽152⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s152N3 (x : ℝ) : ℝ :=
    (-105) +
    (30) * hpl [zero] x +
    (-68) * hpl [one] x +
    (28) * hpl [zero, one] x +
    (28) * hpl [one, zero] x +
    (-28) * hpl [one, one] x +
    (24) * hpl [zero, one, one] x +
    (24) * hpl [one, zero, one] x +
    (24) * hpl [one, one, zero] x +
    (16) * hpl [one, one, one] x +
    (16) * hpl [zero, one, one, one] x +
    (16) * hpl [one, zero, one, one] x +
    (16) * hpl [one, one, zero, one] x +
    (16) * hpl [one, one, one, zero] x

/-- The derivative of `i8Psi4s152N3`. -/
noncomputable def i8Psi4s152dN3 (x : ℝ) : ℝ :=
    0 +
    (30) * (zero.kernel x * hpl [] x) +
    (-68) * (one.kernel x * hpl [] x) +
    (28) * (zero.kernel x * hpl [one] x) +
    (28) * (one.kernel x * hpl [zero] x) +
    (-28) * (one.kernel x * hpl [one] x) +
    (24) * (zero.kernel x * hpl [one, one] x) +
    (24) * (one.kernel x * hpl [zero, one] x) +
    (24) * (one.kernel x * hpl [one, zero] x) +
    (16) * (one.kernel x * hpl [one, one] x) +
    (16) * (zero.kernel x * hpl [one, one, one] x) +
    (16) * (one.kernel x * hpl [zero, one, one] x) +
    (16) * (one.kernel x * hpl [one, zero, one] x) +
    (16) * (one.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s152N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s152N3 (i8Psi4s152dN3 x) x := by
  unfold i8Psi4s152N3 i8Psi4s152dN3
  exact ((((((((((((((hasDerivAt_const x (-105)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (30))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-68))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one, zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one, one, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽152⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s152N4 (x : ℝ) : ℝ :=
    (-4) +
    (1) * hpl [zero] x +
    (-7) * hpl [one] x +
    (2) * hpl [zero, one] x +
    (2) * hpl [one, zero] x +
    (-12) * hpl [one, one] x +
    (4) * hpl [zero, one, one] x +
    (4) * hpl [one, zero, one] x +
    (4) * hpl [one, one, zero] x +
    (-20) * hpl [one, one, one] x +
    (8) * hpl [zero, one, one, one] x +
    (8) * hpl [one, zero, one, one] x +
    (8) * hpl [one, one, zero, one] x +
    (8) * hpl [one, one, one, zero] x

/-- The derivative of `i8Psi4s152N4`. -/
noncomputable def i8Psi4s152dN4 (x : ℝ) : ℝ :=
    0 +
    (1) * (zero.kernel x * hpl [] x) +
    (-7) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (2) * (one.kernel x * hpl [zero] x) +
    (-12) * (one.kernel x * hpl [one] x) +
    (4) * (zero.kernel x * hpl [one, one] x) +
    (4) * (one.kernel x * hpl [zero, one] x) +
    (4) * (one.kernel x * hpl [one, zero] x) +
    (-20) * (one.kernel x * hpl [one, one] x) +
    (8) * (zero.kernel x * hpl [one, one, one] x) +
    (8) * (one.kernel x * hpl [zero, one, one] x) +
    (8) * (one.kernel x * hpl [one, zero, one] x) +
    (8) * (one.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s152N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s152N4 (i8Psi4s152dN4 x) x := by
  unfold i8Psi4s152N4 i8Psi4s152dN4
  exact ((((((((((((((hasDerivAt_const x (-4)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-7))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, one] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons zero [one, one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, one, zero] hx).const_mul (8)))

/-- The part of `Ψ₄⁽152⁾` with constant coefficients. -/
noncomputable def i8Psi4s152W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, zero, one, one] x +
    (-16) * hpl [zero, one, zero, one] x +
    (-16) * hpl [zero, one, one, zero] x +
    (-16) * hpl [zero, zero, one, one, one] x +
    (-16) * hpl [zero, one, zero, one, one] x +
    (-16) * hpl [zero, one, one, zero, one] x +
    (-16) * hpl [zero, one, one, one, zero] x

/-- The derivative of `i8Psi4s152W`. -/
noncomputable def i8Psi4s152dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [zero, one, one] x) +
    (-16) * (zero.kernel x * hpl [one, zero, one] x) +
    (-16) * (zero.kernel x * hpl [one, one, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, one, one, one] x) +
    (-16) * (zero.kernel x * hpl [one, zero, one, one] x) +
    (-16) * (zero.kernel x * hpl [one, one, zero, one] x) +
    (-16) * (zero.kernel x * hpl [one, one, one, zero] x)

theorem hasDerivAt_i8Psi4s152W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s152W (i8Psi4s152dW x) x := by
  unfold i8Psi4s152W i8Psi4s152dW
  exact ((((((((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, one, one, zero] hx).const_mul (-16)))

/-- The piece `Ψ₄⁽152⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s152 (x : ℝ) : ℝ :=
  (i8Psi4s152N0 x + x * i8Psi4s152N1 x + x ^ 2 * i8Psi4s152N2 x + x ^ 3 * i8Psi4s152N3 x +
    x ^ 4 * i8Psi4s152N4 x) / x ^ 2 + i8Psi4s152W x

/-- The derivative of `Ψ₄⁽152⁾`. -/
noncomputable def i8Psi4s152D (x : ℝ) : ℝ :=
  ((i8Psi4s152dN0 x + (i8Psi4s152N1 x + x * i8Psi4s152dN1 x) + (2 * x * i8Psi4s152N2 x +
    x ^ 2 * i8Psi4s152dN2 x) + (3 * x ^ 2 * i8Psi4s152N3 x + x ^ 3 * i8Psi4s152dN3 x) +
    (4 * x ^ 3 * i8Psi4s152N4 x + x ^ 4 * i8Psi4s152dN4 x)) * x ^ 2 - (i8Psi4s152N0 x +
    x * i8Psi4s152N1 x + x ^ 2 * i8Psi4s152N2 x + x ^ 3 * i8Psi4s152N3 x +
    x ^ 4 * i8Psi4s152N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s152dW x

theorem hasDerivAt_i8Psi4s152 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s152 (i8Psi4s152D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s152N0 hx).add (X.mul (hasDerivAt_i8Psi4s152N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s152N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s152N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s152N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s152W hx)
  unfold i8Psi4s152
  refine e.congr_deriv ?_
  unfold i8Psi4s152D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 152 of `p₄` in `ξ`: from `t B1 A0 (-λ)^3/3!`, the term with `log^3 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s152 (x : ℝ) : ℝ :=
  -((8 / 3) * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 3 * (2 + Real.log x * (1 + x) / (1 -
    x)) * (x / (1 - x)))

/-- `p₄⁽152⁾` written over words. -/
noncomputable def i8P4w152 (x : ℝ) : ℝ :=
    (32 - 32 * x) * hpl [one, one, one] x +
    (16 + 16 * x) * hpl [zero, one, one, one] x +
    (16 + 16 * x) * hpl [one, zero, one, one] x +
    (16 + 16 * x) * hpl [one, one, zero, one] x +
    (16 + 16 * x) * hpl [one, one, one, zero] x

theorem i8P4s152_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s152 x = i8P4w152 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s152 i8P4w152
  simp only [i13hw_111 hx, i13hw_1011 hx, i13hw_1101 hx, i13hw_1110 hx, i13_log_one_sub_eq hx]
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
  generalize hpl [zero, one, zero, one, one] x = v37 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v38 at *
  generalize hpl [zero, one, one, negOne, one] x = v39 at *
  generalize hpl [zero, one, one, zero, one] x = v40 at *
  generalize hpl [zero, one, one, one, negOne] x = v41 at *
  generalize hpl [zero, one, one, one, zero] x = v42 at *
  generalize hpl [zero, one, one, one, one] x = v43 at *
  generalize hpl [negOne, negOne, one, one] x = v44 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v45 at *
  generalize hpl [zero, negOne, negOne, one] x = v46 at *
  generalize hpl [zero, negOne, zero, one] x = v47 at *
  generalize hpl [zero, negOne, one, negOne] x = v48 at *
  generalize hpl [zero, negOne, one, one] x = v49 at *
  generalize hpl [zero, zero, negOne, negOne] x = v50 at *
  generalize hpl [zero, zero, negOne, one] x = v51 at *
  generalize hpl [zero, zero, zero, negOne] x = v52 at *
  generalize hpl [zero, zero, zero, one] x = v53 at *
  generalize hpl [zero, zero, one, negOne] x = v54 at *
  generalize hpl [zero, zero, one, one] x = v55 at *
  generalize hpl [zero, one, negOne, negOne] x = v56 at *
  generalize hpl [zero, one, negOne, one] x = v57 at *
  generalize hpl [zero, one, zero, one] x = v58 at *
  generalize hpl [zero, one, one, negOne] x = v59 at *
  generalize hpl [zero, one, one, zero] x = v60 at *
  generalize hpl [zero, one, one, one] x = v61 at *
  generalize hpl [one, zero, one, one] x = v62 at *
  generalize hpl [one, one, zero, one] x = v63 at *
  generalize hpl [one, one, one, zero] x = v64 at *
  generalize hpl [negOne, negOne, one] x = v65 at *
  generalize hpl [negOne, one, one] x = v66 at *
  generalize hpl [zero, negOne, negOne] x = v67 at *
  generalize hpl [zero, negOne, one] x = v68 at *
  generalize hpl [zero, zero, negOne] x = v69 at *
  generalize hpl [zero, zero, one] x = v70 at *
  generalize hpl [zero, one, negOne] x = v71 at *
  generalize hpl [zero, one, one] x = v72 at *
  generalize hpl [one, zero, one] x = v73 at *
  generalize hpl [one, one, zero] x = v74 at *
  generalize hpl [one, one, one] x = v75 at *
  generalize hpl [negOne, one] x = v76 at *
  generalize hpl [zero, negOne] x = v77 at *
  generalize hpl [zero, one] x = v78 at *
  generalize hpl [one, zero] x = v79 at *
  generalize hpl [one, one] x = v80 at *
  generalize hpl [negOne] x = v81 at *
  generalize hpl [zero] x = v82 at *
  generalize hpl [one] x = v83 at *
  ring

/-- **`(Ψ₄⁽152⁾)'(ξ) ξ' = p₄⁽152⁾`**, in terms of `ξ`. -/
theorem i8Psi4s152D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s152D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s152 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s152_eq_w hx]
  unfold i8Psi4s152D i8Psi4s152N0 i8Psi4s152N1 i8Psi4s152N2 i8Psi4s152N3 i8Psi4s152N4 i8Psi4s152dN0
    i8Psi4s152dN1 i8Psi4s152dN2 i8Psi4s152dN3 i8Psi4s152dN4 i8Psi4s152dW i8P4w152
  simp only [kernel_zero, kernel_one, hpl_nil]
  field_simp
  generalize hpl [zero, zero, one, one, one] x = v0 at *
  generalize hpl [zero, one, zero, one, one] x = v1 at *
  generalize hpl [zero, one, one, zero, one] x = v2 at *
  generalize hpl [zero, one, one, one, zero] x = v3 at *
  generalize hpl [zero, zero, one, one] x = v4 at *
  generalize hpl [zero, one, zero, one] x = v5 at *
  generalize hpl [zero, one, one, zero] x = v6 at *
  generalize hpl [zero, one, one, one] x = v7 at *
  generalize hpl [one, zero, one, one] x = v8 at *
  generalize hpl [one, one, zero, one] x = v9 at *
  generalize hpl [one, one, one, zero] x = v10 at *
  generalize hpl [zero, one, one] x = v11 at *
  generalize hpl [one, zero, one] x = v12 at *
  generalize hpl [one, one, zero] x = v13 at *
  generalize hpl [one, one, one] x = v14 at *
  generalize hpl [zero, one] x = v15 at *
  generalize hpl [one, zero] x = v16 at *
  generalize hpl [one, one] x = v17 at *
  generalize hpl [zero] x = v18 at *
  generalize hpl [one] x = v19 at *
  ring

end QED.ThreeLoopD
