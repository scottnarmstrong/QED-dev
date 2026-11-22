/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI8R4P40

/-!
# Set (d), master `I₈`: a primitive of `p₄`, sub-pieces 136 to 138

`p₄` splits into sub-pieces `p₄⁽ⁿ⁾`, each a product `(-λ)^l/l! · t · (monomial of B_i) ·
(part of A_j)` (`QED.ThreeLoopD.i8P4s136`, ...). For each, `Ψ₄⁽ⁿ⁾`, a combination of harmonic
polylogarithms of weight at most five with coefficients in `ℚ[π², ζ(3), ξ, 1/ξ]` computed by the
shuffle-algebra engine of the campaign, is a primitive of `p₄⁽ⁿ⁾ dt/dξ`
(`QED.ThreeLoopD.i8Psi4s136D_mul`, ...).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i8Psi4s136`, `QED.ThreeLoopD.i8Psi4s136D_mul` and their companions.
-/

@[expose] public section

open Set Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The part of `ξ² Ψ₄⁽136⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s136k0N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s136k0N0`. -/
noncomputable def i8Psi4s136k0dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s136k0N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k0N0 (i8Psi4s136k0dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽136⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s136k0N1 (x : ℝ) : ℝ :=
    (8) * hpl [one, one] x +
    (8) * hpl [zero, one, one] x +
    (8) * hpl [one, zero, one] x +
    (8) * hpl [one, one, zero] x +
    (8) * hpl [zero, zero, one, one] x +
    (8) * hpl [zero, one, zero, one] x +
    (8) * hpl [zero, one, one, zero] x +
    (8) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s136k0N1`. -/
noncomputable def i8Psi4s136k0dN1 (x : ℝ) : ℝ :=
    (8) * (one.kernel x * hpl [one] x) +
    (8) * (zero.kernel x * hpl [one, one] x) +
    (8) * (one.kernel x * hpl [zero, one] x) +
    (8) * (one.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one, one] x) +
    (8) * (zero.kernel x * hpl [one, zero, one] x) +
    (8) * (zero.kernel x * hpl [one, one, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s136k0N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k0N1 (i8Psi4s136k0dN1 x) x := by
  unfold i8Psi4s136k0N1 i8Psi4s136k0dN1
  exact (((((((((hasDerivAt_hpl_cons one [one] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽136⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s136k0N2 (x : ℝ) : ℝ :=
    (-65 / 2) * hpl [one] x +
    (-8) * hpl [zero, one] x +
    (11) * hpl [one, zero] x +
    (-17) * hpl [one, one] x +
    (-8) * hpl [zero, zero, one] x +
    (2) * hpl [one, zero, one] x +
    (2) * hpl [one, one, zero] x +
    (-20) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s136k0N2`. -/
noncomputable def i8Psi4s136k0dN2 (x : ℝ) : ℝ :=
    (-65 / 2) * (one.kernel x * hpl [] x) +
    (-8) * (zero.kernel x * hpl [one] x) +
    (11) * (one.kernel x * hpl [zero] x) +
    (-17) * (one.kernel x * hpl [one] x) +
    (-8) * (zero.kernel x * hpl [zero, one] x) +
    (2) * (one.kernel x * hpl [zero, one] x) +
    (2) * (one.kernel x * hpl [one, zero] x) +
    (-20) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s136k0N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k0N2 (i8Psi4s136k0dN2 x) x := by
  unfold i8Psi4s136k0N2 i8Psi4s136k0dN2
  exact (((((((((hasDerivAt_hpl_cons one [] hx).const_mul (-65 / 2)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (11))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-17))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (-20)))

/-- The part of `ξ² Ψ₄⁽136⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s136k0N3 (x : ℝ) : ℝ :=
    (87 / 2) +
    (-11) * hpl [zero] x +
    (31) * hpl [one] x +
    (-22) * hpl [zero, one] x +
    (-10) * hpl [one, zero] x +
    (8) * hpl [one, one] x +
    (12) * hpl [zero, zero, one] x +
    (-8) * hpl [zero, one, one] x +
    (-8) * hpl [one, zero, one] x +
    (-8) * hpl [one, one, zero] x +
    (8) * hpl [zero, zero, one, one] x +
    (8) * hpl [zero, one, zero, one] x +
    (8) * hpl [zero, one, one, zero] x +
    (8) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s136k0N3`. -/
noncomputable def i8Psi4s136k0dN3 (x : ℝ) : ℝ :=
    0 +
    (-11) * (zero.kernel x * hpl [] x) +
    (31) * (one.kernel x * hpl [] x) +
    (-22) * (zero.kernel x * hpl [one] x) +
    (-10) * (one.kernel x * hpl [zero] x) +
    (8) * (one.kernel x * hpl [one] x) +
    (12) * (zero.kernel x * hpl [zero, one] x) +
    (-8) * (zero.kernel x * hpl [one, one] x) +
    (-8) * (one.kernel x * hpl [zero, one] x) +
    (-8) * (one.kernel x * hpl [one, zero] x) +
    (8) * (zero.kernel x * hpl [zero, one, one] x) +
    (8) * (zero.kernel x * hpl [one, zero, one] x) +
    (8) * (zero.kernel x * hpl [one, one, zero] x) +
    (8) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s136k0N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k0N3 (i8Psi4s136k0dN3 x) x := by
  unfold i8Psi4s136k0N3 i8Psi4s136k0dN3
  exact ((((((((((((((hasDerivAt_const x (87 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-11))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (31))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-22))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-10))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽136⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s136k0N4 (x : ℝ) : ℝ :=
    (1) +
    (-1 / 2) * hpl [zero] x +
    (3 / 2) * hpl [one] x +
    (-2) * hpl [zero, one] x +
    (-1) * hpl [one, zero] x +
    (1) * hpl [one, one] x +
    (2) * hpl [zero, zero, one] x +
    (-2) * hpl [zero, one, one] x +
    (-2) * hpl [one, zero, one] x +
    (-2) * hpl [one, one, zero] x +
    (4) * hpl [zero, zero, one, one] x +
    (4) * hpl [zero, one, zero, one] x +
    (4) * hpl [zero, one, one, zero] x +
    (4) * hpl [one, zero, zero, one] x

/-- The derivative of `i8Psi4s136k0N4`. -/
noncomputable def i8Psi4s136k0dN4 (x : ℝ) : ℝ :=
    0 +
    (-1 / 2) * (zero.kernel x * hpl [] x) +
    (3 / 2) * (one.kernel x * hpl [] x) +
    (-2) * (zero.kernel x * hpl [one] x) +
    (-1) * (one.kernel x * hpl [zero] x) +
    (1) * (one.kernel x * hpl [one] x) +
    (2) * (zero.kernel x * hpl [zero, one] x) +
    (-2) * (zero.kernel x * hpl [one, one] x) +
    (-2) * (one.kernel x * hpl [zero, one] x) +
    (-2) * (one.kernel x * hpl [one, zero] x) +
    (4) * (zero.kernel x * hpl [zero, one, one] x) +
    (4) * (zero.kernel x * hpl [one, zero, one] x) +
    (4) * (zero.kernel x * hpl [one, one, zero] x) +
    (4) * (one.kernel x * hpl [zero, zero, one] x)

theorem hasDerivAt_i8Psi4s136k0N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k0N4 (i8Psi4s136k0dN4 x) x := by
  unfold i8Psi4s136k0N4 i8Psi4s136k0dN4
  exact ((((((((((((((hasDerivAt_const x (1)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1 / 2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (3 / 2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero, one] hx).const_mul (4)))

/-- The part of `Ψ₄⁽136⁾` with constant coefficients. -/
noncomputable def i8Psi4s136k0W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, one, zero] x +
    (-8) * hpl [zero, zero, zero, one] x +
    (-8) * hpl [zero, zero, zero, one, one] x +
    (-8) * hpl [zero, zero, one, zero, one] x +
    (-8) * hpl [zero, zero, one, one, zero] x +
    (-8) * hpl [zero, one, zero, zero, one] x

/-- The derivative of `i8Psi4s136k0W`. -/
noncomputable def i8Psi4s136k0dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [one, zero] x) +
    (-8) * (zero.kernel x * hpl [zero, zero, one] x) +
    (-8) * (zero.kernel x * hpl [zero, zero, one, one] x) +
    (-8) * (zero.kernel x * hpl [zero, one, zero, one] x) +
    (-8) * (zero.kernel x * hpl [zero, one, one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, zero, zero, one] x)

theorem hasDerivAt_i8Psi4s136k0W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k0W (i8Psi4s136k0dW x) x := by
  unfold i8Psi4s136k0W i8Psi4s136k0dW
  exact (((((((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, zero, one] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero, one] hx).const_mul (-8)))

/-- Chunk 0 of the piece `Ψ₄⁽136⁾`. -/
noncomputable def i8Psi4s136k0 (x : ℝ) : ℝ :=
  (i8Psi4s136k0N0 x + x * i8Psi4s136k0N1 x + x ^ 2 * i8Psi4s136k0N2 x + x ^ 3 * i8Psi4s136k0N3 x +
    x ^ 4 * i8Psi4s136k0N4 x) / x ^ 2 + i8Psi4s136k0W x

/-- The derivative of `i8Psi4s136k0`. -/
noncomputable def i8Psi4s136k0D (x : ℝ) : ℝ :=
  ((i8Psi4s136k0dN0 x + (i8Psi4s136k0N1 x + x * i8Psi4s136k0dN1 x) + (2 * x * i8Psi4s136k0N2 x +
    x ^ 2 * i8Psi4s136k0dN2 x) + (3 * x ^ 2 * i8Psi4s136k0N3 x + x ^ 3 * i8Psi4s136k0dN3 x) +
    (4 * x ^ 3 * i8Psi4s136k0N4 x + x ^ 4 * i8Psi4s136k0dN4 x)) * x ^ 2 - (i8Psi4s136k0N0 x +
    x * i8Psi4s136k0N1 x + x ^ 2 * i8Psi4s136k0N2 x + x ^ 3 * i8Psi4s136k0N3 x +
    x ^ 4 * i8Psi4s136k0N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s136k0dW x

theorem hasDerivAt_i8Psi4s136k0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k0 (i8Psi4s136k0D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s136k0N0 hx).add (X.mul (hasDerivAt_i8Psi4s136k0N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s136k0N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s136k0N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s136k0N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s136k0W hx)
  unfold i8Psi4s136k0
  refine e.congr_deriv ?_
  unfold i8Psi4s136k0D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 0 of `p₄⁽136⁾` over words. -/
noncomputable def i8P4w136k0 (x : ℝ) : ℝ :=
    (8 + 8 * x) * hpl [zero, zero, one, one] x +
    (8 + 8 * x) * hpl [zero, one, zero, one] x +
    (8 + 8 * x) * hpl [zero, one, one, zero] x +
    (8 + 8 * x) * hpl [one, zero, zero, one] x

theorem i8Psi4s136k0D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s136k0D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w136k0 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s136k0D i8Psi4s136k0N0 i8Psi4s136k0N1 i8Psi4s136k0N2 i8Psi4s136k0N3 i8Psi4s136k0N4
    i8Psi4s136k0dN0 i8Psi4s136k0dN1 i8Psi4s136k0dN2 i8Psi4s136k0dN3 i8Psi4s136k0dN4 i8Psi4s136k0dW
    i8P4w136k0
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

/-- The part of `ξ² Ψ₄⁽136⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s136k1N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s136k1N0`. -/
noncomputable def i8Psi4s136k1dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s136k1N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k1N0 (i8Psi4s136k1dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽136⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s136k1N1 (x : ℝ) : ℝ :=
    (8) * hpl [one, zero, one, zero] x +
    (8) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s136k1N1`. -/
noncomputable def i8Psi4s136k1dN1 (x : ℝ) : ℝ :=
    (8) * (one.kernel x * hpl [zero, one, zero] x) +
    (8) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s136k1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k1N1 (i8Psi4s136k1dN1 x) x := by
  unfold i8Psi4s136k1N1 i8Psi4s136k1dN1
  exact (((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (8)).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽136⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s136k1N2 (x : ℝ) : ℝ :=
    (13) * hpl [one, zero] x +
    (-14) * hpl [one, zero, zero] x +
    (-20) * hpl [one, zero, one, zero] x +
    (-20) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s136k1N2`. -/
noncomputable def i8Psi4s136k1dN2 (x : ℝ) : ℝ :=
    (13) * (one.kernel x * hpl [zero] x) +
    (-14) * (one.kernel x * hpl [zero, zero] x) +
    (-20) * (one.kernel x * hpl [zero, one, zero] x) +
    (-20) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s136k1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k1N2 (i8Psi4s136k1dN2 x) x := by
  unfold i8Psi4s136k1N2 i8Psi4s136k1dN2
  exact (((((hasDerivAt_hpl_cons one [zero] hx).const_mul (13)).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-14))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (-20))).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (-20)))

/-- The part of `ξ² Ψ₄⁽136⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s136k1N3 (x : ℝ) : ℝ :=
    (27) +
    (-27) * hpl [zero] x +
    (14) * hpl [zero, zero] x +
    (-12) * hpl [one, zero] x +
    (12) * hpl [zero, one, zero] x +
    (12) * hpl [one, zero, zero] x +
    (8) * hpl [one, zero, one, zero] x +
    (8) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s136k1N3`. -/
noncomputable def i8Psi4s136k1dN3 (x : ℝ) : ℝ :=
    0 +
    (-27) * (zero.kernel x * hpl [] x) +
    (14) * (zero.kernel x * hpl [zero] x) +
    (-12) * (one.kernel x * hpl [zero] x) +
    (12) * (zero.kernel x * hpl [one, zero] x) +
    (12) * (one.kernel x * hpl [zero, zero] x) +
    (8) * (one.kernel x * hpl [zero, one, zero] x) +
    (8) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s136k1N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k1N3 (i8Psi4s136k1dN3 x) x := by
  unfold i8Psi4s136k1N3 i8Psi4s136k1dN3
  exact ((((((((hasDerivAt_const x (27)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-27))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (14))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (12))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (8)))

/-- The part of `ξ² Ψ₄⁽136⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s136k1N4 (x : ℝ) : ℝ :=
    (1 / 2) +
    (-1) * hpl [zero] x +
    (1) * hpl [zero, zero] x +
    (-1) * hpl [one, zero] x +
    (2) * hpl [zero, one, zero] x +
    (2) * hpl [one, zero, zero] x +
    (4) * hpl [one, zero, one, zero] x +
    (4) * hpl [one, one, zero, zero] x

/-- The derivative of `i8Psi4s136k1N4`. -/
noncomputable def i8Psi4s136k1dN4 (x : ℝ) : ℝ :=
    0 +
    (-1) * (zero.kernel x * hpl [] x) +
    (1) * (zero.kernel x * hpl [zero] x) +
    (-1) * (one.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [one, zero] x) +
    (2) * (one.kernel x * hpl [zero, zero] x) +
    (4) * (one.kernel x * hpl [zero, one, zero] x) +
    (4) * (one.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i8Psi4s136k1N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k1N4 (i8Psi4s136k1dN4 x) x := by
  unfold i8Psi4s136k1N4 i8Psi4s136k1dN4
  exact ((((((((hasDerivAt_const x (1 / 2)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero, one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one, zero, zero] hx).const_mul (4)))

/-- The part of `Ψ₄⁽136⁾` with constant coefficients. -/
noncomputable def i8Psi4s136k1W (x : ℝ) : ℝ :=
    (-8) * hpl [zero, zero, one, zero] x +
    (-8) * hpl [zero, one, zero, zero] x +
    (-8) * hpl [zero, one, zero, one, zero] x +
    (-8) * hpl [zero, one, one, zero, zero] x

/-- The derivative of `i8Psi4s136k1W`. -/
noncomputable def i8Psi4s136k1dW (x : ℝ) : ℝ :=
    (-8) * (zero.kernel x * hpl [zero, one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, zero, zero] x) +
    (-8) * (zero.kernel x * hpl [one, zero, one, zero] x) +
    (-8) * (zero.kernel x * hpl [one, one, zero, zero] x)

theorem hasDerivAt_i8Psi4s136k1W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k1W (i8Psi4s136k1dW x) x := by
  unfold i8Psi4s136k1W i8Psi4s136k1dW
  exact (((((hasDerivAt_hpl_cons zero [zero, one, zero] hx).const_mul (-8)).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one, zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero, zero] hx).const_mul (-8)))

/-- Chunk 1 of the piece `Ψ₄⁽136⁾`. -/
noncomputable def i8Psi4s136k1 (x : ℝ) : ℝ :=
  (i8Psi4s136k1N0 x + x * i8Psi4s136k1N1 x + x ^ 2 * i8Psi4s136k1N2 x + x ^ 3 * i8Psi4s136k1N3 x +
    x ^ 4 * i8Psi4s136k1N4 x) / x ^ 2 + i8Psi4s136k1W x

/-- The derivative of `i8Psi4s136k1`. -/
noncomputable def i8Psi4s136k1D (x : ℝ) : ℝ :=
  ((i8Psi4s136k1dN0 x + (i8Psi4s136k1N1 x + x * i8Psi4s136k1dN1 x) + (2 * x * i8Psi4s136k1N2 x +
    x ^ 2 * i8Psi4s136k1dN2 x) + (3 * x ^ 2 * i8Psi4s136k1N3 x + x ^ 3 * i8Psi4s136k1dN3 x) +
    (4 * x ^ 3 * i8Psi4s136k1N4 x + x ^ 4 * i8Psi4s136k1dN4 x)) * x ^ 2 - (i8Psi4s136k1N0 x +
    x * i8Psi4s136k1N1 x + x ^ 2 * i8Psi4s136k1N2 x + x ^ 3 * i8Psi4s136k1N3 x +
    x ^ 4 * i8Psi4s136k1N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s136k1dW x

theorem hasDerivAt_i8Psi4s136k1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136k1 (i8Psi4s136k1D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s136k1N0 hx).add (X.mul (hasDerivAt_i8Psi4s136k1N1 hx))).add
    ((X.pow 2).mul (hasDerivAt_i8Psi4s136k1N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s136k1N3
    hx))).add ((X.pow 4).mul (hasDerivAt_i8Psi4s136k1N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s136k1W hx)
  unfold i8Psi4s136k1
  refine e.congr_deriv ?_
  unfold i8Psi4s136k1D
  simp only [Pi.pow_apply]
  norm_num

/-- Chunk 1 of `p₄⁽136⁾` over words. -/
noncomputable def i8P4w136k1 (x : ℝ) : ℝ :=
    (8 + 8 * x) * hpl [one, zero, one, zero] x +
    (8 + 8 * x) * hpl [one, one, zero, zero] x

theorem i8Psi4s136k1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s136k1D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4w136k1 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i8Psi4s136k1D i8Psi4s136k1N0 i8Psi4s136k1N1 i8Psi4s136k1N2 i8Psi4s136k1N3 i8Psi4s136k1N4
    i8Psi4s136k1dN0 i8Psi4s136k1dN1 i8Psi4s136k1dN2 i8Psi4s136k1dN3 i8Psi4s136k1dN4 i8Psi4s136k1dW
    i8P4w136k1
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

/-- The piece `Ψ₄⁽136⁾` of the primitive of `p₄ dt/dξ`, the sum of its chunks. -/
noncomputable def i8Psi4s136 (x : ℝ) : ℝ :=
  i8Psi4s136k0 x + i8Psi4s136k1 x

/-- The derivative of `Ψ₄⁽136⁾`. -/
noncomputable def i8Psi4s136D (x : ℝ) : ℝ :=
  i8Psi4s136k0D x + i8Psi4s136k1D x

theorem hasDerivAt_i8Psi4s136 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s136 (i8Psi4s136D x) x := by
  unfold i8Psi4s136 i8Psi4s136D
  exact ((hasDerivAt_i8Psi4s136k0 hx).add (hasDerivAt_i8Psi4s136k1 hx))

/-- The sub-piece 136 of `p₄` in `ξ`: from `t B2 A0 (-λ)^2/2!`, the term with `log^2 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s136 (x : ℝ) : ℝ :=
  4 * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 2 * ((1 + x) / (1 -
    x) * (1 * hpl [zero, zero] x)) * (x / (1 - x))

/-- `p₄⁽136⁾` over words, the sum of its chunks. -/
noncomputable def i8P4w136 (x : ℝ) : ℝ :=
  i8P4w136k0 x + i8P4w136k1 x

theorem i8P4s136_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s136 x = i8P4w136 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s136 i8P4w136 i8P4w136k0 i8P4w136k1
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [one] [one] hx
  have e1 := hpl_mul_hpl [zero, zero] [one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  linear_combination (norm := skip) ((4 + 4 * x) * hpl [zero, zero] x) * e0 + ((8 + 8 * x)) * e1
  field_simp
  generalize hpl [zero, zero, one, one] x = v0 at *
  generalize hpl [zero, one, zero, one] x = v1 at *
  generalize hpl [zero, one, one, zero] x = v2 at *
  generalize hpl [one, zero, zero, one] x = v3 at *
  generalize hpl [one, zero, one, zero] x = v4 at *
  generalize hpl [one, one, zero, zero] x = v5 at *
  generalize hpl [zero, zero] x = v6 at *
  generalize hpl [one, one] x = v7 at *
  generalize hpl [one] x = v8 at *
  ring

/-- **`(Ψ₄⁽136⁾)'(ξ) ξ' = p₄⁽136⁾`**, in terms of `ξ`. -/
theorem i8Psi4s136D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s136D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s136 x := by
  rw [i8P4s136_eq_w hx]
  unfold i8Psi4s136D i8P4w136
  rw [← i8Psi4s136k0D_mul hx, ← i8Psi4s136k1D_mul hx]
  ring

/-- The part of `ξ² Ψ₄⁽137⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s137N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s137N0`. -/
noncomputable def i8Psi4s137dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s137N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s137N0 (i8Psi4s137dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽137⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s137N1 (x : ℝ) : ℝ :=
    (16) * hpl [one, one] x +
    (16) * hpl [zero, one, one] x +
    (16) * hpl [one, zero, one] x +
    (16) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s137N1`. -/
noncomputable def i8Psi4s137dN1 (x : ℝ) : ℝ :=
    (16) * (one.kernel x * hpl [one] x) +
    (16) * (zero.kernel x * hpl [one, one] x) +
    (16) * (one.kernel x * hpl [zero, one] x) +
    (16) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s137N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s137N1 (i8Psi4s137dN1 x) x := by
  unfold i8Psi4s137N1 i8Psi4s137dN1
  exact (((((hasDerivAt_hpl_cons one [one] hx).const_mul (16)).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽137⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s137N2 (x : ℝ) : ℝ :=
    (48) * hpl [one] x +
    (-16) * hpl [zero, one] x +
    (-28) * hpl [one, zero] x +
    (4) * hpl [one, one] x +
    (-40) * hpl [one, zero, one] x +
    (-40) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s137N2`. -/
noncomputable def i8Psi4s137dN2 (x : ℝ) : ℝ :=
    (48) * (one.kernel x * hpl [] x) +
    (-16) * (zero.kernel x * hpl [one] x) +
    (-28) * (one.kernel x * hpl [zero] x) +
    (4) * (one.kernel x * hpl [one] x) +
    (-40) * (one.kernel x * hpl [zero, one] x) +
    (-40) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s137N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s137N2 (i8Psi4s137dN2 x) x := by
  unfold i8Psi4s137N2 i8Psi4s137dN2
  exact (((((((hasDerivAt_hpl_cons one [] hx).const_mul (48)).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-28))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (-40))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-40)))

/-- The part of `ξ² Ψ₄⁽137⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s137N3 (x : ℝ) : ℝ :=
    (-76) +
    (28) * hpl [zero] x +
    (-44) * hpl [one] x +
    (24) * hpl [zero, one] x +
    (24) * hpl [one, zero] x +
    (-16) * hpl [one, one] x +
    (16) * hpl [zero, one, one] x +
    (16) * hpl [one, zero, one] x +
    (16) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s137N3`. -/
noncomputable def i8Psi4s137dN3 (x : ℝ) : ℝ :=
    0 +
    (28) * (zero.kernel x * hpl [] x) +
    (-44) * (one.kernel x * hpl [] x) +
    (24) * (zero.kernel x * hpl [one] x) +
    (24) * (one.kernel x * hpl [zero] x) +
    (-16) * (one.kernel x * hpl [one] x) +
    (16) * (zero.kernel x * hpl [one, one] x) +
    (16) * (one.kernel x * hpl [zero, one] x) +
    (16) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s137N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s137N3 (i8Psi4s137dN3 x) x := by
  unfold i8Psi4s137N3 i8Psi4s137dN3
  exact (((((((((hasDerivAt_const x (-76)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-44))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (16))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (16)))

/-- The part of `ξ² Ψ₄⁽137⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s137N4 (x : ℝ) : ℝ :=
    (-3) +
    (2) * hpl [zero] x +
    (-4) * hpl [one] x +
    (4) * hpl [zero, one] x +
    (4) * hpl [one, zero] x +
    (-4) * hpl [one, one] x +
    (8) * hpl [zero, one, one] x +
    (8) * hpl [one, zero, one] x +
    (8) * hpl [one, one, zero] x

/-- The derivative of `i8Psi4s137N4`. -/
noncomputable def i8Psi4s137dN4 (x : ℝ) : ℝ :=
    0 +
    (2) * (zero.kernel x * hpl [] x) +
    (-4) * (one.kernel x * hpl [] x) +
    (4) * (zero.kernel x * hpl [one] x) +
    (4) * (one.kernel x * hpl [zero] x) +
    (-4) * (one.kernel x * hpl [one] x) +
    (8) * (zero.kernel x * hpl [one, one] x) +
    (8) * (one.kernel x * hpl [zero, one] x) +
    (8) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i8Psi4s137N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s137N4 (i8Psi4s137dN4 x) x := by
  unfold i8Psi4s137N4 i8Psi4s137dN4
  exact (((((((((hasDerivAt_const x (-3)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [zero, one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (8)))

/-- The part of `Ψ₄⁽137⁾` with constant coefficients. -/
noncomputable def i8Psi4s137W (x : ℝ) : ℝ :=
    (-16) * hpl [zero, zero, one] x +
    (-16) * hpl [zero, one, zero] x +
    (-16) * hpl [zero, zero, one, one] x +
    (-16) * hpl [zero, one, zero, one] x +
    (-16) * hpl [zero, one, one, zero] x

/-- The derivative of `i8Psi4s137W`. -/
noncomputable def i8Psi4s137dW (x : ℝ) : ℝ :=
    (-16) * (zero.kernel x * hpl [zero, one] x) +
    (-16) * (zero.kernel x * hpl [one, zero] x) +
    (-16) * (zero.kernel x * hpl [zero, one, one] x) +
    (-16) * (zero.kernel x * hpl [one, zero, one] x) +
    (-16) * (zero.kernel x * hpl [one, one, zero] x)

theorem hasDerivAt_i8Psi4s137W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s137W (i8Psi4s137dW x) x := by
  unfold i8Psi4s137W i8Psi4s137dW
  exact ((((((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (-16)).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [zero, one, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, zero, one] hx).const_mul (-16))).add
      ((hasDerivAt_hpl_cons zero [one, one, zero] hx).const_mul (-16)))

/-- The piece `Ψ₄⁽137⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s137 (x : ℝ) : ℝ :=
  (i8Psi4s137N0 x + x * i8Psi4s137N1 x + x ^ 2 * i8Psi4s137N2 x + x ^ 3 * i8Psi4s137N3 x +
    x ^ 4 * i8Psi4s137N4 x) / x ^ 2 + i8Psi4s137W x

/-- The derivative of `Ψ₄⁽137⁾`. -/
noncomputable def i8Psi4s137D (x : ℝ) : ℝ :=
  ((i8Psi4s137dN0 x + (i8Psi4s137N1 x + x * i8Psi4s137dN1 x) + (2 * x * i8Psi4s137N2 x +
    x ^ 2 * i8Psi4s137dN2 x) + (3 * x ^ 2 * i8Psi4s137N3 x + x ^ 3 * i8Psi4s137dN3 x) +
    (4 * x ^ 3 * i8Psi4s137N4 x + x ^ 4 * i8Psi4s137dN4 x)) * x ^ 2 - (i8Psi4s137N0 x +
    x * i8Psi4s137N1 x + x ^ 2 * i8Psi4s137N2 x + x ^ 3 * i8Psi4s137N3 x +
    x ^ 4 * i8Psi4s137N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s137dW x

theorem hasDerivAt_i8Psi4s137 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s137 (i8Psi4s137D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s137N0 hx).add (X.mul (hasDerivAt_i8Psi4s137N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s137N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s137N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s137N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s137W hx)
  unfold i8Psi4s137
  refine e.congr_deriv ?_
  unfold i8Psi4s137D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 137 of `p₄` in `ξ`: from `t B2 A0 (-λ)^2/2!`, the term with `log^2 (1 -
  ξ) log^0 ξ`. -/
noncomputable def i8P4s137 (x : ℝ) : ℝ :=
  4 * (1 - x) ^ 2 / x * Real.log (1 - x) ^ 2 * ((1 + x) / (1 -
    x) * (2 * hpl [zero] x)) * (x / (1 - x))

/-- `p₄⁽137⁾` written over words. -/
noncomputable def i8P4w137 (x : ℝ) : ℝ :=
    (16 + 16 * x) * hpl [zero, one, one] x +
    (16 + 16 * x) * hpl [one, zero, one] x +
    (16 + 16 * x) * hpl [one, one, zero] x

theorem i8P4s137_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s137 x = i8P4w137 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s137 i8P4w137
  rw [i13_log_one_sub_eq hx]
  have e0 := hpl_mul_hpl [one] [one] hx
  have e1 := hpl_mul_hpl [zero] [one, one] hx
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e0
  simp only [shuffle_cons_cons, shuffle_nil_left, shuffle_nil_right, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero] at e1
  linear_combination (norm := skip) ((8 + 8 * x) * hpl [zero] x) * e0 + ((16 + 16 * x)) * e1
  field_simp
  generalize hpl [zero, one, one] x = v0 at *
  generalize hpl [one, zero, one] x = v1 at *
  generalize hpl [one, one, zero] x = v2 at *
  generalize hpl [one, one] x = v3 at *
  generalize hpl [zero] x = v4 at *
  generalize hpl [one] x = v5 at *
  ring

/-- **`(Ψ₄⁽137⁾)'(ξ) ξ' = p₄⁽137⁾`**, in terms of `ξ`. -/
theorem i8Psi4s137D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s137D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s137 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s137_eq_w hx]
  unfold i8Psi4s137D i8Psi4s137N0 i8Psi4s137N1 i8Psi4s137N2 i8Psi4s137N3 i8Psi4s137N4 i8Psi4s137dN0
    i8Psi4s137dN1 i8Psi4s137dN2 i8Psi4s137dN3 i8Psi4s137dN4 i8Psi4s137dW i8P4w137
  simp only [kernel_zero, kernel_one, hpl_nil]
  field_simp
  generalize hpl [zero, zero, one, one] x = v0 at *
  generalize hpl [zero, one, zero, one] x = v1 at *
  generalize hpl [zero, one, one, zero] x = v2 at *
  generalize hpl [zero, zero, one] x = v3 at *
  generalize hpl [zero, one, zero] x = v4 at *
  generalize hpl [zero, one, one] x = v5 at *
  generalize hpl [one, zero, one] x = v6 at *
  generalize hpl [one, one, zero] x = v7 at *
  generalize hpl [zero, one] x = v8 at *
  generalize hpl [one, zero] x = v9 at *
  generalize hpl [one, one] x = v10 at *
  generalize hpl [zero] x = v11 at *
  generalize hpl [one] x = v12 at *
  ring

/-- The part of `ξ² Ψ₄⁽138⁾` with the factor `ξ ^ 0`. -/
noncomputable def i8Psi4s138N0 (_x : ℝ) : ℝ := 0

/-- The derivative of `i8Psi4s138N0`. -/
noncomputable def i8Psi4s138dN0 (_x : ℝ) : ℝ := 0

theorem hasDerivAt_i8Psi4s138N0 {x : ℝ} (_hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s138N0 (i8Psi4s138dN0 x) x :=
  hasDerivAt_const x 0

/-- The part of `ξ² Ψ₄⁽138⁾` with the factor `ξ ^ 1`. -/
noncomputable def i8Psi4s138N1 (x : ℝ) : ℝ :=
    (28) +
    (28) * hpl [zero] x +
    (28) * hpl [zero, zero] x +
    (24) * hpl [zero, zero, zero] x +
    (12) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s138N1`. -/
noncomputable def i8Psi4s138dN1 (x : ℝ) : ℝ :=
    0 +
    (28) * (zero.kernel x * hpl [] x) +
    (28) * (zero.kernel x * hpl [zero] x) +
    (24) * (zero.kernel x * hpl [zero, zero] x) +
    (12) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s138N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s138N1 (i8Psi4s138dN1 x) x := by
  unfold i8Psi4s138N1 i8Psi4s138dN1
  exact (((((hasDerivAt_const x (28)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (28))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (24))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (12)))

/-- The part of `ξ² Ψ₄⁽138⁾` with the factor `ξ ^ 2`. -/
noncomputable def i8Psi4s138N2 (x : ℝ) : ℝ :=
    (4) * hpl [zero, zero, zero] x +
    (-12) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s138N2`. -/
noncomputable def i8Psi4s138dN2 (x : ℝ) : ℝ :=
    (4) * (zero.kernel x * hpl [zero, zero] x) +
    (-12) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s138N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s138N2 (i8Psi4s138dN2 x) x := by
  unfold i8Psi4s138N2 i8Psi4s138dN2
  exact (((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (4)).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-12)))

/-- The part of `ξ² Ψ₄⁽138⁾` with the factor `ξ ^ 3`. -/
noncomputable def i8Psi4s138N3 (x : ℝ) : ℝ :=
    (-44) +
    (44) * hpl [zero] x +
    (-44) * hpl [zero, zero] x +
    (48) * hpl [zero, zero, zero] x +
    (-36) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s138N3`. -/
noncomputable def i8Psi4s138dN3 (x : ℝ) : ℝ :=
    0 +
    (44) * (zero.kernel x * hpl [] x) +
    (-44) * (zero.kernel x * hpl [zero] x) +
    (48) * (zero.kernel x * hpl [zero, zero] x) +
    (-36) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s138N3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s138N3 (i8Psi4s138dN3 x) x := by
  unfold i8Psi4s138N3 i8Psi4s138dN3
  exact (((((hasDerivAt_const x (-44)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (44))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-44))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (48))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-36)))

/-- The part of `ξ² Ψ₄⁽138⁾` with the factor `ξ ^ 4`. -/
noncomputable def i8Psi4s138N4 (x : ℝ) : ℝ :=
    (-13 / 8) +
    (13 / 4) * hpl [zero] x +
    (-13 / 2) * hpl [zero, zero] x +
    (9) * hpl [zero, zero, zero] x +
    (-6) * hpl [zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s138N4`. -/
noncomputable def i8Psi4s138dN4 (x : ℝ) : ℝ :=
    0 +
    (13 / 4) * (zero.kernel x * hpl [] x) +
    (-13 / 2) * (zero.kernel x * hpl [zero] x) +
    (9) * (zero.kernel x * hpl [zero, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s138N4 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s138N4 (i8Psi4s138dN4 x) x := by
  unfold i8Psi4s138N4 i8Psi4s138dN4
  exact (((((hasDerivAt_const x (-13 / 8)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (13 / 4))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-13 / 2))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (9))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, zero] hx).const_mul (-6)))

/-- The part of `Ψ₄⁽138⁾` with constant coefficients. -/
noncomputable def i8Psi4s138W (x : ℝ) : ℝ :=
    (-36) * hpl [zero, zero, zero, zero, zero] x

/-- The derivative of `i8Psi4s138W`. -/
noncomputable def i8Psi4s138dW (x : ℝ) : ℝ :=
    (-36) * (zero.kernel x * hpl [zero, zero, zero, zero] x)

theorem hasDerivAt_i8Psi4s138W {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s138W (i8Psi4s138dW x) x := by
  unfold i8Psi4s138W i8Psi4s138dW
  exact ((hasDerivAt_hpl_cons zero [zero, zero, zero, zero] hx).const_mul (-36))

/-- The piece `Ψ₄⁽138⁾` of the primitive of `p₄ dt/dξ`. -/
noncomputable def i8Psi4s138 (x : ℝ) : ℝ :=
  (i8Psi4s138N0 x + x * i8Psi4s138N1 x + x ^ 2 * i8Psi4s138N2 x + x ^ 3 * i8Psi4s138N3 x +
    x ^ 4 * i8Psi4s138N4 x) / x ^ 2 + i8Psi4s138W x

/-- The derivative of `Ψ₄⁽138⁾`. -/
noncomputable def i8Psi4s138D (x : ℝ) : ℝ :=
  ((i8Psi4s138dN0 x + (i8Psi4s138N1 x + x * i8Psi4s138dN1 x) + (2 * x * i8Psi4s138N2 x +
    x ^ 2 * i8Psi4s138dN2 x) + (3 * x ^ 2 * i8Psi4s138N3 x + x ^ 3 * i8Psi4s138dN3 x) +
    (4 * x ^ 3 * i8Psi4s138N4 x + x ^ 4 * i8Psi4s138dN4 x)) * x ^ 2 - (i8Psi4s138N0 x +
    x * i8Psi4s138N1 x + x ^ 2 * i8Psi4s138N2 x + x ^ 3 * i8Psi4s138N3 x +
    x ^ 4 * i8Psi4s138N4 x) * (2 * x)) / (x ^ 2) ^ 2 + i8Psi4s138dW x

theorem hasDerivAt_i8Psi4s138 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i8Psi4s138 (i8Psi4s138D x) x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have X := hasDerivAt_id' x
  have e := ((((((hasDerivAt_i8Psi4s138N0 hx).add (X.mul (hasDerivAt_i8Psi4s138N1 hx))).add ((X.pow
    2).mul (hasDerivAt_i8Psi4s138N2 hx))).add ((X.pow 3).mul (hasDerivAt_i8Psi4s138N3 hx))).add
    ((X.pow 4).mul (hasDerivAt_i8Psi4s138N4 hx))).div (X.pow 2) (pow_ne_zero 2 h0)).add
    (hasDerivAt_i8Psi4s138W hx)
  unfold i8Psi4s138
  refine e.congr_deriv ?_
  unfold i8Psi4s138D
  simp only [Pi.pow_apply]
  norm_num

/-- The sub-piece 138 of `p₄` in `ξ`: from `t B2 A0 (-λ)^2/2!`, the term with `log^0 (1 -
  ξ) log^2 ξ`. -/
noncomputable def i8P4s138 (x : ℝ) : ℝ :=
  (1 / 2) * (1 - x) ^ 2 / x * Real.log x ^ 2 * (2 + Real.log x * (1 + x) / (1 - x)) * (2 +
    Real.log x * (1 + x) / (1 - x)) * (x / (1 - x))

/-- `p₄⁽138⁾` written over words. -/
noncomputable def i8P4w138 (x : ℝ) : ℝ :=
    (4 - 4 * x) * hpl [zero, zero] x +
    (12 + 12 * x) * hpl [zero, zero, zero] x +
    ((12 + 12 * x ^ 2 + 24 * x) / ((1 - x))) * hpl [zero, zero, zero, zero] x

theorem i8P4s138_eq_w {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : i8P4s138 x = i8P4w138 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  unfold i8P4s138 i8P4w138
  simp only [i13hw_00, i13hw_000, i13hw_0000]
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
  generalize hpl [zero, zero, zero, zero, zero] x = v23 at *
  generalize hpl [zero, zero, zero, zero, one] x = v24 at *
  generalize hpl [zero, zero, zero, one, negOne] x = v25 at *
  generalize hpl [zero, zero, zero, one, one] x = v26 at *
  generalize hpl [zero, zero, one, negOne, negOne] x = v27 at *
  generalize hpl [zero, zero, one, negOne, one] x = v28 at *
  generalize hpl [zero, zero, one, zero, negOne] x = v29 at *
  generalize hpl [zero, zero, one, zero, one] x = v30 at *
  generalize hpl [zero, zero, one, one, negOne] x = v31 at *
  generalize hpl [zero, zero, one, one, one] x = v32 at *
  generalize hpl [zero, one, negOne, negOne, negOne] x = v33 at *
  generalize hpl [zero, one, negOne, negOne, one] x = v34 at *
  generalize hpl [zero, one, negOne, one, negOne] x = v35 at *
  generalize hpl [zero, one, negOne, one, one] x = v36 at *
  generalize hpl [zero, one, zero, one, negOne] x = v37 at *
  generalize hpl [zero, one, one, negOne, negOne] x = v38 at *
  generalize hpl [zero, one, one, negOne, one] x = v39 at *
  generalize hpl [zero, one, one, one, negOne] x = v40 at *
  generalize hpl [zero, one, one, one, one] x = v41 at *
  generalize hpl [negOne, negOne, one, one] x = v42 at *
  generalize hpl [zero, negOne, negOne, negOne] x = v43 at *
  generalize hpl [zero, negOne, negOne, one] x = v44 at *
  generalize hpl [zero, negOne, zero, one] x = v45 at *
  generalize hpl [zero, negOne, one, negOne] x = v46 at *
  generalize hpl [zero, negOne, one, one] x = v47 at *
  generalize hpl [zero, zero, negOne, negOne] x = v48 at *
  generalize hpl [zero, zero, negOne, one] x = v49 at *
  generalize hpl [zero, zero, zero, negOne] x = v50 at *
  generalize hpl [zero, zero, zero, zero] x = v51 at *
  generalize hpl [zero, zero, zero, one] x = v52 at *
  generalize hpl [zero, zero, one, negOne] x = v53 at *
  generalize hpl [zero, zero, one, one] x = v54 at *
  generalize hpl [zero, one, negOne, negOne] x = v55 at *
  generalize hpl [zero, one, negOne, one] x = v56 at *
  generalize hpl [zero, one, one, negOne] x = v57 at *
  generalize hpl [zero, one, one, one] x = v58 at *
  generalize hpl [negOne, negOne, one] x = v59 at *
  generalize hpl [negOne, one, one] x = v60 at *
  generalize hpl [zero, negOne, negOne] x = v61 at *
  generalize hpl [zero, negOne, one] x = v62 at *
  generalize hpl [zero, zero, negOne] x = v63 at *
  generalize hpl [zero, zero, zero] x = v64 at *
  generalize hpl [zero, zero, one] x = v65 at *
  generalize hpl [zero, one, negOne] x = v66 at *
  generalize hpl [zero, one, one] x = v67 at *
  generalize hpl [negOne, one] x = v68 at *
  generalize hpl [zero, negOne] x = v69 at *
  generalize hpl [zero, zero] x = v70 at *
  generalize hpl [zero, one] x = v71 at *
  generalize hpl [negOne] x = v72 at *
  generalize hpl [zero] x = v73 at *
  generalize hpl [one] x = v74 at *
  ring

/-- **`(Ψ₄⁽138⁾)'(ξ) ξ' = p₄⁽138⁾`**, in terms of `ξ`. -/
theorem i8Psi4s138D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i8Psi4s138D x * (-x ^ 2 / (1 - x ^ 2)) = i8P4s138 x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  rw [i8P4s138_eq_w hx]
  unfold i8Psi4s138D i8Psi4s138N0 i8Psi4s138N1 i8Psi4s138N2 i8Psi4s138N3 i8Psi4s138N4 i8Psi4s138dN0
    i8Psi4s138dN1 i8Psi4s138dN2 i8Psi4s138dN3 i8Psi4s138dN4 i8Psi4s138dW i8P4w138
  simp only [kernel_zero, hpl_nil]
  field_simp
  generalize hpl [zero, zero, zero, zero, zero] x = v0 at *
  generalize hpl [zero, zero, zero, zero] x = v1 at *
  generalize hpl [zero, zero, zero] x = v2 at *
  generalize hpl [zero, zero] x = v3 at *
  generalize hpl [zero] x = v4 at *
  ring

end QED.ThreeLoopD
