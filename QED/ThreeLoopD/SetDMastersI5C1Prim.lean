/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI5C1Rad
public import QED.ThreeLoopD.SetDMastersI13R4S

/-!
# Set (d), master `I₅`: the primitive of the first coefficient, given `t K₁(t)` in closed form

Write `ξ = ξ(t)` (`t = (1 - ξ)²/ξ`) and `H(w) = H(w; ξ)` (harmonic polylogarithms). Numerically
(to `10⁻⁶⁰`), `t K₁(t) = K(ξ)` with (`QED.ThreeLoopD.i5K1x`)

  `K = ζ₂ H(1) + H(0,1) - H(1,0) + H(0,0,1) + 2 H(0,0,-1) + H(0,1,0) + 2 H(0,1,1)`
    `- 2 H(0,1,-1) - H(0,-1,0) - 2 H(0,-1,1) - H(1,0,0) + 6 H(1,0,-1)`.

This file proves everything about `c₁` downstream of that identity. The first coefficient of the
integrand on `(0, 1)` is `g(t) = (-λ + β₁) f₀(ξ) + K(ξ)` (`QED.ThreeLoopD.i5G1x`), `λ = log t`,
`f₀ = 2 Li₂ + log ξ log (1 - ξ)`. The function `Φ₁ = N₀/ξ + N₁ + ξ N₂` (`QED.ThreeLoopD.i5Phi1`,
26 harmonic polylogarithms of weight at most four, constant-coefficient parts `Nⱼ`) satisfies
`Φ₁'(ξ) ξ'(t) = g(t)` (`QED.ThreeLoopD.i5Phi1D_mul`; every word is rewritten in the Lyndon basis
by `QED.ThreeLoopD.i13hw_10` and its companions). Every word beginning with `1` carries the factor
`1 - ξ`, so `Φ₁` is continuous on `(0, 1]`, and

  `Φ₁(1) = 11π²/6 + 5ζ(3) + 4π⁴/45` (`QED.ThreeLoopD.i5Phi1_one`).

## Main results

* `QED.ThreeLoopD.hasDerivAt_i5Phi1`, `QED.ThreeLoopD.i5Phi1D_mul`,
  `QED.ThreeLoopD.hasDerivAt_i5Phi1t`.
* `QED.ThreeLoopD.continuousOn_i5Phi1t`, `QED.ThreeLoopD.i5Phi1_one`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- **The closed form of `t K₁(t)`** as a function of `ξ`. -/
noncomputable def i5K1x (x : ℝ) : ℝ :=
    (π ^ 2 / 6) * hpl [one] x +
    (1) * hpl [zero, one] x +
    (-1) * hpl [one, zero] x +
    (2) * hpl [zero, zero, negOne] x +
    (1) * hpl [zero, zero, one] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, zero] x +
    (-2) * hpl [zero, one, negOne] x +
    (2) * hpl [zero, one, one] x +
    (-1) * hpl [one, zero, zero] x +
    (6) * hpl [one, zero, negOne] x

/-- The part of `ξ Φ₁` with the factor `ξ ^ 0`. -/
noncomputable def i5Phi1N0 (x : ℝ) : ℝ :=
    (2) * hpl [negOne] x +
    (8 + π ^ 2 / 6) * hpl [one] x +
    (2) * hpl [zero, negOne] x +
    (8) * hpl [zero, one] x +
    (-1) * hpl [negOne, zero] x +
    (-2) * hpl [negOne, one] x +
    (-2) * hpl [one, zero] x +
    (-2) * hpl [one, negOne] x +
    (6) * hpl [one, one] x +
    (2) * hpl [zero, zero, negOne] x +
    (5) * hpl [zero, zero, one] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, zero] x +
    (-2) * hpl [zero, one, negOne] x +
    (6) * hpl [zero, one, one] x +
    (-5) * hpl [one, zero, zero] x +
    (6) * hpl [one, zero, negOne] x +
    (-4) * hpl [one, one, zero] x

/-- The derivative of `i5Phi1N0`. -/
noncomputable def i5Phi1dN0 (x : ℝ) : ℝ :=
    (2) * (negOne.kernel x * hpl [] x) +
    (8 + π ^ 2 / 6) * (one.kernel x * hpl [] x) +
    (2) * (zero.kernel x * hpl [negOne] x) +
    (8) * (zero.kernel x * hpl [one] x) +
    (-1) * (negOne.kernel x * hpl [zero] x) +
    (-2) * (negOne.kernel x * hpl [one] x) +
    (-2) * (one.kernel x * hpl [zero] x) +
    (-2) * (one.kernel x * hpl [negOne] x) +
    (6) * (one.kernel x * hpl [one] x) +
    (2) * (zero.kernel x * hpl [zero, negOne] x) +
    (5) * (zero.kernel x * hpl [zero, one] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (1) * (zero.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x) +
    (6) * (zero.kernel x * hpl [one, one] x) +
    (-5) * (one.kernel x * hpl [zero, zero] x) +
    (6) * (one.kernel x * hpl [zero, negOne] x) +
    (-4) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i5Phi1N0 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i5Phi1N0 (i5Phi1dN0 x) x := by
  unfold i5Phi1N0 i5Phi1dN0
  exact ((((((((((((((((((((hasDerivAt_hpl_cons negOne [] hx).const_mul (2)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (8 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-5))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-4)))

/-- The part of `ξ Φ₁` with the factor `ξ ^ 1`. -/
noncomputable def i5Phi1N1 (x : ℝ) : ℝ :=
    (-10 - π ^ 2 / 6) * hpl [zero] x +
    (2 - π ^ 2 / 3) * hpl [one] x +
    (3) * hpl [zero, zero] x +
    (2) * hpl [zero, negOne] x +
    (-4) * hpl [zero, one] x +
    (10) * hpl [one, zero] x +
    (5) * hpl [zero, zero, zero] x +
    (-6) * hpl [zero, zero, negOne] x +
    (4) * hpl [zero, one, zero] x +
    (6) * hpl [one, zero, zero] x +
    (-12) * hpl [one, zero, negOne] x +
    (8) * hpl [one, one, zero] x +
    (-4) * hpl [zero, zero, zero, one] x +
    (4) * hpl [zero, one, zero, zero] x

/-- The derivative of `i5Phi1N1`. -/
noncomputable def i5Phi1dN1 (x : ℝ) : ℝ :=
    (-10 - π ^ 2 / 6) * (zero.kernel x * hpl [] x) +
    (2 - π ^ 2 / 3) * (one.kernel x * hpl [] x) +
    (3) * (zero.kernel x * hpl [zero] x) +
    (2) * (zero.kernel x * hpl [negOne] x) +
    (-4) * (zero.kernel x * hpl [one] x) +
    (10) * (one.kernel x * hpl [zero] x) +
    (5) * (zero.kernel x * hpl [zero, zero] x) +
    (-6) * (zero.kernel x * hpl [zero, negOne] x) +
    (4) * (zero.kernel x * hpl [one, zero] x) +
    (6) * (one.kernel x * hpl [zero, zero] x) +
    (-12) * (one.kernel x * hpl [zero, negOne] x) +
    (8) * (one.kernel x * hpl [one, zero] x) +
    (-4) * (zero.kernel x * hpl [zero, zero, one] x) +
    (4) * (zero.kernel x * hpl [one, zero, zero] x)

theorem hasDerivAt_i5Phi1N1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i5Phi1N1 (i5Phi1dN1 x) x := by
  unfold i5Phi1N1 i5Phi1dN1
  exact (((((((((((((((hasDerivAt_hpl_cons zero [] hx).const_mul (-10 - π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (2 - π ^ 2 / 3))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (3))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (10))).add
      ((hasDerivAt_hpl_cons zero [zero, zero] hx).const_mul (5))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (-12))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (8))).add
      ((hasDerivAt_hpl_cons zero [zero, zero, one] hx).const_mul (-4))).add
      ((hasDerivAt_hpl_cons zero [one, zero, zero] hx).const_mul (4)))

/-- The part of `ξ Φ₁` with the factor `ξ ^ 2`. -/
noncomputable def i5Phi1N2 (x : ℝ) : ℝ :=
    (π ^ 2 / 6) +
    (-8) * hpl [zero] x +
    (-2) * hpl [negOne] x +
    (-10 + π ^ 2 / 6) * hpl [one] x +
    (-1) * hpl [zero, zero] x +
    (4) * hpl [zero, negOne] x +
    (2) * hpl [zero, one] x +
    (1) * hpl [negOne, zero] x +
    (2) * hpl [negOne, one] x +
    (-8) * hpl [one, zero] x +
    (2) * hpl [one, negOne] x +
    (-6) * hpl [one, one] x +
    (2) * hpl [zero, zero, negOne] x +
    (1) * hpl [zero, zero, one] x +
    (-1) * hpl [zero, negOne, zero] x +
    (-2) * hpl [zero, negOne, one] x +
    (1) * hpl [zero, one, zero] x +
    (-2) * hpl [zero, one, negOne] x +
    (6) * hpl [zero, one, one] x +
    (-1) * hpl [one, zero, zero] x +
    (6) * hpl [one, zero, negOne] x +
    (-4) * hpl [one, one, zero] x

/-- The derivative of `i5Phi1N2`. -/
noncomputable def i5Phi1dN2 (x : ℝ) : ℝ :=
    0 +
    (-8) * (zero.kernel x * hpl [] x) +
    (-2) * (negOne.kernel x * hpl [] x) +
    (-10 + π ^ 2 / 6) * (one.kernel x * hpl [] x) +
    (-1) * (zero.kernel x * hpl [zero] x) +
    (4) * (zero.kernel x * hpl [negOne] x) +
    (2) * (zero.kernel x * hpl [one] x) +
    (1) * (negOne.kernel x * hpl [zero] x) +
    (2) * (negOne.kernel x * hpl [one] x) +
    (-8) * (one.kernel x * hpl [zero] x) +
    (2) * (one.kernel x * hpl [negOne] x) +
    (-6) * (one.kernel x * hpl [one] x) +
    (2) * (zero.kernel x * hpl [zero, negOne] x) +
    (1) * (zero.kernel x * hpl [zero, one] x) +
    (-1) * (zero.kernel x * hpl [negOne, zero] x) +
    (-2) * (zero.kernel x * hpl [negOne, one] x) +
    (1) * (zero.kernel x * hpl [one, zero] x) +
    (-2) * (zero.kernel x * hpl [one, negOne] x) +
    (6) * (zero.kernel x * hpl [one, one] x) +
    (-1) * (one.kernel x * hpl [zero, zero] x) +
    (6) * (one.kernel x * hpl [zero, negOne] x) +
    (-4) * (one.kernel x * hpl [one, zero] x)

theorem hasDerivAt_i5Phi1N2 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i5Phi1N2 (i5Phi1dN2 x) x := by
  unfold i5Phi1N2 i5Phi1dN2
  exact ((((((((((((((((((((((hasDerivAt_const x (π ^ 2 / 6)).add
      ((hasDerivAt_hpl_cons zero [] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons negOne [] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons one [] hx).const_mul (-10 + π ^ 2 / 6))).add
      ((hasDerivAt_hpl_cons zero [zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne] hx).const_mul (4))).add
      ((hasDerivAt_hpl_cons zero [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons negOne [zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons negOne [one] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [zero] hx).const_mul (-8))).add
      ((hasDerivAt_hpl_cons one [negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons one [one] hx).const_mul (-6))).add
      ((hasDerivAt_hpl_cons zero [zero, negOne] hx).const_mul (2))).add
      ((hasDerivAt_hpl_cons zero [zero, one] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [negOne, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons zero [negOne, one] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, zero] hx).const_mul (1))).add
      ((hasDerivAt_hpl_cons zero [one, negOne] hx).const_mul (-2))).add
      ((hasDerivAt_hpl_cons zero [one, one] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [zero, zero] hx).const_mul (-1))).add
      ((hasDerivAt_hpl_cons one [zero, negOne] hx).const_mul (6))).add
      ((hasDerivAt_hpl_cons one [one, zero] hx).const_mul (-4)))

/-- `Φ₁ = N₀/ξ + N₁ + ξ N₂`. -/
noncomputable def i5Phi1 (x : ℝ) : ℝ := i5Phi1N0 x / x + i5Phi1N1 x + x * i5Phi1N2 x

/-- The derivative of `Φ₁`. -/
noncomputable def i5Phi1D (x : ℝ) : ℝ :=
  (i5Phi1dN0 x * x - i5Phi1N0 x) / x ^ 2 + i5Phi1dN1 x + (i5Phi1N2 x + x * i5Phi1dN2 x)

theorem hasDerivAt_i5Phi1 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i5Phi1 (i5Phi1D x) x := by
  have e : HasDerivAt (fun y => i5Phi1N0 y / y + i5Phi1N1 y + y * i5Phi1N2 y) _ x :=
    (((hasDerivAt_i5Phi1N0 hx).div (hasDerivAt_id' x) hx.1.ne').add
      (hasDerivAt_i5Phi1N1 hx)).add ((hasDerivAt_id' x).mul (hasDerivAt_i5Phi1N2 hx))
  exact e.congr_deriv (by unfold i5Phi1D; ring)

theorem i5_Li₂_eq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : Li₂ x = hpl [zero, one] x := by
  rw [hpl_zero_one hx, Li_two]

/-- The first coefficient `g = (-λ + β₁) f₀ + K` of the integrand, in terms of `ξ`. -/
noncomputable def i5G1x (x : ℝ) : ℝ :=
  (-(2 * Real.log (1 - x) - Real.log x) + (2 + Real.log x * (1 + x) / (1 - x))) * i5F0 x +
    i5K1x x

/-- **The derivative identity** `Φ₁'(ξ) ξ'(t) = g`. -/
theorem i5Phi1D_mul {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    i5Phi1D x * (-x ^ 2 / (1 - x ^ 2)) = i5G1x x := by
  have h0 : x ≠ 0 := hx.1.ne'
  have h1 : 1 - x ≠ 0 := by linarith [hx.2]
  have h2 : 1 + x ≠ 0 := by linarith [hx.1]
  have h3 : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  unfold i5Phi1D i5Phi1N0 i5Phi1N2 i5Phi1dN0 i5Phi1dN1 i5Phi1dN2 i5G1x i5F0 i5K1x
  simp only [kernel_zero, kernel_one, kernel_negOne, hpl_nil, hpl_zero, i13hw_00, i13hw_m0 hx,
    i13hw_10 hx, i13hw_1m hx, i13hw_11 hx, i13hw_0m0 hx, i13hw_010 hx, i13hw_100 hx, i13hw_10m hx,
    i13hw_110 hx, i5_Li₂_eq hx, i13_log_one_sub_eq hx]
  field_simp
  ring

/-- `g(t)`. -/
noncomputable def i5G1 (t : ℝ) : ℝ := i5G1x (i13Xi t)

/-- `g` is the first coefficient of the integrand once `t K₁(t) = K(ξ)`. -/
theorem i5G1_eq {t : ℝ} (ht : 0 < t) (hK : (t : ℂ) * i5KerC t 1 = i5K1x (i13Xi t)) :
    (t : ℂ) * ((-(Real.log t : ℂ) + i13Be1r t) * i5Ker 0 t + i5KerC t 1) = i5G1 t := by
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [mul_add, hK, i5Ker_zero_eq ht, i8_log_eq ht]
  unfold i5G1 i5G1x i13Be1r
  push_cast
  field_simp

/-- `Φ₁(ξ(t))`. -/
noncomputable def i5Phi1t (t : ℝ) : ℝ := i5Phi1 (i13Xi t)

theorem hasDerivAt_i5Phi1t {t : ℝ} (ht : 0 < t) : HasDerivAt i5Phi1t (i5G1 t) t := by
  have hx0 := i13Xi_pos ht.le
  have hx1 := i13Xi_lt_one ht
  have e := (hasDerivAt_i5Phi1 ⟨hx0, hx1⟩).comp t (hasDerivAt_i13Xi ht)
  rw [i5Phi1D_mul ⟨hx0, hx1⟩] at e
  exact e

/-! ### Continuity on `(0, 1]` and the value at `ξ = 1` -/

theorem i5_cont_coef {p : ℝ → ℝ} (hp : Continuous p) :
    ContinuousOn (fun x => p x / x) (Ioc 0 1) :=
  hp.continuousOn.div continuousOn_id fun _ hx => hx.1.ne'

/-- `Φ₁` as a sum over words, with the factor `1 - ξ` of the words beginning with `1` shown. -/
noncomputable def i5Phi1S (x : ℝ) : ℝ :=
    (π ^ 2 * x ^ 2 / 6) / x +
    (-10 * x - 8 * x ^ 2 - π ^ 2 * x / 6) / x * hpl [zero] x +
    (2 - 2 * x ^ 2) / x * hpl [negOne] x +
    (8 + 10 * x + π ^ 2 / 6 - π ^ 2 * x / 6) / x * ((1 - x) * hpl [one] x) +
    (-x ^ 2 + 3 * x) / x * hpl [zero, zero] x +
    (2 + 2 * x + 4 * x ^ 2) / x * hpl [zero, negOne] x +
    (8 - 4 * x + 2 * x ^ 2) / x * hpl [zero, one] x +
    (-1 + x ^ 2) / x * hpl [negOne, zero] x +
    (-2 + 2 * x ^ 2) / x * hpl [negOne, one] x +
    (-2 + 8 * x) / x * ((1 - x) * hpl [one, zero] x) +
    (-2 - 2 * x) / x * ((1 - x) * hpl [one, negOne] x) +
    (6 + 6 * x) / x * ((1 - x) * hpl [one, one] x) +
    (5 * x) / x * hpl [zero, zero, zero] x +
    (2 - 6 * x + 2 * x ^ 2) / x * hpl [zero, zero, negOne] x +
    (5 + x ^ 2) / x * hpl [zero, zero, one] x +
    (-1 - x ^ 2) / x * hpl [zero, negOne, zero] x +
    (-2 - 2 * x ^ 2) / x * hpl [zero, negOne, one] x +
    (1 + x ^ 2 + 4 * x) / x * hpl [zero, one, zero] x +
    (-2 - 2 * x ^ 2) / x * hpl [zero, one, negOne] x +
    (6 + 6 * x ^ 2) / x * hpl [zero, one, one] x +
    (-5 + x) / x * ((1 - x) * hpl [one, zero, zero] x) +
    (6 - 6 * x) / x * ((1 - x) * hpl [one, zero, negOne] x) +
    (-4 + 4 * x) / x * ((1 - x) * hpl [one, one, zero] x) +
    (-4 * x) / x * hpl [zero, zero, zero, one] x +
    (4 * x) / x * hpl [zero, one, zero, zero] x

theorem continuousOn_i5Phi1S : ContinuousOn i5Phi1S (Ioc 0 1) := by
  unfold i5Phi1S
  exact (((((((((((((((((((((((((i5_cont_coef (p := fun x => π ^ 2 * x ^ 2 / 6) (by fun_prop)).add
      ((i5_cont_coef (p := fun x => -10 * x - 8 * x ^ 2 - π ^ 2 * x / 6) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) []))).add
      ((i5_cont_coef (p := fun x => 2 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) []))).add
      ((i5_cont_coef (p := fun x => 8 + 10 * x + π ^ 2 / 6 - π ^ 2 * x / 6) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one]))).add
      ((i5_cont_coef (p := fun x => -x ^ 2 + 3 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero]))).add
      ((i5_cont_coef (p := fun x => 2 + 2 * x + 4 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne]))).add
      ((i5_cont_coef (p := fun x => 8 - 4 * x + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one]))).add
      ((i5_cont_coef (p := fun x => -1 + x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [zero]))).add
      ((i5_cont_coef (p := fun x => -2 + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := negOne) (by decide) [one]))).add
      ((i5_cont_coef (p := fun x => -2 + 8 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero]))).add
      ((i5_cont_coef (p := fun x => -2 - 2 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, negOne]))).add
      ((i5_cont_coef (p := fun x => 6 + 6 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one]))).add
      ((i5_cont_coef (p := fun x => 5 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero]))).add
      ((i5_cont_coef (p := fun x => 2 - 6 * x + 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, negOne]))).add
      ((i5_cont_coef (p := fun x => 5 + x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, one]))).add
      ((i5_cont_coef (p := fun x => -1 - x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, zero]))).add
      ((i5_cont_coef (p := fun x => -2 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [negOne, one]))).add
      ((i5_cont_coef (p := fun x => 1 + x ^ 2 + 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero]))).add
      ((i5_cont_coef (p := fun x => -2 - 2 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, negOne]))).add
      ((i5_cont_coef (p := fun x => 6 + 6 * x ^ 2) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, one]))).add
      ((i5_cont_coef (p := fun x => -5 + x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, zero]))).add
      ((i5_cont_coef (p := fun x => 6 - 6 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, zero, negOne]))).add
      ((i5_cont_coef (p := fun x => -4 + 4 * x) (by fun_prop)).mul
      (i13_contOn_one_sub_mul_hpl [one, one, zero]))).add
      ((i5_cont_coef (p := fun x => -4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [zero, zero, one]))).add
      ((i5_cont_coef (p := fun x => 4 * x) (by fun_prop)).mul
      (i13_contOn_hpl (a := zero) (by decide) [one, zero, zero])))

theorem i5Phi1_eq_S {x : ℝ} (hx : x ≠ 0) : i5Phi1 x = i5Phi1S x := by
  unfold i5Phi1 i5Phi1S i5Phi1N0 i5Phi1N1 i5Phi1N2
  field_simp
  ring

theorem continuousOn_i5Phi1 : ContinuousOn i5Phi1 (Ioc 0 1) :=
  continuousOn_i5Phi1S.congr fun _ hx => i5Phi1_eq_S hx.1.ne'

theorem continuousOn_i5Phi1t : ContinuousOn i5Phi1t (Ici 0) :=
  continuousOn_i5Phi1.comp continuous_i13Xi.continuousOn fun _ ht =>
    ⟨i13Xi_pos ht, i13Xi_le_one ht⟩

/-- **`Φ₁(1) = 11π²/6 + 5ζ(3) + 4π⁴/45`.** -/
theorem i5Phi1_one : i5Phi1 1 = 11 / 6 * π ^ 2 + 5 * zeta3 + 4 / 45 * π ^ 4 := by
  rw [i5Phi1_eq_S one_ne_zero]
  unfold i5Phi1S
  rw [hpl_zero_at_one, hpl_negOne_at_one, hpl_zero_zero_at_one, hpl_zero_negOne_at_one,
    hpl_zero_one_at_one, hpl_negOne_zero_at_one, hpl_negOne_one_at_one, hpl_zero_zero_zero_at_one,
    hpl_zero_zero_negOne_at_one, hpl_zero_zero_one_at_one, hpl_zero_negOne_zero_at_one,
    hpl_zero_negOne_one_at_one, hpl_zero_one_zero_at_one, hpl_zero_one_negOne_at_one,
    hpl_zero_one_one_at_one, hpl_zero_zero_zero_one_at_one, hpl_zero_one_zero_zero_at_one]
  norm_num
  ring

theorem i5Phi1t_zero : i5Phi1t 0 = 11 / 6 * π ^ 2 + 5 * zeta3 + 4 / 45 * π ^ 4 := by
  unfold i5Phi1t
  rw [i13Xi_zero, i5Phi1_one]

end QED.ThreeLoopD
