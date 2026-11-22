/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.OneLoopQuadratic

/-!
# The one-loop equal-mass bubble in `d` dimensions

The one-loop two-point integral with two unit masses,
`∫ dᵈk / π ^ (d / 2) · 1 / ((k² + 1) ^ a ((k + q)² + 1) ^ b)` (Euclidean, `q² = Q ≥ 0`), has
Symanzik polynomials `U = x₀ + x₁` and `F = Q x₀ x₁ + (x₀ + x₁)²`: the quadratic family
`QED.DimReg.oneLoopQuadFamily 1 (2 + Q) 1` (`QED.DimReg.massiveBubbleFamily`). It is not a
product of `Γ`-functions; its normalized integral is the one-dimensional integral
`I(d; a, b) = Γ(a + b - d/2) / (Γ(a) Γ(b)) ·
  ∫₀^∞ s ^ (a - 1) (1 + s) ^ (a + b - d) (Q s + (1 + s)²) ^ (d/2 - a - b) ds`
for `0 < re a`, `0 < re b`, `0 < re (a + b - d/2)`, `0 < re (d - a - b)`
(`QED.DimReg.integral_massiveBubbleFamily`). For `a = b = 1` the substitution `s = u / (1 - u)`
turns it into the textbook Feynman-parameter form
`Γ(2 - d/2) ∫₀¹ (1 + Q u (1 - u)) ^ (d/2 - 2) du` (`QED.DimReg.integral_massiveBubbleFamily_one`).

This is the massive bubble inserted on the photon line of the set (d) master `I₉`.

## Main results

* `QED.DimReg.lpConvergent_massiveBubble`: absolute convergence.
* `QED.DimReg.integral_massiveBubbleFamily`: the normalized integral.
* `QED.DimReg.integral_massiveBubbleFamily_one`: the Feynman-parameter form for `a = b = 1`.
-/

@[expose] public section

open MeasureTheory Set Complex MvPolynomial

namespace QED.DimReg

/-- The one-loop equal-mass (unit) bubble family with external `q² = Q`: `L = 1`, `U = x₀ + x₁`,
`F = Q x₀ x₁ + (x₀ + x₁)² = x₀² + (2 + Q) x₀ x₁ + x₁²`. -/
noncomputable abbrev massiveBubbleFamily (Q : ℝ) : FeynmanFamily 2 := oneLoopQuadFamily 1 (2 + Q) 1

theorem lpPoly_massiveBubbleFamily (Q : ℝ) (x : Fin 2 → ℝ) :
    (massiveBubbleFamily Q).lpPoly x = x 0 + x 1 + (Q * x 0 * x 1 + (x 0 + x 1) ^ 2) := by
  rw [lpPoly_oneLoopQuadFamily]
  ring

theorem oneLoopQuadPos_massiveBubble {Q : ℝ} (hQ : 0 ≤ Q) : OneLoopQuadPos 1 (2 + Q) 1 :=
  ⟨one_pos, by linarith, one_pos⟩

/-- The one-dimensional integrand `s ^ (a - 1) (1 + s) ^ (a + b - d) (Q s + (1 + s)²) ^
(-(a + b - d/2))` of the equal-mass bubble. -/
noncomputable abbrev massiveBubbleOuter (Q : ℝ) (a b d : ℂ) (s : ℝ) : ℂ :=
  oneLoopQuadOuter 1 (2 + Q) 1 a b d s

/-- The equal-mass bubble's Lee–Pomeransky integral converges absolutely for `0 < re a`,
`0 < re b`, `0 < re (a + b - d/2)`, `0 < re (d - a - b)`, with `(a, b) = (ν₀, ν₁)`. -/
theorem lpConvergent_massiveBubble {Q : ℝ} (hQ : 0 ≤ Q) {ν : Fin 2 → ℂ} {d : ℂ}
    (ha : 0 < (ν 0).re) (hb : 0 < (ν 1).re) (hα : 0 < (ν 0 + ν 1 - d / 2).re)
    (hβ : 0 < (d - ν 0 - ν 1).re) : LPConvergent (massiveBubbleFamily Q).lpPoly ν d :=
  lpConvergent_oneLoopQuad (oneLoopQuadPos_massiveBubble hQ) ha hb hα hβ

/-- **The equal-mass bubble.** In the region of absolute convergence,
`I(d; a, b) = Γ(a + b - d/2) / (Γ(a) Γ(b)) · ∫₀^∞ massiveBubbleOuter Q a b d`. -/
theorem integral_massiveBubbleFamily {Q : ℝ} (hQ : 0 ≤ Q) {ν : Fin 2 → ℂ} {d : ℂ}
    (ha : 0 < (ν 0).re) (hb : 0 < (ν 1).re) (hα : 0 < (ν 0 + ν 1 - d / 2).re)
    (hβ : 0 < (d - ν 0 - ν 1).re) :
    (massiveBubbleFamily Q).integral ν d =
      Gamma (ν 0 + ν 1 - d / 2) / (Gamma (ν 0) * Gamma (ν 1)) *
        ∫ s in Ioi (0 : ℝ), massiveBubbleOuter Q (ν 0) (ν 1) d s :=
  integral_oneLoopQuadFamily (oneLoopQuadPos_massiveBubble hQ) ha hb hα hβ

/-! ### The Feynman-parameter form for `a = b = 1` -/

theorem massiveBubbleOuter_subst {Q : ℝ} (hQ : 0 ≤ Q) (d : ℂ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    |betaPrimeSubstDeriv 1 u| • massiveBubbleOuter Q 1 1 d (betaPrimeSubst 1 u) =
      ((1 + Q * (u * (1 - u)) : ℝ) : ℂ) ^ (d / 2 - 2) := by
  obtain ⟨hu0, hu1⟩ := hu
  have hw : 0 < 1 - u := by linarith
  have hw0 : ((1 - u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  have e1 : 1 + betaPrimeSubst 1 u = (1 - u)⁻¹ := by
    simp only [betaPrimeSubst]; field_simp; ring
  have e2 : oneLoopQuadP 1 (2 + Q) 1 (betaPrimeSubst 1 u) =
      (1 + Q * (u * (1 - u))) * ((1 - u) * (1 - u))⁻¹ := by
    simp only [oneLoopQuadP, betaPrimeSubst]; field_simp; ring
  have hJ : |betaPrimeSubstDeriv 1 u| = ((1 - u) * (1 - u))⁻¹ := by
    rw [betaPrimeSubstDeriv, abs_of_pos (by positivity)]; ring
  have hpos : 0 ≤ 1 + Q * (u * (1 - u)) := by positivity
  rw [massiveBubbleOuter, oneLoopQuadOuter, e2, e1, hJ, sub_self, cpow_zero, one_mul,
    ofReal_inv_cpow hw, ofReal_mul_inv_cpow hpos (by positivity), cpow_ofReal_mul hw.le hw.le,
    Complex.real_smul,
    ofReal_inv, ofReal_mul, show (1 : ℂ) + 1 - d / 2 = 2 - d / 2 by ring, neg_neg,
    show (1 : ℂ) + 1 - d = 2 - d by ring, show -(2 - d / 2) = d / 2 - 2 by ring]
  have hc : ((1 - u : ℝ) : ℂ) ^ (-(2 - d)) * (((1 - u : ℝ) : ℂ) ^ (2 - d / 2) *
      ((1 - u : ℝ) : ℂ) ^ (2 - d / 2)) = ((1 - u : ℝ) : ℂ) * ((1 - u : ℝ) : ℂ) := by
    rw [← cpow_add _ _ hw0, ← cpow_add _ _ hw0, show -(2 - d) + (2 - d / 2 + (2 - d / 2)) =
      1 + 1 by ring, cpow_add _ _ hw0, cpow_one]
  calc _ = (((1 - u : ℝ) : ℂ) * ((1 - u : ℝ) : ℂ))⁻¹ * (((1 - u : ℝ) : ℂ) ^ (-(2 - d)) *
        (((1 - u : ℝ) : ℂ) ^ (2 - d / 2) * ((1 - u : ℝ) : ℂ) ^ (2 - d / 2))) *
        ((1 + Q * (u * (1 - u)) : ℝ) : ℂ) ^ (d / 2 - 2) := by ring
    _ = _ := by rw [hc, inv_mul_cancel₀ (mul_ne_zero hw0 hw0), one_mul]

/-- The substitution `s = u / (1 - u)`:
`∫₀^∞ massiveBubbleOuter Q 1 1 d = ∫₀¹ (1 + Q u (1 - u)) ^ (d/2 - 2) du`. -/
theorem integral_massiveBubbleOuter_one {Q : ℝ} (hQ : 0 ≤ Q) (d : ℂ) :
    ∫ s in Ioi (0 : ℝ), massiveBubbleOuter Q 1 1 d s =
      ∫ u in Ioo (0 : ℝ) 1, ((1 + Q * (u * (1 - u)) : ℝ) : ℂ) ^ (d / 2 - 2) := by
  rw [← image_betaPrimeSubst one_pos, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun u hu => hasDerivWithinAt_betaPrimeSubst one_pos hu) (injOn_betaPrimeSubst one_pos)]
  exact setIntegral_congr_fun measurableSet_Ioo (fun u hu => massiveBubbleOuter_subst hQ d hu)

/-- **The equal-mass bubble in Feynman-parameter form.** For `2 < re d < 4`,
`∫ dᵈk / π ^ (d/2) · 1 / ((k² + 1) ((k + q)² + 1))
= Γ(2 - d/2) ∫₀¹ (1 + Q u (1 - u)) ^ (d/2 - 2) du` (`q² = Q ≥ 0`). -/
theorem integral_massiveBubbleFamily_one {Q : ℝ} (hQ : 0 ≤ Q) {d : ℂ} (h1 : 2 < d.re)
    (h2 : d.re < 4) :
    (massiveBubbleFamily Q).integral (fun _ => 1) d =
      Gamma (2 - d / 2) *
        ∫ u in Ioo (0 : ℝ) 1, ((1 + Q * (u * (1 - u)) : ℝ) : ℂ) ^ (d / 2 - 2) := by
  rw [integral_massiveBubbleFamily hQ (by simp) (by simp) (by simp; linarith) (by simp; linarith),
    integral_massiveBubbleOuter_one hQ, Gamma_one, mul_one, div_one,
    show (1 : ℂ) + 1 - d / 2 = 2 - d / 2 by ring]

end QED.DimReg
