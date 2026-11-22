/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Basic
public import QED.DimReg.BetaPrimeNested
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The one-loop massless bubble in `d` dimensions

The one-loop massless two-point integral `∫ dᵈk / π ^ (d / 2) · 1 / ((k²) ^ a ((k + q)²) ^ b)`
(Euclidean, `q² = Q > 0`) has two Feynman parameters, with Symanzik polynomials `U = x₀ + x₁` and
`F = Q x₀ x₁` (`QED.DimReg.masslessBubbleFamily`). Its Lee–Pomeransky integral
`∫_{(0,∞)²} x₀ ^ (a - 1) x₁ ^ (b - 1) (x₀ + x₁ + Q x₀ x₁) ^ (-d / 2) dx` converges absolutely for
`0 < re a`, `0 < re (d/2 - a)`, `0 < re (a + b - d/2)`, `0 < re (d/2 - b)`, and the normalized
integral is the textbook closed form
`I(d; a, b) = G(a, b) Q ^ (d/2 - a - b)`,
`G(a, b) = Γ(a + b - d/2) Γ(d/2 - a) Γ(d/2 - b) / (Γ(a) Γ(b) Γ(d - a - b))`.

**Proof.** At fixed `x₁ = w`, `x₀ + w + Q x₀ w = w (1 + c x₀)` with `c = (1 + Q w) / w`, so the
`x₀`-integral is a Beta integral of the second kind with parameters `(a, d/2 - a)`, leaving
`w ^ (a + b - d/2 - 1) (1 + Q w) ^ (-a)`, again a Beta integral of the second kind with parameters
`(a + b - d/2, d/2 - b)` (`QED.DimReg.integral_prod_betaPrime`).

## Main results

* `QED.DimReg.lpConvergent_masslessBubble`: absolute convergence.
* `QED.DimReg.lpIntegral_masslessBubble`: the closed form of the Lee–Pomeransky integral.
* `QED.DimReg.integral_masslessBubbleFamily`: `I(d; a, b) = G(a, b) Q ^ (d/2 - a - b)`.
-/

@[expose] public section

open MeasureTheory Set Complex MvPolynomial

namespace QED.DimReg

/-- The one-loop massless bubble family with external `q² = Q`: two propagators, `L = 1`,
`U = x₀ + x₁`, `F = Q x₀ x₁`. -/
noncomputable def masslessBubbleFamily (Q : ℝ) : FeynmanFamily 2 where
  loops := 1
  U := X 0 + X 1
  F := C Q * X 0 * X 1

theorem masslessBubbleFamily_isHomogeneous (Q : ℝ) : (masslessBubbleFamily Q).IsHomogeneous := by
  refine ⟨(isHomogeneous_X _ _).add (isHomogeneous_X _ _), ?_⟩
  exact ((isHomogeneous_C (Fin 2) Q).mul (isHomogeneous_X ℝ (0 : Fin 2))).mul
    (isHomogeneous_X ℝ (1 : Fin 2))

theorem lpPoly_masslessBubbleFamily (Q : ℝ) (x : Fin 2 → ℝ) :
    (masslessBubbleFamily Q).lpPoly x = x 0 + x 1 + Q * x 0 * x 1 := by
  simp [FeynmanFamily.lpPoly, masslessBubbleFamily]

/-- The coefficient `G(a, b) = Γ(a + b - d/2) Γ(d/2 - a) Γ(d/2 - b) / (Γ(a) Γ(b) Γ(d - a - b))`
of the massless bubble. -/
noncomputable def masslessBubbleCoeff (a b d : ℂ) : ℂ :=
  Gamma (a + b - d / 2) * Gamma (d / 2 - a) * Gamma (d / 2 - b) /
    (Gamma a * Gamma b * Gamma (d - a - b))

/-- The bubble integrand on `ℝ × ℝ`. -/
noncomputable def masslessBubbleIntegrand (Q : ℝ) (a b d : ℂ) (z : ℝ × ℝ) : ℂ :=
  (z.1 : ℂ) ^ (a - 1) * (z.2 : ℂ) ^ (b - 1) * ((z.1 + z.2 + Q * z.1 * z.2 : ℝ) : ℂ) ^ (-(d / 2))

theorem measurable_masslessBubbleIntegrand (Q : ℝ) (a b d : ℂ) :
    Measurable (masslessBubbleIntegrand Q a b d) := by
  unfold masslessBubbleIntegrand; fun_prop

theorem lpIntegrand_masslessBubbleFamily (Q : ℝ) (ν : Fin 2 → ℂ) (d : ℂ) (x : Fin 2 → ℝ) :
    lpIntegrand (masslessBubbleFamily Q).lpPoly ν d x =
      masslessBubbleIntegrand Q (ν 0) (ν 1) d (MeasurableEquiv.finTwoArrow x) := by
  simp [lpIntegrand, masslessBubbleIntegrand, lpPoly_masslessBubbleFamily, Fin.prod_univ_two]

theorem preimage_finTwoArrow_quad :
    (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹' (Ioi 0 ×ˢ Ioi 0) = posOrthant 2 := by
  ext x
  simp [mem_posOrthant, Fin.forall_fin_two]

theorem masslessBubbleIntegrand_eq {Q : ℝ} (hQ : 0 ≤ Q) (a b d : ℂ) {t w : ℝ} (ht : 0 < t)
    (hw : 0 < w) :
    masslessBubbleIntegrand Q a b d (t, w) =
      (w : ℂ) ^ (b - 1) * (w : ℂ) ^ (-(d / 2)) *
        betaPrimeIntegrand a (d / 2 - a) ((1 + Q * w) * w⁻¹) t := by
  have h1 : t + w + Q * t * w = w * (1 + (1 + Q * w) * w⁻¹ * t) := by
    field_simp; ring
  rw [masslessBubbleIntegrand, betaPrimeIntegrand, h1, ofReal_mul,
    mul_cpow_ofReal_nonneg hw.le (by positivity), show -(a + (d / 2 - a)) = -(d / 2) by ring]
  ring

theorem masslessBubble_outer_eq {Q : ℝ} (hQ : 0 ≤ Q) (a b d : ℂ) {w : ℝ} (hw : 0 < w) :
    (w : ℂ) ^ (b - 1) * (w : ℂ) ^ (-(d / 2)) * (((1 + Q * w) * w⁻¹ : ℝ) : ℂ) ^ (-a) =
      betaPrimeIntegrand (a + b - d / 2) (d / 2 - b) Q w := by
  have hw0 : (w : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw.ne'
  rw [ofReal_mul_inv_cpow (by positivity) hw, betaPrimeIntegrand,
    show -(a + b - d / 2 + (d / 2 - b)) = -a by ring,
    show a + b - d / 2 - 1 = (b - 1) + (-(d / 2)) + (-(-a)) by ring, cpow_add _ _ hw0,
    cpow_add _ _ hw0]
  ring

theorem masslessBubble_hyp {Q : ℝ} (hQ : 0 < Q) {a b d : ℂ}
    (h2 : 0 < (a + b - d / 2).re) (h3 : 0 < (d / 2 - b).re) :
    IntegrableOn (fun w : ℝ => (w : ℂ) ^ (b - 1) * (w : ℂ) ^ (-(d / 2)) *
      (((1 + Q * w) * w⁻¹ : ℝ) : ℂ) ^ (-a)) (Ioi 0) volume :=
  (integrableOn_betaPrime h2 h3 hQ).congr_fun
    (fun _ hw => (masslessBubble_outer_eq hQ.le a b d hw).symm) measurableSet_Ioi

theorem masslessBubble_c_pos {Q : ℝ} (hQ : 0 ≤ Q) : ∀ w ∈ Ioi (0 : ℝ), 0 < (1 + Q * w) * w⁻¹ :=
  fun w hw => by have : 0 < w := hw; positivity

theorem integrableOn_masslessBubbleIntegrand {Q : ℝ} (hQ : 0 < Q) {a b d : ℂ} (h0 : 0 < a.re)
    (h1 : 0 < (d / 2 - a).re) (h2 : 0 < (a + b - d / 2).re) (h3 : 0 < (d / 2 - b).re) :
    IntegrableOn (masslessBubbleIntegrand Q a b d) (Ioi 0 ×ˢ Ioi 0) := by
  rw [Measure.volume_eq_prod]
  exact integrableOn_prod_betaPrime measurableSet_Ioi h0 h1
    (measurable_masslessBubbleIntegrand Q a b d).aestronglyMeasurable
    (masslessBubble_c_pos hQ.le) (fun t ht w hw => masslessBubbleIntegrand_eq hQ.le a b d ht hw)
    (masslessBubble_hyp hQ h2 h3)

theorem integral_masslessBubbleIntegrand {Q : ℝ} (hQ : 0 < Q) {a b d : ℂ} (h0 : 0 < a.re)
    (h1 : 0 < (d / 2 - a).re) (h2 : 0 < (a + b - d / 2).re) (h3 : 0 < (d / 2 - b).re) :
    ∫ z in Ioi 0 ×ˢ Ioi 0, masslessBubbleIntegrand Q a b d z =
      (Q : ℂ) ^ (-(a + b - d / 2)) *
        (Gamma (a + b - d / 2) * Gamma (d / 2 - b) / Gamma (a + b - d / 2 + (d / 2 - b))) *
        (Gamma a * Gamma (d / 2 - a) / Gamma (a + (d / 2 - a))) := by
  rw [Measure.volume_eq_prod, integral_prod_betaPrime measurableSet_Ioi h0 h1
    (measurable_masslessBubbleIntegrand Q a b d).aestronglyMeasurable
    (masslessBubble_c_pos hQ.le) (fun t ht w hw => masslessBubbleIntegrand_eq hQ.le a b d ht hw)
    (masslessBubble_hyp hQ h2 h3), ← integral_betaPrime h2 h3 hQ]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi
    (fun w hw => masslessBubble_outer_eq hQ.le a b d hw)

/-- The bubble's Lee–Pomeransky integral converges absolutely for `0 < re a`,
`0 < re (d/2 - a)`, `0 < re (a + b - d/2)`, `0 < re (d/2 - b)`. -/
theorem lpConvergent_masslessBubble {Q : ℝ} (hQ : 0 < Q) {ν : Fin 2 → ℂ} {d : ℂ}
    (h0 : 0 < (ν 0).re) (h1 : 0 < (d / 2 - ν 0).re) (h2 : 0 < (ν 0 + ν 1 - d / 2).re)
    (h3 : 0 < (d / 2 - ν 1).re) : LPConvergent (masslessBubbleFamily Q).lpPoly ν d := by
  have e := (volume_preserving_finTwoArrow ℝ).integrableOn_comp_preimage
    MeasurableEquiv.finTwoArrow.measurableEmbedding
    (f := masslessBubbleIntegrand Q (ν 0) (ν 1) d) (s := Ioi 0 ×ˢ Ioi 0)
  rw [preimage_finTwoArrow_quad] at e
  unfold LPConvergent
  exact (e.mpr (integrableOn_masslessBubbleIntegrand hQ h0 h1 h2 h3)).congr_fun
    (fun x _ => (lpIntegrand_masslessBubbleFamily Q ν d x).symm) (measurableSet_posOrthant 2)

/-- The closed form of the bubble's Lee–Pomeransky integral. -/
theorem lpIntegral_masslessBubble {Q : ℝ} (hQ : 0 < Q) {ν : Fin 2 → ℂ} {d : ℂ}
    (h0 : 0 < (ν 0).re) (h1 : 0 < (d / 2 - ν 0).re) (h2 : 0 < (ν 0 + ν 1 - d / 2).re)
    (h3 : 0 < (d / 2 - ν 1).re) :
    lpIntegral (masslessBubbleFamily Q).lpPoly ν d =
      (Q : ℂ) ^ (-(ν 0 + ν 1 - d / 2)) *
        (Gamma (ν 0 + ν 1 - d / 2) * Gamma (d / 2 - ν 1) / Gamma (ν 0)) *
        (Gamma (ν 0) * Gamma (d / 2 - ν 0) / Gamma (d / 2)) := by
  have e := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding (masslessBubbleIntegrand Q (ν 0) (ν 1) d)
    (Ioi 0 ×ˢ Ioi 0)
  rw [preimage_finTwoArrow_quad] at e
  rw [lpIntegral]
  simp_rw [lpIntegrand_masslessBubbleFamily]
  rw [e, integral_masslessBubbleIntegrand hQ h0 h1 h2 h3]
  congr 3 <;> ring_nf

/-- **The massless bubble.** In the region of absolute convergence, the normalized integral is
`I(d; a, b) = G(a, b) Q ^ (d/2 - a - b)`. -/
theorem integral_masslessBubbleFamily {Q : ℝ} (hQ : 0 < Q) {ν : Fin 2 → ℂ} {d : ℂ}
    (h0 : 0 < (ν 0).re) (h1 : 0 < (d / 2 - ν 0).re) (h2 : 0 < (ν 0 + ν 1 - d / 2).re)
    (h3 : 0 < (d / 2 - ν 1).re) :
    (masslessBubbleFamily Q).integral ν d =
      masslessBubbleCoeff (ν 0) (ν 1) d * (Q : ℂ) ^ (d / 2 - ν 0 - ν 1) := by
  have hd : 0 < (d / 2).re := by
    have : d / 2 = ν 0 + (d / 2 - ν 0) := by ring
    rw [this, add_re]; linarith
  have g1 := Gamma_ne_zero_of_re_pos hd
  have g2 := Gamma_ne_zero_of_re_pos h0
  rw [FeynmanFamily.integral, lpIntegral_masslessBubble hQ h0 h1 h2 h3, FeynmanFamily.prefactor,
    masslessBubbleCoeff]
  simp only [masslessBubbleFamily, Fin.sum_univ_two, Fin.prod_univ_two]
  rw [show ((1 : ℕ) + 1 : ℂ) * d / 2 - (ν 0 + ν 1) = d - ν 0 - ν 1 by push_cast; ring,
    show d / 2 - ν 0 - ν 1 = -(ν 0 + ν 1 - d / 2) by ring]
  field_simp

end QED.DimReg
