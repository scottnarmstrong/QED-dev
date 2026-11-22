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
# One-loop two-point integrals with a quadratic second Symanzik polynomial

A one-loop integral with two propagators has `U = x₀ + x₁` and a quadratic form
`F = α x₀² + β x₀ x₁ + γ x₁²` (`QED.DimReg.oneLoopQuadFamily`). Examples (Euclidean, measure
`dᵈk / π ^ (d/2)`):

* the equal-mass bubble `1 / ((k² + 1) ((k + q)² + 1))`, `q² = Q`: `(α, β, γ) = (1, 2 + Q, 1)`
  (`QED.DimReg.massiveBubbleFamily`);
* the on-shell integral with a line of mass `m` and the electron line,
  `1 / ((k² + m²) ((k - p)² + 1))`, `p² = -1`: `F = m² x₀ U + x₁²`, `(α, β, γ) = (m², m², 1)`.

For `α, γ > 0`, `β ≥ 0`, `0 < re a`, `0 < re b`, `0 < re (a + b - d/2)`, `0 < re (d - a - b)`,
the Lee–Pomeransky integral converges and the normalized integral is the one-dimensional integral
`I(d; a, b) = Γ(a + b - d/2) / (Γ(a) Γ(b)) ·
  ∫₀^∞ s ^ (a - 1) (1 + s) ^ (a + b - d) (α s² + β s + γ) ^ (d/2 - a - b) ds`
(`QED.DimReg.integral_oneLoopQuadFamily`).

**Proof.** The substitution `(x₀, x₁) = (y s, y)` (`QED.DimReg.integral_quad_eq_subst`) gives
`G = y (1 + s) (1 + c y)` with `c = P(s) / (1 + s)`, `P(s) = α s² + β s + γ`; the `y`-integral is
a Beta integral of the second kind with parameters `(a + b - d/2, d - a - b)`. Since
`P(s) ≥ κ (1 + s)²` with `κ = min α γ / 2`, the remaining `s`-integrand is dominated by a
multiple of `s ^ (re a - 1) (1 + s) ^ (-(re a + re b))`.

## Main results

* `QED.DimReg.lpConvergent_oneLoopQuad`: absolute convergence.
* `QED.DimReg.lpIntegral_oneLoopQuad`: the Lee–Pomeransky integral.
* `QED.DimReg.integral_oneLoopQuadFamily`: the normalized integral.
-/

@[expose] public section

open MeasureTheory Set Complex MvPolynomial

namespace QED.DimReg

/-- The one-loop two-propagator family with `U = x₀ + x₁`, `F = α x₀² + β x₀ x₁ + γ x₁²`. -/
noncomputable def oneLoopQuadFamily (α β γ : ℝ) : FeynmanFamily 2 where
  loops := 1
  U := X 0 + X 1
  F := C α * X 0 ^ 2 + C β * X 0 * X 1 + C γ * X 1 ^ 2

theorem oneLoopQuadFamily_isHomogeneous (α β γ : ℝ) :
    (oneLoopQuadFamily α β γ).IsHomogeneous := by
  refine ⟨(isHomogeneous_X _ _).add (isHomogeneous_X _ _), ?_⟩
  exact (((isHomogeneous_C (Fin 2) α).mul ((isHomogeneous_X ℝ (0 : Fin 2)).pow 2)).add
    (((isHomogeneous_C (Fin 2) β).mul (isHomogeneous_X ℝ (0 : Fin 2))).mul
      (isHomogeneous_X ℝ (1 : Fin 2)))).add
    ((isHomogeneous_C (Fin 2) γ).mul ((isHomogeneous_X ℝ (1 : Fin 2)).pow 2))

theorem lpPoly_oneLoopQuadFamily (α β γ : ℝ) (x : Fin 2 → ℝ) :
    (oneLoopQuadFamily α β γ).lpPoly x =
      x 0 + x 1 + (α * x 0 ^ 2 + β * x 0 * x 1 + γ * x 1 ^ 2) := by
  simp [FeynmanFamily.lpPoly, oneLoopQuadFamily]

/-- The quadratic `P(s) = α s² + β s + γ`. -/
noncomputable def oneLoopQuadP (α β γ s : ℝ) : ℝ := α * s ^ 2 + β * s + γ

/-- The integrand on `ℝ × ℝ`. -/
noncomputable def oneLoopQuadIntegrand (α β γ : ℝ) (a b d : ℂ) (z : ℝ × ℝ) : ℂ :=
  (z.1 : ℂ) ^ (a - 1) * (z.2 : ℂ) ^ (b - 1) *
    ((z.1 + z.2 + (α * z.1 ^ 2 + β * z.1 * z.2 + γ * z.2 ^ 2) : ℝ) : ℂ) ^ (-(d / 2))

/-- The one-dimensional integrand `s ^ (a - 1) (1 + s) ^ (a + b - d) P(s) ^ (-(a + b - d/2))`
left after the `y`-integration. -/
noncomputable def oneLoopQuadOuter (α β γ : ℝ) (a b d : ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) ^ (a - 1) * ((1 + s : ℝ) : ℂ) ^ (a + b - d) *
    ((oneLoopQuadP α β γ s : ℝ) : ℂ) ^ (-(a + b - d / 2))

/-- The prefactor `s ^ (a - 1) (1 + s) ^ (-d/2)` of the `y`-fiber. -/
noncomputable def oneLoopQuadA (a d : ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) ^ (a - 1) * ((1 + s : ℝ) : ℂ) ^ (-(d / 2))

/-- The scale `c = P(s) / (1 + s)` of the `y`-fiber. -/
noncomputable def oneLoopQuadC (α β γ s : ℝ) : ℝ := oneLoopQuadP α β γ s * (1 + s)⁻¹

/-- The coefficient conditions `0 < α`, `0 ≤ β`, `0 < γ`. -/
structure OneLoopQuadPos (α β γ : ℝ) : Prop where
  α_pos : 0 < α
  β_nonneg : 0 ≤ β
  γ_pos : 0 < γ

variable {α β γ : ℝ}

theorem OneLoopQuadPos.P_pos (h : OneLoopQuadPos α β γ) {s : ℝ} (hs : 0 ≤ s) :
    0 < oneLoopQuadP α β γ s := by
  have := h.α_pos; have := h.β_nonneg; have := h.γ_pos
  unfold oneLoopQuadP; positivity

/-- `P(s) ≥ (min α γ / 2) (1 + s)²` for `s ≥ 0`. -/
theorem OneLoopQuadPos.le_P (h : OneLoopQuadPos α β γ) {s : ℝ} (hs : 0 ≤ s) :
    min α γ / 2 * (1 + s) ^ 2 ≤ oneLoopQuadP α β γ s := by
  have h1 : min α γ ≤ α := min_le_left _ _
  have h2 : min α γ ≤ γ := min_le_right _ _
  have h0 : 0 < min α γ := lt_min h.α_pos h.γ_pos
  have := h.β_nonneg
  unfold oneLoopQuadP
  nlinarith [sq_nonneg (1 - s), mul_nonneg this hs]

theorem OneLoopQuadPos.C_pos (h : OneLoopQuadPos α β γ) {s : ℝ} (hs : 0 < s) :
    0 < oneLoopQuadC α β γ s := by
  have := h.P_pos hs.le
  unfold oneLoopQuadC; positivity

theorem measurable_oneLoopQuadIntegrand (α β γ : ℝ) (a b d : ℂ) :
    Measurable (oneLoopQuadIntegrand α β γ a b d) := by
  unfold oneLoopQuadIntegrand; fun_prop

theorem measurable_quadSubst_oneLoopQuadIntegrand (α β γ : ℝ) (a b d : ℂ) :
    Measurable (quadSubst (oneLoopQuadIntegrand α β γ a b d)) := by
  unfold quadSubst oneLoopQuadIntegrand; fun_prop

theorem quadSubst_oneLoopQuadIntegrand (h : OneLoopQuadPos α β γ) (a b d : ℂ) {y s : ℝ}
    (hy : 0 < y) (hs : 0 < s) :
    quadSubst (oneLoopQuadIntegrand α β γ a b d) (y, s) =
      oneLoopQuadA a d s *
        betaPrimeIntegrand (a + b - d / 2) (d - a - b) (oneLoopQuadC α β γ s) y := by
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have h1 : y * s + y + (α * (y * s) ^ 2 + β * (y * s) * y + γ * y ^ 2) =
      y * (1 + s) * (1 + oneLoopQuadC α β γ s * y) := by
    simp only [oneLoopQuadC, oneLoopQuadP]
    have : (1 + s) ≠ 0 := by positivity
    field_simp
    ring
  have hc := h.C_pos hs
  simp only [quadSubst, oneLoopQuadIntegrand, oneLoopQuadA, betaPrimeIntegrand]
  rw [h1, cpow_ofReal_mul (x := y * (1 + s)) (y := 1 + oneLoopQuadC α β γ s * y) (by positivity)
      (by positivity), cpow_ofReal_mul (x := y) (y := 1 + s) hy.le (by positivity),
    show -(a + b - d / 2 + (d - a - b)) = -(d / 2) by ring,
    show a + b - d / 2 - 1 = 1 + (a - 1) + (b - 1) + -(d / 2) by ring]
  simp only [ofReal_mul, mul_cpow_ofReal_nonneg hy.le hs.le, cpow_add _ _ hy0, cpow_one]
  ring

theorem oneLoopQuad_outer_eq (h : OneLoopQuadPos α β γ) (a b d : ℂ) {s : ℝ} (hs : 0 < s) :
    oneLoopQuadA a d s * ((oneLoopQuadC α β γ s : ℝ) : ℂ) ^ (-(a + b - d / 2)) =
      oneLoopQuadOuter α β γ a b d s := by
  have h1 : ((1 + s : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [oneLoopQuadC, ofReal_mul_inv_cpow (h.P_pos hs.le).le (by positivity), oneLoopQuadA,
    oneLoopQuadOuter, neg_neg, show a + b - d = -(d / 2) + (a + b - d / 2) by ring,
    cpow_add _ _ h1]
  ring

/-- The one-dimensional integrand is dominated by a multiple of `‖betaPrimeIntegrand a b 1‖`,
hence integrable. -/
theorem integrableOn_oneLoopQuadOuter (h : OneLoopQuadPos α β γ) {a b d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hα : 0 < (a + b - d / 2).re) :
    IntegrableOn (oneLoopQuadOuter α β γ a b d) (Ioi 0) := by
  set κ := min α γ / 2 with hκ
  have hκ0 : 0 < κ := by have := lt_min h.α_pos h.γ_pos; rw [hκ]; positivity
  set r := (-(a + b - d / 2)).re with hr
  have hr0 : r ≤ 0 := by
    have := hα
    simp only [hr] at ⊢
    simp at this ⊢
    linarith
  refine (((integrableOn_betaPrime ha hb one_pos).norm).const_mul (κ ^ r)).mono' ?_ ?_
  · unfold oneLoopQuadOuter oneLoopQuadP; fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs : 0 < s := hs
    have h1 : 0 < 1 + s := by positivity
    rw [norm_betaPrimeIntegrand a b one_pos hs, oneLoopQuadOuter, norm_mul, norm_mul,
      norm_cpow_eq_rpow_re_of_pos hs, norm_cpow_eq_rpow_re_of_pos h1,
      norm_cpow_eq_rpow_re_of_pos (h.P_pos hs.le), one_mul, ← hr]
    have hle : oneLoopQuadP α β γ s ^ r ≤ κ ^ r * (1 + s) ^ (2 * r) := by
      rw [Real.rpow_mul h1.le, Real.rpow_two, ← Real.mul_rpow hκ0.le (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (h.le_P hs.le) hr0
    have hsplit : (1 + s) ^ (-(a.re + b.re)) = (1 + s) ^ (a + b - d).re * (1 + s) ^ (2 * r) := by
      rw [← Real.rpow_add h1, hr]
      congr 1
      simp
      ring
    rw [hsplit, show (a - 1).re = a.re - 1 by simp]
    calc s ^ (a.re - 1) * (1 + s) ^ (a + b - d).re * oneLoopQuadP α β γ s ^ r
        ≤ s ^ (a.re - 1) * (1 + s) ^ (a + b - d).re * (κ ^ r * (1 + s) ^ (2 * r)) := by gcongr
      _ = _ := by ring

theorem integrableOn_quadSubst_oneLoopQuadIntegrand (h : OneLoopQuadPos α β γ) {a b d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hα : 0 < (a + b - d / 2).re) (hβ : 0 < (d - a - b).re) :
    IntegrableOn (quadSubst (oneLoopQuadIntegrand α β γ a b d)) (Ioi 0 ×ˢ Ioi 0) := by
  rw [Measure.volume_eq_prod]
  exact integrableOn_prod_betaPrime measurableSet_Ioi hα hβ
    (measurable_quadSubst_oneLoopQuadIntegrand α β γ a b d).aestronglyMeasurable
    (fun s hs => h.C_pos hs) (fun y hy s hs => quadSubst_oneLoopQuadIntegrand h a b d hy hs)
    ((integrableOn_oneLoopQuadOuter h ha hb hα).congr_fun
      (fun s hs => (oneLoopQuad_outer_eq h a b d hs).symm) measurableSet_Ioi)

theorem integral_oneLoopQuadIntegrand (h : OneLoopQuadPos α β γ) {a b d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hα : 0 < (a + b - d / 2).re) (hβ : 0 < (d - a - b).re) :
    ∫ z in Ioi 0 ×ˢ Ioi 0, oneLoopQuadIntegrand α β γ a b d z =
      (∫ s in Ioi (0 : ℝ), oneLoopQuadOuter α β γ a b d s) *
        (Gamma (a + b - d / 2) * Gamma (d - a - b) / Gamma (a + b - d / 2 + (d - a - b))) := by
  have hS := integrableOn_quadSubst_oneLoopQuadIntegrand h ha hb hα hβ
  rw [integral_quad_eq_subst (measurable_oneLoopQuadIntegrand α β γ a b d) hS,
    Measure.volume_eq_prod, integral_prod_betaPrime measurableSet_Ioi hα hβ
    (measurable_quadSubst_oneLoopQuadIntegrand α β γ a b d).aestronglyMeasurable
    (fun s hs => h.C_pos hs) (fun y hy s hs => quadSubst_oneLoopQuadIntegrand h a b d hy hs)
    ((integrableOn_oneLoopQuadOuter h ha hb hα).congr_fun
      (fun s hs => (oneLoopQuad_outer_eq h a b d hs).symm) measurableSet_Ioi)]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun s hs => oneLoopQuad_outer_eq h a b d hs)

theorem lpIntegrand_oneLoopQuadFamily (ν : Fin 2 → ℂ) (d : ℂ) (x : Fin 2 → ℝ) :
    lpIntegrand (oneLoopQuadFamily α β γ).lpPoly ν d x =
      oneLoopQuadIntegrand α β γ (ν 0) (ν 1) d (MeasurableEquiv.finTwoArrow x) := by
  simp [lpIntegrand, oneLoopQuadIntegrand, lpPoly_oneLoopQuadFamily, Fin.prod_univ_two]

theorem preimage_finTwoArrow_Ioi_prod :
    (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ) ⁻¹' (Ioi 0 ×ˢ Ioi 0) = posOrthant 2 := by
  ext x
  simp [mem_posOrthant, Fin.forall_fin_two]

/-- Absolute convergence of the Lee–Pomeransky integral for `0 < re a`, `0 < re b`,
`0 < re (a + b - d/2)`, `0 < re (d - a - b)`, with `(a, b) = (ν₀, ν₁)`. -/
theorem lpConvergent_oneLoopQuad (h : OneLoopQuadPos α β γ) {ν : Fin 2 → ℂ} {d : ℂ}
    (ha : 0 < (ν 0).re) (hb : 0 < (ν 1).re) (hα : 0 < (ν 0 + ν 1 - d / 2).re)
    (hβ : 0 < (d - ν 0 - ν 1).re) : LPConvergent (oneLoopQuadFamily α β γ).lpPoly ν d := by
  have e := (volume_preserving_finTwoArrow ℝ).integrableOn_comp_preimage
    MeasurableEquiv.finTwoArrow.measurableEmbedding
    (f := oneLoopQuadIntegrand α β γ (ν 0) (ν 1) d) (s := Ioi 0 ×ˢ Ioi 0)
  rw [preimage_finTwoArrow_Ioi_prod] at e
  unfold LPConvergent
  exact (e.mpr (integrableOn_quad_of_subst (measurable_oneLoopQuadIntegrand α β γ _ _ d)
    (integrableOn_quadSubst_oneLoopQuadIntegrand h ha hb hα hβ))).congr_fun
    (fun x _ => (lpIntegrand_oneLoopQuadFamily ν d x).symm) (measurableSet_posOrthant 2)

/-- The Lee–Pomeransky integral is `Γ(a + b - d/2) Γ(d - a - b) / Γ(d/2)` times the
one-dimensional integral of `QED.DimReg.oneLoopQuadOuter`. -/
theorem lpIntegral_oneLoopQuad (h : OneLoopQuadPos α β γ) {ν : Fin 2 → ℂ} {d : ℂ}
    (ha : 0 < (ν 0).re) (hb : 0 < (ν 1).re) (hα : 0 < (ν 0 + ν 1 - d / 2).re)
    (hβ : 0 < (d - ν 0 - ν 1).re) :
    lpIntegral (oneLoopQuadFamily α β γ).lpPoly ν d =
      (∫ s in Ioi (0 : ℝ), oneLoopQuadOuter α β γ (ν 0) (ν 1) d s) *
        (Gamma (ν 0 + ν 1 - d / 2) * Gamma (d - ν 0 - ν 1) / Gamma (d / 2)) := by
  have e := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding (oneLoopQuadIntegrand α β γ (ν 0) (ν 1) d)
    (Ioi 0 ×ˢ Ioi 0)
  rw [preimage_finTwoArrow_Ioi_prod] at e
  rw [lpIntegral]
  simp_rw [lpIntegrand_oneLoopQuadFamily]
  rw [e, integral_oneLoopQuadIntegrand h ha hb hα hβ]
  congr 3
  ring

/-- **One-loop two-point integrals with quadratic `F`.** In the region of absolute convergence,
`I(d; a, b) = Γ(a + b - d/2) / (Γ(a) Γ(b)) · ∫₀^∞ oneLoopQuadOuter α β γ a b d`. -/
theorem integral_oneLoopQuadFamily (h : OneLoopQuadPos α β γ) {ν : Fin 2 → ℂ} {d : ℂ}
    (ha : 0 < (ν 0).re) (hb : 0 < (ν 1).re) (hα : 0 < (ν 0 + ν 1 - d / 2).re)
    (hβ : 0 < (d - ν 0 - ν 1).re) :
    (oneLoopQuadFamily α β γ).integral ν d =
      Gamma (ν 0 + ν 1 - d / 2) / (Gamma (ν 0) * Gamma (ν 1)) *
        ∫ s in Ioi (0 : ℝ), oneLoopQuadOuter α β γ (ν 0) (ν 1) d s := by
  have hd : 0 < (d / 2).re := by
    have : d / 2 = (ν 0 + ν 1 - d / 2) + (d - ν 0 - ν 1) := by ring
    rw [this, add_re]; linarith
  have g1 := Gamma_ne_zero_of_re_pos hd
  have g2 := Gamma_ne_zero_of_re_pos hβ
  have g3 := Gamma_ne_zero_of_re_pos ha
  have g4 := Gamma_ne_zero_of_re_pos hb
  rw [FeynmanFamily.integral, lpIntegral_oneLoopQuad h ha hb hα hβ, FeynmanFamily.prefactor]
  simp only [oneLoopQuadFamily, Fin.sum_univ_two, Fin.prod_univ_two]
  rw [show ((1 : ℕ) + 1 : ℂ) * d / 2 - (ν 0 + ν 1) = d - ν 0 - ν 1 by push_cast; ring]
  generalize Gamma (d - ν 0 - ν 1) = G2 at g2 ⊢
  generalize Gamma (d / 2) = G1 at g1 ⊢
  field_simp

/-! ### The on-shell integral with one massive line -/

/-- The on-shell one-loop family `1 / ((k² + m²) ^ a ((k - p)² + 1) ^ b)`, `p² = -1`
(Euclidean): `F = m² x₀ (x₀ + x₁) + x₁²`, i.e. `(α, β, γ) = (m², m², 1)`. -/
noncomputable abbrev onShellMassFamily (m2 : ℝ) : FeynmanFamily 2 := oneLoopQuadFamily m2 m2 1

/-- **The on-shell integral with a massive line.** For `m² > 0` and the convergence conditions,
`I(d; a, b) = Γ(a + b - d/2) / (Γ(a) Γ(b)) ∫₀^∞ s ^ (a - 1) (1 + s) ^ (a + b - d)
(m² s (1 + s) + 1) ^ (d/2 - a - b) ds`. -/
theorem integral_onShellMassFamily {m2 : ℝ} (hm : 0 < m2) {ν : Fin 2 → ℂ} {d : ℂ}
    (ha : 0 < (ν 0).re) (hb : 0 < (ν 1).re) (hα : 0 < (ν 0 + ν 1 - d / 2).re)
    (hβ : 0 < (d - ν 0 - ν 1).re) :
    (onShellMassFamily m2).integral ν d =
      Gamma (ν 0 + ν 1 - d / 2) / (Gamma (ν 0) * Gamma (ν 1)) *
        ∫ s in Ioi (0 : ℝ), oneLoopQuadOuter m2 m2 1 (ν 0) (ν 1) d s :=
  integral_oneLoopQuadFamily ⟨hm, hm.le, one_pos⟩ ha hb hα hβ

end QED.DimReg
