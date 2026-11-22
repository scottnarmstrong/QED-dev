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
# The two-loop vacuum integral with two unit masses and one massless line

The two-loop vacuum ("sunset") integral
`∫∫ dᵈk dᵈl / π ^ d · 1 / ((k² + 1) ^ a (l² + 1) ^ b ((k - l)²) ^ n)` (Euclidean) has three
Feynman parameters, with Symanzik polynomials `U = x₀ x₁ + x₀ x₂ + x₁ x₂` and `F = U (x₀ + x₁)`
(unit masses on lines `0, 1`, massless line `2`; `QED.DimReg.vacuumTwoMassFamily`). Its
Lee–Pomeransky polynomial factorizes, `G = U (1 + x₀ + x₁)`. In its region of absolute convergence
the normalized integral is the closed form (Davydychev–Tausk, Nucl. Phys. B 397 (1993) 123)
`Γ(a + n - d/2) Γ(b + n - d/2) Γ(a + b + n - d) Γ(d/2 - n) /
  (Γ(a) Γ(b) Γ(d/2) Γ(a + b + 2n - d))` (`QED.DimReg.vacuumTwoMassCoeff`).

**Proof.** Three one-dimensional Beta integrals of the second kind:
* in `x₂` at fixed `(u, v) = (x₀, x₁)`: `u v + x₂ (u + v) = u v (1 + c x₂)`, `c = (u + v) / (u v)`,
  parameters `(n, d/2 - n)`;
* the substitution `u = y s`, `v = y` (`QED.DimReg.integral_quad_eq_subst`), then in `y`:
  `1 + u + v = 1 + (1 + s) y`, parameters `(a + b + n - d, 3d/2 - a - b - n)`;
* in `s`: parameters `(a + n - d/2, b + n - d/2)`.

## Main results

* `QED.DimReg.lpConvergent_vacuumTwoMass`: absolute convergence.
* `QED.DimReg.lpIntegral_vacuumTwoMass`: the closed form of the Lee–Pomeransky integral.
* `QED.DimReg.integral_vacuumTwoMassFamily`: the normalized integral equals
  `QED.DimReg.vacuumTwoMassCoeff`.
-/

@[expose] public section

open MeasureTheory Set Complex MvPolynomial

namespace QED.DimReg

/-- The two-loop vacuum family with unit masses on lines `0, 1` and a massless line `2`:
`L = 2`, `U = x₀ x₁ + x₀ x₂ + x₁ x₂`, `F = U (x₀ + x₁)`. -/
noncomputable def vacuumTwoMassFamily : FeynmanFamily 3 where
  loops := 2
  U := X 0 * X 1 + X 0 * X 2 + X 1 * X 2
  F := (X 0 * X 1 + X 0 * X 2 + X 1 * X 2) * (X 0 + X 1)

theorem vacuumTwoMassFamily_isHomogeneous : vacuumTwoMassFamily.IsHomogeneous := by
  have hU : IsHomogeneous (X 0 * X 1 + X 0 * X 2 + X 1 * X 2 : MvPolynomial (Fin 3) ℝ) 2 :=
    (((isHomogeneous_X ℝ _).mul (isHomogeneous_X ℝ _)).add
      ((isHomogeneous_X ℝ _).mul (isHomogeneous_X ℝ _))).add
      ((isHomogeneous_X ℝ _).mul (isHomogeneous_X ℝ _))
  exact ⟨hU, hU.mul ((isHomogeneous_X ℝ _).add (isHomogeneous_X ℝ _))⟩

theorem lpPoly_vacuumTwoMassFamily (x : Fin 3 → ℝ) :
    vacuumTwoMassFamily.lpPoly x =
      (x 0 * x 1 + x 2 * (x 0 + x 1)) * (1 + x 0 + x 1) := by
  simp [FeynmanFamily.lpPoly, vacuumTwoMassFamily]
  ring

/-- The closed form `Γ(a + n - d/2) Γ(b + n - d/2) Γ(a + b + n - d) Γ(d/2 - n) /
(Γ(a) Γ(b) Γ(d/2) Γ(a + b + 2n - d))` of the two-mass vacuum integral. -/
noncomputable def vacuumTwoMassCoeff (a b n d : ℂ) : ℂ :=
  Gamma (a + n - d / 2) * Gamma (b + n - d / 2) * Gamma (a + b + n - d) * Gamma (d / 2 - n) /
    (Gamma a * Gamma b * Gamma (d / 2) * Gamma (a + b + 2 * n - d))

/-! ### The integrand in the coordinates `(x₂, (x₀, x₁))` -/

/-- The Lee–Pomeransky integrand in the coordinates `z = (x₂, (x₀, x₁))`. -/
noncomputable def vacuumTwoMassIntegrand (a b n d : ℂ) (z : ℝ × (ℝ × ℝ)) : ℂ :=
  (z.2.1 : ℂ) ^ (a - 1) * (z.2.2 : ℂ) ^ (b - 1) * (z.1 : ℂ) ^ (n - 1) *
    (((z.2.1 * z.2.2 + z.1 * (z.2.1 + z.2.2)) * (1 + z.2.1 + z.2.2) : ℝ) : ℂ) ^ (-(d / 2))

/-- The prefactor after the `x₂`-integration. -/
noncomputable def vacuumTwoMassA (a b d : ℂ) (w : ℝ × ℝ) : ℂ :=
  (w.1 : ℂ) ^ (a - 1) * (w.2 : ℂ) ^ (b - 1) * ((w.1 * w.2 : ℝ) : ℂ) ^ (-(d / 2)) *
    ((1 + w.1 + w.2 : ℝ) : ℂ) ^ (-(d / 2))

/-- The scale `c = (u + v) / (u v)` of the `x₂`-integration. -/
noncomputable def vacuumTwoMassC (w : ℝ × ℝ) : ℝ := (w.1 + w.2) * (w.1 * w.2)⁻¹

/-- The integrand after the `x₂`-integration (up to `Γ(n) Γ(d/2 - n) / Γ(d/2)`). -/
noncomputable def vacuumTwoMassH (a b n d : ℂ) (w : ℝ × ℝ) : ℂ :=
  vacuumTwoMassA a b d w * ((vacuumTwoMassC w : ℝ) : ℂ) ^ (-n)

/-- The prefactor after the substitution `(u, v) = (y s, y)` and the `y`-integration. -/
noncomputable def vacuumTwoMassA' (a n d : ℂ) (s : ℝ) : ℂ :=
  (s : ℂ) ^ (a - 1 + n - d / 2) * ((1 + s : ℝ) : ℂ) ^ (-n)

theorem measurable_vacuumTwoMassIntegrand (a b n d : ℂ) :
    Measurable (vacuumTwoMassIntegrand a b n d) := by
  unfold vacuumTwoMassIntegrand; fun_prop

theorem measurable_vacuumTwoMassH (a b n d : ℂ) : Measurable (vacuumTwoMassH a b n d) := by
  unfold vacuumTwoMassH vacuumTwoMassA vacuumTwoMassC; fun_prop

theorem measurable_quadSubst_vacuumTwoMassH (a b n d : ℂ) :
    Measurable (quadSubst (vacuumTwoMassH a b n d)) := by
  unfold quadSubst vacuumTwoMassH vacuumTwoMassA vacuumTwoMassC; fun_prop

theorem vacuumTwoMassIntegrand_eq (a b n d : ℂ) {t : ℝ} (ht : 0 < t) {w : ℝ × ℝ}
    (hw : w ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :
    vacuumTwoMassIntegrand a b n d (t, w) =
      vacuumTwoMassA a b d w * betaPrimeIntegrand n (d / 2 - n) (vacuumTwoMassC w) t := by
  obtain ⟨hu, hv⟩ := hw
  have hu : 0 < w.1 := hu
  have hv : 0 < w.2 := hv
  have h1 : (w.1 * w.2 + t * (w.1 + w.2)) * (1 + w.1 + w.2) =
      (w.1 * w.2) * (1 + vacuumTwoMassC w * t) * (1 + w.1 + w.2) := by
    simp only [vacuumTwoMassC]; field_simp
  have hc : 0 < vacuumTwoMassC w := by unfold vacuumTwoMassC; positivity
  simp only [vacuumTwoMassIntegrand]
  rw [h1, cpow_ofReal_mul (by positivity) (by positivity),
    cpow_ofReal_mul (by positivity) (by positivity), vacuumTwoMassA, betaPrimeIntegrand,
    show -(n + (d / 2 - n)) = -(d / 2) by ring]
  ring

theorem quadSubst_vacuumTwoMassH (a b n d : ℂ) {y s : ℝ} (hy : 0 < y) (hs : 0 < s) :
    quadSubst (vacuumTwoMassH a b n d) (y, s) =
      vacuumTwoMassA' a n d s *
        betaPrimeIntegrand (a + b + n - d) (3 * d / 2 - a - b - n) (1 + s) y := by
  have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy.ne'
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hc : vacuumTwoMassC (y * s, y) = (1 + s) * (y * s)⁻¹ := by
    simp only [vacuumTwoMassC]; field_simp; ring
  have h1 : 1 + y * s + y = 1 + (1 + s) * y := by ring
  simp only [quadSubst, vacuumTwoMassH, vacuumTwoMassA, vacuumTwoMassA', betaPrimeIntegrand]
  rw [hc, h1, ofReal_mul_inv_cpow (by positivity) (by positivity),
    cpow_ofReal_mul (by positivity) hy.le,
    show -(a + b + n - d + (3 * d / 2 - a - b - n)) = -(d / 2) by ring]
  simp only [cpow_ofReal_mul hy.le hs.le, neg_neg]
  rw [show a + b + n - d - 1 = 1 + (a - 1) + (b - 1) + -(d / 2) + -(d / 2) + n by ring,
    show a - 1 + n - d / 2 = (a - 1) + -(d / 2) + n by ring]
  simp only [cpow_add _ _ hy0, cpow_add _ _ hs0, cpow_one]
  ring

theorem vacuumTwoMassA'_outer (a b n d : ℂ) {s : ℝ} (hs : 0 < s) :
    vacuumTwoMassA' a n d s * ((1 + s : ℝ) : ℂ) ^ (-(a + b + n - d)) =
      betaPrimeIntegrand (a + n - d / 2) (b + n - d / 2) 1 s := by
  have h1 : ((1 + s : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [vacuumTwoMassA', betaPrimeIntegrand, one_mul, mul_assoc, ← cpow_add _ _ h1]
  congr 2 <;> ring

/-! ### Integrability and value in the coordinates `(x₂, (x₀, x₁))` -/

section

variable {a b n d : ℂ}

theorem integrableOn_quadSubst_vacuumTwoMassH (h2 : 0 < (a + b + n - d).re)
    (h3 : 0 < (3 * d / 2 - a - b - n).re) (h4 : 0 < (a + n - d / 2).re)
    (h5 : 0 < (b + n - d / 2).re) :
    IntegrableOn (quadSubst (vacuumTwoMassH a b n d)) (Ioi 0 ×ˢ Ioi 0) := by
  rw [Measure.volume_eq_prod]
  exact integrableOn_prod_betaPrime measurableSet_Ioi h2 h3
    (measurable_quadSubst_vacuumTwoMassH a b n d).aestronglyMeasurable
    (fun s hs => by have : 0 < s := hs; positivity)
    (fun y hy s hs => quadSubst_vacuumTwoMassH a b n d hy hs)
    ((integrableOn_betaPrime h4 h5 one_pos).congr_fun
      (fun s hs => (vacuumTwoMassA'_outer a b n d hs).symm) measurableSet_Ioi)

theorem integral_vacuumTwoMassH (h2 : 0 < (a + b + n - d).re)
    (h3 : 0 < (3 * d / 2 - a - b - n).re) (h4 : 0 < (a + n - d / 2).re)
    (h5 : 0 < (b + n - d / 2).re) :
    IntegrableOn (vacuumTwoMassH a b n d) (Ioi 0 ×ˢ Ioi 0) ∧
      ∫ w in Ioi 0 ×ˢ Ioi 0, vacuumTwoMassH a b n d w =
        Gamma (a + n - d / 2) * Gamma (b + n - d / 2) /
            Gamma (a + n - d / 2 + (b + n - d / 2)) *
          (Gamma (a + b + n - d) * Gamma (3 * d / 2 - a - b - n) /
            Gamma (a + b + n - d + (3 * d / 2 - a - b - n))) := by
  have hS := integrableOn_quadSubst_vacuumTwoMassH h2 h3 h4 h5
  refine ⟨integrableOn_quad_of_subst (measurable_vacuumTwoMassH a b n d) hS, ?_⟩
  rw [integral_quad_eq_subst (measurable_vacuumTwoMassH a b n d) hS, Measure.volume_eq_prod,
    integral_prod_betaPrime measurableSet_Ioi h2 h3
      (measurable_quadSubst_vacuumTwoMassH a b n d).aestronglyMeasurable
      (fun s hs => by have : 0 < s := hs; positivity)
      (fun y hy s hs => quadSubst_vacuumTwoMassH a b n d hy hs)
      ((integrableOn_betaPrime h4 h5 one_pos).congr_fun
        (fun s hs => (vacuumTwoMassA'_outer a b n d hs).symm) measurableSet_Ioi)]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs => vacuumTwoMassA'_outer a b n d hs),
    integral_betaPrime h4 h5 one_pos, ofReal_one, one_cpow, one_mul]

theorem vacuumTwoMass_C_pos : ∀ w ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), 0 < vacuumTwoMassC w := by
  rintro w ⟨hu, hv⟩
  have hu : 0 < w.1 := hu
  have hv : 0 < w.2 := hv
  unfold vacuumTwoMassC; positivity

theorem integrableOn_vacuumTwoMassIntegrand (h0 : 0 < n.re) (h1 : 0 < (d / 2 - n).re)
    (h2 : 0 < (a + b + n - d).re) (h3 : 0 < (3 * d / 2 - a - b - n).re)
    (h4 : 0 < (a + n - d / 2).re) (h5 : 0 < (b + n - d / 2).re) :
    IntegrableOn (vacuumTwoMassIntegrand a b n d) (Ioi 0 ×ˢ (Ioi 0 ×ˢ Ioi 0)) := by
  rw [Measure.volume_eq_prod]
  exact integrableOn_prod_betaPrime (measurableSet_Ioi.prod measurableSet_Ioi) h0 h1
    (measurable_vacuumTwoMassIntegrand a b n d).aestronglyMeasurable vacuumTwoMass_C_pos
    (fun t ht w hw => vacuumTwoMassIntegrand_eq a b n d ht hw)
    (integral_vacuumTwoMassH h2 h3 h4 h5).1

theorem integral_vacuumTwoMassIntegrand (h0 : 0 < n.re) (h1 : 0 < (d / 2 - n).re)
    (h2 : 0 < (a + b + n - d).re) (h3 : 0 < (3 * d / 2 - a - b - n).re)
    (h4 : 0 < (a + n - d / 2).re) (h5 : 0 < (b + n - d / 2).re) :
    ∫ z in Ioi 0 ×ˢ (Ioi 0 ×ˢ Ioi 0), vacuumTwoMassIntegrand a b n d z =
      Gamma (a + n - d / 2) * Gamma (b + n - d / 2) /
            Gamma (a + n - d / 2 + (b + n - d / 2)) *
          (Gamma (a + b + n - d) * Gamma (3 * d / 2 - a - b - n) /
            Gamma (a + b + n - d + (3 * d / 2 - a - b - n))) *
        (Gamma n * Gamma (d / 2 - n) / Gamma (n + (d / 2 - n))) := by
  rw [Measure.volume_eq_prod, integral_prod_betaPrime (measurableSet_Ioi.prod measurableSet_Ioi)
    h0 h1 (measurable_vacuumTwoMassIntegrand a b n d).aestronglyMeasurable vacuumTwoMass_C_pos
    (fun t ht w hw => vacuumTwoMassIntegrand_eq a b n d ht hw)
    (integral_vacuumTwoMassH h2 h3 h4 h5).1]
  have h := (integral_vacuumTwoMassH h2 h3 h4 h5).2
  simp only [vacuumTwoMassH] at h
  rw [h]

end

/-! ### Transfer to the orthant -/

/-- The coordinates `x ↦ (x₂, (x₀, x₁))` on `ℝ³`. -/
noncomputable def vacuumTwoMassEquiv : (Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow)

theorem vacuumTwoMassEquiv_apply (x : Fin 3 → ℝ) :
    vacuumTwoMassEquiv x = (x 2, (x 0, x 1)) := by
  simp [vacuumTwoMassEquiv, MeasurableEquiv.piFinSuccAbove_apply]
  rfl

theorem measurePreserving_vacuumTwoMassEquiv : MeasurePreserving vacuumTwoMassEquiv := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have h2 := (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
  exact h2.comp h1

theorem preimage_vacuumTwoMassEquiv :
    vacuumTwoMassEquiv ⁻¹' (Ioi 0 ×ˢ (Ioi 0 ×ˢ Ioi 0)) = posOrthant 3 := by
  ext x
  simp only [mem_preimage, vacuumTwoMassEquiv_apply, mem_prod, mem_Ioi, mem_posOrthant,
    Fin.forall_fin_succ, Fin.isValue, IsEmpty.forall_iff, and_true]
  constructor
  · rintro ⟨h2, h0, h1⟩; exact ⟨h0, h1, h2⟩
  · rintro ⟨h0, h1, h2⟩; exact ⟨h2, h0, h1⟩

theorem lpIntegrand_vacuumTwoMassFamily (ν : Fin 3 → ℂ) (d : ℂ) (x : Fin 3 → ℝ) :
    lpIntegrand vacuumTwoMassFamily.lpPoly ν d x =
      vacuumTwoMassIntegrand (ν 0) (ν 1) (ν 2) d (vacuumTwoMassEquiv x) := by
  rw [vacuumTwoMassEquiv_apply, lpIntegrand, lpPoly_vacuumTwoMassFamily, vacuumTwoMassIntegrand,
    Fin.prod_univ_three]

/-- The two-mass vacuum Lee–Pomeransky integral converges absolutely for `0 < re n`,
`0 < re (d/2 - n)`, `0 < re (a + b + n - d)`, `0 < re (3d/2 - a - b - n)`,
`0 < re (a + n - d/2)`, `0 < re (b + n - d/2)`, with `(a, b, n) = (ν₀, ν₁, ν₂)`. -/
theorem lpConvergent_vacuumTwoMass {ν : Fin 3 → ℂ} {d : ℂ} (h0 : 0 < (ν 2).re)
    (h1 : 0 < (d / 2 - ν 2).re) (h2 : 0 < (ν 0 + ν 1 + ν 2 - d).re)
    (h3 : 0 < (3 * d / 2 - ν 0 - ν 1 - ν 2).re) (h4 : 0 < (ν 0 + ν 2 - d / 2).re)
    (h5 : 0 < (ν 1 + ν 2 - d / 2).re) : LPConvergent vacuumTwoMassFamily.lpPoly ν d := by
  have e := measurePreserving_vacuumTwoMassEquiv.integrableOn_comp_preimage
    vacuumTwoMassEquiv.measurableEmbedding (f := vacuumTwoMassIntegrand (ν 0) (ν 1) (ν 2) d)
    (s := Ioi 0 ×ˢ (Ioi 0 ×ˢ Ioi 0))
  rw [preimage_vacuumTwoMassEquiv] at e
  unfold LPConvergent
  exact (e.mpr (integrableOn_vacuumTwoMassIntegrand h0 h1 h2 h3 h4 h5)).congr_fun
    (fun x _ => (lpIntegrand_vacuumTwoMassFamily ν d x).symm) (measurableSet_posOrthant 3)

/-- The closed form of the two-mass vacuum Lee–Pomeransky integral. -/
theorem lpIntegral_vacuumTwoMass {ν : Fin 3 → ℂ} {d : ℂ} (h0 : 0 < (ν 2).re)
    (h1 : 0 < (d / 2 - ν 2).re) (h2 : 0 < (ν 0 + ν 1 + ν 2 - d).re)
    (h3 : 0 < (3 * d / 2 - ν 0 - ν 1 - ν 2).re) (h4 : 0 < (ν 0 + ν 2 - d / 2).re)
    (h5 : 0 < (ν 1 + ν 2 - d / 2).re) :
    lpIntegral vacuumTwoMassFamily.lpPoly ν d =
      Gamma (ν 0 + ν 2 - d / 2) * Gamma (ν 1 + ν 2 - d / 2) / Gamma (ν 0 + ν 1 + 2 * ν 2 - d) *
        (Gamma (ν 0 + ν 1 + ν 2 - d) * Gamma (3 * d / 2 - ν 0 - ν 1 - ν 2) / Gamma (d / 2)) *
        (Gamma (ν 2) * Gamma (d / 2 - ν 2) / Gamma (d / 2)) := by
  have e := measurePreserving_vacuumTwoMassEquiv.setIntegral_preimage_emb
    vacuumTwoMassEquiv.measurableEmbedding (vacuumTwoMassIntegrand (ν 0) (ν 1) (ν 2) d)
    (Ioi 0 ×ˢ (Ioi 0 ×ˢ Ioi 0))
  rw [preimage_vacuumTwoMassEquiv] at e
  rw [lpIntegral]
  simp_rw [lpIntegrand_vacuumTwoMassFamily]
  rw [e, integral_vacuumTwoMassIntegrand h0 h1 h2 h3 h4 h5]
  congr 4 <;> ring_nf

/-- **The two-mass vacuum integral.** In the region of absolute convergence the normalized
integral is `QED.DimReg.vacuumTwoMassCoeff ν₀ ν₁ ν₂ d`. -/
theorem integral_vacuumTwoMassFamily {ν : Fin 3 → ℂ} {d : ℂ} (h0 : 0 < (ν 2).re)
    (h1 : 0 < (d / 2 - ν 2).re) (h2 : 0 < (ν 0 + ν 1 + ν 2 - d).re)
    (h3 : 0 < (3 * d / 2 - ν 0 - ν 1 - ν 2).re) (h4 : 0 < (ν 0 + ν 2 - d / 2).re)
    (h5 : 0 < (ν 1 + ν 2 - d / 2).re) :
    vacuumTwoMassFamily.integral ν d = vacuumTwoMassCoeff (ν 0) (ν 1) (ν 2) d := by
  have g1 := Gamma_ne_zero_of_re_pos h0
  have g2 := Gamma_ne_zero_of_re_pos h3
  rw [FeynmanFamily.integral, lpIntegral_vacuumTwoMass h0 h1 h2 h3 h4 h5, FeynmanFamily.prefactor,
    vacuumTwoMassCoeff]
  simp only [vacuumTwoMassFamily, Fin.sum_univ_three, Fin.prod_univ_three]
  rw [show ((2 : ℕ) + 1 : ℂ) * d / 2 - (ν 0 + ν 1 + ν 2) = 3 * d / 2 - ν 0 - ν 1 - ν 2 by
    push_cast; ring]
  have hd : 0 < (d / 2).re := by
    have : d / 2 = ν 2 + (d / 2 - ν 2) := by ring
    rw [this, add_re]; linarith
  have g3 := Gamma_ne_zero_of_re_pos hd
  generalize Gamma (3 * d / 2 - ν 0 - ν 1 - ν 2) = G3 at g2 ⊢
  generalize Gamma (ν 2) = G2 at g1 ⊢
  generalize Gamma (d / 2) = Gd at g3 ⊢
  field_simp

end QED.DimReg
