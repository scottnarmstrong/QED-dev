/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceSigma
public import QED.GradedProof.RPi4Join

/-!
# (R-Π₄) step L6d2: the photon-weight marginal of the face majorant

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. On the product
`Δ_{p+1} × Δ_q` of the join coordinates, with the photon the last line of the face block
(`θ = W_last`), the face majorant `θ (c + θσ)^{-2}` integrates to at most
`|Δ_q| |Δ_p| · 2 c^{-1/2} σ^{-3/2}`: by the cone over the photon vertex
(`integral_simplex_cone`) the marginal of `θ` has density `(1 - θ)^p |Δ_p| ≤ |Δ_p|`, and
`integral_face_majorant_le` bounds the remaining one-dimensional integral.

* `integral_sigM_simplex_le` (the face block alone), **`integral_sigM_prod_le`** (the product).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop (sum_simplexPoint continuous_simplexPoint')
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet
  simplexPoint_mem_stdSimplex isCompact_simplexSet)

/-- The face majorant as a function of the barycentric point. -/
noncomputable def margF (m : ℕ) (c σ : ℝ) (z : Fin (m + 2) → ℝ) : ℝ :=
  z (Fin.last (m + 1)) * ((c + z (Fin.last (m + 1)) * σ) ^ 2)⁻¹

theorem continuous_margF {m : ℕ} {c σ : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ) :
    ContinuousOn (fun x : Fin (m + 1) → ℝ => margF m c σ (simplexPoint x))
      (simplexSet (m + 1)) := by
  have h1 : Continuous fun x : Fin (m + 1) → ℝ => simplexPoint x (Fin.last (m + 1)) :=
    (continuous_apply _).comp continuous_simplexPoint'
  refine h1.continuousOn.mul (ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_)
  have := (simplexPoint_mem_stdSimplex hx).1 (Fin.last (m + 1))
  positivity

theorem margF_le {m : ℕ} {c σ : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ) {z : Fin (m + 2) → ℝ}
    (h0 : 0 ≤ z (Fin.last (m + 1))) (h1 : z (Fin.last (m + 1)) ≤ 1) :
    margF m c σ z ≤ (c ^ 2)⁻¹ := by
  have hle : c ≤ c + z (Fin.last (m + 1)) * σ := le_add_of_nonneg_right (mul_nonneg h0 hσ)
  calc margF m c σ z ≤ 1 * (c ^ 2)⁻¹ :=
        mul_le_mul h1 (inv_anti₀ (by positivity) (pow_le_pow_left₀ hc.le hle 2)) (by positivity)
          zero_le_one
    _ = _ := one_mul _

/-- **The marginal bound on the face block.** -/
theorem integral_sigM_simplex_le {m : ℕ} {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
    ∫ x in simplexSet (m + 1), margF m c σ (simplexPoint x) ≤
      (volume (simplexSet m)).toReal * (2 * (c ^ (-(1 / 2) : ℝ) * σ ^ (-(3 / 2) : ℝ))) := by
  have hint : IntegrableOn (fun x => margF m c σ (simplexPoint x)) (simplexSet (m + 1)) :=
    (continuous_margF hc hσ.le).integrableOn_compact (isCompact_simplexSet _)
  rw [integral_simplex_cone hint]
  have hin : ∀ ρ y, margF m c σ (Fin.snoc (ρ • simplexPoint y) (1 - ρ)) =
      (1 - ρ) * ((c + (1 - ρ) * σ) ^ 2)⁻¹ := fun ρ y => by simp [margF]
  simp only [hin, setIntegral_const, smul_eq_mul]
  set vol := (volume (simplexSet m)).toReal
  have hv : 0 ≤ vol := ENNReal.toReal_nonneg
  have hcont : ContinuousOn (fun ρ : ℝ => (1 - ρ) * ((c + (1 - ρ) * σ) ^ 2)⁻¹) (uIcc 0 1) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.inv₀ (by fun_prop) fun ρ hρ => ?_)
    rw [uIcc_of_le zero_le_one] at hρ
    have : 0 ≤ 1 - ρ := by linarith [hρ.2]
    positivity
  have hmono : ∫ ρ in (0 : ℝ)..1, ρ ^ m * (vol * ((1 - ρ) * ((c + (1 - ρ) * σ) ^ 2)⁻¹)) ≤
      ∫ ρ in (0 : ℝ)..1, vol * ((1 - ρ) * ((c + (1 - ρ) * σ) ^ 2)⁻¹) := by
    refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun ρ hρ => ?_
    · exact (ContinuousOn.mul (by fun_prop) (continuousOn_const.mul hcont)).intervalIntegrable
    · exact (continuousOn_const.mul hcont).intervalIntegrable
    · have h1 : 0 ≤ 1 - ρ := by linarith [hρ.2]
      have hX : 0 ≤ vol * ((1 - ρ) * ((c + (1 - ρ) * σ) ^ 2)⁻¹) := by positivity
      exact (mul_le_of_le_one_left hX (pow_le_one₀ hρ.1 hρ.2))
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_ (integral_face_majorant_le hc hσ)) hv
  have := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => θ * ((c + θ * σ) ^ 2)⁻¹) (a := 0) (b := 1) 1
  simpa using this

/-- **The marginal bound on the product `Δ_{m+1} × Δ_q`.** -/
theorem integral_sigM_prod_le {m q : ℕ} {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
    ∫ x in simplexSet (m + 1) ×ˢ simplexSet q,
        sigM (fun x : (Fin (m + 1) → ℝ) × (Fin q → ℝ) => simplexPoint x.1 (Fin.last (m + 1)))
          c σ x ≤
      (volume (simplexSet q)).toReal *
        ((volume (simplexSet m)).toReal * (2 * (c ^ (-(1 / 2) : ℝ) * σ ^ (-(3 / 2) : ℝ)))) := by
  have hcont := continuous_margF (m := m) hc hσ.le
  have hint : IntegrableOn (fun x : (Fin (m + 1) → ℝ) × (Fin q → ℝ) =>
      margF m c σ (simplexPoint x.1)) (simplexSet (m + 1) ×ˢ simplexSet q) := by
    refine ContinuousOn.integrableOn_compact ((isCompact_simplexSet _).prod
      (isCompact_simplexSet _)) ?_
    exact hcont.comp continuous_fst.continuousOn fun x hx => hx.1
  have hprod := setIntegral_prod (μ := (volume : Measure (Fin (m + 1) → ℝ)))
    (ν := (volume : Measure (Fin q → ℝ)))
    (fun x : (Fin (m + 1) → ℝ) × (Fin q → ℝ) => margF m c σ (simplexPoint x.1))
    (s := simplexSet (m + 1)) (t := simplexSet q) (by rw [← Measure.volume_eq_prod]; exact hint)
  rw [← Measure.volume_eq_prod] at hprod
  have e : (fun x : (Fin (m + 1) → ℝ) × (Fin q → ℝ) =>
      sigM (fun x : (Fin (m + 1) → ℝ) × (Fin q → ℝ) => simplexPoint x.1 (Fin.last (m + 1))) c σ x) =
      fun x => margF m c σ (simplexPoint x.1) := rfl
  rw [e, hprod]
  simp only [setIntegral_const, smul_eq_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_sigM_simplex_le hc hσ) ENNReal.toReal_nonneg

end QED.GradedProof.RPi4

end
