/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Set (d), master `I₁₂`: the substitution `x = ρθ` on the unit square

The map `(ρ, θ) ↦ (ρθ, θ)` sends `(0, 1)²` bijectively onto the triangle `0 < x < θ < 1`, with
Jacobian `θ`. Hence, for `ψ` with `(ρ, θ) ↦ ψ(ρθ, θ)` integrable on the square,

  `∫_{(0,1)²} ψ(ρθ, θ) dρ dθ = ∫₀¹ dx ∫ₓ¹ ψ(x, θ) / θ dθ`,

with the inner and outer integrands integrable.

## Main results

* `QED.ThreeLoopD.i12_integral_tri`.
-/

@[expose] public section

open Real Filter Topology Set MeasureTheory

namespace QED.ThreeLoopD

/-- The map `(ρ, θ) ↦ (ρθ, θ)`. -/
noncomputable def i12TriMap (z : ℝ × ℝ) : ℝ × ℝ := (z.1 * z.2, z.2)

/-- The derivative of `(ρ, θ) ↦ (ρθ, θ)`. -/
noncomputable def i12TriDeriv (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (z.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + z.1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem hasFDerivAt_i12TriMap (z : ℝ × ℝ) : HasFDerivAt i12TriMap (i12TriDeriv z) z := by
  have hx := hasFDerivAt_fst (𝕜 := ℝ) (p := z) (E := ℝ) (F := ℝ)
  have hw := hasFDerivAt_snd (𝕜 := ℝ) (p := z) (E := ℝ) (F := ℝ)
  have h := (hx.mul hw).prodMk hw
  convert h using 1
  · funext v; simp [i12TriMap]
  · ext <;> simp [i12TriDeriv]

theorem det_i12TriDeriv (z : ℝ × ℝ) : (i12TriDeriv z).det = z.2 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, i12TriDeriv]

/-- The triangle `0 < x < θ < 1`, inside the square. -/
def i12Tri : Set (ℝ × ℝ) := (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) ∩ {q | q.1 < q.2}

theorem injOn_i12TriMap : InjOn i12TriMap (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  intro z hz w _ h
  simp only [i12TriMap, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [h2] at h1
  have := mul_right_cancel₀ (show w.2 ≠ 0 by rw [← h2]; exact hz.2.1.ne') h1
  exact Prod.ext this h2

theorem image_i12TriMap : i12TriMap '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) = i12Tri := by
  ext q
  constructor
  · rintro ⟨z, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    refine ⟨⟨⟨mul_pos h1 h3, show z.1 * z.2 < 1 by nlinarith⟩, h3, h4⟩, ?_⟩
    show z.1 * z.2 < z.2
    nlinarith
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    have h5' : q.1 < q.2 := h5
    refine ⟨(q.1 / q.2, q.2), ⟨⟨div_pos h1 h3, (div_lt_one h3).2 h5'⟩, h3, h4⟩, ?_⟩
    simp only [i12TriMap]
    rw [div_mul_cancel₀ _ h3.ne']

theorem measurableSet_i12Tri : MeasurableSet i12Tri :=
  (measurableSet_Ioo.prod measurableSet_Ioo).inter (measurableSet_lt measurable_fst measurable_snd)

/-- **The substitution `x = ρθ`**:
`∫_{(0,1)²} ψ(ρθ, θ) = ∫₀¹ dx ∫ₓ¹ ψ(x, θ) / θ dθ`, with integrability of both sides. -/
theorem i12_integral_tri {ψ : ℝ × ℝ → ℝ}
    (hψ : IntegrableOn (fun z : ℝ × ℝ => ψ (z.1 * z.2, z.2)) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) :
    (∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        IntegrableOn (fun θ => ψ (x, θ) / θ) (Ioo x 1)) ∧
      IntegrableOn (fun x => ∫ θ in Ioo x 1, ψ (x, θ) / θ) (Ioo 0 1) ∧
      ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ψ (z.1 * z.2, z.2) =
        ∫ x in Ioo (0 : ℝ) 1, ∫ θ in Ioo x 1, ψ (x, θ) / θ := by
  have : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  have hd : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      HasFDerivWithinAt i12TriMap (i12TriDeriv z) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) z :=
    fun z _ => (hasFDerivAt_i12TriMap z).hasFDerivWithinAt
  set f : ℝ × ℝ → ℝ := fun q => ψ q / q.2 with hf
  have hpt : ∀ z ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      |(i12TriDeriv z).det| • f (i12TriMap z) = ψ (z.1 * z.2, z.2) := by
    intro z hz
    rw [det_i12TriDeriv, abs_of_pos hz.2.1, smul_eq_mul]
    simp only [hf, i12TriMap]
    field_simp [hz.2.1.ne']
  have hfT : IntegrableOn f i12Tri := by
    rw [← image_i12TriMap, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS hd
      injOn_i12TriMap]
    exact hψ.congr_fun (fun z hz => (hpt z hz).symm) hS
  have heq : ∫ z in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ψ (z.1 * z.2, z.2) = ∫ q in i12Tri, f q := by
    rw [← image_i12TriMap, integral_image_eq_integral_abs_det_fderiv_smul volume hS hd
      injOn_i12TriMap]
    exact setIntegral_congr_fun hS fun z hz => (hpt z hz).symm
  set S : Set (ℝ × ℝ) := {q | q.1 < q.2} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_fst measurable_snd
  have hind : IntegrableOn (S.indicator f) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rw [IntegrableOn, integrable_indicator_iff hSm, IntegrableOn, Measure.restrict_restrict hSm,
      inter_comm]
    exact hfT
  have hTeq : ∫ q in i12Tri, f q = ∫ q in Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, S.indicator f q := by
    rw [integral_indicator hSm, Measure.restrict_restrict hSm, inter_comm]
    rfl
  have hind0 := hind
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hind
  have hslice : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ θ : ℝ,
      (Ioo x 1).indicator (fun θ => ψ (x, θ) / θ) θ =
        (Ioo (0 : ℝ) 1).indicator (fun θ => S.indicator f (x, θ)) θ := by
    intro x hx θ
    by_cases h1 : θ ∈ Ioo x 1
    · have h2 : θ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1, h1.1], h1.2⟩
      have h3 : (x, θ) ∈ S := h1.1
      rw [indicator_of_mem h1, indicator_of_mem h2, indicator_of_mem h3]
    · rw [indicator_of_notMem h1]
      by_cases h2 : θ ∈ Ioo (0 : ℝ) 1
      · have h3 : (x, θ) ∉ S := fun h => h1 ⟨h, h2.2⟩
        rw [indicator_of_mem h2, indicator_of_notMem h3]
      · rw [indicator_of_notMem h2]
  have hinner : ∀ x ∈ Ioo (0 : ℝ) 1,
      ∫ θ in Ioo x 1, ψ (x, θ) / θ = ∫ θ in Ioo (0 : ℝ) 1, S.indicator f (x, θ) := by
    intro x hx
    rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo]
    exact integral_congr_ae (ae_of_all _ (hslice x hx))
  have hae : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      IntegrableOn (fun θ => ψ (x, θ) / θ) (Ioo x 1) := by
    filter_upwards [hind.prod_right_ae, ae_restrict_mem measurableSet_Ioo] with x hx hx'
    rw [← integrable_indicator_iff measurableSet_Ioo]
    have : IntegrableOn (fun θ => S.indicator f (x, θ)) (Ioo (0 : ℝ) 1) volume := hx
    rw [← integrable_indicator_iff measurableSet_Ioo] at this
    exact this.congr (ae_of_all _ fun θ => (hslice x hx' θ).symm)
  refine ⟨hae, ?_, ?_⟩
  · exact (show IntegrableOn (fun x => ∫ θ in Ioo (0 : ℝ) 1, S.indicator f (x, θ)) (Ioo 0 1)
      volume from hind.integral_prod_left).congr_fun (fun x hx => (hinner x hx).symm)
      measurableSet_Ioo
  · rw [Measure.volume_eq_prod] at hind0
    rw [heq, hTeq, Measure.volume_eq_prod, setIntegral_prod _ hind0]
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => (hinner x hx).symm

end QED.ThreeLoopD
