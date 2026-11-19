/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtAssemblyBound

/-!
# The energy-first integral and integrals over spectral parameters

Generic layer of the `ε → 0⁺` engine (helper level). After the integration by parts in the
Feynman parameters of the inserted vacuum polarizations, the outer integrand is an integral over
spectral parameters `x ∈ X` (one parameter in `(0, 1)` per insertion, or a product of them) of
one-loop vertices. Given bounds of the form `QED.TwoLoop.VPHalfAtAssembly.Good` uniform in `x`,
this file exchanges the energy-first integral with the parameter integral and passes to the
limit inside it. Everything holds for an arbitrary finite measure `ν` on a measurable space `X`
(`ν` = Lebesgue measure on `(0, 1]`, on `(0, 1]²`, …).

* `efi_integral_swap`: the energy-first integral commutes with `∫ dν` under the two integrability
  conditions of Fubini (energy × parameter at fixed spatial momentum, then space × parameter).
* `integrable_of_good_param`: both conditions from a jointly measurable family that is `Good`
  with one constant `C` and one pointwise bound `G` for `ν`-almost every `x`.
* `efi_integral_eq_of_good`: hence `∫_D ∫ g x dν = ∫ (∫_D g x) dν`, both stages integrable.
* **`tendsto_integral_efi_of_good`**: dominated convergence in the parameter: if the family
  `g i` is `Good` with a constant `C` independent of `i` and the energy-first integrals converge
  for almost every `x`, then `∫ (∫_D g i x) dν → ∫ F dν`; the limit `F` is integrable
  (`integrable_of_tendsto_efi_of_good`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace QED.TwoLoop.VPHalfAtGen

open QED.OneLoop QED.TwoLoop.VPUnitNested QED.TwoLoop.VPHalfAtAssembly

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- **The energy-first integral commutes with an integral over parameters**, under the two
integrability conditions of Fubini. -/
theorem efi_integral_swap [SFinite ν] (g : X → (Fin 4 → ℝ) → ℂ)
    (h1 : ∀ v : Fin 3 → ℝ, Integrable (fun q : ℝ × X => g q.2 (Fin.cons q.1 v : Fin 4 → ℝ))
      ((volume : Measure ℝ).prod ν))
    (h2 : Integrable (fun q : (Fin 3 → ℝ) × X => ∫ t : ℝ, g q.2 (Fin.cons t q.1 : Fin 4 → ℝ))
      ((volume : Measure (Fin 3 → ℝ)).prod ν)) :
    EFInt (fun ℓ => ∫ x, g x ℓ ∂ν) ∧
      energyFirstIntegral (fun ℓ => ∫ x, g x ℓ ∂ν) = ∫ x, energyFirstIntegral (g x) ∂ν := by
  have hin : ∀ v : Fin 3 → ℝ, ∫ t : ℝ, ∫ x, g x (Fin.cons t v : Fin 4 → ℝ) ∂ν =
      ∫ x, (∫ t : ℝ, g x (Fin.cons t v : Fin 4 → ℝ)) ∂ν := fun v =>
    integral_integral_swap (f := fun (t : ℝ) (x : X) => g x (Fin.cons t v : Fin 4 → ℝ)) (h1 v)
  refine ⟨⟨fun v => (h1 v).integral_prod_left, ?_⟩, ?_⟩
  · simp_rw [hin]
    exact h2.integral_prod_left
  · unfold energyFirstIntegral
    simp_rw [hin]
    exact integral_integral_swap (f := fun (v : Fin 3 → ℝ) (x : X) =>
      ∫ t : ℝ, g x (Fin.cons t v : Fin 4 → ℝ)) h2

/-- **The two integrability conditions from uniform `Good` bounds**, for a jointly measurable
family and a finite measure. -/
theorem integrable_of_good_param [IsFiniteMeasure ν] (g : X → (Fin 4 → ℝ) → ℂ)
    (hgm : Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ => g q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ))
    {C : ℝ} {G : (Fin 3 → ℝ) → ℝ} (hg : ∀ᵐ x ∂ν, Good (g x) C G) :
    (∀ v : Fin 3 → ℝ, Integrable (fun q : ℝ × X => g q.2 (Fin.cons q.1 v : Fin 4 → ℝ))
      ((volume : Measure ℝ).prod ν)) ∧
    Integrable (fun q : (Fin 3 → ℝ) × X => ∫ t : ℝ, g q.2 (Fin.cons t q.1 : Fin 4 → ℝ))
      ((volume : Measure (Fin 3 → ℝ)).prod ν) := by
  constructor
  · intro v
    have hm : Measurable fun q : ℝ × X => g q.2 (Fin.cons q.1 v : Fin 4 → ℝ) :=
      hgm.comp (by fun_prop : Measurable fun q : ℝ × X => (((v, q.2), q.1) :
        ((Fin 3 → ℝ) × X) × ℝ))
    refine Integrable.mono' (g := fun q : ℝ × X => G v * (1 + q.1 ^ 2)⁻¹ * 1)
      ((integrable_inv_one_add_sq.const_mul (G v)).mul_prod (integrable_const (1 : ℝ)))
      hm.aestronglyMeasurable ?_
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := ν)).ae hg
    filter_upwards [h2] with q hq
    rw [mul_one]
    exact hq.2 v q.1
  · have hm : StronglyMeasurable fun q : (Fin 3 → ℝ) × X =>
        ∫ t : ℝ, g q.2 (Fin.cons t q.1 : Fin 4 → ℝ) :=
      hgm.stronglyMeasurable.integral_prod_right'
    refine Integrable.mono' (g := fun q : (Fin 3 → ℝ) × X => C * (1 + ‖q.1‖) ^ (-(5 : ℝ)) * 1)
      ((integrable_one_add_norm_five.const_mul C).mul_prod (integrable_const (1 : ℝ)))
      hm.aestronglyMeasurable ?_
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin 3 → ℝ)))
      (ν := ν)).ae hg
    filter_upwards [h2] with q hq
    rw [mul_one]
    exact hq.1.2 q.1

/-- **The exchange from uniform `Good` bounds.** -/
theorem efi_integral_eq_of_good [IsFiniteMeasure ν] (g : X → (Fin 4 → ℝ) → ℂ)
    (hgm : Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ => g q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ))
    {C : ℝ} {G : (Fin 3 → ℝ) → ℝ} (hg : ∀ᵐ x ∂ν, Good (g x) C G) :
    EFInt (fun ℓ => ∫ x, g x ℓ ∂ν) ∧
      energyFirstIntegral (fun ℓ => ∫ x, g x ℓ ∂ν) = ∫ x, energyFirstIntegral (g x) ∂ν := by
  obtain ⟨h1, h2⟩ := integrable_of_good_param g hgm hg
  exact efi_integral_swap g h1 h2

/-- The parameter integrand `x ↦ ∫_D g x` is strongly measurable and bounded by `C ∫ (1+‖v‖)⁻⁵`. -/
theorem aestronglyMeasurable_efi_param [IsFiniteMeasure ν] (g : X → (Fin 4 → ℝ) → ℂ)
    (hgm : Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ => g q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ))
    {C : ℝ} {G : (Fin 3 → ℝ) → ℝ} (hg : ∀ᵐ x ∂ν, Good (g x) C G) :
    AEStronglyMeasurable (fun x => energyFirstIntegral (g x)) ν := by
  obtain ⟨-, h2⟩ := integrable_of_good_param g hgm hg
  exact h2.integral_prod_right.aestronglyMeasurable

/-- **Dominated convergence in the spectral parameters**: a family `g i` that is `Good` with a
constant `C` independent of `i` (eventually), whose energy-first integrals converge for almost
every parameter. -/
theorem tendsto_integral_efi_of_good [IsFiniteMeasure ν] {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] (g : ι → X → (Fin 4 → ℝ) → ℂ) (F : X → ℂ) {C : ℝ}
    (hgm : ∀ᶠ i in l, Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ =>
      g i q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ))
    (hg : ∀ᶠ i in l, ∃ G : (Fin 3 → ℝ) → ℝ, ∀ᵐ x ∂ν, Good (g i x) C G)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun i => energyFirstIntegral (g i x)) l (𝓝 (F x))) :
    Tendsto (fun i => ∫ x, energyFirstIntegral (g i x) ∂ν) l (𝓝 (∫ x, F x ∂ν)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C * I5) ?_ ?_
    (integrable_const _) hlim
  · filter_upwards [hgm, hg] with i hm ⟨G, hG⟩
    exact aestronglyMeasurable_efi_param (g i) hm hG
  · filter_upwards [hg] with i ⟨G, hG⟩
    filter_upwards [hG] with x hx
    exact hx.1.norm_efi_le

/-- The parameter integrand `x ↦ ∫_D g x` is strongly measurable for a jointly measurable family
(no integrability needed). -/
theorem stronglyMeasurable_efi_param (g : X → (Fin 4 → ℝ) → ℂ)
    (hgm : Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ => g q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ)) :
    StronglyMeasurable (fun x => energyFirstIntegral (g x)) := by
  have hH : Measurable fun q : (X × (Fin 3 → ℝ)) × ℝ => g q.1.1 (Fin.cons q.2 q.1.2 : Fin 4 → ℝ) :=
    hgm.comp (by fun_prop : Measurable fun q : (X × (Fin 3 → ℝ)) × ℝ =>
      (((q.1.2, q.1.1), q.2) : ((Fin 3 → ℝ) × X) × ℝ))
  have h1 : StronglyMeasurable fun q : X × (Fin 3 → ℝ) =>
      ∫ t : ℝ, g q.1 (Fin.cons t q.2 : Fin 4 → ℝ) :=
    hH.stronglyMeasurable.integral_prod_right'
  exact h1.integral_prod_right'

/-- **The limit of the parameter integrands is integrable**, under the hypotheses of dominated
convergence. -/
theorem integrable_of_tendsto_efi_of_good [IsFiniteMeasure ν] {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] [l.NeBot] (g : ι → X → (Fin 4 → ℝ) → ℂ) (F : X → ℂ) {C : ℝ}
    (hgm : ∀ i, Measurable fun q : ((Fin 3 → ℝ) × X) × ℝ =>
      g i q.1.2 (Fin.cons q.2 q.1.1 : Fin 4 → ℝ))
    (hg : ∀ᶠ i in l, ∃ G : (Fin 3 → ℝ) → ℝ, ∀ᵐ x ∂ν, Good (g i x) C G)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun i => energyFirstIntegral (g i x)) l (𝓝 (F x))) :
    Integrable F ν := by
  have hmeas : AEStronglyMeasurable F ν :=
    aestronglyMeasurable_of_tendsto_ae l
      (fun i => (stronglyMeasurable_efi_param (g i) (hgm i)).aestronglyMeasurable) hlim
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually hg)
  have hae : ∀ᵐ x ∂ν, ∀ n, N ≤ n → ‖energyFirstIntegral (g (u n) x)‖ ≤ C * I5 := by
    rw [ae_all_iff]
    intro n
    by_cases hn : N ≤ n
    · obtain ⟨G, hG⟩ := hN n hn
      filter_upwards [hG] with x hx _ using hx.1.norm_efi_le
    · exact Eventually.of_forall fun x h => absurd h hn
  refine Integrable.mono' (integrable_const (C * I5)) hmeas ?_
  filter_upwards [hae, hlim] with x h1 h2
  exact le_of_tendsto (h2.comp hu).norm (eventually_atTop.2 ⟨N, h1⟩)

end QED.TwoLoop.VPHalfAtGen

end
