/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Nested equals joint at three loops: the Fubini step

Helper level, Phase 5 Stage 1a, the measure-theoretic part of obligation O3-6. The joint
energy-first integral (T₉) of three loop momenta integrates the three energies first and then
the nine spatial components,
`∫ d³v₁ d³v₂ d³w (∫ dt₁ dt₂ dt₃ F)`.
The nested form applies the one-loop energy-first integral (D) three times, `ℓ 0 = q₁`
innermost (the first bubble), then `ℓ 1 = q₂` (the second bubble), then `ℓ 2 = k` (the photon):
`∫ d³w ∫ dt₃ (∫ d³v₂ ∫ dt₂ (∫ d³v₁ ∫ dt₁ F))`.

* `QED.ChainProof.jointEnergyFirstIntegral_three_eq_nested`: the two agree when both stages of the
  joint prescription are integrable (the frozen `jointEnergyFirstIntegrable 3`, the form of the
  integrability companion (HC₀)) and two Fubini conditions hold:
  - `hK`: for almost every spatial photon momentum `w`, the energy integral over `t₁, t₂` is
    integrable jointly in the photon energy `t₃` and the two spatial loop momenta `(v₁, v₂)`;
  - `hQ`: for almost every `w`, `t₃` and `v₂`, the energy integral over `t₁` is integrable jointly
    in `(t₂, v₁)`.

* `QED.ChainProof.jointEnergyFirstIntegral_three_eq_nested_innerFirst`: the same conclusion under
  conditions adapted to the two-loop bounds. The first bubble is integrated completely at fixed
  `(t₂, t₃, v₂, w)` (`hA`), and what remains is a two-loop integrand whose outer factor carries the
  first bubble's closed form `Π_ε(k)` (logarithmic in `k`), with the two-loop Fubini condition
  (`hB`). The direct route needs `∫ d³v |g(k, v)|` of each inner energy integral `g` to grow slower
  than `(1 + |k⁰|)^{13/2}` against the `(1 + |k⁰|)⁻¹⁴` decay of the outer factor (two electron and
  three regulated photon propagators); the proved two-loop bound
  `QED.TwoLoop.NestedVPFubiniBound.exists_norm_spatialG_le_poly` gives only the exponent `17/2`.
  On the inner-first route that bound enters once, against `(1 + |k⁰|)⁻¹⁴` times a logarithm.

As at two loops (`QED.TwoLoop.NestedVP.jointEnergyFirstIntegral_eq_nested`), the energy `t₁` is
always integrated first and never exchanged with a spatial component; every Fubini step is on a
signed integral already known to be integrable. The conditions `hK`, `hQ` are where the analytic
content of O3-6 lies (bounds on the inner one-loop energy integrals, polynomial in the photon
momentum, against the decay of the outer factor); they are **not** proved here.
-/

@[expose] public section

open MeasureTheory

namespace QED.ChainProof

section Fin3

variable {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]

/-- The measurable equivalence `α × (α × α) ≃ (Fin 3 → α)`, `(a, (b, c)) ↦ ![b, c, a]`. -/
noncomputable def finThreeEquiv (α : Type*) [MeasurableSpace α] :
    α × (α × α) ≃ᵐ (Fin 3 → α) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) MeasurableEquiv.finTwoArrow.symm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => α) 2).symm

omit [SigmaFinite (volume : Measure α)] in
theorem finThreeEquiv_apply (p : α × (α × α)) : finThreeEquiv α p = ![p.2.1, p.2.2, p.1] := by
  funext i
  fin_cases i <;> rfl

theorem measurePreserving_finThreeEquiv : MeasurePreserving (finThreeEquiv α) := by
  refine MeasurePreserving.trans (μb := (volume : Measure α).prod volume) ?_ ?_
  · exact (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow α).symm
  · exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => α) 2).symm

/-- An integral over `Fin 3 → α` is an integral over `α × (α × α)`. -/
theorem integral_finThree (g : (Fin 3 → α) → ℂ) :
    ∫ x, g x = ∫ p : α × (α × α), g ![p.2.1, p.2.2, p.1] := by
  rw [← measurePreserving_finThreeEquiv.integral_comp' (g := g)]
  simp only [finThreeEquiv_apply]

/-- Integrability over `Fin 3 → α` is integrability over `α × (α × α)`. -/
theorem integrable_finThree_iff (g : (Fin 3 → α) → ℂ) :
    Integrable g ↔ Integrable fun p : α × (α × α) => g ![p.2.1, p.2.2, p.1] := by
  rw [← measurePreserving_finThreeEquiv.integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp only [Function.comp_def, finThreeEquiv_apply]

end Fin3

/-- The family of three loop momenta with energies `t₁, t₂, t₃` and spatial momenta
`w₁, w₂, w₃`. -/
theorem cons_finThree (t₁ t₂ t₃ : ℝ) (w₁ w₂ w₃ : Fin 3 → ℝ) :
    (fun s => (Fin.cons (![t₁, t₂, t₃] s) (![w₁, w₂, w₃] s) : Fin 4 → ℝ)) =
      ![(Fin.cons t₁ w₁ : Fin 4 → ℝ), Fin.cons t₂ w₂, Fin.cons t₃ w₃] := by
  funext s
  fin_cases s <;> rfl

/-- **Nested equals joint at three loops, the Fubini step** (O3-6). If both stages of the joint
energy-first integral (T₉) of `F` are integrable and the Fubini conditions `hK`, `hQ` hold, then
the joint integral is the energy-first integral (D) in `ℓ 2` of the energy-first integral in
`ℓ 1` of the energy-first integral in `ℓ 0`. -/
theorem jointEnergyFirstIntegral_three_eq_nested (F : (Fin 3 → Fin 4 → ℝ) → ℂ)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 F)
    (hK : ∀ᵐ w : Fin 3 → ℝ, Integrable fun p : ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) =>
      ∫ t₂ : ℝ, ∫ t₁ : ℝ, F ![Fin.cons t₁ p.2.1, Fin.cons t₂ p.2.2, Fin.cons p.1 w])
    (hQ : ∀ᵐ w : Fin 3 → ℝ, ∀ᵐ t₃ : ℝ, ∀ᵐ w₂ : Fin 3 → ℝ,
      Integrable fun p : ℝ × (Fin 3 → ℝ) =>
        ∫ t₁ : ℝ, F ![Fin.cons t₁ p.2, Fin.cons p.1 w₂, Fin.cons t₃ w]) :
    QED.TwoLoop.jointEnergyFirstIntegral 3 F =
      QED.OneLoop.energyFirstIntegral fun k =>
        QED.OneLoop.energyFirstIntegral fun q₂ =>
          QED.OneLoop.energyFirstIntegral fun q₁ => F ![q₁, q₂, k] := by
  obtain ⟨hF₁, hF₂⟩ := hF
  -- the energies `(t₁, t₂, t₃)` at fixed spatial momenta
  have hin : ∀ w₁ w₂ w₃ : Fin 3 → ℝ,
      ∫ t : Fin 3 → ℝ, F (fun s => (Fin.cons (t s) (![w₁, w₂, w₃] s) : Fin 4 → ℝ)) =
        ∫ t₃ : ℝ, ∫ t₂ : ℝ, ∫ t₁ : ℝ, F ![Fin.cons t₁ w₁, Fin.cons t₂ w₂, Fin.cons t₃ w₃] := by
    intro w₁ w₂ w₃
    have hint := (integrable_finThree_iff _).mp (hF₁ ![w₁, w₂, w₃])
    simp only [cons_finThree] at hint
    rw [integral_finThree]
    simp only [cons_finThree]
    refine (integral_prod _ hint).trans ?_
    refine integral_congr_ae (hint.prod_right_ae.mono fun t₃ ht₃ => ?_)
    exact integral_prod_symm
      (fun q : ℝ × ℝ => F ![Fin.cons q.1 w₁, Fin.cons q.2 w₂, Fin.cons t₃ w₃]) ht₃
  -- the spatial momenta `(v₁, v₂, w)`
  have hout := (integrable_finThree_iff _).mp hF₂
  simp only [hin] at hout
  unfold QED.TwoLoop.jointEnergyFirstIntegral QED.OneLoop.energyFirstIntegral
  rw [integral_finThree]
  simp only [hin]
  refine (integral_prod _ hout).trans ?_
  refine integral_congr_ae ((hK.and hQ).mono fun w hw => ?_)
  obtain ⟨hKw, hQw⟩ := hw
  -- `t₃` out of `(v₁, v₂)` at fixed `w`
  refine (integral_integral_swap (f := fun (v : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (t₃ : ℝ) =>
      ∫ t₂ : ℝ, ∫ t₁ : ℝ, F ![Fin.cons t₁ v.1, Fin.cons t₂ v.2, Fin.cons t₃ w]) hKw.swap).trans ?_
  refine integral_congr_ae ((hKw.prod_right_ae.and hQw).mono fun t₃ ht₃ => ?_)
  obtain ⟨hv, hQt⟩ := ht₃
  -- `(v₁, v₂)` as `v₂` outside `v₁`
  refine (integral_prod_symm _ hv).trans ?_
  -- `t₂` out of `v₁` at fixed `v₂`
  refine integral_congr_ae (hQt.mono fun w₂ hw₂ => ?_)
  exact integral_integral_swap (f := fun (w₁ : Fin 3 → ℝ) (t₂ : ℝ) =>
    ∫ t₁ : ℝ, F ![Fin.cons t₁ w₁, Fin.cons t₂ w₂, Fin.cons t₃ w]) hw₂.swap

/-- **Nested equals joint at three loops, inner bubble first** (O3-6, the route that reuses the
two-loop bounds). If both stages of the joint energy-first integral of `F` are integrable and
* `hA`: for almost every `w` and `v₂`, the energy integral over `t₁` is integrable jointly in
  `((t₂, t₃), v₁)` (the first bubble is then integrated completely, at fixed `(t₂, t₃, v₂, w)`);
* `hB`: for almost every `w`, the function `(t₃, v₂) ↦ ∫ dt₂ ∫ d³v₁ ∫ dt₁ F` is integrable (the
  Fubini condition of the two-loop nested form for the integrand with the first bubble done),

then the joint integral is the threefold nested energy-first integral. With the first bubble in
closed form (`QED.TwoLoop.VPHalfAt.energyFirstIntegral_vacuumPolarizationIntegrand_eq`, of
logarithmic growth in `k`), `hB` is the two-loop condition `hG` of
`QED.TwoLoop.NestedVPFubiniBound` with the outer factor multiplied by `Π_ε(k)`, and `hA` needs only
a bound on `∫ dt₂ |A(k, q₂)|` for the unintegrated second bubble, polynomial in `k`. -/
theorem jointEnergyFirstIntegral_three_eq_nested_innerFirst (F : (Fin 3 → Fin 4 → ℝ) → ℂ)
    (hF : QED.TwoLoop.jointEnergyFirstIntegrable 3 F)
    (hA : ∀ᵐ w : Fin 3 → ℝ, ∀ᵐ w₂ : Fin 3 → ℝ,
      Integrable fun p : (ℝ × ℝ) × (Fin 3 → ℝ) =>
        ∫ t₁ : ℝ, F ![Fin.cons t₁ p.2, Fin.cons p.1.1 w₂, Fin.cons p.1.2 w])
    (hB : ∀ᵐ w : Fin 3 → ℝ, Integrable fun p : ℝ × (Fin 3 → ℝ) =>
      ∫ t₂ : ℝ, ∫ w₁ : Fin 3 → ℝ, ∫ t₁ : ℝ,
        F ![Fin.cons t₁ w₁, Fin.cons t₂ p.2, Fin.cons p.1 w]) :
    QED.TwoLoop.jointEnergyFirstIntegral 3 F =
      QED.OneLoop.energyFirstIntegral fun k =>
        QED.OneLoop.energyFirstIntegral fun q₂ =>
          QED.OneLoop.energyFirstIntegral fun q₁ => F ![q₁, q₂, k] := by
  obtain ⟨hF₁, hF₂⟩ := hF
  have hin : ∀ w₁ w₂ w₃ : Fin 3 → ℝ,
      ∫ t : Fin 3 → ℝ, F (fun s => (Fin.cons (t s) (![w₁, w₂, w₃] s) : Fin 4 → ℝ)) =
        ∫ t₃ : ℝ, ∫ t₂ : ℝ, ∫ t₁ : ℝ, F ![Fin.cons t₁ w₁, Fin.cons t₂ w₂, Fin.cons t₃ w₃] := by
    intro w₁ w₂ w₃
    have hint := (integrable_finThree_iff _).mp (hF₁ ![w₁, w₂, w₃])
    simp only [cons_finThree] at hint
    rw [integral_finThree]
    simp only [cons_finThree]
    refine (integral_prod _ hint).trans ?_
    refine integral_congr_ae (hint.prod_right_ae.mono fun t₃ ht₃ => ?_)
    exact integral_prod_symm
      (fun q : ℝ × ℝ => F ![Fin.cons q.1 w₁, Fin.cons q.2 w₂, Fin.cons t₃ w₃]) ht₃
  have hout := (integrable_finThree_iff _).mp hF₂
  simp only [hin] at hout
  unfold QED.TwoLoop.jointEnergyFirstIntegral QED.OneLoop.energyFirstIntegral
  rw [integral_finThree]
  simp only [hin]
  refine (integral_prod _ hout).trans ?_
  refine integral_congr_ae (((hA.and hB).and hout.prod_right_ae).mono fun w hw => ?_)
  obtain ⟨⟨hAw, hBw⟩, hvw⟩ := hw
  -- `(v₁, v₂)` as `v₂` outside `v₁`
  refine (integral_prod_symm _ hvw).trans ?_
  -- the first bubble inside `(t₂, t₃)`, at fixed `v₂`
  have hstep : ∀ᵐ w₂ : Fin 3 → ℝ,
      (∫ w₁ : Fin 3 → ℝ, ∫ t₃ : ℝ, ∫ t₂ : ℝ, ∫ t₁ : ℝ,
        F ![Fin.cons t₁ w₁, Fin.cons t₂ w₂, Fin.cons t₃ w]) =
      ∫ t₃ : ℝ, ∫ t₂ : ℝ, ∫ w₁ : Fin 3 → ℝ, ∫ t₁ : ℝ,
        F ![Fin.cons t₁ w₁, Fin.cons t₂ w₂, Fin.cons t₃ w] := by
    refine hAw.mono fun w₂ hw₂ => ?_
    have h1 : (∫ w₁ : Fin 3 → ℝ, ∫ t₃ : ℝ, ∫ t₂ : ℝ, ∫ t₁ : ℝ,
          F ![Fin.cons t₁ w₁, Fin.cons t₂ w₂, Fin.cons t₃ w]) =
        ∫ w₁ : Fin 3 → ℝ, ∫ q : ℝ × ℝ, ∫ t₁ : ℝ,
          F ![Fin.cons t₁ w₁, Fin.cons q.1 w₂, Fin.cons q.2 w] := by
      refine integral_congr_ae (hw₂.prod_left_ae.mono fun w₁ hw₁ => ?_)
      exact (integral_prod_symm (fun q : ℝ × ℝ => ∫ t₁ : ℝ,
        F ![Fin.cons t₁ w₁, Fin.cons q.1 w₂, Fin.cons q.2 w]) hw₁).symm
    rw [h1]
    refine (integral_integral_swap (f := fun (w₁ : Fin 3 → ℝ) (q : ℝ × ℝ) => ∫ t₁ : ℝ,
      F ![Fin.cons t₁ w₁, Fin.cons q.1 w₂, Fin.cons q.2 w]) hw₂.swap).trans ?_
    exact integral_prod_symm (fun q : ℝ × ℝ => ∫ w₁ : Fin 3 → ℝ, ∫ t₁ : ℝ,
      F ![Fin.cons t₁ w₁, Fin.cons q.1 w₂, Fin.cons q.2 w]) hw₂.integral_prod_left
  refine (integral_congr_ae hstep).trans ?_
  -- `t₃` out of `v₂`
  exact integral_integral_swap (f := fun (w₂ : Fin 3 → ℝ) (t₃ : ℝ) =>
    ∫ t₂ : ℝ, ∫ w₁ : Fin 3 → ℝ, ∫ t₁ : ℝ, F ![Fin.cons t₁ w₁, Fin.cons t₂ w₂, Fin.cons t₃ w])
    hBw.swap

end QED.ChainProof

end
