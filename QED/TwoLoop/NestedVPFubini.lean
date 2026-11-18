/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral
public import QED.Frozen.TwoLoop.JointEnergyFirstIntegrable
public import QED.Frozen.OneLoop.EnergyFirstIntegral
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Nested equals joint: the Fubini step

Part of obligation O2-8 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3). The joint energy-first
integral (T₉) of two loop momenta integrates both energies first and then all six spatial
components,
`∫ d³v₁ d³v₂ (∫ dt₁ dt₂ F)`.
The nested form applies the one-loop energy-first integral (D) twice, the loop momentum `ℓ 0`
innermost:
`∫ d³v₂ ∫ dt₂ (∫ d³v₁ ∫ dt₁ F)`.

* `QED.TwoLoop.NestedVP.jointEnergyFirstIntegral_eq_nested`: the two agree when both stages of the
  joint prescription are integrable (the frozen `jointEnergyFirstIntegrable`, the form in which
  O2-7 states well-definedness) and, for almost every `v₂`, the energy integral over `t₁` is
  integrable jointly in `(t₂, v₁)`.

The proof uses three Fubini steps, each on signed integrals that are already known to be
integrable: `(t₁, t₂)` at fixed spatial momenta (the first stage of the joint prescription),
`(v₁, v₂)` (its second stage), and `(t₂, v₁)` at fixed `v₂` (the extra hypothesis). The energy
`t₁` is always integrated first and never exchanged: Tonelli fails on energies × space (section
4.3), and no absolute integrability over the energy `t₁` together with any spatial component is
used.
-/

public section

open MeasureTheory

namespace QED.TwoLoop.NestedVP

/-- An integral over `Fin 2 → α` is an integral over `α × α`. -/
theorem integral_finTwo {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    (g : (Fin 2 → α) → ℂ) : ∫ x, g x = ∫ p : α × α, g ![p.1, p.2] := by
  have h := ((volume_preserving_finTwoArrow α).symm).integral_comp'
    (g := g)
  rw [← h]
  rfl

/-- Integrability over `Fin 2 → α` is integrability over `α × α`. -/
theorem integrable_finTwo_iff {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    (g : (Fin 2 → α) → ℂ) : Integrable g ↔ Integrable fun p : α × α => g ![p.1, p.2] :=
  (((volume_preserving_finTwoArrow α).symm).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).symm

/-- The family of two loop momenta with energies `t₁, t₂` and spatial momenta `w₁, w₂`. -/
theorem cons_finTwo (t₁ t₂ : ℝ) (w₁ w₂ : Fin 3 → ℝ) :
    (fun s => (Fin.cons (![t₁, t₂] s) (![w₁, w₂] s) : Fin 4 → ℝ)) =
      ![(Fin.cons t₁ w₁ : Fin 4 → ℝ), Fin.cons t₂ w₂] := by
  funext s
  fin_cases s <;> rfl

/-- **Nested equals joint, the Fubini step** (O2-8). If both stages of the joint energy-first
integral (T₉) of `F` are integrable, and for almost every spatial momentum `v₂` of the second loop
the energy integral over `t₁` is integrable in `(t₂, v₁)`, then the joint integral is the
energy-first integral (D) in `ℓ 1` of the energy-first integral (D) in `ℓ 0`. -/
theorem jointEnergyFirstIntegral_eq_nested (F : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (hF : jointEnergyFirstIntegrable 2 F)
    (hG : ∀ᵐ w₂ : Fin 3 → ℝ, Integrable fun p : ℝ × (Fin 3 → ℝ) =>
      ∫ t₁ : ℝ, F ![Fin.cons t₁ p.2, Fin.cons p.1 w₂]) :
    jointEnergyFirstIntegral 2 F =
      QED.OneLoop.energyFirstIntegral fun k =>
        QED.OneLoop.energyFirstIntegral fun q => F ![q, k] := by
  obtain ⟨hF₁, hF₂⟩ := hF
  -- the energies: `(t₁, t₂)` at fixed spatial momenta
  have hin : ∀ w₁ w₂ : Fin 3 → ℝ,
      ∫ t : Fin 2 → ℝ, F (fun s => (Fin.cons (t s) (![w₁, w₂] s) : Fin 4 → ℝ)) =
        ∫ t₂ : ℝ, ∫ t₁ : ℝ, F ![Fin.cons t₁ w₁, Fin.cons t₂ w₂] := by
    intro w₁ w₂
    have hint := (integrable_finTwo_iff _).mp (hF₁ ![w₁, w₂])
    simp only [cons_finTwo] at hint
    rw [integral_finTwo]
    simp only [cons_finTwo]
    exact integral_prod_symm (fun p : ℝ × ℝ => F ![Fin.cons p.1 w₁, Fin.cons p.2 w₂]) hint
  -- the spatial momenta: `(v₁, v₂)`
  have hout := (integrable_finTwo_iff _).mp hF₂
  simp only [hin] at hout
  unfold jointEnergyFirstIntegral QED.OneLoop.energyFirstIntegral
  rw [integral_finTwo]
  simp only [hin]
  refine (integral_prod_symm _ hout).trans ?_
  -- `(t₂, v₁)` at fixed `v₂`
  refine integral_congr_ae (hG.mono fun w₂ hw₂ => ?_)
  exact integral_integral_swap (f := fun (w₁ : Fin 3 → ℝ) (t₂ : ℝ) =>
    ∫ t₁ : ℝ, F ![Fin.cons t₁ w₁, Fin.cons t₂ w₂])
    hw₂.swap

end QED.TwoLoop.NestedVP

end
