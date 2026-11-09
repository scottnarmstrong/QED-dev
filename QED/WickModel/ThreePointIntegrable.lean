/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.ThreePointClassification
import QED.WickModel.ThreePointIntegrableLoops
import QED.WickModel.ThreePointIntegrableTadpole
import QED.WickModel.Compatibility
import QED.Wick.Classification

/-!
# Integrability of the one-loop contractions of the three-point function

For `ε > 0`, regulator fermions heavier than the electron and the Pauli–Villars conditions, the
loop integrand of every connected contraction with a loop line, with one external fermion pair
and one external photon of momentum `r' - r` at order at most `e³` (packet 6c-1, decision
D-30), is integrable in both stages of the energy-first prescription M1, for all momenta `r'`,
`r` and all indices.

The contractions are classified by their vertex sequence:

* no vertex: the externals are not attached;
* one vertex, or two vertices (a gauge vertex with a fermion or photon counterterm, the two
  gauge vertices having no contraction): the contraction is a tree and has no loop line;
* three gauge vertices: the vertex correction (the 1PI contractions), the self-energy loops on
  the electron legs, the vacuum polarization loop on the photon leg, and the tadpoles
  (`isNonOnePIShape_of`), each integrable by `QED.WickModel.ThreePointIntegrableLoops` and
  `QED.WickModel.ThreePointIntegrableTadpole`.

## Main statements

* `integrable_connected_threePoint`: the integrability of the loop integrands.
-/

@[expose] public section

open Complex MeasureTheory

namespace QED.WickModel

/-! ### Trees -/

/-- With one vertex and the externals attached there is no internal line, so no loop line. -/
theorem not_isLoopLine_of_fin_one {κ : Fin 1 → Wick.VertexKind} {C : Contraction 1 1 κ}
    (hext : ExternalsAttached C) (f : Line C) : ¬ IsLoopLine f := by
  intro _
  obtain ⟨t, ht⟩ : ∃ t, C.1.1 (.inl 0) = .inr t := by
    rcases h : C.1.1 (.inl 0) with i | t
    · exact absurd h (hext.1 0 i)
    · exact ⟨t, rfl⟩
  have hfv : ∀ x y : Wick.FermionVertex κ, x = y := fun x y =>
    Subtype.ext (Subsingleton.elim _ _)
  rcases f with f | g
  · obtain ⟨s, hs⟩ := f
    rcases h : C.1.1 (.inr s) with i | s'
    · simp [h] at hs
    · rw [hfv s' t, ← ht] at h
      exact Sum.inr_ne_inl (C.1.1.injective h)
  · obtain ⟨s, s', -, hkey⟩ := g
    have hκ0 : (κ 0).photonSlots ≤ 1 := by
      have := t.2
      rw [Subsingleton.elim t.1 0] at this
      revert this
      cases κ 0 <;> decide
    have hs : (κ s.1).photonSlots ≤ 1 := by
      rw [Subsingleton.elim s.1 0]
      exact hκ0
    have hs' : (κ s'.1).photonSlots ≤ 1 := by
      rw [Subsingleton.elim s'.1 0]
      exact hκ0
    have h1 := s.2.2
    have h2 := s'.2.2
    have h3 := s.1.2
    have h4 := s'.1.2
    simp only [Wick.photonKey] at hkey
    omega

/-- A gauge vertex and a fermion counterterm: the connected contraction is a chain whose single
internal line is a bridge, so there is no loop line. -/
theorem not_isLoopLine_of_fermionCt {κ : Fin 2 → Wick.VertexKind} {g h : Fin 2} (hgh : g ≠ h)
    (hκg : κ g = .gauge) (hκh : κ h = .fermionCt) {C : Contraction 1 1 κ}
    (hext : ExternalsAttached C) (hconn : VerticesConnected C) (f : Line C) :
    ¬ IsLoopLine f := by
  have hX := fv_cases_fermionCt hgh hκg hκh
  rcases isCtChain_of_connected hgh hκg hκh hext hconn with hC | hC
  · refine not_isLoopLine_of_forall_eq (hC.eq_inl_line hgh hκg hκh hX) ?_ f
    rw [hC.ends_line]
    exact hgh.symm
  · refine not_isLoopLine_of_forall_eq (hC.eq_inl_line hgh hκg hκh fun x => (hX x).symm) ?_ f
    rw [hC.ends_line]
    exact hgh

/-- A gauge vertex and a photon counterterm: the connected contraction has a single internal
line, a bridge, so there is no loop line. -/
theorem not_isLoopLine_of_photonCt {κ : Fin 2 → Wick.VertexKind} {g h : Fin 2} (hgh : g ≠ h)
    (hκg : κ g = .gauge) (hκh : κ h = .photonCt) {C : Contraction 1 1 κ}
    (hext : ExternalsAttached C) (hconn : VerticesConnected C) (f : Line C) :
    ¬ IsLoopLine f := by
  obtain ⟨j, hC⟩ := exists_isPhotonCtLeg hgh hκg hκh hext hconn
  refine not_isLoopLine_of_forall_eq (hC.eq_inr_photonLine hgh hκg hκh hext) ?_ f
  rcases hC.ends_photonLine hgh hκg hκh with h' | h' <;> rw [h']
  · exact hgh
  · exact hgh.symm

/-- Two vertices of total order at most `3`: a connected contraction has no loop line. -/
theorem not_isLoopLine_of_fin_two {κ : Fin 2 → Wick.VertexKind} (hκ : ∑ t, (κ t).order ≤ 3)
    {C : Contraction 1 1 κ} (hext : ExternalsAttached C) (hconn : VerticesConnected C)
    (f : Line C) : ¬ IsLoopLine f := by
  rcases fin_two_of_sum_order_le hκ with rfl | rfl | rfl | rfl | rfl
  · exact ((isEmpty_contraction_of_not_two_dvd (nf := 1) (by decide) :
      IsEmpty (Contraction 1 1 ![Wick.VertexKind.gauge, .gauge])).false C).elim
  · exact not_isLoopLine_of_fermionCt (g := 0) (h := 1) (by decide) rfl rfl hext hconn f
  · exact not_isLoopLine_of_fermionCt (g := 1) (h := 0) (by decide) rfl rfl hext hconn f
  · exact not_isLoopLine_of_photonCt (g := 0) (h := 1) (by decide) rfl rfl hext hconn f
  · exact not_isLoopLine_of_photonCt (g := 1) (h := 0) (by decide) rfl rfl hext hconn f

/-! ### The theorem -/

/-- **The loop integrands of the three-point function are integrable** (the first conjunct of
packet 6c-1's goal, decision D-30). For `m > 0`, regulator fermions heavier than the electron
and the Pauli–Villars conditions `1 + c₁ + c₂ = 0`, `m² + c₁ M₁² + c₂ M₂² = 0`, at every
`ε > 0`: the regulated amplitude of every connected contraction with attached externals and a
loop line, with one external fermion pair and one external photon of momentum `r' - r` at order
at most `3`, is integrable in the loop energy at every spatial loop momentum, and its energy
integral is integrable over the spatial loop momentum, for all momenta `r'`, `r` and all
indices. -/
theorem integrable_connected_threePoint (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) :
    ∀ ε > 0, ∀ (N : ℕ) (κ : Fin N → Wick.VertexKind), ∑ t, (κ t).order ≤ 3 →
      ∀ C : Contraction 1 1 κ, ExternalsAttached C → VerticesConnected C →
      (∃ f : Line C, IsLoopLine f) →
      ∀ (r' r : Fin 4 → ℝ) (α β μ : Fin 4),
        (∀ v : Fin 3 → ℝ, Integrable fun t : ℝ =>
          regulatedAmplitude { P with ε := ε } C ![r'] ![r] ![r' - r] (Fin.cons t v) ![α] ![β]
            ![μ]) ∧
        Integrable fun v : Fin 3 → ℝ => ∫ t : ℝ,
          regulatedAmplitude { P with ε := ε } C ![r'] ![r] ![r' - r] (Fin.cons t v) ![α] ![β]
            ![μ] := by
  intro ε hε N κ hκ C hext hconn hloop r' r α β μ
  obtain ⟨f, hf⟩ := hloop
  have hε' : 0 < ({ P with ε := ε } : Params).ε := hε
  change IntegrableEnergyFirst fun ℓ =>
    regulatedAmplitude { P with ε := ε } C ![r'] ![r] ![r' - r] ℓ ![α] ![β] ![μ]
  obtain rfl | rfl | rfl | rfl : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 := by
    have := le_three_of_sum_order_le hκ
    omega
  · exact absurd hext (not_externalsAttached_of_fin_zero C)
  · exact absurd hf (not_isLoopLine_of_fin_one hext f)
  · exact absurd hf (not_isLoopLine_of_fin_two hκ hext hconn f)
  · obtain rfl := Wick.eq_gauge3_of_sum_order_le hκ
    by_cases h1 : IsOnePI C
    · exact integrableEnergyFirst_of_isOnePI _ hε' h1 r' r α β μ
    · rcases isNonOnePIShape_of ⟨⟨hext, hconn⟩, h1⟩ with ⟨a, b, c, hC⟩ | ⟨a, b, c, hC⟩ |
        ⟨a, v, w, hC⟩ | ⟨a, b, c, u, hC⟩
      · exact hC.integrableEnergyFirst _ hε' r' r α β μ
      · exact hC.integrableEnergyFirst _ hε' r' r α β μ
      · exact hC.integrableEnergyFirst (P := { P with ε := ε }) hm hM₁ hM₂ hPV₁ hPV₂ hε' r' r
          α β μ
      · exact hC.integrableEnergyFirst_regulatedAmplitude (P := { P with ε := ε }) hm hM₁ hM₂
          hPV₁ hPV₂ hε' ![r'] ![r] ![r' - r] ![α] ![β] ![μ]

end QED.WickModel

end
