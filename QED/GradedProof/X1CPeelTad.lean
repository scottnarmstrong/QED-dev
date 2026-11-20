/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelDefs
public import QED.GradedProof.X1CCountPeelIn
public import QED.Frozen.Graded.ConnectedPart
public import QED.TwoLoop.RelabelInvariance

/-!
# (X₁) piece C: tadpole removal

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (the graph theory of the peels). A connected `(1,1)`
contraction with attached externals that is not tadpole-free (`PeelTadFree`) has a photon bridge
one side of which carries no external, so its value vanishes
(`contractionValue_eq_zero_of_isBridge`) when the external momenta are conserved. Hence:

* `peelTad_countSum_eq_zero`: a graded sum of a weight vanishing on the selection is `0`;
* **`peelTad_connectedPart`**: `connectedPart 1 1 K = selectedPart peelSelG K` for conserved
  external momenta, by splitting the connected part (`countSum_split`) along `PeelTadFree`;
* **`peelTad_h0`**: the hypothesis `h0` of `countDyson_dysonFive_t9` for `SelG := peelSelG`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open Finset
open QED.WickModel (Params Contraction VerticesConnected ExternalsAttached fermionSign
  externalMomentum)
open QED.Graded

/-- A graded sum of a weight that vanishes on the selection is `0`. -/
theorem peelTad_countSum_eq_zero {nf nA : ℕ} (Sel : CountSel nf nA) (W : CountWt nf nA) (K : ℕ)
    (h : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (g : Grading κ),
      Sel C g → W C g = 0) : countSum Sel W K = 0 := by
  refine sum_eq_zero fun N _ => mul_eq_zero_of_right _ (sum_eq_zero fun κ _ =>
    sum_eq_zero fun g _ => sum_eq_zero fun C hC => h C g (mem_countSel.1 hC))

/-- The value of an attached connected contraction that is not tadpole-free vanishes. -/
theorem peelTad_value_eq_zero (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 nA κ) (gr : Grading κ) (hA : ExternalsAttached C)
    (hV : VerticesConnected C) (hT : ¬ PeelTadFree C) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (hs : ∑ i, pIn i + ∑ j, kIn j - ∑ i, pOut i = 0)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue P Φ D C gr pOut pIn kIn αOut βIn μ = 0 := by
  simp only [PeelTadFree, PeelExtAt, not_forall, not_or, not_exists, not_and] at hT
  obtain ⟨g, hb, w, hw, hfo, hfi, hph⟩ := hT
  exact contractionValue_eq_zero_of_isBridge P Φ D gr hb hw (fun s h => hfo s h)
    (fun s h => hfi s h) (fun j a h => hph j a h) hV pOut pIn kIn
    (by rw [QED.TwoLoop.Relabel.sum_externalMomentum hA, hs]) αOut βIn μ

/-- **Tadpole removal**: for conserved external momenta the connected `(1,1)` part is the
selected part over the tadpole-free contractions. -/
theorem peelTad_connectedPart (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (nA K : ℕ) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (hs : ∑ i, pIn i + ∑ j, kIn j - ∑ i, pOut i = 0)
    (αOut βIn : Fin 1 → Fin 4) (μ : Fin nA → Fin 4) :
    connectedPart P Φ D 1 nA K pOut pIn kIn αOut βIn μ =
      selectedPart P Φ D 1 nA (fun C _ => ExternalsAttached C ∧ VerticesConnected C ∧
        PeelTadFree C) K pOut pIn kIn αOut βIn μ := by
  simp only [connectedPart, selectedPart_eq_countSum]
  rw [countSum_split _ (fun C _ => PeelTadFree C), peelTad_countSum_eq_zero, zero_add]
  · simp only [and_assoc]
  · rintro N κ C g ⟨⟨hA, hV⟩, hT⟩
    rw [peelTad_value_eq_zero P Φ D C g hA hV hT pOut pIn kIn hs, mul_zero]

/-- **`h0` of `countDyson_dysonFive_t9`** for `SelG := peelSelG`. -/
theorem peelTad_h0 (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (r' r : Fin 4 → ℝ) (α β μ : Fin 4) :
    connectedPart P Φ D 1 1 5 ![r'] ![r] ![r' - r] ![α] ![β] ![μ] =
      selectedPart P Φ D 1 1 peelSelG 5 ![r'] ![r] ![r' - r] ![α] ![β] ![μ] :=
  peelTad_connectedPart P Φ D 1 5 ![r'] ![r] ![r' - r] (by simp) ![α] ![β] ![μ]

end QED.GradedProof.X1C

end
