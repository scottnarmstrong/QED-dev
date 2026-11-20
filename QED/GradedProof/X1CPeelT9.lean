/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CT9Glue
import QED.LeptonProof.EmbedOneZero
import QED.WickModel.TwoPointClassificationTree

/-!
# (X₁) piece C: the (T₉′) inputs of the peels at every graded order up to `5`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5 (counting). The value-level peels (`selectedPart_peelIn` and
its mirrors) take (T₉′) for *every* selected piece of graded order at most `K`, not only for the
pieces of a glue of graded order `5`. For `K ≤ 5`:

* `peel_hT₁`: an attached connected `(1,1)` contraction of graded order `≤ 5` (graded order
  `≤ 3` from `t9_vertex_le_three`, `5` from `t9_vertex_five`; graded order `4` is impossible:
  `peel_odd_gradedOrder`, one external photon makes the order odd).
* `peel_hT₂`: a 1PI `(1,0)` contraction of graded order `≤ 5` (`t9_selfEnergy`; graded order `5`
  is impossible, the order is even).
* `peel_hTP`: a 1PI `(0,2)` contraction of graded order `≤ 5` (`t9_vacuumPolarization`).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction loopCount lineMomentum₂ IsOnePI VerticesConnected
  ExternalsAttached)
open QED.Graded

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The total order of a contracted kind sequence has the parity of the number of external
photons. -/
theorem peel_two_dvd_sum_order_add (C : Contraction nf nA κ) :
    2 ∣ ∑ t, (κ t).order + nA := by
  by_contra hodd
  have hmod : (∑ t, (κ t).photonSlots) % 2 = (∑ t, (κ t).order) % 2 := by
    rw [Finset.sum_nat_mod, Finset.sum_nat_mod Finset.univ 2 (fun t => (κ t).order)]
    simp only [QED.Lepton.Proof.photonSlots_mod_two]
  have hE : IsEmpty (Contraction nf nA κ) := by
    apply QED.WickModel.isEmpty_contraction_of_not_two_dvd
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    omega
  exact hE.false C

/-- **A contraction with one external photon has odd graded order.** -/
theorem peel_odd_gradedOrder (C : Contraction nf 1 κ) (g : Grading κ) :
    ¬ 2 ∣ gradedOrder κ g := by
  have hd := peel_two_dvd_sum_order_add C
  have h2 : ∑ t : CtVertex κ, 2 * g t = 2 * ∑ t, g t := (Finset.mul_sum _ _ _).symm
  unfold gradedOrder
  rw [h2]
  omega

variable {P : Params} {F : Type} [Fintype F] [DecidableEq F] {Φ : Lepton.Flavors F}
  {D : Counterterms F} {rep : F → F} {m₀ : ℝ}

/-- **(T₉′) of an attached connected vertex piece of graded order at most `5`**, in the form of
`hT₁` of `selectedPart_peelIn`. -/
theorem peel_hT₁ (H : T9Hyps P Φ D rep m₀) (C : Contraction 1 1 κ) (hA : ExternalsAttached C)
    (hV : VerticesConnected C) (g : Grading κ) (hg : gradedOrder κ g ≤ 5) {r' r q : Fin 4 → ℝ}
    (hmom : r' = r + q) (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![r] ![q]
        (lineMomentum₂ C ![r'] ![r] ![q] ℓ) αOut βIn μ := by
  have hodd := peel_odd_gradedOrder C g
  rcases (by omega : gradedOrder κ g ≤ 3 ∨ gradedOrder κ g = 5) with h | h
  · exact t9_vertex_le_three P Φ D H.hε rep H.hrep H.hPV₁ H.hPV₂ H.hD C hA hV g h r' r q
      αOut βIn μ
  · exact t9_vertex_five P Φ D H.hε rep H.hrep H.hPV₁ H.hPV₂ H.hD C hA hV g h hmom αOut βIn μ

/-- **(T₉′) of a 1PI self-energy piece of graded order at most `5`**, in the form of `hT₂` of
`selectedPart_peelIn`. -/
theorem peel_hT₂ (H : T9Hyps P Φ D rep m₀) (C : Contraction 1 0 κ) (hC : IsOnePI C)
    (g : Grading κ) (hg : gradedOrder κ g ≤ 5) (p : Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![p] ![]
        (lineMomentum₂ C ![p] ![p] ![] ℓ) αOut βIn ![] := by
  obtain ⟨-, hd⟩ := t9_two_le_gradedOrder C (by norm_num)
    (t9_pos_of_isOnePI C hC (Or.inl one_pos)) g
  exact t9_selfEnergy H C hC g (by omega) p αOut βIn

/-- **(T₉′) of a 1PI vacuum-polarization piece of graded order at most `5`**. -/
theorem peel_hTP (H : T9Hyps P Φ D rep m₀) (C : Contraction 0 2 κ) (hC : IsOnePI C)
    (g : Grading κ) (hg : gradedOrder κ g ≤ 5) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![] ![k, -k]
        (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![] ![μ, ν] := by
  obtain ⟨-, hd⟩ := t9_two_le_gradedOrder C (by norm_num)
    (t9_pos_of_isOnePI C hC (Or.inr two_pos)) g
  exact t9_vacuumPolarization H C hC g (by omega) k μ ν

end QED.GradedProof.X1C

end
