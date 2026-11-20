/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CT9Glue

/-!
# (X₁) piece C: (T₉′) of every piece of graded order at most `5`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C. The three peels (`selectedPart_peelIn`, `selectedPart_peelOut`,
`selectedPart_peelP`) at order `K ≤ 5` take (T₉′) for every vertex piece and every 1PI
self-energy or vacuum-polarization piece of graded order at most `K`. This file supplies them
from `T9Hyps`:

* `plumb_odd_gradedOrder`: a contraction with an odd number of external photons has odd graded
  order (photon-slot parity), so a `(1,1)` piece has graded order `1`, `3` or `5`;
* `plumb_t9_vertex`: an attached connected `(1,1)` piece of graded order `≤ 5`
  (`t9_vertex_le_three` at orders `≤ 3`, `t9_vertex_five` at order `5`);
* `plumb_t9_selfEnergy`, `plumb_t9_vacuumPolarization`: 1PI pieces of graded order `≤ 5` (order
  `5` is odd and does not occur, the rest is `t9_selfEnergy`, `t9_vacuumPolarization`).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction loopCount lineMomentum₂ IsOnePI VerticesConnected
  ExternalsAttached)
open QED.Graded

section Parity

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- With an odd number of external photons, the total order of a contracted kind sequence is
odd. -/
theorem plumb_odd_sum_order (C : Contraction nf nA κ) (h : ¬ 2 ∣ nA) :
    ¬ 2 ∣ ∑ t, (κ t).order := by
  intro hev
  have hmod : (∑ t, (κ t).photonSlots) % 2 = (∑ t, (κ t).order) % 2 := by
    rw [Finset.sum_nat_mod, Finset.sum_nat_mod Finset.univ 2 (fun t => (κ t).order)]
    simp only [QED.Lepton.Proof.photonSlots_mod_two]
  have hE : IsEmpty (Contraction nf nA κ) := by
    apply QED.WickModel.isEmpty_contraction_of_not_two_dvd
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    simp only [Fintype.card_fin]
    omega
  exact hE.false C

/-- **A contraction with an odd number of external photons has odd graded order.** -/
theorem plumb_odd_gradedOrder (C : Contraction nf nA κ) (h : ¬ 2 ∣ nA) (g : Grading κ) :
    ¬ 2 ∣ gradedOrder κ g := by
  have hd := plumb_odd_sum_order C h
  have h2 : ∑ t : CtVertex κ, 2 * g t = 2 * ∑ t, g t := (Finset.mul_sum _ _ _).symm
  unfold gradedOrder
  rw [h2]
  omega

end Parity

variable {P : Params} {F : Type} [Fintype F] [DecidableEq F] {Φ : Lepton.Flavors F}
  {D : Counterterms F} {rep : F → F} {m₀ : ℝ} {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- **(T₉′) of an attached connected vertex piece of graded order at most `5`**, in the form of
`hT₁` of the three peels. -/
theorem plumb_t9_vertex (H : T9Hyps P Φ D rep m₀) (C : Contraction 1 1 κ)
    (hA : ExternalsAttached C) (hV : VerticesConnected C) (g : Grading κ)
    (hg : gradedOrder κ g ≤ 5) {r' r q : Fin 4 → ℝ} (hmom : r' = r + q)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![r] ![q]
        (lineMomentum₂ C ![r'] ![r] ![q] ℓ) αOut βIn μ := by
  have hodd := plumb_odd_gradedOrder C (by norm_num) g
  rcases (by omega : gradedOrder κ g ≤ 3 ∨ gradedOrder κ g = 5) with h | h
  · exact t9_vertex_le_three P Φ D H.hε rep H.hrep H.hPV₁ H.hPV₂ H.hD C hA hV g h r' r q
      αOut βIn μ
  · exact t9_vertex_five P Φ D H.hε rep H.hrep H.hPV₁ H.hPV₂ H.hD C hA hV g h hmom αOut βIn μ

/-- **(T₉′) of a 1PI self-energy piece of graded order at most `5`**. -/
theorem plumb_t9_selfEnergy (H : T9Hyps P Φ D rep m₀) (C : Contraction 1 0 κ) (hC : IsOnePI C)
    (g : Grading κ) (hg : gradedOrder κ g ≤ 5) (p : Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![p] ![]
        (lineMomentum₂ C ![p] ![p] ![] ℓ) αOut βIn ![] := by
  obtain ⟨-, hd⟩ := t9_two_le_gradedOrder C (by norm_num)
    (t9_pos_of_isOnePI C hC (Or.inl one_pos)) g
  exact t9_selfEnergy H C hC g (by omega) p αOut βIn

/-- **(T₉′) of a 1PI vacuum-polarization piece of graded order at most `5`**. -/
theorem plumb_t9_vacuumPolarization (H : T9Hyps P Φ D rep m₀) (C : Contraction 0 2 κ)
    (hC : IsOnePI C) (g : Grading κ) (hg : gradedOrder κ g ≤ 5) (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![] ![k, -k]
        (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![] ![μ, ν] := by
  obtain ⟨-, hd⟩ := t9_two_le_gradedOrder C (by norm_num)
    (t9_pos_of_isOnePI C hC (Or.inr two_pos)) g
  exact t9_vacuumPolarization H C hC g (by omega) k μ ν

end QED.GradedProof.X1C

end
