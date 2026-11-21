/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajDPNull
public import QED.GradedProof.RPi4MajDInc

/-!
# (R-Π₄) step L10, two loops: the increments without the padded piece

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.UV). The
padded merged piece vanishes at the entry `(2, 3)`
(`QED.GradedProof.RPi4.majDPieceP_two_three`), so the increment input
`QED.GradedProof.RPi4.MajDIncPieces` of the three classes reduces to the pieces with seven and
six lines.

* `MajDIncPiecesAB`: `MajDRayInc` of the ten pieces with seven lines and the four with six;
* **`majDInc_classes_of_piecesAB`**: the three `MajDRayInc` inputs of the classes from
  `MajDIncPiecesAB`.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2

section Pieces

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (μ ν : Fin 4)

/-- **The increments of the merged pieces with seven and with six lines**, every three-flavour
combination with masses `≥ m₀`. -/
def MajDIncPiecesAB (m₀ : ℝ) : Prop :=
  ∀ M X Y : ℝ, m₀ ≤ M → m₀ ≤ X → m₀ ≤ Y →
    (∀ i j : Fin 4, i ≤ j → MajDRayInc (majDPieceA base c Num M X Y μ ν i j)) ∧
      ∀ i : Fin 4, MajDRayInc (majDPieceB base c Num M X Y μ ν i)

end Pieces

/-- `MajDIncPiecesAB` of a class numerator at `(2, 3)` is `MajDIncPieces`. -/
theorem majDIncPieces_of_AB
    (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (e : ℝ) (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l))
    (hcov : ∀ m, TCov2 (vNum e 0 1 A base c m)) {m₀ : ℝ}
    (h : MajDIncPiecesAB base c (vNum e 0 1 A base c) 2 3 m₀) :
    MajDIncPieces base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) 2 3 m₀ := by
  have h4 : ∀ k, vNumE4 e 0 1 A k 2 3 = 0 :=
    majDP_E4_two_three _ (vNumE4_cov e A base c hA hcov) fun _ => rfl
  intro M X Y hM hX hY
  obtain ⟨hA', hB'⟩ := h M X Y hM hX hY
  refine ⟨hA', hB', (MajDRayInc.zero).congr fun s _ u _ => ?_⟩
  rw [majDPieceP_two_three base c _ h4]

/-- **The three class densities' increments from the pieces with seven and six lines.** -/
theorem majDInc_classes_of_piecesAB (e : ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀)
    (hA : MajDIncPiecesAB baseVA cVA (vNum e 0 1 aVA baseVA cVA) 2 3 m₀)
    (hB : MajDIncPiecesAB baseVB cVB (vNum e 0 1 aVB baseVB cVB) 2 3 m₀)
    (hC : MajDIncPiecesAB baseVC cVC (vNum e 0 1 aVC baseVC cVC) 2 3 m₀)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    (MajDRayInc fun u k => vDens aVA baseVA cVA Φ e m₀ u k 2 3) ∧
      (MajDRayInc fun u k => vDens aVB baseVB cVB Φ e m₀ u k 2 3) ∧
        MajDRayInc fun u k => vDens aVC baseVC cVC Φ e m₀ u k 2 3 :=
  majDInc_classes_of_pieces e hm₀
    (majDIncPieces_of_AB _ _ _ e (isOddG_aVA · · · ·) (tcov_vNumA e 0 1 baseVA cVA) hA)
    (majDIncPieces_of_AB _ _ _ e (isOddG_aVB · · · ·) (tcov_vNumB e 0 1 baseVB cVB) hB)
    (majDIncPieces_of_AB _ _ _ e (isOddG_aVC · · · ·) (tcov_vNumC e 0 1 baseVC cVC) hC) Φ hmass

end QED.GradedProof.RPi4

end
