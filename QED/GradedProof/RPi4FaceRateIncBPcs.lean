/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncBDer
public import QED.GradedProof.RPi4FaceRateIncPcs
public import QED.GradedProof.RPi4MajDPNull

/-!
# (R-Π₄) step L10, T2.UV: the increment rate (B) without the padded piece

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The padded merged
piece vanishes at the entry `(2, 3)` (`QED.GradedProof.RPi4.majDPieceP_two_three`), so the input
`QED.GradedProof.RPi4.FaceRateIncPieces … FaceRateIncB m₀` of
`QED.GradedProof.RPi4.faceRateInc_decDil_of_pieces` reduces to the ten pieces with seven lines
and the four with six.

* `faceRateIncB_pieceP_two_three`: the padded piece has the increment rate (B) trivially;
* `FaceRateIncBPiecesAB`: the increment rate (B) of the pieces `A_{ij}`, `B_i`;
* **`faceRateIncPieces_b_of_AB`**, `faceRateIncPieces_b_VA/VB/VC`: `FaceRateIncPieces` from them.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

section Pad

variable (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (e : ℝ)

/-- **The padded piece at `(2, 3)` has the increment rate (B)**: it vanishes. -/
theorem faceRateIncB_pieceP_two_three (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l))
    (hcov : ∀ m, TCov2 (vNum e 0 1 A base c m)) (M X Y : ℝ) :
    FaceRateIncB (majDPieceP base c (vNumE4 e 0 1 A) M X Y 2 3) := by
  have h4 : ∀ k, vNumE4 e 0 1 A k 2 3 = 0 :=
    majDP_E4_two_three _ (vNumE4_cov e A base c hA hcov) fun _ => rfl
  have h0 : majDPieceP base c (vNumE4 e 0 1 A) M X Y 2 3 = fun _ _ => 0 :=
    funext₂ fun u k => majDPieceP_two_three base c _ h4 M X Y u k
  rw [h0]
  exact FaceRateIncB.zero

/-- The increment rate (B) of the merged pieces `A_{ij}` and `B_i` at `(2, 3)`, masses `≥ m₀`. -/
def FaceRateIncBPiecesAB (m₀ : ℝ) : Prop :=
  ∀ M X Y : ℝ, m₀ ≤ M → m₀ ≤ X → m₀ ≤ Y →
    (∀ i j : Fin 4, i ≤ j → FaceRateIncB (majDPieceA base c (vNum e 0 1 A base c) M X Y 2 3 i j))
      ∧ ∀ i : Fin 4, FaceRateIncB (majDPieceB base c (vNum e 0 1 A base c) M X Y 2 3 i)

/-- **`FaceRateIncPieces … FaceRateIncB` from the pieces `A_{ij}`, `B_i`.** -/
theorem faceRateIncPieces_b_of_AB (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l))
    (hcov : ∀ m, TCov2 (vNum e 0 1 A base c m)) {m₀ : ℝ}
    (h : FaceRateIncBPiecesAB A base c e m₀) :
    FaceRateIncPieces base c (vNum e 0 1 A base c) (vNumE4 e 0 1 A) 2 3 FaceRateIncB m₀ :=
  fun M X Y hM hX hY => ⟨(h M X Y hM hX hY).1, (h M X Y hM hX hY).2,
    faceRateIncB_pieceP_two_three A base c e hA hcov M X Y⟩

end Pad

variable (e : ℝ) {m₀ : ℝ}

theorem faceRateIncPieces_b_VA (h : FaceRateIncBPiecesAB aVA baseVA cVA e m₀) :
    FaceRateIncPieces baseVA cVA (vNum e 0 1 aVA baseVA cVA) (vNumE4 e 0 1 aVA) 2 3
      FaceRateIncB m₀ :=
  faceRateIncPieces_b_of_AB _ _ _ e (isOddG_aVA · · · ·) (tcov_vNumA e 0 1 baseVA cVA) h

theorem faceRateIncPieces_b_VB (h : FaceRateIncBPiecesAB aVB baseVB cVB e m₀) :
    FaceRateIncPieces baseVB cVB (vNum e 0 1 aVB baseVB cVB) (vNumE4 e 0 1 aVB) 2 3
      FaceRateIncB m₀ :=
  faceRateIncPieces_b_of_AB _ _ _ e (isOddG_aVB · · · ·) (tcov_vNumB e 0 1 baseVB cVB) h

theorem faceRateIncPieces_b_VC (h : FaceRateIncBPiecesAB aVC baseVC cVC e m₀) :
    FaceRateIncPieces baseVC cVC (vNum e 0 1 aVC baseVC cVC) (vNumE4 e 0 1 aVC) 2 3
      FaceRateIncB m₀ :=
  faceRateIncPieces_b_of_AB _ _ _ e (isOddG_aVC · · · ·) (tcov_vNumC e 0 1 baseVC cVC) h

end QED.GradedProof.RPi4

end
