/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncAPiece
public import QED.GradedProof.RPi4FaceIdRayAQClass

/-!
# (R-Π₄) step L10: (A) for increments of the merged pieces of the three classes

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The merged pieces
`A_{ij}`, `B_i` of the classes `VA`, `VB`, `VC` at the entry `(2, 3)` satisfy (A) for increments
at every photon mass (`QED.GradedProof.RPi4.FaceRateIncAQPiecesAB`) for masses `≥ m₀ > 0`. With
`m₀ = l` this is the input `hA` of
`QED.GradedProof.RPi4.vacuumPolarizationPart_two_lepton_limit_of_incPieces`.

The decided data (line classes, cut pairs, flow lines, integer checks) are those of
`QED.GradedProof.RPi4.faceIdRayAQ_vDens_VA` (and `VB`, `VC`); the integrability data (flow
bounds, rows, criteria, refined bounds) are those of `QED.GradedProof.RPi4.tcov_vDens_VA`.

* `faceRateIncAQ_piecesAB`;
* `faceRateIncAQ_piecesAB_VA`, `faceRateIncAQ_piecesAB_VB`, `faceRateIncAQ_piecesAB_VC`;
* **`faceRateIncAQ_piecesAB_incPieces`**.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance

section Pieces

variable (e : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l)) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (clB : Fin 5 → Fin 3) (hclB : ∀ r, base r = faceIdRayAQRowZ (clB r)) {m₀ : ℝ} (hm₀ : 0 < m₀)
  {d₀ d₁ : ℕ} (K₂ K₁ K₃ : Fin 3 → Prop) [DecidablePred K₂] [DecidablePred K₁]
  [DecidablePred K₃]
  (hBd : ∀ {n : ℕ} (α : Fin (n + 1) → Fin 2 → ℝ) (cl : Fin (n + 1) → Fin 3),
    (∀ t, α t = faceIdRayAQRow (cl t)) → ∀ (cs : Fin (n + 1) → ℝ) (Q : Fin 3 → LoopQuartic),
      (∀ t, LoopDegLe 0 d₀ (Q t) ∧ LoopDegLe 1 d₁ (Q t)) → FaceIdRayAQBd α cs cl K₂ K₁ K₃ Q)
  (hd₀ : loopDegOf base 0 ≤ d₀) (hd₁ : loopDegOf base 1 ≤ d₁)
  (tA : Fin 4 → Fin 4 → Fin 7 × Fin 7) (tB : Fin 4 → Fin 6 × Fin 6) (jA : Fin 7) (jB : Fin 6)
  (hjA : jA = 1 ∨ jA = 3)
  (hokA : ∀ i j : Fin 4, i ≤ j →
    FaceIdRayAQPieceOK (faceIdRayAQClA clB i j) (tA i j).1 (tA i j).2 jA K₂ K₁ K₃)
  (hokB : ∀ i : Fin 4, FaceIdRayAQPieceOK (faceIdRayAQClB clB i) (tB i).1 (tB i).2 jB K₂ K₁ K₃)
  (hcsA : ∀ i j : Fin 4, i ≤ j → c (shA i j (tA i j).1.castSucc) ≠ c (shA i j (tA i j).2.castSucc))
  (hcsB : ∀ i : Fin 4, c (shB i (tB i).1.castSucc) ≠ c (shB i (tB i).2.castSucc))
  (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])
  (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
  (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
  (hBA : ∀ m k a b i j, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
    fun ℓ => vNum e 0 1 A base c m k ℓ a b)
  (hBB : ∀ m k a b i, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3} 4
    fun ℓ => vNum e 0 1 A base c m k ℓ a b)

include hA hclB hm₀ hBd hd₀ hd₁ hjA hokA hokB hcsA hcsB hflow hrow hrow4 hcA hcB hBA hBB

/-- **(A) for increments of the merged pieces `A_{ij}`, `B_i` of a class**, masses `≥ m₀`. -/
theorem faceRateIncAQ_piecesAB : FaceRateIncAQPiecesAB A base c e m₀ := by
  intro M X Y hM hX hY
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · obtain ⟨ht, hcl, c₁, c₂, c₃, c₄⟩ := hokA i j hij
    exact faceRateIncAQ_pieceA e A hA base c clB hclB hm₀ 2 3 K₂ K₁ K₃ hBd y₁ y₂ hflow hrow
      hrow4 hd₀ hd₁ hM hX hY i j _ _ ht hcl (hcsA i j hij) jA hjA c₁ c₂ c₃ c₄ (hcA i j)
      fun m k a b => hBA m k a b i j
  · obtain ⟨ht, hcl, c₁, c₂, c₃, c₄⟩ := hokB i
    exact faceRateIncAQ_pieceB e A hA base c clB hclB hm₀ 2 3 K₂ K₁ K₃ hBd y₁ y₂ hflow hrow
      hrow4 hd₀ hd₁ hX hY i _ _ ht hcl (hcsB i) jB c₁ c₂ c₃ c₄ (hcB i)
      fun m k a b => hBB m k a b i

end Pieces

/-! ### The three classes -/

section Classes

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (e : ℝ)

include hm₀

/-- **(A) for increments of the merged pieces, class `VA`.** -/
theorem faceRateIncAQ_piecesAB_VA : FaceRateIncAQPiecesAB aVA baseVA cVA e m₀ :=
  faceRateIncAQ_piecesAB e aVA (fun a b ρ σ => isOddG_aVA a b ρ σ) baseVA cVA faceIdRayAQClVA
    (by decide) hm₀ (· ≠ 0) (· ≠ 0) (· = 2)
    (fun α cl hα cs Q hQ => faceIdRayAQBd_VA α cl hα cs Q hQ)
    (by rw [loopDegOf_VA_zero]) (by rw [loopDegOf_VA])
    (fun _ _ => (0, 3)) (fun _ => (0, 3)) 3 3 (Or.inr rfl) (by decide) (by decide)
    (fun i j _ => by fin_cases i <;> fin_cases j <;> norm_num [shA, cVA])
    (fun i => by fin_cases i <;> norm_num [shB, cVA])
    ![0, 0] ![-1, -1] flowVA (by decide) (by decide) critA_VA critB_VA
    (fun m k a' b' i j => rb_vNum e 0 1 aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')

/-- **(A) for increments of the merged pieces, class `VB`.** -/
theorem faceRateIncAQ_piecesAB_VB : FaceRateIncAQPiecesAB aVB baseVB cVB e m₀ :=
  faceRateIncAQ_piecesAB e aVB (fun a b ρ σ => isOddG_aVB a b ρ σ) baseVB cVB faceIdRayAQClVB
    (by decide) hm₀ (fun _ => True) (· ≠ 1) (· ≠ 0)
    (fun α cl hα cs Q hQ => faceIdRayAQBd_VB α cl hα cs Q hQ)
    (by rw [loopDegOf_VB.2]; norm_num) (by rw [loopDegOf_VB.1]; norm_num)
    faceIdRayAQCutVB faceIdRayAQCutVBB 1 1 (Or.inl rfl) (by decide) (by decide)
    (fun i j _ => by fin_cases i <;> fin_cases j <;> norm_num [shA, cVB, faceIdRayAQCutVB])
    (fun i => by fin_cases i <;> norm_num [shB, cVB, faceIdRayAQCutVBB])
    ![0, 1] ![-1, 0] flowVB (by decide) (by decide) critA_VB critB_VB
    (fun m k a' b' i j => rb_vNum e 0 1 aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')

/-- **(A) for increments of the merged pieces, class `VC`.** -/
theorem faceRateIncAQ_piecesAB_VC : FaceRateIncAQPiecesAB aVC baseVC cVC e m₀ :=
  faceRateIncAQ_piecesAB e aVC (fun a b ρ σ => isOddG_aVC a b ρ σ) baseVC cVC faceIdRayAQClVC
    (by decide) hm₀ (· ≠ 0) (· ≠ 0) (· = 2)
    (fun α cl hα cs Q hQ => faceIdRayAQBd_VA α cl hα cs Q hQ)
    (by rw [loopDegOf_VC_zero]) (by rw [loopDegOf_VC])
    (fun _ _ => (0, 1)) (fun _ => (0, 1)) 3 3 (Or.inr rfl) (by decide) (by decide)
    (fun i j _ => by fin_cases i <;> fin_cases j <;> norm_num [shA, cVC])
    (fun i => by fin_cases i <;> norm_num [shB, cVC])
    ![0, 1] ![-1, 0] flowVC (by decide) (by decide) critA_VC critB_VC
    (fun m k a' b' i j => rb_vNum e 0 1 aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')

end Classes

/-- **The input `hA` of `vacuumPolarizationPart_two_lepton_limit_of_incPieces`**: (A) for
increments of the merged pieces of `VA`, `VB`, `VC` for masses `≥ l`, every `l ≥ 1`. -/
theorem faceRateIncAQ_piecesAB_incPieces (e : ℝ) :
    ∀ l : ℝ, 1 ≤ l → FaceRateIncAQPiecesAB aVA baseVA cVA e l ∧
      FaceRateIncAQPiecesAB aVB baseVB cVB e l ∧ FaceRateIncAQPiecesAB aVC baseVC cVC e l :=
  fun _ hl => have hl0 := one_pos.trans_le hl
    ⟨faceRateIncAQ_piecesAB_VA hl0 e, faceRateIncAQ_piecesAB_VB hl0 e,
      faceRateIncAQ_piecesAB_VC hl0 e⟩

end QED.GradedProof.RPi4

end
