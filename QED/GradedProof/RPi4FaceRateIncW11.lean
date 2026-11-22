/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceRateIncW10
public import QED.GradedProof.RPi4MajDPRB
public import QED.GradedProof.RPi4FaceRateIncBPcs

/-!
# (R-Π₄) step L10, B-inc: the increment rate (B) of the merged pieces of the three classes

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The increment
rate (B) `QED.GradedProof.RPi4.FaceRateIncB` holds for each merged piece `A_{ij}`, `B_i` of
`QED.GradedProof.RPi4.triDens` (`faceRateIncB_vpPiece_of_nodes` in place of
`QED.GradedProof.RPi4.faceIdRayB_vpPiece_of_nodes` in the proof of
`QED.GradedProof.RPi4.majDPR_rateB_pieces`), for the three classes `VA`, `VB`, `VC` and all
masses `≥ m₀`. This is the input `QED.GradedProof.RPi4.FaceRateIncBPiecesAB` of
`QED.GradedProof.RPi4.faceRateIncPieces_b_VA` (and `VB`, `VC`).

* `faceRateIncB_majDPieces`;
* `faceRateIncBPiecesAB_VA`, `faceRateIncBPiecesAB_VB`, `faceRateIncBPiecesAB_VC`;
* **`faceRateIncPieces_b_VA_of_pos`** (and `VB`, `VC`): the `FaceRateIncB` input of the
  increment, for every `m₀ > 0`;
* **`faceRateIncBPiecesAB_incPieces`**: the three classes for every `l ≥ 1`;
* **`faceRateInc_decDil_of_piecesA`**: `faceRateInc_decDil_of_pieces` without its (B) inputs.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance
open QED.WickModel (Params)

/-! ### The increment rate (B) of each merged piece -/

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])
  {m₀ : ℝ} (hm₀ : 0 < m₀)

include hflow hrow hrow4 hm₀

/-- **The increment rate (B) of each merged piece `A`, `B` of `triDens`.** Hypotheses as in
`QED.GradedProof.RPi4.majDPR_rateB_pieces`. -/
theorem faceRateIncB_majDPieces
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E0 E2 : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hE : ∀ m k ℓ a b, Num m k ℓ a b =
      E0 k ℓ a b + (m : ℂ) ^ 2 * E2 k ℓ a b + ((m : ℂ) ^ 2) ^ 2 * E4 k a b)
    (hP : ∀ m k a b, IsLoopPoly 2 4 fun ℓ => Num m k ℓ a b)
    (hP2 : ∀ k a b, IsLoopPoly 2 2 fun ℓ => E2 k ℓ a b)
    (hBA : ∀ m k a b i j, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun ℓ => Num m k ℓ a b)
    (hBB : ∀ m k a b i, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3} 4
      fun ℓ => Num m k ℓ a b)
    {d : ℕ} (hk : ∀ m ℓ a b, IsLoopPoly 1 d fun y => Num m (y 0) ℓ a b)
    {d₁ d₀ : ℕ} (hd₁ : d₁ ≤ 3) (hd₀ : d₀ ≤ 3)
    (hD₁ : ∀ (C : ℂ) m k a b, ∃ Q : LoopQuartic, LoopDegLe 1 d₁ Q ∧
      Q.eval = fun ℓ => C * Num m k ℓ a b)
    (hD₀ : ∀ (C : ℂ) m k a b, ∃ Q : LoopQuartic, LoopDegLe 0 d₀ Q ∧
      Q.eval = fun ℓ => C * Num m k ℓ a b)
    (hSub₁ : ∀ (C : ℂ) m m' k a b, ∃ Q : LoopQuartic, Q.quart = 0 ∧ LoopDegLe 1 d₁ Q ∧
      Q.eval = fun ℓ => C * (Num m k ℓ a b - Num m' k ℓ a b))
    (hSub₀ : ∀ (C : ℂ) m m' k a b, ∃ Q : LoopQuartic, Q.quart = 0 ∧ LoopDegLe 0 d₀ Q ∧
      Q.eval = fun ℓ => C * (Num m k ℓ a b - Num m' k ℓ a b))
    (hshA : ∀ i j : Fin 4, i ≤ j → FaceShapeOK base (fun l : Fin 7 => shA i j l.castSucc) d₁ d₀)
    (hshB : ∀ i : Fin 4, FaceShapeOK base (fun l : Fin 6 => shB i l.castSucc) d₁ d₀)
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (μ ν : Fin 4) :
    (∀ i j : Fin 4, i ≤ j → FaceRateIncB (majDPieceA base c Num M X Y μ ν i j)) ∧
      ∀ i : Fin 4, FaceRateIncB (majDPieceB base c Num M X Y μ ν i) := by
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)
  -- the ten pieces with eight lines
  have PA : ∀ i j : Fin 4, FaceRateIncB fun t k => if i ≤ j then
      pairDens (fun ℓ => C * Num M k ℓ μ ν)
        (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
        (fun l => c (shA i j l.castSucc) • k)
        ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0]
        (Fin.last 6) t
      else 0 := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true]
      obtain ⟨⟨a1, b1, c1⟩, ⟨a0, b0, c0⟩⟩ := hshA i j hij
      have hMf : ∀ l, m₀ ≤ mA M X Y i j l := fun l => by unfold mA; split_ifs <;> assumption
      exact faceRateIncB_vpPiece_of_nodes base c y₁ y₂ hflow hrow hrow4 (Or.inr rfl) (shA i j)
        (fun l => by fin_cases l <;> simp [shA, Fin.ext_iff] <;> omega) (hcA i j)
        (fun k ℓ => C * Num M k ℓ μ ν) (fun k => (hP M k μ ν).const_mul _)
        (fun k => (hBA M k μ ν i j).const_mul _) (fun ℓ => (hk M ℓ μ ν).const_mul _)
        (fun k => by obtain ⟨Q, h1, h2⟩ := hD₁ C M k μ ν; exact ⟨Q, h2, h1, Or.inl rfl⟩)
        (fun k => by obtain ⟨Q, h1, h2⟩ := hD₀ C M k μ ν; exact ⟨Q, h2, h1, Or.inl rfl⟩)
        hd₁ hd₀ a1 b1 c1 a0 b0 c0 hm₀ _ rfl
        (fun l hl => by
          fin_cases l
          exacts [hMf 0, hMf 1, hMf 2, hMf 3, hX, hY, absurd rfl hl])
    · simp only [hij, ite_false]
      exact FaceRateIncB.zero
  -- the four pieces with seven lines
  have PB : ∀ i : Fin 4, FaceRateIncB fun t k =>
      pairDens (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν))
        (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
        (fun l => c (shB i l.castSucc) • k)
        ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] (Fin.last 5) t := by
    intro i
    have hpoly : ∀ k, IsLoopPoly 2 3 fun ℓ =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν) := by
      intro k
      have e : (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) =
          fun ℓ => (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
            (E2 k ℓ μ ν + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * E4 k μ ν) := by
        funext ℓ; rw [hE, hE]; ring
      rw [e]
      exact (((hP2 k μ ν).add (IsLoopPoly.const _)).const_mul _).mono (by norm_num)
    obtain ⟨⟨a1, b1, c1⟩, ⟨a0, b0, c0⟩⟩ := hshB i
    have hMf : ∀ l, m₀ ≤ mB X Y i l := fun l => by unfold mB; split_ifs <;> assumption
    exact faceRateIncB_vpPiece_of_nodes base c y₁ y₂ hflow hrow hrow4 (Or.inl rfl) (shB i)
      (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]; omega) (hcB i)
      (fun k ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) hpoly
      (fun k => (((hBB X k μ ν i).sub (hBB M k μ ν i)).const_mul _).mono (by decide) le_rfl)
      (fun ℓ => ((hk X ℓ μ ν).sub (hk M ℓ μ ν)).const_mul _)
      (fun k => by
        obtain ⟨Q, h0, h1, h2⟩ := hSub₁ (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) X M k μ ν
        exact ⟨Q, h2, h1, Or.inr h0⟩)
      (fun k => by
        obtain ⟨Q, h0, h1, h2⟩ := hSub₀ (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) X M k μ ν
        exact ⟨Q, h2, h1, Or.inr h0⟩)
      hd₁ hd₀ a1 b1 c1 a0 b0 c0 hm₀ _ rfl
      (fun l hl => by
        fin_cases l
        exacts [hMf 0, hMf 1, hMf 2, hMf 3, hY, absurd rfl hl])
  refine ⟨fun i j hij => ?_, PB⟩
  have h := PA i j
  simp only [hij, ite_true] at h
  exact h

end Setting

section Classes

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (e : ℝ)

include hm₀

/-- **The increment rate (B) of the merged pieces of the class `VA`** at `(2, 3)`. -/
theorem faceRateIncBPiecesAB_VA : FaceRateIncBPiecesAB aVA baseVA cVA e m₀ := by
  intro M X Y hM hX hY
  have hA := fun a b ρ σ => isOddG_aVA a b ρ σ
  obtain ⟨hshA, hshB, -⟩ := faceShapeOK_VA
  exact faceRateIncB_majDPieces baseVA cVA ![0, 0] ![-1, -1] flowVA (by decide) (by decide) hm₀
    critA_VA critB_VA _ _ _ _ (vNum_eq e 0 1 aVA baseVA cVA hA)
    (isLoopPoly_vNum e 0 1 aVA baseVA cVA) (isLoopPoly_vNumE2 e 0 1 aVA baseVA cVA)
    (fun m k a' b' i j => rb_vNum e 0 1 aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e 0 1 aVA baseVA cVA) (d₁ := 1) (d₀ := 3) (by norm_num) le_rfl
    (fun C m k a b => by
      have h := exists_loopQuartic_vNum e 0 1 aVA baseVA cVA 1 C m k a b
      rw [loopDegOf_VA] at h; exact h)
    (fun C m k a b => by
      have h := exists_loopQuartic_vNum e 0 1 aVA baseVA cVA 0 C m k a b
      rw [loopDegOf_VA_zero] at h; exact h)
    (fun C m m' k a b => by
      have h := exists_loopQuartic_vNum_sub_cubic e 0 1 hA baseVA cVA 1 C m m' k a b
      rw [loopDegOf_VA] at h; exact h)
    (fun C m m' k a b => by
      have h := exists_loopQuartic_vNum_sub_cubic e 0 1 hA baseVA cVA 0 C m m' k a b
      rw [loopDegOf_VA_zero] at h; exact h)
    hshA hshB hM hX hY 2 3

/-- **The increment rate (B) of the merged pieces of the class `VB`** at `(2, 3)`. -/
theorem faceRateIncBPiecesAB_VB : FaceRateIncBPiecesAB aVB baseVB cVB e m₀ := by
  intro M X Y hM hX hY
  have hA := fun a b ρ σ => isOddG_aVB a b ρ σ
  obtain ⟨hshA, hshB, -⟩ := faceShapeOK_VB
  exact faceRateIncB_majDPieces baseVB cVB ![0, 1] ![-1, 0] flowVB (by decide) (by decide) hm₀
    critA_VB critB_VB _ _ _ _ (vNum_eq e 0 1 aVB baseVB cVB hA)
    (isLoopPoly_vNum e 0 1 aVB baseVB cVB) (isLoopPoly_vNumE2 e 0 1 aVB baseVB cVB)
    (fun m k a' b' i j => rb_vNum e 0 1 aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e 0 1 aVB baseVB cVB) (d₁ := 2) (d₀ := 2) (by norm_num) (by norm_num)
    (fun C m k a b => by
      have h := exists_loopQuartic_vNum e 0 1 aVB baseVB cVB 1 C m k a b
      rw [loopDegOf_VB.1] at h; exact h)
    (fun C m k a b => by
      have h := exists_loopQuartic_vNum e 0 1 aVB baseVB cVB 0 C m k a b
      rw [loopDegOf_VB.2] at h; exact h)
    (fun C m m' k a b => by
      have h := exists_loopQuartic_vNum_sub_cubic e 0 1 hA baseVB cVB 1 C m m' k a b
      rw [loopDegOf_VB.1] at h; exact h)
    (fun C m m' k a b => by
      have h := exists_loopQuartic_vNum_sub_cubic e 0 1 hA baseVB cVB 0 C m m' k a b
      rw [loopDegOf_VB.2] at h; exact h)
    hshA hshB hM hX hY 2 3

/-- **The increment rate (B) of the merged pieces of the class `VC`** at `(2, 3)`. -/
theorem faceRateIncBPiecesAB_VC : FaceRateIncBPiecesAB aVC baseVC cVC e m₀ := by
  intro M X Y hM hX hY
  have hA := fun a b ρ σ => isOddG_aVC a b ρ σ
  obtain ⟨hshA, hshB, -⟩ := faceShapeOK_VC
  exact faceRateIncB_majDPieces baseVC cVC ![0, 1] ![-1, 0] flowVC (by decide) (by decide) hm₀
    critA_VC critB_VC _ _ _ _ (vNum_eq e 0 1 aVC baseVC cVC hA)
    (isLoopPoly_vNum e 0 1 aVC baseVC cVC) (isLoopPoly_vNumE2 e 0 1 aVC baseVC cVC)
    (fun m k a' b' i j => rb_vNum e 0 1 aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e 0 1 aVC baseVC cVC) (d₁ := 1) (d₀ := 3) (by norm_num) le_rfl
    (fun C m k a b => by
      have h := exists_loopQuartic_vNum e 0 1 aVC baseVC cVC 1 C m k a b
      rw [loopDegOf_VC] at h; exact h)
    (fun C m k a b => by
      have h := exists_loopQuartic_vNum e 0 1 aVC baseVC cVC 0 C m k a b
      rw [loopDegOf_VC_zero] at h; exact h)
    (fun C m m' k a b => by
      have h := exists_loopQuartic_vNum_sub_cubic e 0 1 hA baseVC cVC 1 C m m' k a b
      rw [loopDegOf_VC] at h; exact h)
    (fun C m m' k a b => by
      have h := exists_loopQuartic_vNum_sub_cubic e 0 1 hA baseVC cVC 0 C m m' k a b
      rw [loopDegOf_VC_zero] at h; exact h)
    hshA hshB hM hX hY 2 3

/-- **The `FaceRateIncB` input of the increment for the class `VA`.** -/
theorem faceRateIncPieces_b_VA_of_pos :
    FaceRateIncPieces baseVA cVA (vNum e 0 1 aVA baseVA cVA) (vNumE4 e 0 1 aVA) 2 3
      FaceRateIncB m₀ :=
  faceRateIncPieces_b_VA e (faceRateIncBPiecesAB_VA hm₀ e)

/-- **The `FaceRateIncB` input of the increment for the class `VB`.** -/
theorem faceRateIncPieces_b_VB_of_pos :
    FaceRateIncPieces baseVB cVB (vNum e 0 1 aVB baseVB cVB) (vNumE4 e 0 1 aVB) 2 3
      FaceRateIncB m₀ :=
  faceRateIncPieces_b_VB e (faceRateIncBPiecesAB_VB hm₀ e)

/-- **The `FaceRateIncB` input of the increment for the class `VC`.** -/
theorem faceRateIncPieces_b_VC_of_pos :
    FaceRateIncPieces baseVC cVC (vNum e 0 1 aVC baseVC cVC) (vNumE4 e 0 1 aVC) 2 3
      FaceRateIncB m₀ :=
  faceRateIncPieces_b_VC e (faceRateIncBPiecesAB_VC hm₀ e)

end Classes

/-- **The (B) input of the increment for the three classes**, every `l ≥ 1` (the hypothesis
`hB` of `vacuumPolarizationPart_two_lepton_limit_of_incPieces`). -/
theorem faceRateIncBPiecesAB_incPieces (e : ℝ) : ∀ l : ℝ, 1 ≤ l →
    FaceRateIncBPiecesAB aVA baseVA cVA e l ∧ FaceRateIncBPiecesAB aVB baseVB cVB e l ∧
      FaceRateIncBPiecesAB aVC baseVC cVC e l := fun _ hl =>
  ⟨faceRateIncBPiecesAB_VA (one_pos.trans_le hl) e, faceRateIncBPiecesAB_VB (one_pos.trans_le hl) e,
    faceRateIncBPiecesAB_VC (one_pos.trans_le hl) e⟩

/-- **`MajFaceRateInc` at `decDil l (decCfg 1 4)` without the (B) inputs**: the hypotheses
`hAb hBb hCb` of `faceRateInc_decDil_of_pieces` are `faceRateIncPieces_b_VA_of_pos` (and `VB`,
`VC`). -/
theorem faceRateInc_decDil_of_piecesA (P : Params) (he : P.e ≠ 0) {l : ℝ} (hl : 1 ≤ l)
    (hA : FaceIdRateRay fun u k => vDens aVA baseVA cVA (decDil l (decCfg 1 4)) P.e l u k 2 3)
    (hB : FaceIdRateRay fun u k => vDens aVB baseVB cVB (decDil l (decCfg 1 4)) P.e l u k 2 3)
    (hC : FaceIdRateRay fun u k => vDens aVC baseVC cVC (decDil l (decCfg 1 4)) P.e l u k 2 3)
    (hAa : FaceRateIncPieces baseVA cVA (vNum P.e 0 1 aVA baseVA cVA) (vNumE4 P.e 0 1 aVA) 2 3
      FaceRateIncAPow l)
    (hBa : FaceRateIncPieces baseVB cVB (vNum P.e 0 1 aVB baseVB cVB) (vNumE4 P.e 0 1 aVB) 2 3
      FaceRateIncAPow l)
    (hCa : FaceRateIncPieces baseVC cVC (vNum P.e 0 1 aVC baseVC cVC) (vNumE4 P.e 0 1 aVC) 2 3
      FaceRateIncAPow l) :
    MajFaceRateInc (decDil l (decCfg 1 4)) (fun _ => 0) P.e l :=
  have hl0 : 0 < l := one_pos.trans_le hl
  faceRateInc_decDil_of_pieces P he hl hA hB hC hAa hBa hCa
    (faceRateIncPieces_b_VA_of_pos hl0 P.e) (faceRateIncPieces_b_VB_of_pos hl0 P.e)
    (faceRateIncPieces_b_VC_of_pos hl0 P.e)

end QED.GradedProof.RPi4

end
