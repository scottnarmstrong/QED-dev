/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajDPRRed
public import QED.GradedProof.RPi4FaceIdRayBClass
public import QED.GradedProof.RPi4MajDPNull

/-!
# (R-Π₄) step L10, `MajDRay`: the ray half of the merged pieces from the gain bound

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10. The rate (B)
`QED.GradedProof.RPi4.FaceIdRayRateB` holds for each merged piece `A_{ij}`, `B_i` of
`QED.GradedProof.RPi4.triDens` separately (the piece haves of
`QED.GradedProof.RPi4.faceIdRayB_triDens`, exported), for the three classes `VA`, `VB`, `VC`
and all masses `≥ m₀`. With `QED.GradedProof.RPi4.majDRayRay_of_pow_rateB` the input
`QED.GradedProof.RPi4.MajDPiecesRay` of `QED.GradedProof.RPi4.majD_wireDRay_of_rayPieces`
reduces to the gain bound `QED.GradedProof.RPi4.MajDRayPow` of each piece (`MajDPiecesPow`).

* `majDPR_rateB_pieces`; `MajDPiecesRateB`, `majDPR_rateB_VA`, `majDPR_rateB_VB`,
  `majDPR_rateB_VC`;
* `MajDPiecesPow`, `majDPiecesRay_of_pow_rateB`, `majDPiecesRay_VA_of_pow`,
  `majDPiecesRay_VB_of_pow`, `majDPiecesRay_VC_of_pow`;
* **`majD_wireDRay_of_powPieces`**: `MajDPiecesPow` of the three classes at `(2, 3)` gives
  `QED.GradedProof.RPi4.WireDRay`.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

/-! ### The rate (B) of each merged piece -/

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])
  {m₀ : ℝ} (hm₀ : 0 < m₀)

include hflow hrow hrow4 hm₀

/-- **The rate (B) of each merged piece `A`, `B` of `triDens`.** Hypotheses as in
`QED.GradedProof.RPi4.faceIdRayB_triDens` without those of the padded piece. -/
theorem majDPR_rateB_pieces
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
    (∀ i j : Fin 4, i ≤ j → FaceIdRayRateB (majDPieceA base c Num M X Y μ ν i j)) ∧
      ∀ i : Fin 4, FaceIdRayRateB (majDPieceB base c Num M X Y μ ν i) := by
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)
  -- the ten pieces with eight lines
  have PA : ∀ i j : Fin 4, FaceIdRayRateB fun t k => if i ≤ j then
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
      exact faceIdRayB_vpPiece_of_nodes base c y₁ y₂ hflow hrow hrow4 (Or.inr rfl) (shA i j)
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
      exact FaceIdRayRateB.zero
  -- the four pieces with seven lines
  have PB : ∀ i : Fin 4, FaceIdRayRateB fun t k =>
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
    exact faceIdRayB_vpPiece_of_nodes base c y₁ y₂ hflow hrow hrow4 (Or.inl rfl) (shB i)
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

section Preds

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (μ ν : Fin 4)

/-- The rate (B) of every merged piece `A`, `B`, all masses `≥ m₀`. -/
def MajDPiecesRateB (m₀ : ℝ) : Prop :=
  ∀ M X Y : ℝ, m₀ ≤ M → m₀ ≤ X → m₀ ≤ Y →
    (∀ i j : Fin 4, i ≤ j → FaceIdRayRateB (majDPieceA base c Num M X Y μ ν i j)) ∧
      ∀ i : Fin 4, FaceIdRayRateB (majDPieceB base c Num M X Y μ ν i)

/-- **The gain bound of every merged piece `A`, `B`**, all masses `≥ m₀`. -/
def MajDPiecesPow (m₀ : ℝ) : Prop :=
  ∀ M X Y : ℝ, m₀ ≤ M → m₀ ≤ X → m₀ ≤ Y →
    (∀ i j : Fin 4, i ≤ j → MajDRayPow (majDPieceA base c Num M X Y μ ν i j)) ∧
      ∀ i : Fin 4, MajDRayPow (majDPieceB base c Num M X Y μ ν i)

theorem majDPiecesRay_of_pow_rateB {m₀ : ℝ} (hP : MajDPiecesPow base c Num μ ν m₀)
    (hB : MajDPiecesRateB base c Num μ ν m₀) : MajDPiecesRay base c Num μ ν m₀ :=
  fun M X Y hM hX hY =>
    ⟨fun i j hij => majDRayRay_of_pow_rateB ((hP M X Y hM hX hY).1 i j hij)
        ((hB M X Y hM hX hY).1 i j hij),
      fun i => majDRayRay_of_pow_rateB ((hP M X Y hM hX hY).2 i) ((hB M X Y hM hX hY).2 i)⟩

end Preds

section Classes

variable {m₀ : ℝ} (hm₀ : 0 < m₀) (e : ℝ) (μ ν : Fin 4)

include hm₀

/-- **The rate (B) of the merged pieces of the class `VA`.** -/
theorem majDPR_rateB_VA :
    MajDPiecesRateB baseVA cVA (vNum e 0 1 aVA baseVA cVA) μ ν m₀ := by
  intro M X Y hM hX hY
  have hA := fun a b ρ σ => isOddG_aVA a b ρ σ
  obtain ⟨hshA, hshB, -⟩ := faceShapeOK_VA
  exact majDPR_rateB_pieces baseVA cVA ![0, 0] ![-1, -1] flowVA (by decide) (by decide) hm₀
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
    hshA hshB hM hX hY μ ν

/-- **The rate (B) of the merged pieces of the class `VB`.** -/
theorem majDPR_rateB_VB :
    MajDPiecesRateB baseVB cVB (vNum e 0 1 aVB baseVB cVB) μ ν m₀ := by
  intro M X Y hM hX hY
  have hA := fun a b ρ σ => isOddG_aVB a b ρ σ
  obtain ⟨hshA, hshB, -⟩ := faceShapeOK_VB
  exact majDPR_rateB_pieces baseVB cVB ![0, 1] ![-1, 0] flowVB (by decide) (by decide) hm₀
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
    hshA hshB hM hX hY μ ν

/-- **The rate (B) of the merged pieces of the class `VC`.** -/
theorem majDPR_rateB_VC :
    MajDPiecesRateB baseVC cVC (vNum e 0 1 aVC baseVC cVC) μ ν m₀ := by
  intro M X Y hM hX hY
  have hA := fun a b ρ σ => isOddG_aVC a b ρ σ
  obtain ⟨hshA, hshB, -⟩ := faceShapeOK_VC
  exact majDPR_rateB_pieces baseVC cVC ![0, 1] ![-1, 0] flowVC (by decide) (by decide) hm₀
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
    hshA hshB hM hX hY μ ν

theorem majDPiecesRay_VA_of_pow
    (h : MajDPiecesPow baseVA cVA (vNum e 0 1 aVA baseVA cVA) μ ν m₀) :
    MajDPiecesRay baseVA cVA (vNum e 0 1 aVA baseVA cVA) μ ν m₀ :=
  majDPiecesRay_of_pow_rateB _ _ _ _ _ h (majDPR_rateB_VA hm₀ e μ ν)

theorem majDPiecesRay_VB_of_pow
    (h : MajDPiecesPow baseVB cVB (vNum e 0 1 aVB baseVB cVB) μ ν m₀) :
    MajDPiecesRay baseVB cVB (vNum e 0 1 aVB baseVB cVB) μ ν m₀ :=
  majDPiecesRay_of_pow_rateB _ _ _ _ _ h (majDPR_rateB_VB hm₀ e μ ν)

theorem majDPiecesRay_VC_of_pow
    (h : MajDPiecesPow baseVC cVC (vNum e 0 1 aVC baseVC cVC) μ ν m₀) :
    MajDPiecesRay baseVC cVC (vNum e 0 1 aVC baseVC cVC) μ ν m₀ :=
  majDPiecesRay_of_pow_rateB _ _ _ _ _ h (majDPR_rateB_VC hm₀ e μ ν)

/-- **`WireDRay` from the gain bound of the merged pieces of the three classes.** -/
theorem majD_wireDRay_of_powPieces
    (hA : MajDPiecesPow baseVA cVA (vNum e 0 1 aVA baseVA cVA) 2 3 m₀)
    (hB : MajDPiecesPow baseVB cVB (vNum e 0 1 aVB baseVB cVB) 2 3 m₀)
    (hC : MajDPiecesPow baseVC cVC (vNum e 0 1 aVC baseVC cVC) 2 3 m₀)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    WireDRay Φ e m₀ :=
  majD_wireDRay_of_rayPieces e hm₀ (majDPiecesRay_VA_of_pow hm₀ e 2 3 hA)
    (majDPiecesRay_VB_of_pow hm₀ e 2 3 hB) (majDPiecesRay_VC_of_pow hm₀ e 2 3 hC) Φ hmass

end Classes

end QED.GradedProof.RPi4

end
