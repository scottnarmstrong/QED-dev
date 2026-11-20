/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdTri

/-!
# (R-Π₄) step L6d3: the three classes as one-loop limits

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The
block-summed density `blockDens` and the class densities `vDens` of `VA`, `VB`, `VC` satisfy
`FaceIdPL` at one momentum `k` below threshold, with `Ψ` the flavour sum of the face integrals
of the fifteen pieces (`faceIdBlockPsi`). The self-energy shifts are `β = 0` (`VA`: midpoint
`ℓ₀/2`) and `β = 1` (`VC`: midpoint `(k + ℓ₀)/2`); `VB` has vertex faces only, with loop-`0`
rest momenta in `{0, -k}`.

* `faceIdBlockPsi`, **`faceId_blockDens_PL`**;
* `faceIdShape2_VA`, `faceIdShape2_VB`, `faceIdShape2_VC`;
* **`faceId_vDens_PL_VA`**, **`faceId_vDens_PL_VB`**, **`faceId_vDens_PL_VC`**.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Matrix
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

/-- **The face integrals of a block-summed class**: `∑_f c_f faceIdTriPsi(M_f, X, X + 1)`. -/
noncomputable def faceIdBlockPsi (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
    (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) {F : Type} [Fintype F] (Φ : Lepton.Flavors F)
    (m₀ β : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4) (ε : ℝ) : ℂ :=
  ∑ f, (Φ.coeff f : ℂ) *
    faceIdTriPsi base c Num E4 (Φ.mass f) (blockX Φ m₀) (blockX Φ m₀ + 1) β k μ ν ε

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])
  {m₀ : ℝ} (hm₀ : 0 < m₀) {k : Fin 4 → ℝ} (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k)
  (hc1 : ∀ r : Fin 5, base r = ![1, 0] → c r = 0 ∨ c r = 1)
  {s : ℝ} (hs : s = 1 ∨ s = -1) (hc0 : ∀ r : Fin 5, base r = ![0, 1] → c r = 0 ∨ c r = s)

include hflow hrow hrow4 hm₀ hk hc1 hs hc0

/-- **A block-summed class as a one-loop limit.** -/
theorem faceId_blockDens_PL
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
    (hshP : FaceShapeOK base (fun l : Fin 6 => shB 0 l.castSucc) 0 2)
    (hsA : ∀ i j : Fin 4, i ≤ j → FaceIdShape2 base (shA i j) d₁ d₀)
    (hsB : ∀ i : Fin 4, FaceIdShape2 base (shB i) d₁ d₀)
    (hsP : FaceIdShape2 base (shB 0) 0 2)
    (hb0 : base 0 = ![1, 0]) (β : ℝ)
    (hβA : ∀ i j : Fin 4, i ≤ j → faceIdCard base (shA i j) ![1, 0] = 2 →
      ∀ f : Fin 7, base (shA i j f.castSucc) = ![0, 1] → c 4 - c (shA i j f.castSucc) = β)
    (hβB : ∀ i : Fin 4, faceIdCard base (shB i) ![1, 0] = 2 →
      ∀ f : Fin 6, base (shB i f.castSucc) = ![0, 1] → c 4 - c (shB i f.castSucc) = β)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) (μ ν : Fin 4) :
    FaceIdPL (fun t => blockDens base c Num E4 Φ m₀ t k μ ν)
      (faceIdBlockPsi base c Num E4 Φ m₀ β k μ ν) := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  exact FaceIdPL.sum Finset.univ fun f _ => (faceId_triDens_PL base c y₁ y₂ hflow hrow hrow4 hm₀
    hk hc1 hs hc0 hcA hcB Num E0 E2 E4 hE hP hP2 hBA hBB hd₁ hd₀ hD₁ hD₀ hSub₁ hSub₀ hshA hshB
    hshP hsA hsB hsP hb0 β hβA hβB (hmass f) hX (by linarith) μ ν).const_mul (Φ.coeff f : ℂ)

end Setting

theorem faceIdShape2_VA : (∀ i j : Fin 4, i ≤ j → FaceIdShape2 baseVA (shA i j) 1 3) ∧
    (∀ i : Fin 4, FaceIdShape2 baseVA (shB i) 1 3) ∧ FaceIdShape2 baseVA (shB 0) 0 2 := by
  decide

theorem faceIdShape2_VB : (∀ i j : Fin 4, i ≤ j → FaceIdShape2 baseVB (shA i j) 2 2) ∧
    (∀ i : Fin 4, FaceIdShape2 baseVB (shB i) 2 2) ∧ FaceIdShape2 baseVB (shB 0) 0 2 := by
  decide

theorem faceIdShape2_VC : (∀ i j : Fin 4, i ≤ j → FaceIdShape2 baseVC (shA i j) 1 3) ∧
    (∀ i : Fin 4, FaceIdShape2 baseVC (shB i) 1 3) ∧ FaceIdShape2 baseVC (shB 0) 0 2 := by
  decide

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {k : Fin 4 → ℝ}
  (hk : -(2 * m₀) ^ 2 < Minkowski.dot k k) (μ ν : Fin 4)

include hm₀ hmass hk

/-- **The class `VA` as a one-loop limit** at one momentum below threshold. -/
theorem faceId_vDens_PL_VA :
    FaceIdPL (fun t => vDens aVA baseVA cVA Φ e m₀ t k μ ν)
      (faceIdBlockPsi baseVA cVA (vNum e 0 1 aVA baseVA cVA) (vNumE4 e 0 1 aVA) Φ m₀ 0 k
        μ ν) := by
  have hA := fun a b ρ σ => isOddG_aVA a b ρ σ
  obtain ⟨hshA, hshB, hshP⟩ := faceShapeOK_VA
  obtain ⟨hsA, hsB, hsP⟩ := faceIdShape2_VA
  exact faceId_blockDens_PL baseVA cVA ![0, 0] ![-1, -1] flowVA (by decide) (by decide) hm₀ hk
    (by intro r hr; fin_cases r <;> simp_all [baseVA, cVA]) (s := 1) (by norm_num)
    (by intro r hr; fin_cases r <;> simp_all [baseVA, cVA])
    critA_VA critB_VA _ _ _ _ (vNum_eq e 0 1 aVA baseVA cVA hA)
    (isLoopPoly_vNum e 0 1 aVA baseVA cVA) (isLoopPoly_vNumE2 e 0 1 aVA baseVA cVA)
    (fun m k a' b' i j => rb_vNum e 0 1 aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (d₁ := 1) (d₀ := 3) (by norm_num) (by norm_num)
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
    hshA hshB hshP hsA hsB hsP rfl 0
    (fun i j _ _ f hf => by
      have h : shA i j f.castSucc = 1 := by revert i j f; decide
      rw [h]; simp [cVA])
    (fun i _ f hf => by
      have h : shB i f.castSucc = 1 := by revert i f; decide
      rw [h]; simp [cVA])
    Φ hmass μ ν

/-- **The class `VB` as a one-loop limit** at one momentum below threshold. -/
theorem faceId_vDens_PL_VB :
    FaceIdPL (fun t => vDens aVB baseVB cVB Φ e m₀ t k μ ν)
      (faceIdBlockPsi baseVB cVB (vNum e 0 1 aVB baseVB cVB) (vNumE4 e 0 1 aVB) Φ m₀ 0 k
        μ ν) := by
  have hA := fun a b ρ σ => isOddG_aVB a b ρ σ
  obtain ⟨hshA, hshB, hshP⟩ := faceShapeOK_VB
  obtain ⟨hsA, hsB, hsP⟩ := faceIdShape2_VB
  exact faceId_blockDens_PL baseVB cVB ![0, 1] ![-1, 0] flowVB (by decide) (by decide) hm₀ hk
    (by intro r hr; fin_cases r <;> simp_all [baseVB, cVB]) (s := -1) (by norm_num)
    (by intro r hr; fin_cases r <;> simp_all [baseVB, cVB])
    critA_VB critB_VB _ _ _ _ (vNum_eq e 0 1 aVB baseVB cVB hA)
    (isLoopPoly_vNum e 0 1 aVB baseVB cVB) (isLoopPoly_vNumE2 e 0 1 aVB baseVB cVB)
    (fun m k a' b' i j => rb_vNum e 0 1 aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (d₁ := 2) (d₀ := 2) (by norm_num) (by norm_num)
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
    hshA hshB hshP hsA hsB hsP rfl 0
    (fun i j hij h => absurd h (by revert i j; decide))
    (fun i h => absurd h (by revert i; decide))
    Φ hmass μ ν

/-- **The class `VC` as a one-loop limit** at one momentum below threshold. -/
theorem faceId_vDens_PL_VC :
    FaceIdPL (fun t => vDens aVC baseVC cVC Φ e m₀ t k μ ν)
      (faceIdBlockPsi baseVC cVC (vNum e 0 1 aVC baseVC cVC) (vNumE4 e 0 1 aVC) Φ m₀ 1 k
        μ ν) := by
  have hA := fun a b ρ σ => isOddG_aVC a b ρ σ
  obtain ⟨hshA, hshB, hshP⟩ := faceShapeOK_VC
  obtain ⟨hsA, hsB, hsP⟩ := faceIdShape2_VC
  exact faceId_blockDens_PL baseVC cVC ![0, 1] ![-1, 0] flowVC (by decide) (by decide) hm₀ hk
    (by intro r hr; fin_cases r <;> simp_all [baseVC, cVC]) (s := 1) (by norm_num)
    (by intro r hr; fin_cases r <;> simp_all [baseVC, cVC])
    critA_VC critB_VC _ _ _ _ (vNum_eq e 0 1 aVC baseVC cVC hA)
    (isLoopPoly_vNum e 0 1 aVC baseVC cVC) (isLoopPoly_vNumE2 e 0 1 aVC baseVC cVC)
    (fun m k a' b' i j => rb_vNum e 0 1 aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e 0 1 aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (d₁ := 1) (d₀ := 3) (by norm_num) (by norm_num)
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
    hshA hshB hshP hsA hsB hsP rfl 1
    (fun i j _ _ f hf => by
      have h : shA i j f.castSucc = 2 := by revert i j f; decide
      rw [h]; simp [cVC])
    (fun i _ f hf => by
      have h : shB i f.castSucc = 2 := by revert i f; decide
      rw [h]; simp [cVC])
    Φ hmass μ ν

end Classes

end QED.GradedProof.RPi4

end
