/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdVpGen
public import QED.GradedProof.RPi4InstClass

/-!
# (R-Π₄) step L6d3: the fifteen pieces as one-loop limits

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d3. The density
`triDens` of the three-flavour combination (the fifteen merged pieces) satisfies `FaceIdPL` at
one momentum `k` below threshold, with `Ψ = faceIdTriPsi` the sum of the face integrals
`faceIdPsi = faceIdPsi1 + faceIdPsi0` of the pieces (`faceId_triDens_PL`). The hypotheses are
those of `heavyRate_triDens` (without the momentum degree), the extra face-block conditions
`FaceIdShape2` (decidable), the rest momenta of the class (`c ∈ {0, 1}` on rows `(1, 0)`,
`c ∈ {0, s}` on rows `(0, 1)`, `s = ±1`) and the self-energy shift `β` where a self-energy face
occurs. The slice Laplacians of the six-line numerators are constant (`faceId_lapF_const`).

* `faceIdPsi`, `FaceIdShape2`, `faceIdTriPsi`, **`faceId_triDens_PL`**.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Matrix
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

/-- **The one-loop integral of both faces of a merged piece.** -/
noncomputable def faceIdPsi {m : ℕ} (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
    (sh : Fin (m + 2) → Fin 5) (N : (Fin 2 → Fin 4 → ℝ) → ℂ) (Ms : Fin (m + 1) → ℝ) (β : ℝ)
    (k : Fin 4 → ℝ) (ε : ℝ) : ℂ :=
  faceIdPsi1 base c sh N Ms β k ε + faceIdPsi0 base c sh N Ms k ε

/-- The face-block conditions beyond `FaceShapeOK`: the loop-`0` block has at least three lines,
and a block of three lines has numerator degree `≤ 2` along its loop. -/
def FaceIdShape2 {m : ℕ} (base : Fin 5 → Fin 2 → ℤ) (sh : Fin (m + 2) → Fin 5) (d₁ d₀ : ℕ) :
    Prop :=
  3 ≤ faceIdCard base sh ![0, 1] ∧ (faceIdCard base sh ![1, 0] = 3 → d₁ ≤ 2) ∧
    (faceIdCard base sh ![0, 1] = 3 → d₀ ≤ 2)

instance {m : ℕ} (base : Fin 5 → Fin 2 → ℤ) (sh : Fin (m + 2) → Fin 5) (d₁ d₀ : ℕ) :
    Decidable (FaceIdShape2 base sh d₁ d₀) := by
  unfold FaceIdShape2 faceIdCard; infer_instance

/-- **The face integrals of the fifteen pieces of `triDens`.** -/
noncomputable def faceIdTriPsi (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
    (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) (M X Y β : ℝ) (k : Fin 4 → ℝ) (μ ν : Fin 4)
    (ε : ℝ) : ℂ :=
  (∑ i : Fin 4, ∑ j : Fin 4, if i ≤ j then
      faceIdPsi base c (shA i j) (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k ℓ μ ν)
        ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0] β k ε
    else 0) +
  ∑ i : Fin 4, faceIdPsi base c (shB i) (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        (Num X k ℓ μ ν - Num M k ℓ μ ν))
      ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] β k ε +
  faceIdPsi base c (shB 0) (fun ℓ => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
      E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ)) ![Y, Y, Y, Y, Y, 0] β k ε

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

/-- **The fifteen pieces of `triDens` as one-loop limits.** -/
theorem faceId_triDens_PL
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
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (μ ν : Fin 4) :
    FaceIdPL (fun t => triDens base c Num E4 M X Y t k μ ν)
      (faceIdTriPsi base c Num E4 M X Y β k μ ν) := by
  have hk' : -(4 * m₀ ^ 2) < Minkowski.dot (s • k) (s • k) := by
    rcases hs with rfl | rfl
    · rw [one_smul]; linarith
    · rw [neg_one_smul, QED.GradedProof.SE2.dot_neg_neg]; linarith
  have hpp : ∀ {m : ℕ} (sh : Fin (m + 2) → Fin 5) (l : Fin (m + 1)),
      base (sh l.castSucc) = ![0, 1] → c (sh l.castSucc) • k = 0 ∨ c (sh l.castSucc) • k = s • k :=
    fun sh l hl => by rcases hc0 _ hl with h | h <;> simp [h]
  have hcl : ∀ {m : ℕ} (sh : Fin (m + 2) → Fin 5) (l : Fin (m + 1)),
      base (sh l.castSucc) = ![1, 0] → c (sh l.castSucc) = 0 ∨ c (sh l.castSucc) = 1 :=
    fun sh l hl => hc1 _ hl
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
  have hl6 : ∀ i j, shA i j (Fin.last 6).castSucc = 4 := fun i j => rfl
  have hl5 : ∀ i, shB i (Fin.last 5).castSucc = 4 := fun i => rfl
  -- the ten pieces with eight lines
  have PA : ∀ i j : Fin 4, FaceIdPL (fun t => if i ≤ j then
      pairDens (fun ℓ => C * Num M k ℓ μ ν)
        (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
        (fun l => c (shA i j l.castSucc) • k)
        ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0]
        (Fin.last 6) t
      else 0) fun ε => if i ≤ j then
        faceIdPsi base c (shA i j) (fun ℓ => C * Num M k ℓ μ ν)
          ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2, mA M X Y i j 3, X, Y, 0] β k ε
      else 0 := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true]
      obtain ⟨⟨a1, b1, c1⟩, ⟨a0, b0, c0⟩⟩ := hshA i j hij
      obtain ⟨e0, e1, e2⟩ := hsA i j hij
      have hMf : ∀ l, m₀ ≤ mA M X Y i j l := fun l => by unfold mA; split_ifs <;> assumption
      exact faceId_vp_PL_gen base c hrow hrow4 y₁ y₂ hflow (Or.inr rfl) (shA i j)
        (fun l => by fin_cases l <;> simp [shA, Fin.ext_iff] <;> omega) (hcA i j)
        (fun ℓ => C * Num M k ℓ μ ν) ((hP M k μ ν).const_mul _)
        ((hBA M k μ ν i j).const_mul _) hm₀ _ rfl
        (fun l hl => by
          fin_cases l
          exacts [hMf 0, hMf 1, hMf 2, hMf 3, hX, hY, absurd rfl hl]) hk
        (by obtain ⟨Q, h1, h2⟩ := hD₁ C M k μ ν; exact ⟨Q, h2, h1, Or.inl rfl⟩)
        (by obtain ⟨Q, h1, h2⟩ := hD₀ C M k μ ν; exact ⟨Q, h2, h1, Or.inl rfl⟩)
        hd₁ hd₀ a1 b1 e1 c1 e0 e2 c0 (hcl _) β
        (fun h f hf => by rw [hl6]; exact hβA i j hij h f hf)
        (fun h => absurd h (by omega)) (fun _ => hk') (fun _ => hpp _)
        (fun h => absurd h (by omega))
    · simp only [hij, ite_false]
      exact FaceIdPL.zero
  -- the four pieces with seven lines
  have PB : ∀ i : Fin 4, FaceIdPL (fun t =>
      pairDens (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν))
        (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
        (fun l => c (shB i l.castSucc) • k)
        ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] (Fin.last 5) t)
      (faceIdPsi base c (shB i) (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        (Num X k ℓ μ ν - Num M k ℓ μ ν))
        ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, 0] β k) := by
    intro i
    have e : (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) =
        fun ℓ => (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
          (E2 k ℓ μ ν + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * E4 k μ ν) := by
      funext ℓ; rw [hE, hE]; ring
    have hq2 : IsLoopPoly 2 2 fun ℓ =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν) := by
      rw [e]
      exact ((hP2 k μ ν).add (IsLoopPoly.const _)).const_mul _
    obtain ⟨⟨a1, b1, c1⟩, ⟨a0, b0, c0⟩⟩ := hshB i
    obtain ⟨e0, e1, e2⟩ := hsB i
    have hMf : ∀ l, m₀ ≤ mB X Y i l := fun l => by unfold mB; split_ifs <;> assumption
    exact faceId_vp_PL_gen base c hrow hrow4 y₁ y₂ hflow (Or.inl rfl) (shB i)
      (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]; omega) (hcB i) _
      (hq2.mono (by norm_num))
      (((hBB X k μ ν i).sub (hBB M k μ ν i)).const_mul _ |>.mono (by decide) le_rfl) hm₀ _ rfl
      (fun l hl => by
        fin_cases l
        exacts [hMf 0, hMf 1, hMf 2, hMf 3, hY, absurd rfl hl]) hk
      (by
        obtain ⟨Q, h0, h1, h2⟩ := hSub₁ (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) X M k μ ν
        exact ⟨Q, h2, h1, Or.inr h0⟩)
      (by
        obtain ⟨Q, h0, h1, h2⟩ := hSub₀ (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) X M k μ ν
        exact ⟨Q, h2, h1, Or.inr h0⟩)
      hd₁ hd₀ a1 b1 e1 c1 e0 e2 c0 (hcl _) β
      (fun h f hf => by rw [hl5]; exact hβB i h f hf)
      (fun _ _ => by
        obtain ⟨C', hC'⟩ := faceId_lapF_const hq2 1
        exact ⟨C', fun _ => hC' _⟩) (fun _ => hk') (fun _ => hpp _)
      (fun _ _ => by
        obtain ⟨C', hC'⟩ := faceId_lapF_const hq2 0
        exact ⟨C', fun _ => hC' _⟩)
  -- the padded piece
  have PC : FaceIdPL (fun t =>
      pairDens (fun ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
        (castLoopMatrix fun l : Fin 6 => base (shB 0 l.castSucc))
        (fun l => c (shB 0 l.castSucc) • k) ![Y, Y, Y, Y, Y, 0] (Fin.last 5) t)
      (faceIdPsi base c (shB 0) (fun ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
        ![Y, Y, Y, Y, Y, 0] β k) := by
    have hq2 : IsLoopPoly 2 2 fun ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ) :=
      ((IsLoopPoly.const (n := 0) _).mul
        ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0)).mono (by norm_num)
    obtain ⟨⟨a1, b1, c1⟩, ⟨a0, b0, c0⟩⟩ := hshP
    obtain ⟨e0, e1, e2⟩ := hsP
    obtain ⟨haf1, haf0⟩ := affDeg_row10 base ((0 : Fin 4).castSucc) hb0
    exact faceId_vp_PL_gen base c hrow hrow4 y₁ y₂ hflow (Or.inl rfl) (shB 0)
      (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]) (hcB 0) _ (hq2.mono (by norm_num))
      (((rb_propDenom_pad base (ppc c k) (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0).const_mul _).mono (by decide) (by norm_num)) hm₀ _ rfl
      (fun l hl => by
        fin_cases l
        exacts [hY, hY, hY, hY, hY, absurd rfl hl]) hk (d₁ := 0) (d₀ := 2)
      (by
        obtain ⟨Q, h0, h1, h2⟩ := exists_loopQuartic_pad base (ppc c k) 1 (C * E4 k μ ν) Y
        rw [haf1] at h1
        exact ⟨Q, h2, h1, Or.inr h0⟩)
      (by
        obtain ⟨Q, h0, h1, h2⟩ := exists_loopQuartic_pad base (ppc c k) 0 (C * E4 k μ ν) Y
        rw [haf0] at h1
        exact ⟨Q, h2, h1, Or.inr h0⟩)
      (by norm_num) (by norm_num) a1 b1 e1 c1 e0 e2 c0 (hcl _) β
      (fun h f hf => by rw [hl5]; exact hβB 0 h f hf)
      (fun _ _ => by
        obtain ⟨C', hC'⟩ := faceId_lapF_const hq2 1
        exact ⟨C', fun _ => hC' _⟩) (fun _ => hk') (fun _ => hpp _)
      (fun _ _ => by
        obtain ⟨C', hC'⟩ := faceId_lapF_const hq2 0
        exact ⟨C', fun _ => hC' _⟩)
  refine (((FaceIdPL.sum Finset.univ fun i _ => FaceIdPL.sum Finset.univ fun j _ =>
    PA i j).add (FaceIdPL.sum Finset.univ fun i _ => PB i)).add PC).congr
    (fun t => ?_) fun ε _ => ?_
  · simp only [triDens, hC]
  · simp only [faceIdTriPsi, hC]

end Setting

end QED.GradedProof.RPi4

end
