/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceIdRayBNum
public import QED.GradedProof.RPi4InstClass
public import QED.GradedProof.RPi4DecRep

/-!
# (R-Π₄) step L10, T2.UV: the rate along the ray of the three vacuum-polarization classes

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10: input (B) of
`QED.GradedProof.RPi4.faceIdRay_of_size_rate`. The class densities `vDens` of `VA`, `VB`, `VC`
satisfy `‖u · vDens(u, k'(s)) - L(s)‖ ≤ B s^p u^{-1/2}` for `u ≥ s ≥ 1` along the ray
`k'(s) = tiltVec √s s` (`FaceIdRayRateB`). The assembly is that of
`QED.GradedProof.RPi4.heavyRate_vDens_VA` (file `RPi4InstClass`) with the piece rate
`QED.GradedProof.RPi4.faceIdRayB_vpPiece_of_nodes` in place of `heavyRate_vpPiece`; no segment
of momenta below threshold is needed (the ray is Euclidean).

* `faceIdRayB_triDens` (the fifteen pieces of `triDens`), `faceIdRayB_blockDens` (block sum);
* `faceIdRayB_vDens_VA`, `faceIdRayB_vDens_VB`, `faceIdRayB_vDens_VC`: the three classes;
* **`faceIdRayB_cfg4_VA`**, **`faceIdRayB_cfg4_VB`**, **`faceIdRayB_cfg4_VC`**: the three
  classes at `decCfg 1 4`, `m₀ = 1`, `(μ, ν) = (2, 3)`, as consumed by `faceIdRay_of_size_rate`.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix
open scoped Real

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.GradedProof.SE2
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance

/-! ### The fifteen pieces and the block sum -/

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1])
  {m₀ : ℝ} (hm₀ : 0 < m₀)

include hflow hrow hrow4 hm₀

/-- **The rate along the ray of the fifteen pieces of `triDens`.** Hypotheses as in
`QED.GradedProof.RPi4.pairInt_triVal`, plus representatives of the numerators of degree `≤ d₁`
along loop `1` and `≤ d₀` along loop `0` (without quartic part for the differences), the face
blocks of the merged shapes, and line `0` of row `(1, 0)` (the padded piece). -/
theorem faceIdRayB_triDens
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
    (hshP : FaceShapeOK base (fun l : Fin 6 => shB 0 l.castSucc) 0 2)
    (hb0 : base 0 = ![1, 0])
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (μ ν : Fin 4) :
    FaceIdRayRateB fun t k => triDens base c Num E4 M X Y t k μ ν := by
  have hE4 : ∀ k ℓ a b, E4 k a b =
      1 / 12 * (Num 2 k ℓ a b - 4 * Num 1 k ℓ a b + 3 * Num 0 k ℓ a b) := fun k ℓ a b => by
    rw [hE, hE, hE]; push_cast; ring
  have hk4 : ∀ (ℓ : Fin 2 → Fin 4 → ℝ) a b, IsLoopPoly 1 d fun y => E4 (y 0) a b := by
    intro ℓ a b
    have e : (fun y : Fin 1 → Fin 4 → ℝ => E4 (y 0) a b) = fun y =>
        1 / 12 * (Num 2 (y 0) ℓ a b - 4 * Num 1 (y 0) ℓ a b + 3 * Num 0 (y 0) ℓ a b) :=
      funext fun y => hE4 (y 0) ℓ a b
    rw [e]
    exact (((hk 2 ℓ a b).sub ((hk 1 ℓ a b).const_mul 4)).add
      ((hk 0 ℓ a b).const_mul 3)).const_mul _
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
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
  -- the padded piece
  have PC : FaceIdRayRateB fun t k =>
      pairDens (fun ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
        (castLoopMatrix fun l : Fin 6 => base (shB 0 l.castSucc))
        (fun l => c (shB 0 l.castSucc) • k) ![Y, Y, Y, Y, Y, 0] (Fin.last 5) t := by
    obtain ⟨⟨a1, b1, c1⟩, ⟨a0, b0, c0⟩⟩ := hshP
    obtain ⟨haf1, haf0⟩ := affDeg_row10 base ((0 : Fin 4).castSucc) hb0
    exact faceIdRayB_vpPiece_of_nodes base c y₁ y₂ hflow hrow hrow4 (Or.inl rfl) (shB 0)
      (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]) (hcB 0)
      (fun k ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
      (fun k => ((IsLoopPoly.const (n := 0) _).mul
        ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0)).mono (by norm_num))
      (fun k => ((rb_propDenom_pad base (ppc c k) (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0).const_mul _).mono (by decide) (by norm_num))
      (fun ℓ => ((hk4 ℓ μ ν).const_mul C).mul
        ((isLoopAffine_lineMomentum_k base c _ ℓ).isLoopPoly_propDenom Y 0))
      (d₁ := 0) (d₀ := 2)
      (fun k => by
        obtain ⟨Q, h0, h1, h2⟩ := exists_loopQuartic_pad base (ppc c k) 1 (C * E4 k μ ν) Y
        rw [haf1] at h1
        exact ⟨Q, h2, h1, Or.inr h0⟩)
      (fun k => by
        obtain ⟨Q, h0, h1, h2⟩ := exists_loopQuartic_pad base (ppc c k) 0 (C * E4 k μ ν) Y
        rw [haf0] at h1
        exact ⟨Q, h2, h1, Or.inr h0⟩)
      (by norm_num) (by norm_num) a1 b1 c1 a0 b0 c0 hm₀ _ rfl
      (fun l hl => by
        fin_cases l
        exacts [hY, hY, hY, hY, hY, absurd rfl hl])
  refine (((FaceIdRayRateB.sum Finset.univ fun i _ => FaceIdRayRateB.sum Finset.univ fun j _ =>
    PA i j).add (FaceIdRayRateB.sum Finset.univ fun i _ => PB i)).add PC).congr
    fun u _ t _ => ?_
  simp only [triDens, hC]

/-- **The rate along the ray of the block-summed flavour sum.** -/
theorem faceIdRayB_blockDens
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
    (hshP : FaceShapeOK base (fun l : Fin 6 => shB 0 l.castSucc) 0 2)
    (hb0 : base 0 = ![1, 0])
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) (μ ν : Fin 4) :
    FaceIdRayRateB fun t k => blockDens base c Num E4 Φ m₀ t k μ ν := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  exact FaceIdRayRateB.sum Finset.univ fun f _ => (faceIdRayB_triDens base c y₁ y₂ hflow hrow hrow4
    hm₀ hcA hcB Num E0 E2 E4 hE hP hP2 hBA hBB hk hd₁ hd₀ hD₁ hD₀ hSub₁ hSub₀ hshA hshB
    hshP hb0 (hmass f) hX (by linarith) μ ν).const_mul (Φ.coeff f : ℂ)

end Setting

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) (μ ν : Fin 4)

include hm₀ hmass

/-- **The rate along the ray of the class `VA`.** -/
theorem faceIdRayB_vDens_VA :
    FaceIdRayRateB fun t k => vDens aVA baseVA cVA Φ e m₀ t k μ ν := by
  have hA := fun a b ρ σ => isOddG_aVA a b ρ σ
  obtain ⟨hshA, hshB, hshP⟩ := faceShapeOK_VA
  exact faceIdRayB_blockDens baseVA cVA ![0, 0] ![-1, -1] flowVA (by decide) (by decide) hm₀
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
    hshA hshB hshP rfl Φ hmass μ ν

/-- **The rate along the ray of the class `VB`.** -/
theorem faceIdRayB_vDens_VB :
    FaceIdRayRateB fun t k => vDens aVB baseVB cVB Φ e m₀ t k μ ν := by
  have hA := fun a b ρ σ => isOddG_aVB a b ρ σ
  obtain ⟨hshA, hshB, hshP⟩ := faceShapeOK_VB
  exact faceIdRayB_blockDens baseVB cVB ![0, 1] ![-1, 0] flowVB (by decide) (by decide) hm₀
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
    hshA hshB hshP rfl Φ hmass μ ν

/-- **The rate along the ray of the class `VC`.** -/
theorem faceIdRayB_vDens_VC :
    FaceIdRayRateB fun t k => vDens aVC baseVC cVC Φ e m₀ t k μ ν := by
  have hA := fun a b ρ σ => isOddG_aVC a b ρ σ
  obtain ⟨hshA, hshB, hshP⟩ := faceShapeOK_VC
  exact faceIdRayB_blockDens baseVC cVC ![0, 1] ![-1, 0] flowVC (by decide) (by decide) hm₀
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
    hshA hshB hshP rfl Φ hmass μ ν

end Classes

/-! ### The three classes at `decCfg 1 4` -/

theorem faceIdRayB_cfg4_mass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
  dec_cfg_mass_ge le_rfl one_pos (by norm_num)

/-- **Input (B) of `faceIdRay_of_size_rate` for the class `VA`.** -/
theorem faceIdRayB_cfg4_VA (e : ℝ) :
    FaceIdRayRateB fun u k => vDens aVA baseVA cVA (decCfg 1 4) e 1 u k 2 3 :=
  faceIdRayB_vDens_VA (decCfg 1 4) one_pos faceIdRayB_cfg4_mass e 2 3

/-- **Input (B) of `faceIdRay_of_size_rate` for the class `VB`.** -/
theorem faceIdRayB_cfg4_VB (e : ℝ) :
    FaceIdRayRateB fun u k => vDens aVB baseVB cVB (decCfg 1 4) e 1 u k 2 3 :=
  faceIdRayB_vDens_VB (decCfg 1 4) one_pos faceIdRayB_cfg4_mass e 2 3

/-- **Input (B) of `faceIdRay_of_size_rate` for the class `VC`.** -/
theorem faceIdRayB_cfg4_VC (e : ℝ) :
    FaceIdRayRateB fun u k => vDens aVC baseVC cVC (decCfg 1 4) e 1 u k 2 3 :=
  faceIdRayB_vDens_VC (decCfg 1 4) one_pos faceIdRayB_cfg4_mass e 2 3

end QED.GradedProof.RPi4

end
