/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1EPvCont
public import QED.GradedProof.RPi4LightClass

/-!
# (X₁) piece E: the two-loop classes of `Π⁽⁴⁾` are continuous at `k = 0`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece E. The `ε → 0⁺` limits of the two-loop classes `VA`, `VB`, `VC` of the
order-`e⁴` vacuum polarization are the explicit values `QED.GradedProof.RPi4.vVal`
(`QED.GradedProof.RPi4.vpjv_VA` etc.): block sums of three-flavour combinations `triVal` of
parametric values of pieces with seven and eight lines. Each is continuous at `k = 0`; the chain
follows `QED.GradedProof.RPi4.lightBdd_vVal_VA` with
`QED.GradedProof.X1E.continuousAt_pvOf_zero` in place of the light-pair bound.

* `continuousAt_vpPiece`: a piece with positive masses;
* `continuousAt_triVal`, `continuousAt_blockVal`;
* `continuousAt_vVal_VA`, `continuousAt_vVal_VB`, `continuousAt_vVal_VC`.
-/

@[expose] public section

open Complex Filter Topology Matrix MeasureTheory

namespace QED.GradedProof.X1E

open QED.GradedProof.VP2 QED.GradedProof.SE2 QED.GradedProof.RPi4
open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet)

/-- **A piece of a vacuum-polarization class is continuous at `k = 0`**, for masses with
`Mᵢ² ≥ c > 0`. -/
theorem continuousAt_vpPiece (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) {n : ℕ}
    (hn : n = 6 ∨ n = 7) (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ) {cc : ℝ}
    (hc : 0 < cc) (hMs : ∀ l, cc ≤ Ms l ^ 2) {E : Finset (Fin (n + 1))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun i => base (sh i))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (hpoly : ∀ k, IsLoopPoly 2 (n - 3) (N k))
    (hB : ∀ k, RefinedBound (castLoopMatrix fun i => base (sh i)) E 4 (N k))
    {d : ℕ} (hk : ∀ ℓ, IsLoopPoly 1 d fun y => N (y 0) ℓ) :
    ContinuousAt (fun k => pvOf (N k) (castLoopMatrix fun l => base (sh l))
      (fun l => c (sh l) • k) Ms) 0 := by
  have hcrit' := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit
  have h6 : 6 ≤ n := by omega
  let D : SEData :=
    { m := n
      α := castLoopMatrix fun i => base (sh i)
      cs := fun i => c (sh i)
      M := Ms
      E := E
      hm := h6
      hcrit := hcrit' }
  have hspan : ∃ a b, D.α a 0 * D.α b 1 - D.α a 1 * D.α b 0 ≠ 0 :=
    NoSubdivergence.span (α := D.α) fun k => by
      have := D.hcrit.noSubdivergenceOfOrder k; omega
  have hQ : ∀ k, ∃ Q : LoopQuartic, Q.eval = N k ∧
      ∀ q, IntegrableOn (QED.TwoLoop.PauliZeroLimit.paramNum Q D.α q D.M) (simplexSet D.m) :=
    fun k => by
      obtain ⟨Q, hq, hb, he⟩ := good_of_poly hn (hpoly k) (hB k)
      exact ⟨Q, he, fun q => integrableOn_paramNum_good (D := D) ⟨hq, hb⟩ q⟩
  exact continuousAt_pvOf_zero (show 5 ≤ n by omega) D.α hspan D.cs D.M hc hMs N hk hQ

theorem le_sq_of_le {a x : ℝ} (ha : 0 ≤ a) (h : a ≤ x) : a ^ 2 ≤ x ^ 2 :=
  pow_le_pow_left₀ ha h 2

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀) {mγ Λ : ℝ}
  (hmγ : 0 < mγ) (hΛ : 0 < Λ)

include hm₀ hmγ hΛ

/-- **The three-flavour combination is continuous at `k = 0`.** -/
theorem continuousAt_triVal
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
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (μ ν : Fin 4) :
    ContinuousAt (fun k => triVal base c Num E4 mγ Λ M X Y k μ ν) 0 := by
  set cc : ℝ := min (m₀ ^ 2) (min (mγ ^ 2) (Λ ^ 2)) with hcc
  have hcc0 : 0 < cc := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have h1 : cc ≤ m₀ ^ 2 := min_le_left _ _
  have h2 : cc ≤ mγ ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : cc ≤ Λ ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hf : ∀ x, m₀ ≤ x → cc ≤ x ^ 2 := fun x hx => h1.trans (le_sq_of_le hm₀.le hx)
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
  have PA : ∀ i j : Fin 4, ContinuousAt (fun k => if i ≤ j then
      pieceVal base c (shA i j) ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2,
        mA M X Y i j 3, X, Y, mγ, Λ]
        (fun k ℓ a b => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          Num M k ℓ a b) k μ ν
      else 0) 0 := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true, pieceVal]
      refine continuousAt_vpPiece base c (Or.inr rfl) (shA i j) _ hcc0 (fun l => ?_) (hcA i j)
        (fun k ℓ => C * Num M k ℓ μ ν) (fun k => (hP M k μ ν).const_mul _)
        (fun k => (hBA M k μ ν i j).const_mul _) (fun ℓ => (hk M ℓ μ ν).const_mul _)
      have hmA : ∀ l, m₀ ≤ mA M X Y i j l := fun l => by unfold mA; split_ifs <;> assumption
      fin_cases l
      exacts [hf _ (hmA 0), hf _ (hmA 1), hf _ (hmA 2), hf _ (hmA 3), hf _ hX, hf _ hY, h2, h3]
    · simp only [hij, ite_false]
      exact continuousAt_const
  -- the four pieces with seven lines
  have PB : ∀ i : Fin 4, ContinuousAt (fun k =>
      pieceVal base c (shB i) ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, mγ, Λ]
        (fun k ℓ a b => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ a b - Num M k ℓ a b))
        k μ ν) 0 := by
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
    simp only [pieceVal]
    refine continuousAt_vpPiece base c (Or.inl rfl) (shB i) _ hcc0 (fun l => ?_) (hcB i)
      (fun k ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ μ ν - Num M k ℓ μ ν)) hpoly
      (fun k => (((hBB X k μ ν i).sub (hBB M k μ ν i)).const_mul _).mono (by decide) le_rfl)
      (fun ℓ => ((hk X ℓ μ ν).sub (hk M ℓ μ ν)).const_mul _)
    have hmB : ∀ l, m₀ ≤ mB X Y i l := fun l => by unfold mB; split_ifs <;> assumption
    fin_cases l
    exacts [hf _ (hmB 0), hf _ (hmB 1), hf _ (hmB 2), hf _ (hmB 3), hf _ hY, h2, h3]
  -- the padded piece
  have PC : ContinuousAt (fun k =>
      pieceVal base c (shB 0) ![Y, Y, Y, Y, Y, mγ, Λ]
        (fun k ℓ a b => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * E4 k a b *
          propDenom Y 0 (fm base (ppc c k) 0 ℓ)) k μ ν) 0 := by
    simp only [pieceVal]
    refine continuousAt_vpPiece base c (Or.inl rfl) (shB 0) _ hcc0 (fun l => ?_) (hcB 0)
      (fun k ℓ => C * E4 k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
      (fun k => ((IsLoopPoly.const (n := 0) _).mul
        ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0)).mono (by norm_num))
      (fun k => ((rb_propDenom_pad base (ppc c k) (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0).const_mul _).mono (by decide) (by norm_num))
      (fun ℓ => ((hk4 ℓ μ ν).const_mul C).mul
        ((isLoopAffine_lineMomentum_k base c _ ℓ).isLoopPoly_propDenom Y 0))
    fin_cases l
    exacts [hf _ hY, hf _ hY, hf _ hY, hf _ hY, hf _ hY, h2, h3]
  exact ((tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => PA i j).add
    (tendsto_finsetSum _ fun i _ => PB i)).add PC

/-- **The block-summed flavour sum is continuous at `k = 0`.** -/
theorem continuousAt_blockVal
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
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) (μ ν : Fin 4) :
    ContinuousAt (fun k => blockVal base c Num E4 Φ m₀ mγ Λ k μ ν) 0 := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  exact tendsto_finsetSum _ fun f _ => (continuousAt_triVal base c hm₀ hmγ hΛ hcA hcB Num E0 E2
    E4 hE hP hP2 hBA hBB hk (hmass f) hX (by linarith) μ ν).const_mul (Φ.coeff f : ℂ)

end Setting

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (μ ν : Fin 4)

include hm₀ hmass ha hb

/-- **The class `VA` is continuous at `k = 0`.** -/
theorem continuousAt_vVal_VA :
    ContinuousAt (fun k => vVal aVA baseVA cVA Φ e m₀ a b k μ ν) 0 :=
  continuousAt_blockVal baseVA cVA hm₀ ha hb critA_VA critB_VA _ _ _ _
    (vNum_eq e a b aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_vNum e a b aVA baseVA cVA) (isLoopPoly_vNumE2 e a b aVA baseVA cVA)
    (fun m k a' b' i j => rb_vNum e a b aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e a b aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e a b aVA baseVA cVA) Φ hmass μ ν

/-- **The class `VB` is continuous at `k = 0`.** -/
theorem continuousAt_vVal_VB :
    ContinuousAt (fun k => vVal aVB baseVB cVB Φ e m₀ a b k μ ν) 0 :=
  continuousAt_blockVal baseVB cVB hm₀ ha hb critA_VB critB_VB _ _ _ _
    (vNum_eq e a b aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_vNum e a b aVB baseVB cVB) (isLoopPoly_vNumE2 e a b aVB baseVB cVB)
    (fun m k a' b' i j => rb_vNum e a b aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e a b aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e a b aVB baseVB cVB) Φ hmass μ ν

/-- **The class `VC` is continuous at `k = 0`.** -/
theorem continuousAt_vVal_VC :
    ContinuousAt (fun k => vVal aVC baseVC cVC Φ e m₀ a b k μ ν) 0 :=
  continuousAt_blockVal baseVC cVC hm₀ ha hb critA_VC critB_VC _ _ _ _
    (vNum_eq e a b aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_vNum e a b aVC baseVC cVC) (isLoopPoly_vNumE2 e a b aVC baseVC cVC)
    (fun m k a' b' i j => rb_vNum e a b aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (fun m k a' b' i => rb_vNum e a b aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a' b')
    (isLoopPoly_vNum_k e a b aVC baseVC cVC) Φ hmass μ ν

end Classes

end QED.GradedProof.X1E

end
