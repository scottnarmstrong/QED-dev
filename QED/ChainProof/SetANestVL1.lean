/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetANestVPiece
public import QED.ChainProof.SetANestVRB
public import QED.GradedProof.VP2VLim

/-!
# The spatial integral of the inner energy integral of `VA`, `VB`, `VC`

Helper level for the set (a) headline (HA₆), obligation (N), step NL for `VA`, `VB`, `VC`: the
analytic core (`hB`) of the nested form, in integrated form. For the block-summed two-loop
vacuum-polarization integrand `F = vSumF` of each class, at every `ε > 0` and photon indices,

`∫ d⁶v |∫ dt F_ε(k; t, v)| ≤ C (1 + Σ_μ k_μ²)⁴`

with `C` independent of the photon momentum `k`, together with the integrability of both
stages at every `k` (`EL1`).

* `EL1 F`: the property; closed under sums, multiples, pointwise equality (`EL1.add`, …);
* `el1_piece`: a piece over a shape of a vacuum-polarization routing, from
  `QED.ChainProof.SetANestV.integral_norm_energyIntegral_le` and the additive numerator bound
  `QED.ChainProof.SetANestV.RBK`;
* `el1_pieceA`, `el1_pieceB`, `el1_gTriple`, `el1_gBlock`: the pieces with eight and seven lines,
  the three-flavour combination and the flavour sum, as in
  `QED.ChainProof.SetASpec.saUj_gTriple`, `saUj_gBlock`;
* **`el1_VA`**, **`el1_VB`**, **`el1_VC`**.

No condition on the masses is needed: at `ε > 0` no denominator vanishes.
-/

@[expose] public section

open Complex MeasureTheory Filter

namespace QED.ChainProof.SetANestV

open QED.Integration.TwoLoop (loopMomenta lineDenom lineMomentum castLoopMatrix LoopQuartic
  IntNoSubdivergenceRefined noSubdivergenceRefined_castLoopMatrix_iff loopNorm lineWeight)
open QED.TwoLoop.Bridge (IsLoopPoly propDenom)

/-- **The spatial integral of the energy integral grows at most like `(1 + Σ k²)⁴`**, at every
`ε > 0` and indices, with both stages integrable. -/
def EL1 (F : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ i j : Fin 4, ∃ C : ℝ, ∀ k : Fin 4 → ℝ,
    (∀ v : Fin 2 → Fin 3 → ℝ, Integrable fun t : Fin 2 → ℝ => F ε k (loopMomenta t v) i j) ∧
    Integrable (fun v : Fin 2 → Fin 3 → ℝ => ∫ t : Fin 2 → ℝ, F ε k (loopMomenta t v) i j) ∧
    ∫ v : Fin 2 → Fin 3 → ℝ, ‖∫ t : Fin 2 → ℝ, F ε k (loopMomenta t v) i j‖ ≤
      C * (1 + kSq k) ^ 4

namespace EL1

variable {F G : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}

theorem add (hF : EL1 F) (hG : EL1 G) : EL1 fun ε k ℓ i j => F ε k ℓ i j + G ε k ℓ i j := by
  intro ε hε i j
  obtain ⟨C, hC⟩ := hF ε hε i j
  obtain ⟨D, hD⟩ := hG ε hε i j
  refine ⟨C + D, fun k => ?_⟩
  obtain ⟨f1, f2, f3⟩ := hC k
  obtain ⟨g1, g2, g3⟩ := hD k
  have hs : ∀ v : Fin 2 → Fin 3 → ℝ, (∫ t : Fin 2 → ℝ,
      F ε k (loopMomenta t v) i j + G ε k (loopMomenta t v) i j) =
      (∫ t : Fin 2 → ℝ, F ε k (loopMomenta t v) i j) +
        ∫ t : Fin 2 → ℝ, G ε k (loopMomenta t v) i j :=
    fun v => integral_add (f1 v) (g1 v)
  refine ⟨fun v => (f1 v).add (g1 v), ?_, ?_⟩
  · simp only [hs]
    exact f2.add g2
  · simp only [hs]
    calc ∫ v, ‖(∫ t : Fin 2 → ℝ, F ε k (loopMomenta t v) i j) +
          ∫ t : Fin 2 → ℝ, G ε k (loopMomenta t v) i j‖
        ≤ ∫ v, (‖∫ t : Fin 2 → ℝ, F ε k (loopMomenta t v) i j‖ +
          ‖∫ t : Fin 2 → ℝ, G ε k (loopMomenta t v) i j‖) :=
          integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _)
            (f2.norm.add g2.norm) (Eventually.of_forall fun v => norm_add_le _ _)
      _ = (∫ v, ‖∫ t : Fin 2 → ℝ, F ε k (loopMomenta t v) i j‖) +
          ∫ v, ‖∫ t : Fin 2 → ℝ, G ε k (loopMomenta t v) i j‖ := integral_add f2.norm g2.norm
      _ ≤ C * (1 + kSq k) ^ 4 + D * (1 + kSq k) ^ 4 := add_le_add f3 g3
      _ = _ := by ring

theorem mul (hF : EL1 F) (c : ℝ → ℂ) : EL1 fun ε k ℓ i j => c ε * F ε k ℓ i j := by
  intro ε hε i j
  obtain ⟨C, hC⟩ := hF ε hε i j
  refine ⟨‖c ε‖ * C, fun k => ?_⟩
  obtain ⟨f1, f2, f3⟩ := hC k
  refine ⟨fun v => (f1 v).const_mul _, ?_, ?_⟩
  · simp only [integral_const_mul]
    exact f2.const_mul _
  · simp only [integral_const_mul, norm_mul]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left f3 (norm_nonneg _)

theorem const_mul (hF : EL1 F) (c : ℂ) : EL1 fun ε k ℓ i j => c * F ε k ℓ i j :=
  hF.mul fun _ => c

theorem congr (hF : EL1 F) (e : ∀ ε : ℝ, 0 < ε → ∀ k ℓ i j, F ε k ℓ i j = G ε k ℓ i j) :
    EL1 G := by
  intro ε hε i j
  obtain ⟨C, hC⟩ := hF ε hε i j
  refine ⟨C, fun k => ?_⟩
  simp only [← e ε hε]
  exact hC k

theorem zero : EL1 fun _ _ _ _ _ => 0 := fun ε _ i j =>
  ⟨0, fun k => ⟨fun v => integrable_zero _ _ _, by simp, by simp⟩⟩

theorem sum {ι : Type*} (s : Finset ι)
    {F : ι → ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ}
    (hF : ∀ a ∈ s, EL1 (F a)) : EL1 fun ε k ℓ i j => ∑ a ∈ s, F a ε k ℓ i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : EL1 fun _ _ _ _ _ => 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hF b (Finset.mem_insert_of_mem hb))

end EL1

/-- A family bounded in `k`, constant in the loop momenta. -/
theorem RBK.bdd {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {g : (Fin 4 → ℝ) → ℂ} {D : ℝ}
    (hg : ∀ k, ‖g k‖ ≤ D) : RBK α ∅ 0 fun k _ => g k := by
  have hD : 0 ≤ D := (norm_nonneg _).trans (hg 0)
  exact ⟨D, hD, fun k A _ ℓ => by simpa [QED.Integration.TwoLoop.lineWeight] using hg k⟩

/-! ### A piece -/

section Piece

open QED.GradedProof.VP2 (good_of_poly)

/-- **A piece over a shape of a vacuum-polarization routing** is `EL1`, under the additive bound
on its numerator. -/
theorem el1_piece (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ) {E : Finset (Fin (n + 1))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun i => base (sh i))
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hpoly : ∀ k i j, IsLoopPoly 2 (n - 3) fun ℓ => N k ℓ i j)
    (hB : ∀ i j, RBK (castLoopMatrix fun i => base (sh i)) E 4 fun k ℓ => N k ℓ i j) :
    EL1 fun ε k ℓ i j => N k ℓ i j * ∏ l,
      (propDenom (Ms l) ε (lineMomentum (castLoopMatrix base) (fun r => c r • k) (sh l) ℓ))⁻¹ := by
  intro ε hε i j
  have hcrit' := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit
  set α : Fin (n + 1) → Fin 2 → ℝ := castLoopMatrix fun i => base (sh i) with hα
  have hgood := fun k => good_of_poly hn (hpoly k i j) ((hB i j).refinedBound k)
  choose Q hq _ he using hgood
  have hdeg : 7 ≤ n ∨ (6 ≤ n ∧ ∀ k, (Q k).quart = 0) := by
    rcases hn with rfl | rfl
    · exact Or.inr ⟨le_rfl, fun k => (hq k).resolve_left (by norm_num)⟩
    · exact Or.inl le_rfl
  obtain ⟨Cb, hCb, hBk⟩ := hB i j
  have hB' : ∀ k (A : Matrix (Fin 2) (Fin 2) ℝ), A.PosDef → ∀ ℓ,
      ‖(Q k).eval ℓ‖ ≤ Cb * lineWeight α E A * (1 + ∑ μ, k μ ^ 2 + loopNorm A ℓ) ^ 2 := by
    intro k A hA ℓ
    rw [he k]
    refine (hBk k A hA ℓ).trans_eq ?_
    have h0 : 0 ≤ 1 + kSq k + loopNorm A ℓ := by
      linarith [kSq_nonneg k, QED.Integration.TwoLoop.loopNorm_nonneg hA ℓ]
    have e4 : Real.sqrt (1 + kSq k + loopNorm A ℓ) ^ 4 = (1 + kSq k + loopNorm A ℓ) ^ 2 := by
      rw [show Real.sqrt (1 + kSq k + loopNorm A ℓ) ^ 4 =
        (Real.sqrt (1 + kSq k + loopNorm A ℓ) ^ 2) ^ 2 by ring, Real.sq_sqrt h0]
    rw [e4]
    rfl
  obtain ⟨C, -, hC⟩ := integral_norm_energyIntegral_le α E (fun i => c (sh i)) Ms hcrit' hε Q
    hdeg hCb hB'
  refine ⟨C, fun k => ?_⟩
  have e : ∀ ℓ, N k ℓ i j * ∏ l, (propDenom (Ms l) ε
      (lineMomentum (castLoopMatrix base) (fun r => c r • k) (sh l) ℓ))⁻¹ =
      (Q k).eval ℓ * ∏ l, (lineDenom α (fun i => c (sh i) • k) Ms ε l ℓ)⁻¹ := fun ℓ => by
    rw [he k]
    rfl
  simp only [e]
  exact hC k

end Piece

section Setting

open QED.GradedProof.VP2 QED.TwoLoop.Bridge

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (mγ Λ : ℝ)

/-- **A piece with eight lines** is `EL1`. -/
theorem el1_pieceA (i j : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (Mf : Fin 4 → ℝ) (X Y : ℝ) (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hpoly : ∀ k a b, IsLoopPoly 2 4 fun ℓ => N k ℓ a b)
    (hB : ∀ a b, RBK (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun k ℓ => N k ℓ a b) :
    EL1 fun ε k ℓ a b => N k ℓ a b *
      ((∏ l : Fin 4, (propDenom (Mf l) ε (fm base (ppc c k) l ℓ))⁻¹) *
        (propDenom X ε (fm base (ppc c k) i ℓ))⁻¹ * (propDenom Y ε (fm base (ppc c k) j ℓ))⁻¹ *
        ((propDenom mγ ε (phm base (ppc c k) ℓ))⁻¹ *
          (propDenom Λ ε (phm base (ppc c k) ℓ))⁻¹)) := by
  have h := el1_piece base c (Or.inr rfl) (shA i j) ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, mγ, Λ] hcrit
    N hpoly hB
  refine h.congr fun ε _ k ℓ a b => ?_
  rw [Fin.prod_univ_eight]
  simp only [Fin.prod_univ_four, shA, Matrix.cons_val, fm, phm]
  ring

/-- **A piece with seven lines** is `EL1`. -/
theorem el1_pieceB (i : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Mf : Fin 4 → ℝ) (Y : ℝ) (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hpoly : ∀ k a b, IsLoopPoly 2 3 fun ℓ => N k ℓ a b)
    (hB : ∀ a b, RBK (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3, 4} 4
      fun k ℓ => N k ℓ a b) :
    EL1 fun ε k ℓ a b => N k ℓ a b *
      ((∏ l : Fin 4, (propDenom (Mf l) ε (fm base (ppc c k) l ℓ))⁻¹) *
        (propDenom Y ε (fm base (ppc c k) i ℓ))⁻¹ *
        ((propDenom mγ ε (phm base (ppc c k) ℓ))⁻¹ *
          (propDenom Λ ε (phm base (ppc c k) ℓ))⁻¹)) := by
  have h := el1_piece base c (Or.inl rfl) (shB i) ![Mf 0, Mf 1, Mf 2, Mf 3, Y, mγ, Λ] hcrit
    N hpoly hB
  refine h.congr fun ε _ k ℓ a b => ?_
  rw [Fin.prod_univ_seven]
  simp only [Fin.prod_univ_four, shB, Matrix.cons_val, fm, phm]
  ring

/-- **The three-flavour combination of a two-loop numerator** is `EL1`. -/
theorem el1_gTriple
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E0 E2 : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hE : ∀ m k ℓ a b, Num m k ℓ a b =
      E0 k ℓ a b + (m : ℂ) ^ 2 * E2 k ℓ a b + ((m : ℂ) ^ 2) ^ 2 * E4 k a b)
    (hP : ∀ m k a b, IsLoopPoly 2 4 fun ℓ => Num m k ℓ a b)
    (hP2 : ∀ k a b, IsLoopPoly 2 2 fun ℓ => E2 k ℓ a b)
    (hBA : ∀ m a b i j, RBK (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun k ℓ => Num m k ℓ a b)
    (hBB : ∀ m a b i, RBK (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3} 4
      fun k ℓ => Num m k ℓ a b)
    (hE4b : ∀ a b, ∃ D : ℝ, ∀ k, ‖E4 k a b‖ ≤ D)
    {M X Y : ℝ} (hMX : M ^ 2 - X ^ 2 ≠ 0)
    (hMY : M ^ 2 - Y ^ 2 ≠ 0) (hXY : X ^ 2 - Y ^ 2 ≠ 0) :
    EL1 fun ε k ℓ a b => gH base c Num mγ Λ M ε k ℓ a b +
      (triA M X Y : ℂ) * gH base c Num mγ Λ X ε k ℓ a b +
      (triB M X Y : ℂ) * gH base c Num mγ Λ Y ε k ℓ a b := by
  have h01 : (M : ℂ) ^ 2 - (X : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hMX
  have h02 : (M : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hMY
  have h12 : (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hXY
  have hd : ∀ (m ε : ℝ) (k : Fin 4 → ℝ) (l : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ),
      propDenom m ε (fm base (ppc c k) l ℓ) =
        propDenom 0 ε (fm base (ppc c k) l ℓ) + (m : ℂ) ^ 2 :=
    fun m ε k l ℓ => propDenom_eq_add m ε _
  -- the ten pieces with eight lines
  have PA : ∀ i j : Fin 4, EL1 fun ε k ℓ a b =>
      if i ≤ j then
        vD base (ppc c k) mγ Λ ε ℓ * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (E0 k ℓ a b + (M : ℂ) ^ 2 * E2 k ℓ a b + ((M : ℂ) ^ 2) ^ 2 * E4 k a b) *
          ((∏ l : Fin 4, (propDenom 0 ε (fm base (ppc c k) l ℓ) + if l ≤ i then (M : ℂ) ^ 2
              else if l ≤ j then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)⁻¹) *
            (propDenom 0 ε (fm base (ppc c k) i ℓ) + (X : ℂ) ^ 2)⁻¹ *
            (propDenom 0 ε (fm base (ppc c k) j ℓ) + (Y : ℂ) ^ 2)⁻¹)
      else 0 := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true]
      have h := el1_pieceA base c mγ Λ i j (hcA i j) (mA M X Y i j) X Y
        (fun k ℓ a b => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k ℓ a b)
        (fun k a b => (hP M k a b).const_mul _) (fun a b => (hBA M a b i j).const_mul _)
      refine h.congr fun ε _ k ℓ a b => ?_
      rw [Finset.prod_congr rfl fun l _ => by rw [hd _ ε k l ℓ, sq_mA], hd X ε k i ℓ,
        hd Y ε k j ℓ, hE]
      simp only [vD]
      ring
    · simp only [hij, ite_false]
      exact EL1.zero
  -- the four pieces with seven lines
  have PB : ∀ i : Fin 4, EL1 fun ε k ℓ a b =>
      -(vD base (ppc c k) mγ Λ ε ℓ * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
          (E2 k ℓ a b + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * E4 k a b) *
        ((∏ l : Fin 4, (propDenom 0 ε (fm base (ppc c k) l ℓ) +
            if l ≤ i then (X : ℂ) ^ 2 else (Y : ℂ) ^ 2)⁻¹) *
          (propDenom 0 ε (fm base (ppc c k) i ℓ) + (Y : ℂ) ^ 2)⁻¹) := by
    intro i
    have hpoly : ∀ k a b, IsLoopPoly 2 3 fun ℓ =>
        -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ a b - Num M k ℓ a b) := by
      intro k a b
      have e : (fun ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ a b - Num M k ℓ a b)) =
          fun ℓ => (-((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2)) *
            (E2 k ℓ a b + ((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * E4 k a b) := by
        funext ℓ; rw [hE, hE]; ring
      rw [e]
      exact (((hP2 k a b).add (IsLoopPoly.const _)).const_mul _).mono (by norm_num)
    have h := el1_pieceB base c mγ Λ i (hcB i) (mB X Y i) Y
      (fun k ℓ a b => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ a b - Num M k ℓ a b)) hpoly
      (fun a b => (((hBB X a b i).sub (hBB M a b i)).const_mul _).mono (by decide) le_rfl)
    refine h.congr fun ε _ k ℓ a b => ?_
    rw [Finset.prod_congr rfl fun l _ => by rw [hd _ ε k l ℓ, sq_mB], hd Y ε k i ℓ, hE, hE]
    simp only [vD]
    ring
  -- the padded piece
  have PC : EL1 fun ε k ℓ a b =>
      vD base (ppc c k) mγ Λ ε ℓ * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        E4 k a b * ∏ l : Fin 4, (propDenom 0 ε (fm base (ppc c k) l ℓ) + (Y : ℂ) ^ 2)⁻¹ := by
    set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
    have hb4 : ∀ a b, RBK (castLoopMatrix fun n => base (shB 0 n)) ∅ 0
        fun k (_ : Fin 2 → Fin 4 → ℝ) => C * E4 k a b := fun a b => by
      obtain ⟨D, hD⟩ := hE4b a b
      exact RBK.bdd (D := ‖C‖ * D) fun k => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hD k) (norm_nonneg _)
    have h1 := el1_pieceB base c mγ Λ 0 (hcB 0) (fun _ => Y) Y
      (fun k ℓ a b => C * E4 k a b * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
      (fun k a b => ((IsLoopPoly.const (n := 0) _).mul
        ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0)).mono (by norm_num))
      (fun a b => (((hb4 a b).mul (rbk_propDenom_pad base c (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0) (Finset.disjoint_empty_left _))).mono (by decide) (by norm_num))
    have h2 := (el1_pieceB base c mγ Λ 0 (hcB 0) (fun _ => Y) Y
      (fun k _ a b => C * E4 k a b) (fun k a b => IsLoopPoly.const _)
      (fun a b => (hb4 a b).mono (Finset.empty_subset _) (by norm_num))).mul
      (fun ε : ℝ => -((ε : ℂ) * I))
    refine (h1.add h2).congr fun ε hε k ℓ a b => ?_
    have hne := propDenom_ne_zero (M := Y) hε.ne' (fm base (ppc c k) 0 ℓ)
    have hpd : propDenom Y 0 (fm base (ppc c k) 0 ℓ) =
        propDenom Y ε (fm base (ppc c k) 0 ℓ) + (ε : ℂ) * I := by
      simp only [propDenom]; push_cast; ring
    rw [hpd, show (∏ l : Fin 4, (propDenom 0 ε (fm base (ppc c k) l ℓ) + (Y : ℂ) ^ 2)⁻¹) =
        ∏ l : Fin 4, (propDenom Y ε (fm base (ppc c k) l ℓ))⁻¹ from
      Finset.prod_congr rfl fun l _ => by rw [hd Y ε k l ℓ]]
    simp only [vD, Fin.prod_univ_four]
    field_simp
    ring
  have hS := ((EL1.sum Finset.univ fun i _ => EL1.sum Finset.univ fun j _ => PA i j).add
    (EL1.sum Finset.univ fun i _ => PB i)).add PC
  refine hS.congr fun ε hε k ℓ a b => ?_
  have nz : ∀ (m : ℝ) (l : Fin 4), propDenom 0 ε (fm base (ppc c k) l ℓ) + (m : ℂ) ^ 2 ≠ 0 :=
    fun m l => by rw [← hd]; exact propDenom_ne_zero hε.ne' _
  have htA : ((triA M X Y : ℝ) : ℂ) =
      ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triA]; push_cast; rfl
  have htB : ((triB M X Y : ℝ) : ℂ) =
      ((M : ℂ) ^ 2 - (X : ℂ) ^ 2) / ((X : ℂ) ^ 2 - (Y : ℂ) ^ 2) := by
    simp only [triB]; push_cast; rfl
  rw [← tri_v_eq (fun l => propDenom 0 ε (fm base (ppc c k) l ℓ)) (vD base (ppc c k) mγ Λ ε ℓ)
    (E0 k ℓ a b) (E2 k ℓ a b) (E4 k a b) ((M : ℂ) ^ 2) ((X : ℂ) ^ 2) ((Y : ℂ) ^ 2) h01 h02 h12
    (nz M) (nz X) (nz Y)]
  simp only [gH, hE, htA, htB, hd M ε k, hd X ε k, hd Y ε k]


/-- **The block-summed flavour sum of a two-loop numerator** is `EL1`. -/
theorem el1_gBlock
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Num : ℝ → (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E0 E2 : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (E4 : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hE : ∀ m k ℓ a b, Num m k ℓ a b =
      E0 k ℓ a b + (m : ℂ) ^ 2 * E2 k ℓ a b + ((m : ℂ) ^ 2) ^ 2 * E4 k a b)
    (hP : ∀ m k a b, IsLoopPoly 2 4 fun ℓ => Num m k ℓ a b)
    (hP2 : ∀ k a b, IsLoopPoly 2 2 fun ℓ => E2 k ℓ a b)
    (hBA : ∀ m a b i j, RBK (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun k ℓ => Num m k ℓ a b)
    (hBB : ∀ m a b i, RBK (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3} 4
      fun k ℓ => Num m k ℓ a b)
    (hE4b : ∀ a b, ∃ D : ℝ, ∀ k, ‖E4 k a b‖ ≤ D)
    {m₀ : ℝ} (hm₀ : 0 < m₀) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (rep : F → F) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) :
    EL1 fun ε k ℓ a b =>
      ∑ f, (Φ.coeff f : ℂ) * gH base c Num mγ Λ (Φ.mass f) ε k ℓ a b := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set X : ℝ := m₀ + 1 + ∑ g, Φ.mass g with hX
  have hS0 : 0 ≤ ∑ g, Φ.mass g := Finset.sum_nonneg fun g _ => (hpos g).le
  have hlt : ∀ g, Φ.mass g < X := fun g => by
    have := Finset.single_le_sum (fun g _ => (hpos g).le) (Finset.mem_univ g)
    linarith
  have hXY : X ^ 2 - (X + 1) ^ 2 ≠ 0 := by nlinarith
  have h1 : ∀ g, Φ.mass g ^ 2 - X ^ 2 ≠ 0 := fun g => by
    have := hlt g; have := hpos g; nlinarith
  have h2 : ∀ g, Φ.mass g ^ 2 - (X + 1) ^ 2 ≠ 0 := fun g => by
    have := hlt g; have := hpos g; nlinarith
  refine (EL1.sum Finset.univ fun f _ => (el1_gTriple base c mγ Λ hcA hcB Num E0 E2 E4 hE hP
    hP2 hBA hBB hE4b (h1 f) (h2 f) hXY).const_mul (Φ.coeff f : ℂ)).congr
      fun ε _ k ℓ a b => ?_
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
    (fun _ M => gH base c Num mγ Λ M ε k ℓ a b)]

end Setting


/-! ### The classes -/

section Classes

open QED.GradedProof.VP2

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ}
  (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (e mγ Λ : ℝ)

include hm₀ hmass hrep hPV₁ hPV₂

/-- **The class `VA`**: the spatial integral of its inner energy integral grows at most like
`(1 + Σ k²)⁴`. -/
theorem el1_VA : EL1 (vSumF Φ e aVA baseVA cVA mγ Λ) :=
  el1_gBlock baseVA cVA mγ Λ critA_VA critB_VA _ _ _ _
    (vNum_eq e mγ Λ aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVA baseVA cVA) (isLoopPoly_vNumE2 e mγ Λ aVA baseVA cVA)
    (fun m a b i j => rbk_vNum baseVA cVA e mγ Λ aVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m a b)
    (fun m a b i => rbk_vNum baseVA cVA e mγ Λ aVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m a b)
    (fun a b => ⟨_, fun k => le_of_eq (congrArg norm (rfl :
      vNumE4 e mγ Λ aVA k a b = vNumE4 e mγ Λ aVA 0 a b))⟩)
    hm₀ Φ rep hmass hrep hPV₁ hPV₂

/-- **The class `VB`**: the spatial integral of its inner energy integral grows at most like
`(1 + Σ k²)⁴`. -/
theorem el1_VB : EL1 (vSumF Φ e aVB baseVB cVB mγ Λ) :=
  el1_gBlock baseVB cVB mγ Λ critA_VB critB_VB _ _ _ _
    (vNum_eq e mγ Λ aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVB baseVB cVB) (isLoopPoly_vNumE2 e mγ Λ aVB baseVB cVB)
    (fun m a b i j => rbk_vNum baseVB cVB e mγ Λ aVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m a b)
    (fun m a b i => rbk_vNum baseVB cVB e mγ Λ aVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m a b)
    (fun a b => ⟨_, fun k => le_of_eq (congrArg norm (rfl :
      vNumE4 e mγ Λ aVB k a b = vNumE4 e mγ Λ aVB 0 a b))⟩)
    hm₀ Φ rep hmass hrep hPV₁ hPV₂

/-- **The class `VC`**: the spatial integral of its inner energy integral grows at most like
`(1 + Σ k²)⁴`. -/
theorem el1_VC : EL1 (vSumF Φ e aVC baseVC cVC mγ Λ) :=
  el1_gBlock baseVC cVC mγ Λ critA_VC critB_VC _ _ _ _
    (vNum_eq e mγ Λ aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVC baseVC cVC) (isLoopPoly_vNumE2 e mγ Λ aVC baseVC cVC)
    (fun m a b i j => rbk_vNum baseVC cVC e mγ Λ aVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m a b)
    (fun m a b i => rbk_vNum baseVC cVC e mγ Λ aVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m a b)
    (fun a b => ⟨_, fun k => le_of_eq (congrArg norm (rfl :
      vNumE4 e mγ Λ aVC k a b = vNumE4 e mγ Λ aVC 0 a b))⟩)
    hm₀ Φ rep hmass hrep hPV₁ hPV₂

end Classes

end QED.ChainProof.SetANestV

end
