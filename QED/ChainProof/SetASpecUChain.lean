/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetASpecUForm
public import QED.ChainProof.SetASpecVCls

/-!
# Set (a): the uniform spectral form of the classes `VA`, `VB`, `VC`

Helper level for the set (a) headline (HA₆) `QED.ThreeLoop.isFormFactorPair_vertexSetA_pauli_limit`.
The `ε`-uniform copy (`QED.ChainProof.SetASpec.SAUJ`) of `QED.ChainProof.SetASpec.saUj_gTriple`,
`saUj_gBlock`, `saUj_VA`, `saUj_VB`, `saUj_VC`. The only `ε`-dependent coefficient is the padding
`-iε` of the piece `PC` of the three-flavour combination, a uniform coefficient
(`SAUCoef.of_continuous`).

* `saUj_pieceA`, `saUj_pieceB`: the pieces with eight and seven lines;
* **`saUj_gTriple`**, **`saUj_gBlock`**: the three-flavour combination and the flavour sum;
* **`saUj_VA`**, **`saUj_VB`**, **`saUj_VC`**.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.ChainProof.SetASpec

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2 QED.GradedProof.VP2

/-! ### The pieces -/

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  {m₀ Mlo mγ Λ : ℝ} (hlo0 : 0 ≤ Mlo) (hlo : Mlo ≤ m₀) (hloγ : Mlo ≤ mγ) (hloΛ : Mlo ≤ Λ)
  (hrow : ∀ y : Fin 2 → ℝ, ∃ r : Fin 4, ∑ s, (base r.castSucc s : ℝ) * y s + c r.castSucc ≠ 0)

include hflow hlo0 hlo hloγ hloΛ hrow

/-- **A piece with eight lines** is `SAUJ` (uniform). -/
theorem saUj_pieceA (i j : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {X Y : ℝ} (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hpoly : ∀ k a b, IsLoopPoly 2 4 fun ℓ => N k ℓ a b)
    (hB : ∀ k a b, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun ℓ => N k ℓ a b)
    (hcov : TCov2 N) (hK : SAPolyK 4 N) :
    SAUJ Mlo fun ε k ℓ a b => N k ℓ a b *
      ((∏ l : Fin 4, (propDenom (Mf l) ε (fm base (ppc c k) l ℓ))⁻¹) *
        (propDenom X ε (fm base (ppc c k) i ℓ))⁻¹ * (propDenom Y ε (fm base (ppc c k) j ℓ))⁻¹ *
        ((propDenom mγ ε (phm base (ppc c k) ℓ))⁻¹ *
          (propDenom Λ ε (phm base (ppc c k) ℓ))⁻¹)) := by
  have h := saUj_piece base c y₁ y₂ hflow (Or.inr rfl) (shA i j)
    ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, mγ, Λ] hcrit N hpoly hB hcov hK
    (fun y => by
      obtain ⟨r, hr⟩ := hrow y
      refine ⟨⟨r, by omega⟩, ?_⟩
      have e : shA i j ⟨r, by omega⟩ = r.castSucc := by fin_cases r <;> rfl
      rw [e]
      exact hr) hlo0
    (fun n => by
      fin_cases n
      exacts [hlo.trans (hMf 0), hlo.trans (hMf 1), hlo.trans (hMf 2), hlo.trans (hMf 3),
        hlo.trans hX, hlo.trans hY, hloγ, hloΛ])
  refine h.congr fun ε _ k ℓ a b => ?_
  rw [Fin.prod_univ_eight]
  simp only [Fin.prod_univ_four, shA, Matrix.cons_val, fm, phm]
  ring

/-- **A piece with seven lines** is `SAUJ` (uniform). -/
theorem saUj_pieceB (i : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {Y : ℝ} (hY : m₀ ≤ Y)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hpoly : ∀ k a b, IsLoopPoly 2 3 fun ℓ => N k ℓ a b)
    (hB : ∀ k a b, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3, 4} 4
      fun ℓ => N k ℓ a b)
    (hcov : TCov2 N) (hK : SAPolyK 4 N) :
    SAUJ Mlo fun ε k ℓ a b => N k ℓ a b *
      ((∏ l : Fin 4, (propDenom (Mf l) ε (fm base (ppc c k) l ℓ))⁻¹) *
        (propDenom Y ε (fm base (ppc c k) i ℓ))⁻¹ *
        ((propDenom mγ ε (phm base (ppc c k) ℓ))⁻¹ *
          (propDenom Λ ε (phm base (ppc c k) ℓ))⁻¹)) := by
  have h := saUj_piece base c y₁ y₂ hflow (Or.inl rfl) (shB i)
    ![Mf 0, Mf 1, Mf 2, Mf 3, Y, mγ, Λ] hcrit N hpoly hB hcov hK
    (fun y => by
      obtain ⟨r, hr⟩ := hrow y
      refine ⟨⟨r, by omega⟩, ?_⟩
      have e : shB i ⟨r, by omega⟩ = r.castSucc := by fin_cases r <;> rfl
      rw [e]
      exact hr) hlo0
    (fun n => by
      fin_cases n
      exacts [hlo.trans (hMf 0), hlo.trans (hMf 1), hlo.trans (hMf 2), hlo.trans (hMf 3),
        hlo.trans hY, hloγ, hloΛ])
  refine h.congr fun ε _ k ℓ a b => ?_
  rw [Fin.prod_univ_seven]
  simp only [Fin.prod_univ_four, shB, Matrix.cons_val, fm, phm]
  ring

/-- **The three-flavour combination of a two-loop numerator** is `SAUJ` (uniform). -/
theorem saUj_gTriple
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
    (hcov : ∀ m, TCov2 (Num m)) (hK : ∀ m, SAPolyK 4 (Num m))
    (hK4 : SAPolyK 2 fun k (_ : Fin 2 → Fin 4 → ℝ) a b => E4 k a b)
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (hMX : M ^ 2 - X ^ 2 ≠ 0)
    (hMY : M ^ 2 - Y ^ 2 ≠ 0) (hXY : X ^ 2 - Y ^ 2 ≠ 0) :
    SAUJ Mlo fun ε k ℓ a b => gH base c Num mγ Λ M ε k ℓ a b +
      (triA M X Y : ℂ) * gH base c Num mγ Λ X ε k ℓ a b +
      (triB M X Y : ℂ) * gH base c Num mγ Λ Y ε k ℓ a b := by
  have h01 : (M : ℂ) ^ 2 - (X : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hMX
  have h02 : (M : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hMY
  have h12 : (X : ℂ) ^ 2 - (Y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hXY
  -- `E₄` through the masses `0, 1, 2`
  have hE4 : ∀ k ℓ a b, E4 k a b =
      1 / 12 * (Num 2 k ℓ a b - 4 * Num 1 k ℓ a b + 3 * Num 0 k ℓ a b) := fun k ℓ a b => by
    rw [hE, hE, hE]; push_cast; ring
  have cov4 : TCov2 fun k (_ : Fin 2 → Fin 4 → ℝ) a b => E4 k a b := by
    have e : (fun k (ℓ : Fin 2 → Fin 4 → ℝ) a b => E4 k a b) = fun k ℓ a b =>
        1 / 12 * (Num 2 k ℓ a b - 4 * Num 1 k ℓ a b + 3 * Num 0 k ℓ a b) :=
      funext fun k => funext fun ℓ => funext fun a => funext fun b => hE4 k ℓ a b
    rw [e]
    exact (((hcov 2).sub ((hcov 1).const_mul 4)).add ((hcov 0).const_mul 3)).const_mul _
  have hd : ∀ (m ε : ℝ) (k : Fin 4 → ℝ) (l : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ),
      propDenom m ε (fm base (ppc c k) l ℓ) =
        propDenom 0 ε (fm base (ppc c k) l ℓ) + (m : ℂ) ^ 2 :=
    fun m ε k l ℓ => propDenom_eq_add m ε _
  -- the ten pieces with eight lines
  have PA : ∀ i j : Fin 4, SAUJ Mlo fun ε k ℓ a b =>
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
      have h := saUj_pieceA base c y₁ y₂ hflow hlo0 hlo hloγ hloΛ hrow i j (hcA i j) (mA M X Y i j)
        (fun l => by unfold mA; split_ifs <;> assumption) hX hY
        (fun k ℓ a b => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k ℓ a b)
        (fun k a b => (hP M k a b).const_mul _) (fun k a b => (hBA M k a b i j).const_mul _)
        ((hcov M).const_mul _) ((hK M).const_mul _)
      refine h.congr fun ε _ k ℓ a b => ?_
      rw [Finset.prod_congr rfl fun l _ => by rw [hd _ ε k l ℓ, sq_mA], hd X ε k i ℓ,
        hd Y ε k j ℓ, hE]
      simp only [vD]
      ring
    · simp only [hij, ite_false]
      exact SAUJ.zero
  -- the four pieces with seven lines
  have PB : ∀ i : Fin 4, SAUJ Mlo fun ε k ℓ a b =>
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
    have h := saUj_pieceB base c y₁ y₂ hflow hlo0 hlo hloγ hloΛ hrow i (hcB i) (mB X Y i)
      (fun l => by unfold mB; split_ifs <;> assumption) hY
      (fun k ℓ a b => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ a b - Num M k ℓ a b)) hpoly
      (fun k a b => (((hBB X k a b i).sub (hBB M k a b i)).const_mul _).mono (by decide) le_rfl)
      (((hcov X).sub (hcov M)).const_mul _) (((hK X).sub (hK M)).const_mul _)
    refine h.congr fun ε _ k ℓ a b => ?_
    rw [Finset.prod_congr rfl fun l _ => by rw [hd _ ε k l ℓ, sq_mB], hd Y ε k i ℓ, hE, hE]
    simp only [vD]
    ring
  -- the padded piece
  have PC : SAUJ Mlo fun ε k ℓ a b =>
      vD base (ppc c k) mγ Λ ε ℓ * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        E4 k a b * ∏ l : Fin 4, (propDenom 0 ε (fm base (ppc c k) l ℓ) + (Y : ℂ) ^ 2)⁻¹ := by
    set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
    have cov1 : TCov2 fun k ℓ a b => C * E4 k a b * propDenom Y 0 (fm base (ppc c k) 0 ℓ) := by
      have e : (fun k ℓ a b => C * E4 k a b * propDenom Y 0 (fm base (ppc c k) 0 ℓ)) =
          fun k ℓ a b => propDenom Y 0 (fm base (ppc c k) 0 ℓ) * (C * E4 k a b) :=
        funext fun k => funext fun ℓ => funext fun a => funext fun b => mul_comm _ _
      rw [e]
      exact (cov4.const_mul C).mul_inv fun L S S' hL k ℓ =>
        propDenom_lineMomentum_inv base c Y 0 _ L S S' hL k ℓ
    have h1 := saUj_pieceB base c y₁ y₂ hflow hlo0 hlo hloγ hloΛ hrow 0 (hcB 0) (fun _ => Y)
      (fun _ => hY) hY
      (fun k ℓ a b => C * E4 k a b * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
      (fun k a b => ((IsLoopPoly.const (n := 0) _).mul
        ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0)).mono (by norm_num))
      (fun k a b => ((rb_propDenom_pad base (ppc c k) (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0).const_mul _).mono (by decide) (by norm_num)) cov1
      ((hK4.const_mul C).mul (saPolyK_propDenom base c Y 0 _))
    have h2 := (saUj_pieceB base c y₁ y₂ hflow hlo0 hlo hloγ hloΛ hrow 0 (hcB 0) (fun _ => Y)
      (fun _ => hY) hY
      (fun k _ a b => C * E4 k a b) (fun k a b => IsLoopPoly.const _)
      (fun k a b => (RefinedBound.const _).mono (Finset.empty_subset _) (by norm_num))
      (cov4.const_mul C) ((hK4.const_mul C).mono (by norm_num))).mul
      (SAUCoef.of_continuous (c := fun ε : ℝ => -((ε : ℂ) * I)) (by fun_prop))
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
  have hS := ((SAUJ.sum Finset.univ fun i _ => SAUJ.sum Finset.univ fun j _ => PA i j).add
    (SAUJ.sum Finset.univ fun i _ => PB i)).add PC
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

/-- **The block-summed flavour sum of a two-loop numerator** is `SAUJ` (uniform). -/
theorem saUj_gBlock
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
    (hcov : ∀ m, TCov2 (Num m)) (hK : ∀ m, SAPolyK 4 (Num m))
    (hK4 : SAPolyK 2 fun k (_ : Fin 2 → Fin 4 → ℝ) a b => E4 k a b)
    (hm₀ : 0 < m₀) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (rep : F → F) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) :
    SAUJ Mlo fun ε k ℓ a b =>
      ∑ f, (Φ.coeff f : ℂ) * gH base c Num mγ Λ (Φ.mass f) ε k ℓ a b := by
  have hpos : ∀ g, 0 < Φ.mass g := fun g => hm₀.trans_le (hmass g)
  set X : ℝ := m₀ + 1 + ∑ g, Φ.mass g with hX
  have hS0 : 0 ≤ ∑ g, Φ.mass g := Finset.sum_nonneg fun g _ => (hpos g).le
  have hlt : ∀ g, Φ.mass g < X := fun g => by
    have := Finset.single_le_sum (fun g _ => (hpos g).le) (Finset.mem_univ g)
    linarith
  have hX0 : m₀ ≤ X := by linarith
  have hXY : X ^ 2 - (X + 1) ^ 2 ≠ 0 := by nlinarith
  have h1 : ∀ g, Φ.mass g ^ 2 - X ^ 2 ≠ 0 := fun g => by
    have := hlt g; have := hpos g; nlinarith
  have h2 : ∀ g, Φ.mass g ^ 2 - (X + 1) ^ 2 ≠ 0 := fun g => by
    have := hlt g; have := hpos g; nlinarith
  refine (SAUJ.sum Finset.univ fun f _ => (saUj_gTriple base c y₁ y₂ hflow hlo0
    hlo hloγ hloΛ hrow hcA hcB Num E0 E2 E4 hE hP hP2 hBA hBB hcov hK hK4 (hmass f) hX0
    (by linarith) (h1 f) (h2 f) hXY).const_mul
      (Φ.coeff f : ℂ)).congr fun ε _ k ℓ a b => ?_
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
    (fun _ M => gH base c Num mγ Λ M ε k ℓ a b)]

end Setting

/-! ### The classes -/

section Classes

variable {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F) {m₀ : ℝ}
  (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
  (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
  (hPV₂ : ∀ b, rep b = b →
    ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
  (e : ℝ) {mγ Λ Mlo : ℝ} (hlo0 : 0 ≤ Mlo) (hlo : Mlo ≤ m₀) (hloγ : Mlo ≤ mγ) (hloΛ : Mlo ≤ Λ)

include hm₀ hmass hrep hPV₁ hPV₂ hlo0 hlo hloγ hloΛ

theorem saUj_VA : SAUJ Mlo (vSumF Φ e aVA baseVA cVA mγ Λ) :=
  saUj_gBlock baseVA cVA ![0, 0] ![-1, -1] flowVA hlo0 hlo hloγ hloΛ saRow_VA critA_VA critB_VA
    _ _ _ _
    (vNum_eq e mγ Λ aVA baseVA cVA fun a b ρ σ => isOddG_aVA a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVA baseVA cVA) (isLoopPoly_vNumE2 e mγ Λ aVA baseVA cVA)
    (fun m k a b i j => rb_vNum e mγ Λ aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumA e mγ Λ baseVA cVA) (saPolyK_vNum e mγ Λ aVA baseVA cVA)
    (saPolyK_vNumE4 e mγ Λ aVA) hm₀ Φ rep hmass hrep hPV₁ hPV₂

theorem saUj_VB : SAUJ Mlo (vSumF Φ e aVB baseVB cVB mγ Λ) :=
  saUj_gBlock baseVB cVB ![0, 1] ![-1, 0] flowVB hlo0 hlo hloγ hloΛ saRow_VB critA_VB critB_VB
    _ _ _ _
    (vNum_eq e mγ Λ aVB baseVB cVB fun a b ρ σ => isOddG_aVB a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVB baseVB cVB) (isLoopPoly_vNumE2 e mγ Λ aVB baseVB cVB)
    (fun m k a b i j => rb_vNum e mγ Λ aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumB e mγ Λ baseVB cVB) (saPolyK_vNum e mγ Λ aVB baseVB cVB)
    (saPolyK_vNumE4 e mγ Λ aVB) hm₀ Φ rep hmass hrep hPV₁ hPV₂

theorem saUj_VC : SAUJ Mlo (vSumF Φ e aVC baseVC cVC mγ Λ) :=
  saUj_gBlock baseVC cVC ![0, 1] ![-1, 0] flowVC hlo0 hlo hloγ hloΛ saRow_VC critA_VC critB_VC
    _ _ _ _
    (vNum_eq e mγ Λ aVC baseVC cVC fun a b ρ σ => isOddG_aVC a b ρ σ)
    (isLoopPoly_vNum e mγ Λ aVC baseVC cVC) (isLoopPoly_vNumE2 e mγ Λ aVC baseVC cVC)
    (fun m k a b i j => rb_vNum e mγ Λ aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (fun m k a b i => rb_vNum e mγ Λ aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k a b)
    (tcov_vNumC e mγ Λ baseVC cVC) (saPolyK_vNum e mγ Λ aVC baseVC cVC)
    (saPolyK_vNumE4 e mγ Λ aVC) hm₀ Φ rep hmass hrep hPV₁ hPV₂

end Classes

end QED.ChainProof.SetASpec

end
