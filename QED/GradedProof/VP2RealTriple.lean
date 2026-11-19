/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2RealJ
public import QED.GradedProof.VP2VTriple

/-!
# The three-flavour combination of a two-loop numerator: the phase of the limit

Helper level for the Phase 5 Stage 2 goal (G-ex₂) `QED.Graded.existsUnique_withLevel_one`
(decision D-57), input `VPReal`; the phase counterpart of `QED/GradedProof/VP2VTriple.lean`, with
the same proofs and one extra hypothesis: the numerator family satisfies `N̄um = d Num` at real
momenta. All combination coefficients (`triA`, `triB`, `(X² - M²)(Y² - M²)`, the `ε = 0`
denominator of the padded piece) are real, and the multiplier `-iε` of the padding has limit `0`.

* `vpjc_pieceA`, `vpjc_pieceB`: the pieces with eight and seven lines;
* `vpjc_gTriple`: the three-flavour Pauli–Villars combination is `VPJC (2 m₀) d`;
* `vpjc_gBlock`: so is the flavour sum under the block Pauli–Villars conditions.
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.VP2Real

open QED.Integration.TwoLoop QED.TwoLoop.CountertermLimit QED.TwoLoop.Bridge
open QED.TwoLoop.LimitCovariance QED.GradedProof.SE2 QED.GradedProof.VP2
open QED.TwoLoop.ClassIntegrable (RefinedBoundMat)

/-- The denominator at `ε = 0` is real. -/
theorem conj_propDenom_zero (M : ℝ) (p : Fin 4 → ℝ) :
    starRingEnd ℂ (propDenom M 0 p) = propDenom M 0 p := by
  simp only [propDenom, ofReal_zero, zero_mul, sub_zero, Complex.conj_ofReal]

section Setting

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)

variable (y₁ y₂ : Fin 2 → ℝ)
  (hflow : ∀ j : Fin 5, |∑ s, (base j s : ℝ) * y₁ s + c j| +
    |∑ s, (base j s : ℝ) * y₂ s + c j| ≤ if j = 4 then 0 else 1)
  {m₀ : ℝ} (hm₀ : 0 < m₀) {mγ Λ : ℝ} (hmγ : 0 < mγ) (hΛ : 0 < Λ)

include hflow hm₀ hmγ hΛ

/-- **A piece with eight lines** and a phase-`d` numerator is `VPJC`. -/
theorem vpjc_pieceA (i j : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {X Y : ℝ} (hX : m₀ ≤ X) (hY : m₀ ≤ Y)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hpoly : ∀ k a b, IsLoopPoly 2 4 fun ℓ => N k ℓ a b)
    (hB : ∀ k a b, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun ℓ => N k ℓ a b)
    (hcov : TCov2 N) {d : ℕ} (hk : ∀ ℓ a b, IsLoopPoly 1 d fun y => N (y 0) ℓ a b) {ph : ℂ}
    (hph : ∀ k ℓ a b, starRingEnd ℂ (N k ℓ a b) = ph * N k ℓ a b) :
    VPJC (2 * m₀) ph fun ε k ℓ a b => N k ℓ a b *
      ((∏ l : Fin 4, (propDenom (Mf l) ε (fm base (ppc c k) l ℓ))⁻¹) *
        (propDenom X ε (fm base (ppc c k) i ℓ))⁻¹ * (propDenom Y ε (fm base (ppc c k) j ℓ))⁻¹ *
        ((propDenom mγ ε (phm base (ppc c k) ℓ))⁻¹ *
          (propDenom Λ ε (phm base (ppc c k) ℓ))⁻¹)) := by
  have hm := fun l => hm₀.le.trans (hMf l)
  have h := vpjc_piece base c y₁ y₂ hflow (Or.inr rfl) (shA i j)
    ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, mγ, Λ] hcrit N hpoly hB hcov hk hm₀
    (fun n hn => by
      fin_cases n
      exacts [hMf 0, hMf 1, hMf 2, hMf 3, hX, hY, absurd rfl hn, absurd rfl hn])
    (fun n => by
      fin_cases n
      exacts [hm 0, hm 1, hm 2, hm 3, hm₀.le.trans hX, hm₀.le.trans hY, hmγ.le, hΛ.le])
    (cc_pos hm₀ hmγ hΛ)
    (fun n => by
      fin_cases n
      exacts [cc_le hm₀ (hMf 0), cc_le hm₀ (hMf 1), cc_le hm₀ (hMf 2),
        cc_le hm₀ (hMf 3), cc_le hm₀ hX, cc_le hm₀ hY,
        cc_le_γ, cc_le_Λ]) hph
  refine h.congr fun ε _ k ℓ a b => ?_
  rw [Fin.prod_univ_eight]
  simp only [Fin.prod_univ_four, shA, Matrix.cons_val, fm, phm]
  ring

/-- **A piece with seven lines** and a phase-`d` numerator is `VPJC`. -/
theorem vpjc_pieceB (i : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {Y : ℝ} (hY : m₀ ≤ Y)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Fin 4 → Fin 4 → ℂ)
    (hpoly : ∀ k a b, IsLoopPoly 2 3 fun ℓ => N k ℓ a b)
    (hB : ∀ k a b, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3, 4} 4
      fun ℓ => N k ℓ a b)
    (hcov : TCov2 N) {d : ℕ} (hk : ∀ ℓ a b, IsLoopPoly 1 d fun y => N (y 0) ℓ a b) {ph : ℂ}
    (hph : ∀ k ℓ a b, starRingEnd ℂ (N k ℓ a b) = ph * N k ℓ a b) :
    VPJC (2 * m₀) ph fun ε k ℓ a b => N k ℓ a b *
      ((∏ l : Fin 4, (propDenom (Mf l) ε (fm base (ppc c k) l ℓ))⁻¹) *
        (propDenom Y ε (fm base (ppc c k) i ℓ))⁻¹ *
        ((propDenom mγ ε (phm base (ppc c k) ℓ))⁻¹ *
          (propDenom Λ ε (phm base (ppc c k) ℓ))⁻¹)) := by
  have hm := fun l => hm₀.le.trans (hMf l)
  have h := vpjc_piece base c y₁ y₂ hflow (Or.inl rfl) (shB i)
    ![Mf 0, Mf 1, Mf 2, Mf 3, Y, mγ, Λ] hcrit N hpoly hB hcov hk hm₀
    (fun n hn => by
      fin_cases n
      exacts [hMf 0, hMf 1, hMf 2, hMf 3, hY, absurd rfl hn, absurd rfl hn])
    (fun n => by
      fin_cases n
      exacts [hm 0, hm 1, hm 2, hm 3, hm₀.le.trans hY, hmγ.le, hΛ.le])
    (cc_pos hm₀ hmγ hΛ)
    (fun n => by
      fin_cases n
      exacts [cc_le hm₀ (hMf 0), cc_le hm₀ (hMf 1), cc_le hm₀ (hMf 2),
        cc_le hm₀ (hMf 3), cc_le hm₀ hY, cc_le_γ, cc_le_Λ]) hph
  refine h.congr fun ε _ k ℓ a b => ?_
  rw [Fin.prod_univ_seven]
  simp only [Fin.prod_univ_four, shB, Matrix.cons_val, fm, phm]
  ring

/-- **The three-flavour combination of a phase-`d` two-loop numerator** is `VPJC`. -/
theorem vpjc_gTriple
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
    (hcov : ∀ m, TCov2 (Num m)) {d : ℕ}
    (hk : ∀ m ℓ a b, IsLoopPoly 1 d fun y => Num m (y 0) ℓ a b)
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (hMX : M ^ 2 - X ^ 2 ≠ 0)
    (hMY : M ^ 2 - Y ^ 2 ≠ 0) (hXY : X ^ 2 - Y ^ 2 ≠ 0) {ph : ℂ}
    (hph : ∀ m k ℓ a b, starRingEnd ℂ (Num m k ℓ a b) = ph * Num m k ℓ a b) :
    VPJC (2 * m₀) ph fun ε k ℓ a b => gH base c Num mγ Λ M ε k ℓ a b +
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
  have hk4 : ∀ (ℓ : Fin 2 → Fin 4 → ℝ) a b, IsLoopPoly 1 d fun y => E4 (y 0) a b := by
    intro ℓ a b
    have e : (fun y : Fin 1 → Fin 4 → ℝ => E4 (y 0) a b) = fun y =>
        1 / 12 * (Num 2 (y 0) ℓ a b - 4 * Num 1 (y 0) ℓ a b + 3 * Num 0 (y 0) ℓ a b) :=
      funext fun y => hE4 (y 0) ℓ a b
    rw [e]
    exact (((hk 2 ℓ a b).sub ((hk 1 ℓ a b).const_mul 4)).add
      ((hk 0 ℓ a b).const_mul 3)).const_mul _
  have hph4 : ∀ k a b, starRingEnd ℂ (E4 k a b) = ph * E4 k a b := fun k a b => by
    rw [hE4 k 0 a b]
    simp only [map_mul, map_sub, map_add, map_div₀, map_one, map_ofNat, hph]
    ring
  have hd : ∀ (m ε : ℝ) (k : Fin 4 → ℝ) (l : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ),
      propDenom m ε (fm base (ppc c k) l ℓ) =
        propDenom 0 ε (fm base (ppc c k) l ℓ) + (m : ℂ) ^ 2 :=
    fun m ε k l ℓ => propDenom_eq_add m ε _
  -- the ten pieces with eight lines
  have PA : ∀ i j : Fin 4, VPJC (2 * m₀) ph fun ε k ℓ a b =>
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
      have h := vpjc_pieceA (ph := ph) base c y₁ y₂ hflow hm₀ hmγ hΛ i j (hcA i j) (mA M X Y i j)
        (fun l => by unfold mA; split_ifs <;> assumption) hX hY
        (fun k ℓ a b => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * Num M k ℓ a b)
        (fun k a b => (hP M k a b).const_mul _) (fun k a b => (hBA M k a b i j).const_mul _)
        ((hcov M).const_mul _) (fun ℓ a b => (hk M ℓ a b).const_mul _)
        (fun k ℓ a b => by
          simp only [map_mul, map_sub, map_pow, Complex.conj_ofReal, hph]; ring)
      refine h.congr fun ε _ k ℓ a b => ?_
      rw [Finset.prod_congr rfl fun l _ => by rw [hd _ ε k l ℓ, sq_mA], hd X ε k i ℓ,
        hd Y ε k j ℓ, hE]
      simp only [vD]
      ring
    · simp only [hij, ite_false]
      exact VPJC.zero
  -- the four pieces with seven lines
  have PB : ∀ i : Fin 4, VPJC (2 * m₀) ph fun ε k ℓ a b =>
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
    have h := vpjc_pieceB (ph := ph) base c y₁ y₂ hflow hm₀ hmγ hΛ i (hcB i) (mB X Y i)
      (fun l => by unfold mB; split_ifs <;> assumption) hY
      (fun k ℓ a b => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * (Num X k ℓ a b - Num M k ℓ a b)) hpoly
      (fun k a b => (((hBB X k a b i).sub (hBB M k a b i)).const_mul _).mono (by decide) le_rfl)
      (((hcov X).sub (hcov M)).const_mul _)
      (fun ℓ a b => ((hk X ℓ a b).sub (hk M ℓ a b)).const_mul _)
      (fun k ℓ a b => by
        simp only [map_mul, map_sub, map_neg, map_pow, Complex.conj_ofReal, hph]; ring)
    refine h.congr fun ε _ k ℓ a b => ?_
    rw [Finset.prod_congr rfl fun l _ => by rw [hd _ ε k l ℓ, sq_mB], hd Y ε k i ℓ, hE, hE]
    simp only [vD]
    ring
  -- the padded piece
  have PC : VPJC (2 * m₀) ph fun ε k ℓ a b =>
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
    have h1 := vpjc_pieceB (ph := ph) base c y₁ y₂ hflow hm₀ hmγ hΛ 0 (hcB 0) (fun _ => Y)
      (fun _ => hY) hY
      (fun k ℓ a b => C * E4 k a b * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
      (fun k a b => ((IsLoopPoly.const (n := 0) _).mul
        ((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0)).mono (by norm_num))
      (fun k a b => ((rb_propDenom_pad base (ppc c k) (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0).const_mul _).mono (by decide) (by norm_num)) cov1
      (fun ℓ a b => ((hk4 ℓ a b).const_mul C).mul
        ((isLoopAffine_lineMomentum_k base c _ ℓ).isLoopPoly_propDenom Y 0))
      (fun k ℓ a b => by
        rw [map_mul, map_mul, hC, conj_propDenom_zero, hph4]
        simp only [map_mul, map_sub, map_pow, Complex.conj_ofReal]; ring)
    have h2 := (vpjc_pieceB (ph := ph) base c y₁ y₂ hflow hm₀ hmγ hΛ 0 (hcB 0) (fun _ => Y)
      (fun _ => hY) hY
      (fun k _ a b => C * E4 k a b) (fun k a b => IsLoopPoly.const _)
      (fun k a b => (RefinedBound.const _).mono (Finset.empty_subset _) (by norm_num))
      (cov4.const_mul C) (fun ℓ a b => (hk4 ℓ a b).const_mul C)
      (fun k ℓ a b => by
        rw [map_mul, hC, hph4]
        simp only [map_mul, map_sub, map_pow, Complex.conj_ofReal]; ring)).mul
      (c := fun ε : ℝ => -((ε : ℂ) * I)) (c₀ := 0) (by
        have := ((continuous_ofReal.tendsto (0 : ℝ)).mul_const I).neg
        rw [ofReal_zero]
        simp only [ofReal_zero, zero_mul, neg_zero] at this
        exact this.mono_left nhdsWithin_le_nhds)
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
  have hS := ((VPJC.sum Finset.univ fun i _ => VPJC.sum Finset.univ fun j _ => PA i j).add
    (VPJC.sum Finset.univ fun i _ => PB i)).add PC
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

/-- **The block-summed flavour sum of a phase-`d` two-loop numerator** is `VPJC`. -/
theorem vpjc_gBlock
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
    (hcov : ∀ m, TCov2 (Num m)) {d : ℕ}
    (hk : ∀ m ℓ a b, IsLoopPoly 1 d fun y => Num m (y 0) ℓ a b)
    {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F) (rep : F → F)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) {ph : ℂ}
    (hph : ∀ m k ℓ a b, starRingEnd ℂ (Num m k ℓ a b) = ph * Num m k ℓ a b) :
    VPJC (2 * m₀) ph fun ε k ℓ a b =>
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
  refine (VPJC.sum Finset.univ fun f _ => (vpjc_gTriple base c y₁ y₂ hflow hm₀ hmγ hΛ hcA hcB Num
    E0 E2 E4 hE hP hP2 hBA hBB hcov hk (hmass f) hX0 (by linarith) (h1 f) (h2 f) hXY hph).const_mul
      (Φ.coeff f)).congr fun ε _ k ℓ a b => ?_
  rw [sum_block_eq_sum_triple Φ rep hrep hPV₁ hPV₂ X (X + 1)
    (fun _ M => gH base c Num mγ Λ M ε k ℓ a b)]

end Setting

end QED.GradedProof.VP2Real

end
