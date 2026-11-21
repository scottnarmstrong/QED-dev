/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4MajLIncPiece
public import QED.GradedProof.RPi4MajLClass
public import QED.GradedProof.RPi4MajLipMid

/-!
# (R-Π₄) step L10, two loops: increments of the class entries along the ray, light pairs

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L10 (T2.IR,
increments). The increment counterpart of `QED/GradedProof/RPi4MajLClass.lean`: the pieces of a
class numerator are `MajLRayInc` (`QED.GradedProof.RPi4.maj_lrayInc_vpPiece`), with the same
quartic decompositions and top-monomial bounds as for `MajLRay`.

* `majLInc_pieceA`, `majLInc_pieceB`, `majLInc_triVal`, `majLInc_blockVal`;
* **`majLInc_vVal_VA`**, **`majLInc_vVal_VB`**, **`majLInc_vVal_VC`**: the class entries
  `vVal(…) μ ν` are `MajLRayInc` (any flavour set with masses `≥ m₀ > 0`);
* **`majLInc_decDil`**: the three `MajLRayInc` inputs of `MajLipIns` at the dilated
  configurations `decDil l (decCfg 1 4)`, `l ≥ 1`, `m₀ = l`.
-/

@[expose] public section

open Complex MeasureTheory Set

namespace QED.GradedProof.RPi4

open QED.GradedProof.VP2 QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration.Feynman (simplexSet simplexPoint)

section Pieces

variable (e : ℝ) (A : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
  (hA : ∀ a b ρ σ l, IsOddG (A a b ρ σ l)) (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ)
  (hrow : ∀ r : Fin 5, r ≠ 4 → base r = ![1, 0] ∨ base r = ![0, 1])
  (hrow4 : base 4 = ![1, -1]) {m₀ : ℝ} (hm₀ : 0 < m₀) (μ ν : Fin 4)

include hA hrow hrow4 hm₀

/-- **Increments of a piece with eight lines along the ray.** -/
theorem majLInc_pieceA (i j : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hrb : ∀ m k, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun ℓ => vNum e 0 1 A base c m k ℓ μ ν)
    {j' : Fin 7} (hj' : j' = 1 ∨ j' = 3)
    (hcw : MajIntCrit (fun n => base (shA i j n)) 0 j'.castSucc)
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {M X Y : ℝ} (hX : m₀ ≤ X) (hY : m₀ ≤ Y) (C : ℂ) :
    MajLRayInc fun a b k => pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) *
      (C * vNum e 0 1 A base c M k ℓ μ ν))
      (castLoopMatrix fun l => base (shA i j l)) (fun l => c (shA i j l) • k)
      ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, a, b] := by
  set α := castLoopMatrix fun n => base (shA i j n) with hα
  have hE := vNum_eq e 0 1 A base c hA
  have h0 : ∀ k ℓ, vNum e 0 1 A base c 0 k ℓ μ ν = vNumE0 e 0 1 A base c k ℓ μ ν :=
    fun k ℓ => by rw [hE]; simp
  have h12 : ∀ k ℓ, vNumE2 e 0 1 A base c k ℓ μ ν = vNum e 0 1 A base c 1 k ℓ μ ν -
      vNum e 0 1 A base c 0 k ℓ μ ν - vNumE4 e 0 1 A k μ ν := fun k ℓ => by
    rw [hE, hE]; push_cast; ring
  obtain ⟨Q2, hQ2⟩ := IsLoopPoly.exists_loopQuartic
    (F := fun ℓ => C * vNumE0 e 0 1 A base c (majRayVec 1) ℓ μ ν)
    (by simpa only [h0] using (isLoopPoly_vNum e 0 1 A base c 0 (majRayVec 1) μ ν).const_mul C)
  obtain ⟨Q1, hq1, hQ1⟩ := maj_quartic_of_poly (le_refl 3)
    ((((isLoopPoly_vNumE2 e 0 1 A base c (majRayVec 1) μ ν).const_mul (C * (M : ℂ) ^ 2))).mono
      (by norm_num) :
        IsLoopPoly 2 3 fun ℓ => C * (M : ℂ) ^ 2 * vNumE2 e 0 1 A base c (majRayVec 1) ℓ μ ν)
  obtain ⟨Q0, hq0, hQ0⟩ := maj_quartic_of_poly (le_refl 3)
    (IsLoopPoly.const (L := 2) (n := 3) (C * ((M : ℂ) ^ 2) ^ 2 * vNumE4 e 0 1 A (majRayVec 1) μ ν))
  set Q : Fin 3 → LoopQuartic := ![Q0, Q1, Q2] with hQ
  have hrb0 := hrb 0 (majRayVec 1)
  simp only [h0] at hrb0
  refine maj_lrayInc_vpPiece base c hrow hrow4 (Or.inr rfl) (shA i j)
    (fun l => by fin_cases l <;> simp [shA, Fin.ext_iff] <;> omega)
    (fun a b => ![Mf 0, Mf 1, Mf 2, Mf 3, X, Y, a, b])
    (fun a b l => by fin_cases l <;> simp) hcrit _ Q ?_ (fun _ => Or.inl le_rfl) ?_ hm₀
    (fun l hl => by
      fin_cases l
      exacts [hMf 0, hMf 1, hMf 2, hMf 3, hX, hY, absurd rfl hl, absurd rfl hl]) ?_
  · intro r hr ℓ
    have hr0 : r ≠ 0 := by positivity
    rw [hE, Fin.sum_univ_three]
    simp only [hQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hQ0, hQ1, hQ2, Fin.val_zero, Fin.val_one, Fin.val_two,
      maj_vNumE0_smul base c e 0 1 A (majRayVec 1) ℓ hr0,
      maj_vNumE2_smul base c e 0 1 A (majRayVec 1) ℓ hr0, vNumE4]
    ring
  · intro t
    fin_cases t
    · simp only [hQ, Fin.zero_eta, Matrix.cons_val_zero, hQ0]
      exact (RefinedBound.const _).mono (Finset.empty_subset _) (by norm_num)
    · show RefinedBound _ _ 4 Q1.eval
      rw [hQ1]
      simp only [h12]
      refine (((hrb 1 (majRayVec 1)).sub (hrb 0 (majRayVec 1))).sub ((RefinedBound.const _).mono
        (Finset.empty_subset _) (by norm_num))).const_mul (C * (M : ℂ) ^ 2)
    · simp only [hQ, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        hQ2]
      exact hrb0.const_mul C
  · intro hU hV
    obtain ⟨Cτ, hCτ0, hCτ⟩ := maj_exists_abs_flow_le α (fun l => c (shA i j l))
    set E0 : ℂ := ∑ ρ, ∑ σ, kV e 0 1 ρ σ * vE0 (A μ ν ρ σ) (fun _ => majRayVec 1) with hE0
    have hj6 : (j' : ℕ) < 6 := by rcases hj' with rfl | rfl <;> decide
    have hne : (0 : Fin 7) ≠ j' := by rcases hj' with rfl | rfl <;> decide
    refine maj_top_of_flow α _ _ Q2 (i := 0) (j := j') (by decide) hj6 hne
      (maj_integrableOn_weight α (by rcases hj' with rfl | rfl <;> decide) (maj_crit_of_int hcw))
      hU (pow_pos hm₀ 2) hV (K := 6 * ‖C‖ * ‖E0‖ * Cτ ^ 2) (by positivity) ?_
    intro x hx hUp
    have hz : ∀ l, 0 ≤ simplexPoint x l :=
      (QED.Integration.Feynman.simplexPoint_mem_stdSimplex hx).1
    set z := simplexPoint x with hzd
    set τ := majFlow α z (fun l => c (shA i j l)) with hτ
    have hfl : ∀ l : Fin 4, fm base (ppc c (majRayVec 1)) l
        (-loopShift α (fun l => c (shA i j l) • majRayVec 1) z) =
          (![τ 0, τ 1, τ 2, τ 3] l) • majRayVec 1 := by
      intro l
      fin_cases l
      · exact maj_fm_shift base c (shA i j) z (majRayVec 1) (l' := 0) rfl
      · exact maj_fm_shift base c (shA i j) z (majRayVec 1) (l' := 1) rfl
      · exact maj_fm_shift base c (shA i j) z (majRayVec 1) (l' := 2) rfl
      · exact maj_fm_shift base c (shA i j) z (majRayVec 1) (l' := 3) rfl
    have hval : Q2.eval (-loopShift α (fun l => c (shA i j l) • majRayVec 1) z) =
        C * (((τ 0 * τ 1 * τ 2 * τ 3 : ℝ)) : ℂ) * E0 := by
      rw [hQ2]
      dsimp only
      rw [maj_vNumE0_flow base c e 0 1 A (majRayVec 1) _ _ hfl μ ν]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hE0]
      push_cast
      ring
    have hU0 : symanzikU α z ≠ 0 := hUp.ne'
    have hprod : |τ 0 * τ 1 * τ 2 * τ 3| *
        (2 * Real.sqrt (z (0 : Fin 7).castSucc * z j'.castSucc)) ≤
          Cτ ^ 2 * remainder α z (fun l => c (shA i j l)) := by
      have hw : 0 ≤ 2 * Real.sqrt (z (0 : Fin 7).castSucc * z j'.castSucc) := by positivity
      rcases hj' with rfl | rfl
      · refine maj_abs_four_le hw hCτ0 ?_ (hCτ z hz hU0 2) (hCτ z hz hU0 3)
        exact maj_abs_flow_mul_le α hz hU0 (fun l => c (shA i j l)) (show (0 : Fin 8) ≠ 1 by decide)
      · rw [show τ 0 * τ 1 * τ 2 * τ 3 = τ 0 * τ 3 * τ 1 * τ 2 by ring]
        refine maj_abs_four_le hw hCτ0 ?_ (hCτ z hz hU0 1) (hCτ z hz hU0 2)
        exact maj_abs_flow_mul_le α hz hU0 (fun l => c (shA i j l)) (show (0 : Fin 8) ≠ 3 by decide)
    have hUp2 : 0 < symanzikU α z ^ 2 := pow_pos hUp 2
    simp only [coeffOne, ← hzd, hval]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hUp2, norm_mul,
      norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h6 : ‖(((7 - 4).factorial : ℕ) : ℂ)‖ = 6 := by norm_num [Nat.factorial]
    rw [h6]
    have hU2 := inv_nonneg.mpr hUp2.le
    calc (symanzikU α z ^ 2)⁻¹ * (6 * (‖C‖ * |τ 0 * τ 1 * τ 2 * τ 3| * ‖E0‖)) *
          (2 * Real.sqrt (z (0 : Fin 7).castSucc * z j'.castSucc))
        = 6 * ‖C‖ * ‖E0‖ * (symanzikU α z ^ 2)⁻¹ * (|τ 0 * τ 1 * τ 2 * τ 3| *
          (2 * Real.sqrt (z (0 : Fin 7).castSucc * z j'.castSucc))) := by ring
      _ ≤ 6 * ‖C‖ * ‖E0‖ * (symanzikU α z ^ 2)⁻¹ *
          (Cτ ^ 2 * remainder α z (fun l => c (shA i j l))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring

omit hA in
/-- **Increments of a piece with seven lines along the ray**: numerator `r² F(ℓ/r) + d`. -/
theorem majLInc_pieceB (i : Fin 4)
    (hcrit : IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (Mf : Fin 4 → ℝ) (hMf : ∀ l, m₀ ≤ Mf l) {Y : ℝ} (hY : m₀ ≤ Y)
    (N : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → ℂ) (F : (Fin 2 → Fin 4 → ℝ) → ℂ) (d : ℂ)
    (hF : IsLoopPoly 2 3 F)
    (hFB : RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3, 4} 4 F)
    (hN : ∀ r : ℝ, 1 ≤ r → ∀ ℓ, N (r • majRayVec 1) ℓ = (r : ℂ) ^ 2 * F (r⁻¹ • ℓ) + d) :
    MajLRayInc fun a b k => pvOf (fun ℓ => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * N k ℓ)
      (castLoopMatrix fun l => base (shB i l)) (fun l => c (shB i l) • k)
      ![Mf 0, Mf 1, Mf 2, Mf 3, Y, a, b] := by
  obtain ⟨Q1, hq1, hQ1⟩ := maj_quartic_of_poly le_rfl hF
  obtain ⟨Q0, hq0, hQ0⟩ := maj_quartic_of_poly (le_refl 3)
    (IsLoopPoly.const (L := 2) (n := 3) d)
  refine maj_lrayInc_vpPiece base c hrow hrow4 (Or.inl rfl) (shB i)
    (fun l => by fin_cases l <;> simp [shB, Fin.ext_iff]; omega)
    (fun a b => ![Mf 0, Mf 1, Mf 2, Mf 3, Y, a, b])
    (fun a b l => by fin_cases l <;> simp) hcrit N ![Q0, Q1, majZeroQ] ?_ ?_ ?_ hm₀
    (fun l hl => by
      fin_cases l
      exacts [hMf 0, hMf 1, hMf 2, hMf 3, hY, absurd rfl hl, absurd rfl hl])
    (fun _ _ => maj_top_zero _ _ _)
  · intro r hr ℓ
    rw [hN r hr ℓ, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hQ0, hQ1, majZeroQ_eval, Fin.val_zero, Fin.val_one,
      Fin.val_two]
    ring
  · intro t
    fin_cases t
    exacts [Or.inr hq0, Or.inr hq1, Or.inr rfl]
  · intro t
    fin_cases t
    · show RefinedBound _ _ 4 Q0.eval
      rw [hQ0]
      exact (RefinedBound.const _).mono (Finset.empty_subset _) (by norm_num)
    · show RefinedBound _ _ 4 Q1.eval
      rw [hQ1]
      exact hFB
    · show RefinedBound _ _ 4 majZeroQ.eval
      rw [show majZeroQ.eval = fun _ => (0 : ℂ) from funext majZeroQ_eval]
      exact (RefinedBound.const _).mono (Finset.empty_subset _) (by norm_num)

/-- **The class pieces combined, increments**: `triVal` at a light pair along the ray. -/
theorem majLInc_triVal
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (hBA : ∀ m k i j, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun ℓ => vNum e 0 1 A base c m k ℓ μ ν)
    (hBB : ∀ m k i, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3} 4
      fun ℓ => vNum e 0 1 A base c m k ℓ μ ν)
    {j' : Fin 7} (hj' : j' = 1 ∨ j' = 3)
    (hcw : ∀ i j, MajIntCrit (fun n => base (shA i j n)) 0 j'.castSucc)
    {M X Y : ℝ} (hM : m₀ ≤ M) (hX : m₀ ≤ X) (hY : m₀ ≤ Y) :
    MajLRayInc fun a b k =>
      triVal base c (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNum e 0 1 A base c m k ℓ μ ν)
        (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNumE4 e 0 1 A k μ ν) a b M X Y k μ ν := by
  set C : ℂ := ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) with hC
  have hE := vNum_eq e 0 1 A base c hA
  have PA : ∀ i j : Fin 4, MajLRayInc fun a b k => if i ≤ j then
      pieceVal base c (shA i j) ![mA M X Y i j 0, mA M X Y i j 1, mA M X Y i j 2,
        mA M X Y i j 3, X, Y, a, b]
        (fun k ℓ μ ν => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNum e 0 1 A base c m k ℓ μ ν)
            M k ℓ μ ν) k μ ν
      else 0 := by
    intro i j
    by_cases hij : i ≤ j
    · simp only [hij, ite_true]
      refine (majLInc_pieceA e A hA base c hrow hrow4 hm₀ μ ν i j (hcA i j)
        (fun m k => hBA m k i j) hj' (hcw i j) (mA M X Y i j)
        (fun l => by unfold mA; split_ifs <;> assumption) (M := M) hX hY C).congr
        fun u _ a b _ _ => ?_
      simp only [pieceVal]
      exact pvOf_congr_fun (fun ℓ => by simp only [hC]; ring) _ _ _
    · simp only [hij, ite_false]
      exact MajLRayInc.zero
  have PB : ∀ i : Fin 4, MajLRayInc fun a b k =>
      pieceVal base c (shB i) ![mB X Y i 0, mB X Y i 1, mB X Y i 2, mB X Y i 3, Y, a, b]
        (fun k ℓ μ ν => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          ((fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNum e 0 1 A base c m k ℓ μ ν)
              X k ℓ μ ν -
            (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNum e 0 1 A base c m k ℓ μ ν)
              M k ℓ μ ν)) k μ ν := by
    intro i
    set K' : ℂ := -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) with hK'
    have hFB : RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3, 4} 4
        fun ℓ => K' * vNumE2 e 0 1 A base c (majRayVec 1) ℓ μ ν := by
      have h := (((hBB 1 (majRayVec 1) i).sub (hBB 0 (majRayVec 1) i)).sub
        ((RefinedBound.const (vNumE4 e 0 1 A (majRayVec 1) μ ν)).mono (Finset.empty_subset _)
          (by norm_num))).const_mul K'
      have e2 : (fun ℓ => K' * vNumE2 e 0 1 A base c (majRayVec 1) ℓ μ ν) = fun ℓ =>
          K' * (vNum e 0 1 A base c 1 (majRayVec 1) ℓ μ ν -
            vNum e 0 1 A base c 0 (majRayVec 1) ℓ μ ν - vNumE4 e 0 1 A (majRayVec 1) μ ν) :=
        funext fun ℓ => by rw [maj_vNumE2_eq e A hA base c μ ν]
      rw [e2]
      exact h.mono (by decide) le_rfl
    refine (majLInc_pieceB base c hrow hrow4 hm₀ i (hcB i) (mB X Y i)
      (fun l => by unfold mB; split_ifs <;> assumption) hY
      (fun k ℓ => -((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
        (vNum e 0 1 A base c X k ℓ μ ν - vNum e 0 1 A base c M k ℓ μ ν))
      (fun ℓ => K' * vNumE2 e 0 1 A base c (majRayVec 1) ℓ μ ν)
      (K' * (((M : ℂ) ^ 2 + (X : ℂ) ^ 2) * vNumE4 e 0 1 A (majRayVec 1) μ ν))
      (((isLoopPoly_vNumE2 e 0 1 A base c (majRayVec 1) μ ν).const_mul K').mono (by norm_num))
      hFB ?_).congr fun u _ a b _ _ => ?_
    · intro r hr ℓ
      have hr0 : r ≠ 0 := by positivity
      rw [hE, hE, maj_vNumE2_smul base c e 0 1 A (majRayVec 1) ℓ hr0]
      simp only [vNumE4, hK']
      ring
    · simp only [pieceVal]
      exact pvOf_congr_fun (fun ℓ => by ring) _ _ _
  have PC : MajLRayInc fun a b k =>
      pieceVal base c (shB 0) ![Y, Y, Y, Y, Y, a, b]
        (fun k ℓ μ ν => ((X : ℂ) ^ 2 - (M : ℂ) ^ 2) * ((Y : ℂ) ^ 2 - (M : ℂ) ^ 2) *
          (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNumE4 e 0 1 A k μ ν) k μ ν *
          propDenom Y 0 (fm base (ppc c k) 0 ℓ)) k μ ν := by
    set D : ℂ := C * vNumE4 e 0 1 A (majRayVec 1) μ ν with hD
    refine (majLInc_pieceB base c hrow hrow4 hm₀ 0 (hcB 0) (fun _ => Y) (fun _ => hY) hY
      (fun k ℓ => C * vNumE4 e 0 1 A k μ ν * propDenom Y 0 (fm base (ppc c k) 0 ℓ))
      (fun ℓ => D * (propDenom Y 0 (fm base (ppc c (majRayVec 1)) 0 ℓ) - (Y : ℂ) ^ 2))
      (D * (Y : ℂ) ^ 2)
      (((((isLoopAffine_lineMomentum _ _ _).isLoopPoly_propDenom Y 0).sub
        (IsLoopPoly.const _)).const_mul D).mono (by norm_num))
      ((((rb_propDenom_pad base (ppc c (majRayVec 1)) (shB 0) 0 4 (by decide) 0 rfl rfl Y
        0).sub ((RefinedBound.const _).mono (Finset.empty_subset _) (by norm_num))).const_mul
        D).mono (by decide) (by norm_num)) ?_).congr fun u _ a b _ _ => ?_
    · intro r hr ℓ
      have hr0 : r ≠ 0 := by positivity
      rw [maj_fm_smul base c (majRayVec 1) 0 ℓ hr0]
      simp only [hD, vNumE4, propDenom, Minkowski.dot_eq, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    · simp only [pieceVal]
      exact pvOf_congr_fun (fun ℓ => by simp only [hC]; ring) _ _ _
  refine (((MajLRayInc.sum Finset.univ fun i _ => MajLRayInc.sum Finset.univ fun j _ => PA i j).add
    (MajLRayInc.sum Finset.univ fun i _ => PB i)).add PC).congr fun u _ a b _ _ => ?_
  simp only [triVal]

/-- **Increments of the block-summed flavour sum at a light pair along the ray.** -/
theorem majLInc_blockVal
    (hcA : ∀ i j, IntNoSubdivergenceRefined 2 {0, 1, 2, 3} fun n => base (shA i j n))
    (hcB : ∀ i, IntNoSubdivergenceRefined 2 {0, 1, 2, 3, 4} fun n => base (shB i n))
    (hBA : ∀ m k i j, RefinedBound (castLoopMatrix fun n => base (shA i j n)) {0, 1, 2, 3} 4
      fun ℓ => vNum e 0 1 A base c m k ℓ μ ν)
    (hBB : ∀ m k i, RefinedBound (castLoopMatrix fun n => base (shB i n)) {0, 1, 2, 3} 4
      fun ℓ => vNum e 0 1 A base c m k ℓ μ ν)
    {j' : Fin 7} (hj' : j' = 1 ∨ j' = 3)
    (hcw : ∀ i j, MajIntCrit (fun n => base (shA i j n)) 0 j'.castSucc)
    {F : Type} [Fintype F] (Φ : Lepton.Flavors F) (hmass : ∀ g, m₀ ≤ Φ.mass g) :
    MajLRayInc fun a b k =>
      blockVal base c (fun m k ℓ μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNum e 0 1 A base c m k ℓ μ ν)
        (fun k μ ν => ((b ^ 2 - a ^ 2 : ℝ) : ℂ) * vNumE4 e 0 1 A k μ ν) Φ m₀ a b k μ ν := by
  have hS0 : 0 ≤ ∑ g, Φ.mass g :=
    Finset.sum_nonneg fun g _ => hm₀.le.trans (hmass g)
  have hX : m₀ ≤ blockX Φ m₀ := by simp only [blockX]; linarith
  exact MajLRayInc.sum Finset.univ fun f _ => (majLInc_triVal e A hA base c hrow hrow4 hm₀ μ ν
    hcA hcB hBA hBB hj' hcw (hmass f) hX (by linarith)).const_mul (Φ.coeff f : ℂ)

end Pieces

section Classes

variable {F : Type} [Fintype F] (Φ : Lepton.Flavors F) {m₀ : ℝ} (hm₀ : 0 < m₀)
  (hmass : ∀ g, m₀ ≤ Φ.mass g) (e : ℝ) (μ ν : Fin 4)

include hm₀ hmass

/-- **Increments of the class `VA` at light comparable pairs along the ray.** -/
theorem majLInc_vVal_VA : MajLRayInc fun a b k => vVal aVA baseVA cVA Φ e m₀ a b k μ ν :=
  (majLInc_blockVal e aVA (fun a b ρ σ => isOddG_aVA a b ρ σ) baseVA cVA (by decide) (by decide) hm₀
    μ ν critA_VA critB_VA
    (fun m k i j => rb_vNum e 0 1 aVA baseVA cVA (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k μ ν)
    (fun m k i => rb_vNum e 0 1 aVA baseVA cVA (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k μ ν)
    (j' := 3) (Or.inr rfl) (by decide) Φ hmass).congr fun u _ a b _ _ => by
      rw [vVal_eq_blockVal]

/-- **Increments of the class `VB` at light comparable pairs along the ray.** -/
theorem majLInc_vVal_VB : MajLRayInc fun a b k => vVal aVB baseVB cVB Φ e m₀ a b k μ ν :=
  (majLInc_blockVal e aVB (fun a b ρ σ => isOddG_aVB a b ρ σ) baseVB cVB (by decide) (by decide) hm₀
    μ ν critA_VB critB_VB
    (fun m k i j => rb_vNum e 0 1 aVB baseVB cVB (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k μ ν)
    (fun m k i => rb_vNum e 0 1 aVB baseVB cVB (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k μ ν)
    (j' := 1) (Or.inl rfl) (by decide) Φ hmass).congr fun u _ a b _ _ => by
      rw [vVal_eq_blockVal]

/-- **Increments of the class `VC` at light comparable pairs along the ray.** -/
theorem majLInc_vVal_VC : MajLRayInc fun a b k => vVal aVC baseVC cVC Φ e m₀ a b k μ ν :=
  (majLInc_blockVal e aVC (fun a b ρ σ => isOddG_aVC a b ρ σ) baseVC cVC (by decide) (by decide) hm₀
    μ ν critA_VC critB_VC
    (fun m k i j => rb_vNum e 0 1 aVC baseVC cVC (shA i j) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k μ ν)
    (fun m k i => rb_vNum e 0 1 aVC baseVC cVC (shB i) ![0, 1, 2, 3]
      (e4_cases _ _ ⟨rfl, rfl, rfl, rfl⟩) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) m k μ ν)
    (j' := 3) (Or.inr rfl) (by decide) Φ hmass).congr fun u _ a b _ _ => by
      rw [vVal_eq_blockVal]

end Classes

/-- **The three `MajLRayInc` inputs of `MajLipIns` at `decDil l (decCfg 1 4)`, `l ≥ 1`**
(`m₀ = l`). -/
theorem majLInc_decDil (e : ℝ) {l : ℝ} (hl : 1 ≤ l) :
    (MajLRayInc fun a b k => vVal aVA baseVA cVA (decDil l (decCfg 1 4)) e l a b k 2 3) ∧
      (MajLRayInc fun a b k => vVal aVB baseVB cVB (decDil l (decCfg 1 4)) e l a b k 2 3) ∧
      (MajLRayInc fun a b k => vVal aVC baseVC cVC (decDil l (decCfg 1 4)) e l a b k 2 3) := by
  have hl0 : 0 < l := one_pos.trans_le hl
  have hmass : ∀ g, (1 : ℝ) ≤ (decCfg 1 4).mass g :=
    dec_cfg_mass_ge le_rfl one_pos (by norm_num)
  have hm : ∀ g, l ≤ (decDil l (decCfg 1 4)).mass g := fun g => by
    simpa using majLip_decDil_mass_ge hl0.le hmass g
  exact ⟨majLInc_vVal_VA _ hl0 hm e 2 3, majLInc_vVal_VB _ hl0 hm e 2 3,
    majLInc_vVal_VC _ hl0 hm e 2 3⟩

end QED.GradedProof.RPi4

end
