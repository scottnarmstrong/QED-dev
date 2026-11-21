/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKBMerge
public import QED.GradedProof.VP2VAlg

/-!
# Set (a), stage B2: the pieces of a class density on the five-line simplex

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage B2. The pieces of
the photon-mass density `QED.GradedProof.RPi4.triDens` of a class live on the line data of the
shapes `shB i` (six lines: the fermion line `i` doubled) and `shA i j` (seven lines: the fermion
lines `i` and `j` doubled). Merging the doubled lines (`ksB_merge`) moves both to the five-line
simplex `Δ₄` of the class data (rows `base`, photon line `4`), where they become divided
differences, in the mass of the doubled lines, of the five-line collapsed integrand
`ksBAtom(mf)` with fermion masses `mf`:

* `ksBdd f mf i b = (f(mf with line i of mass b) - f(mf))/(mfᵢ² - b²)`;
* **`ksB_pieceB_merge`**: `∫_{Δ₅} pieceF(shB i, masses (mf, Y)) = ∫_{Δ₄} ksBdd ksBAtom mf i Y`;
* **`ksB_pieceA_merge`**: `∫_{Δ₆} pieceF(shA i j, masses (mf, X, Y)) =
  ∫_{Δ₄} ksBdd (ksBdd ksBAtom · i X) mf j Y`.

The right integrands are integrable as they stand (not term by term). The hypotheses are the
integrability of the piece, the vanishing quartic contraction of the numerator (the last merge
lands on `Ê₅`), and `V > 0` on `Δ₄` for every fermion mass vector that occurs.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.ChainProof.SetAKS

open QED.Integration.TwoLoop QED.Integration.SimplexMerge QED.GradedProof.RPi4
open QED.GradedProof.VP2 (shA shB)
open QED.GradedProof.WI2 (dbl ehat)
open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)

/-! ### Line data and masses -/

/-- The masses of the five-line class data: fermion masses `mf`, photon `0`. -/
def ksBM5 (mf : Fin 4 → ℝ) : Fin 5 → ℝ := ![mf 0, mf 1, mf 2, mf 3, 0]

/-- The masses of a six-line piece: fermion masses `mf`, the copy `X`, photon `0`. -/
def ksBM6 (mf : Fin 4 → ℝ) (X : ℝ) : Fin 6 → ℝ := ![mf 0, mf 1, mf 2, mf 3, X, 0]

/-- The masses of a seven-line piece: fermion masses `mf`, the copies `X`, `Y`, photon `0`. -/
def ksBM7 (mf : Fin 4 → ℝ) (X Y : ℝ) : Fin 7 → ℝ := ![mf 0, mf 1, mf 2, mf 3, X, Y, 0]

/-- **The divided difference in the mass of the fermion line `i`.** -/
noncomputable def ksBdd (f : (Fin 4 → ℝ) → ℂ) (mf : Fin 4 → ℝ) (i : Fin 4) (b : ℝ) : ℂ :=
  (f (Function.update mf i b) - f mf) / ((mf i ^ 2 - b ^ 2 : ℝ) : ℂ)

/-- **The five-line collapsed integrand** of the class data (rows `base`, shifts `c l • k`,
photon line `4`) with fermion masses `mf`, at the Feynman point `z`. -/
noncomputable def ksBAtom (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (k : Fin 4 → ℝ)
    (Q : LoopQuartic) (u : ℝ) (z : Fin 5 → ℝ) (mf : Fin 4 → ℝ) : ℂ :=
  pieceF 5 Q (castLoopMatrix base) (fun l => c l • k) (ksBM5 mf) (Fin.last 4) u z

theorem ksB_rows_shA {β : Type*} (g : Fin 5 → β) (i j : Fin 4) :
    (fun l : Fin 7 => g (shA i j l.castSucc)) =
      fun l => dbl (j.castSucc.castSucc : Fin 6) (fun l : Fin 6 => g (shB i l.castSucc))
        (Equiv.swap (5 : Fin 7) 6 l) := by
  funext l
  fin_cases l <;> fin_cases j <;> rfl

theorem ksB_rows_shB {β : Type*} (g : Fin 5 → β) (i : Fin 4) :
    (fun l : Fin 6 => g (shB i l.castSucc)) =
      fun l => dbl (i.castSucc : Fin 5) g (Equiv.swap (4 : Fin 6) 5 l) := by
  funext l
  fin_cases l <;> fin_cases i <;> rfl

theorem ksB_masses7 (mf : Fin 4 → ℝ) (X Y : ℝ) :
    ksBM7 mf X Y = fun l => (Fin.snoc (ksBM6 mf X) Y : Fin 7 → ℝ) (Equiv.swap (5 : Fin 7) 6 l) := by
  funext l
  fin_cases l <;> rfl

theorem ksB_masses6 (mf : Fin 4 → ℝ) (X : ℝ) :
    ksBM6 mf X = fun l => (Fin.snoc (ksBM5 mf) X : Fin 6 → ℝ) (Equiv.swap (4 : Fin 6) 5 l) := by
  funext l
  fin_cases l <;> rfl

theorem ksB_update_M6 (mf : Fin 4 → ℝ) (X Y : ℝ) (j : Fin 4) :
    Function.update (ksBM6 mf X) j.castSucc.castSucc Y = ksBM6 (Function.update mf j Y) X := by
  funext l
  fin_cases j <;> fin_cases l <;> simp [ksBM6, Function.update]

theorem ksB_update_M5 (mf : Fin 4 → ℝ) (X : ℝ) (j : Fin 4) :
    Function.update (ksBM5 mf) j.castSucc X = ksBM5 (Function.update mf j X) := by
  funext l
  fin_cases j <;> fin_cases l <;> simp [ksBM5, Function.update]

theorem ksB_M6_apply (mf : Fin 4 → ℝ) (X : ℝ) (j : Fin 4) :
    ksBM6 mf X j.castSucc.castSucc = mf j := by
  fin_cases j <;> rfl

theorem ksB_M5_apply (mf : Fin 4 → ℝ) (j : Fin 4) : ksBM5 mf j.castSucc = mf j := by
  fin_cases j <;> rfl

/-! ### The derivative hypotheses of the merges -/

theorem ksB_hd_five {Q : LoopQuartic} (hC4 : ∀ A, Q.contractFour A = 0)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) (w : ℝ) (hw : 0 < w) :
    HasDerivAt (ehat 5 Q A X) (-ehat (5 + 1) Q A X w) (w : ℂ) :=
  ksB_hasDerivAt_ehat_five Q A X (hC4 A) (ofReal_ne_zero.2 hw.ne')

theorem ksB_hc_five (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ)
    (w : ℝ) (hw : 0 < w) : ContinuousAt (ehat (5 + 1) Q A X) (w : ℂ) :=
  ksB_continuousAt_ehat 0 Q A X (ofReal_ne_zero.2 hw.ne')

theorem ksB_hd_six (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ) (w : ℝ)
    (hw : 0 < w) : HasDerivAt (ehat 6 Q A X) (-ehat (6 + 1) Q A X w) (w : ℂ) :=
  QED.GradedProof.WI2.hasDerivAt_ehat 0 Q A X (ofReal_ne_zero.2 hw.ne')

theorem ksB_hc_six (Q : LoopQuartic) (A : Matrix (Fin 2) (Fin 2) ℝ) (X : LoopIndex → ℂ)
    (w : ℝ) (hw : 0 < w) : ContinuousAt (ehat (6 + 1) Q A X) (w : ℂ) :=
  ksB_continuousAt_ehat 1 Q A X (ofReal_ne_zero.2 hw.ne')

/-! ### The six-line pieces -/

section Pieces

variable (base : Fin 5 → Fin 2 → ℤ) (c : Fin 5 → ℝ) (k : Fin 4 → ℝ) (Q : LoopQuartic) (u : ℝ)

/-- `V > 0` on `Δ₄` for the class data with fermion masses `mf`. -/
def KsBPos (mf : Fin 4 → ℝ) : Prop :=
  ∀ y ∈ simplexSet 4, symanzikU (castLoopMatrix base) (simplexPoint y) ≠ 0 →
    0 < symanzikV (castLoopMatrix base) (fun l => c l • k) (ksBM5 mf) (simplexPoint y) +
      simplexPoint y (Fin.last 4) * u

/-- **A combination of six-line pieces on `Δ₄`.** Terms `r ∈ s` with weights `w r`, fermion
masses `mf r` and copy mass `X`. -/
theorem ksB_merge_six {ι : Type*} (s : Finset ι) (hC4 : ∀ A, Q.contractFour A = 0) (i : Fin 4)
    (w : ι → ℂ) (mf : ι → Fin 4 → ℝ) (X : ℝ) (hX : ∀ r ∈ s, mf r i ^ 2 ≠ X ^ 2)
    (hI : IntegrableOn (fun x => ∑ r ∈ s, w r * pieceF 6 Q
      (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
      (fun l => c (shB i l.castSucc) • k) (ksBM6 (mf r) X) (Fin.last 5) u (simplexPoint x))
      (simplexSet 5))
    (hpos : ∀ r ∈ s, KsBPos base c k u (mf r) ∧
      KsBPos base c k u (Function.update (mf r) i X)) :
    IntegrableOn (fun y => ∑ r ∈ s, w r *
      ksBdd (ksBAtom base c k Q u (simplexPoint y)) (mf r) i X) (simplexSet 4) ∧
    ∫ x in simplexSet 5, ∑ r ∈ s, w r * pieceF 6 Q
        (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
        (fun l => c (shB i l.castSucc) • k) (ksBM6 (mf r) X) (Fin.last 5) u (simplexPoint x) =
      ∫ y in simplexSet 4, ∑ r ∈ s, w r *
        ksBdd (ksBAtom base c k Q u (simplexPoint y)) (mf r) i X := by
  set e := Equiv.swap (4 : Fin 6) 5
  have hα : (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc)) =
      fun l => dbl (i.castSucc : Fin 5) (castLoopMatrix base) (e l) :=
    ksB_rows_shB (castLoopMatrix base) i
  have hp : (fun l : Fin 6 => c (shB i l.castSucc) • k) =
      fun l => dbl (i.castSucc : Fin 5) (fun l => c l • k) (e l) :=
    ksB_rows_shB (fun l => c l • k) i
  have hγ : e (Fin.last 5) = (Fin.last 4).castSucc := by decide
  simp only [hα, hp, ksB_masses6]
  obtain ⟨hP1, hP2⟩ := ksB_integral_pieceF_perm s e 6 (fun _ => Q)
    (dbl (i.castSucc : Fin 5) (castLoopMatrix base)) (dbl (i.castSucc : Fin 5) fun l => c l • k)
    w (fun r => Fin.snoc (ksBM5 (mf r)) X) (Fin.last 5) u
  rw [hγ] at hP1 hP2
  have hM := ksB_merge s 5 (fun _ => Q) (i := i.castSucc) (γ := Fin.last 4)
    (castLoopMatrix base) (fun l => c l • k) w (fun r => ksBM5 (mf r)) (fun _ => X) u
    (by norm_num) (fun _ _ => ksB_hd_five hC4) (fun _ _ => ksB_hc_five Q)
    (Fin.castSucc_lt_last i).ne' (fun r hr => by rw [ksB_M5_apply]; exact hX r hr)
    (hP1.1 hI) (fun r hr y hy hU => ⟨(hpos r hr).1 y hy hU, by
      rw [ksB_update_M5]; exact (hpos r hr).2 y hy hU⟩)
  simp only [ksB_M5_apply] at hM
  refine ⟨hM.1.congr_fun (fun y _ => ?_) (measurableSet_simplexSet 4),
    hP2.trans (hM.2.trans (setIntegral_congr_fun (measurableSet_simplexSet 4) fun y _ => ?_))⟩ <;>
  simp only [ksBdd, ksBAtom]
  all_goals
    refine Finset.sum_congr rfl fun r _ => ?_
    erw [ksB_update_M5]

/-- **A six-line piece on `Δ₄`.** -/
theorem ksB_pieceB_merge (hC4 : ∀ A, Q.contractFour A = 0) (i : Fin 4) (mf : Fin 4 → ℝ)
    {Y : ℝ} (hY : mf i ^ 2 ≠ Y ^ 2)
    (hI : IntegrableOn (fun x => pieceF 6 Q
      (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
      (fun l => c (shB i l.castSucc) • k) (ksBM6 mf Y) (Fin.last 5) u (simplexPoint x))
      (simplexSet 5))
    (hpos : KsBPos base c k u mf ∧ KsBPos base c k u (Function.update mf i Y)) :
    IntegrableOn (fun y => ksBdd (ksBAtom base c k Q u (simplexPoint y)) mf i Y)
      (simplexSet 4) ∧
    ∫ x in simplexSet 5, pieceF 6 Q (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
        (fun l => c (shB i l.castSucc) • k) (ksBM6 mf Y) (Fin.last 5) u (simplexPoint x) =
      ∫ y in simplexSet 4, ksBdd (ksBAtom base c k Q u (simplexPoint y)) mf i Y := by
  have h := ksB_merge_six base c k Q u ({()} : Finset Unit) hC4 i (fun _ => 1) (fun _ => mf) Y
    (fun _ _ => hY) (by simpa only [Finset.sum_singleton, one_mul] using hI) (fun _ _ => hpos)
  simpa only [Finset.sum_singleton, one_mul] using h

/-- `V > 0` on `Δ₅` for the six-line data of `shB i` with fermion masses `mf` and copy mass
`X`. -/
def KsBPos6 (i : Fin 4) (mf : Fin 4 → ℝ) (X : ℝ) : Prop :=
  ∀ y ∈ simplexSet 5, symanzikU (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
      (simplexPoint y) ≠ 0 →
    0 < symanzikV (castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc))
      (fun l => c (shB i l.castSucc) • k) (ksBM6 mf X) (simplexPoint y) +
      simplexPoint y (Fin.last 5) * u

/-- **A seven-line piece on `Δ₄`**: the two doubled lines merged, `j` (copy mass `Y`) first,
then `i` (copy mass `X`). -/
theorem ksB_pieceA_merge (hC4 : ∀ A, Q.contractFour A = 0) (i j : Fin 4) (mf : Fin 4 → ℝ)
    {X Y : ℝ} (hY : mf j ^ 2 ≠ Y ^ 2) (hX₁ : Function.update mf j Y i ^ 2 ≠ X ^ 2)
    (hX₂ : mf i ^ 2 ≠ X ^ 2)
    (hI : IntegrableOn (fun x => pieceF 7 Q
      (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
      (fun l => c (shA i j l.castSucc) • k) (ksBM7 mf X Y) (Fin.last 6) u (simplexPoint x))
      (simplexSet 6))
    (hpos6 : KsBPos6 base c k u i mf X ∧ KsBPos6 base c k u i (Function.update mf j Y) X)
    (hpos : KsBPos base c k u mf ∧ KsBPos base c k u (Function.update mf i X) ∧
      KsBPos base c k u (Function.update mf j Y) ∧
      KsBPos base c k u (Function.update (Function.update mf j Y) i X)) :
    IntegrableOn (fun y => ksBdd (fun mf' => ksBdd (ksBAtom base c k Q u (simplexPoint y)) mf'
      i X) mf j Y) (simplexSet 4) ∧
    ∫ x in simplexSet 6, pieceF 7 Q (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc))
        (fun l => c (shA i j l.castSucc) • k) (ksBM7 mf X Y) (Fin.last 6) u (simplexPoint x) =
      ∫ y in simplexSet 4, ksBdd (fun mf' => ksBdd (ksBAtom base c k Q u (simplexPoint y)) mf'
        i X) mf j Y := by
  set e := Equiv.swap (5 : Fin 7) 6
  set α6 := castLoopMatrix fun l : Fin 6 => base (shB i l.castSucc)
  set p6 : Fin 6 → Fin 4 → ℝ := fun l => c (shB i l.castSucc) • k
  have hα : (castLoopMatrix fun l : Fin 7 => base (shA i j l.castSucc)) =
      fun l => dbl (j.castSucc.castSucc : Fin 6) α6 (e l) :=
    ksB_rows_shA (castLoopMatrix base) i j
  have hp : (fun l : Fin 7 => c (shA i j l.castSucc) • k) =
      fun l => dbl (j.castSucc.castSucc : Fin 6) p6 (e l) :=
    ksB_rows_shA (fun l => c l • k) i j
  have hγ : e (Fin.last 6) = (Fin.last 5).castSucc := by decide
  simp only [hα, hp, ksB_masses7] at hI ⊢
  obtain ⟨hP1, hP2⟩ := ksB_integral_pieceF_perm ({()} : Finset Unit) e 7 (fun _ => Q)
    (dbl (j.castSucc.castSucc : Fin 6) α6) (dbl (j.castSucc.castSucc : Fin 6) p6)
    (fun _ => 1) (fun _ => Fin.snoc (ksBM6 mf X) Y) (Fin.last 6) u
  simp only [Finset.sum_singleton, one_mul, hγ] at hP1 hP2
  have hj : Fin.last 5 ≠ (j.castSucc.castSucc : Fin 6) := by fin_cases j <;> decide
  have hM := ksB_merge ({()} : Finset Unit) 6 (fun _ => Q) (i := j.castSucc.castSucc)
    (γ := Fin.last 5) α6 p6 (fun _ => 1) (fun _ => ksBM6 mf X) (fun _ => Y) u
    (by norm_num) (fun _ _ => ksB_hd_six Q) (fun _ _ => ksB_hc_six Q) hj
    (fun _ _ => by rw [ksB_M6_apply]; exact hY)
    (by simpa only [Finset.sum_singleton, one_mul] using hP1.1 hI)
    (fun _ _ y hy hU => ⟨hpos6.1 y hy hU, by rw [ksB_update_M6]; exact hpos6.2 y hy hU⟩)
  simp only [Finset.sum_singleton, one_mul, ksB_M6_apply] at hM
  set C : ℂ := ((mf j ^ 2 - Y ^ 2 : ℝ) : ℂ)
  set w : Fin 2 → ℂ := ![1 / C, -(1 / C)]
  set mfs : Fin 2 → Fin 4 → ℝ := ![Function.update mf j Y, mf]
  have hS6 : EqOn (fun y => (pieceF 6 Q α6 p6 (Function.update (ksBM6 mf X)
      (j.castSucc.castSucc : Fin 6) Y) (Fin.last 5) u (simplexPoint y) -
      pieceF 6 Q α6 p6 (ksBM6 mf X) (Fin.last 5) u (simplexPoint y)) / C)
      (fun y => ∑ r, w r * pieceF 6 Q α6 p6 (ksBM6 (mfs r) X) (Fin.last 5) u (simplexPoint y))
      (simplexSet 5) := fun y _ => by
    simp only [Fin.sum_univ_two, w, mfs, Matrix.cons_val_zero, Matrix.cons_val_one]
    erw [ksB_update_M6]
    ring
  have h6 := ksB_merge_six base c k Q u Finset.univ hC4 i w mfs X
    (fun r _ => by fin_cases r <;> assumption)
    (hM.1.congr_fun hS6 (measurableSet_simplexSet 5))
    (fun r _ => by fin_cases r
                   · exact ⟨hpos.2.2.1, hpos.2.2.2⟩
                   · exact ⟨hpos.1, hpos.2.1⟩)
  have hS4 : EqOn (fun y => ∑ r, w r * ksBdd (ksBAtom base c k Q u (simplexPoint y)) (mfs r) i X)
      (fun y => ksBdd (fun mf' => ksBdd (ksBAtom base c k Q u (simplexPoint y)) mf' i X) mf j Y)
      (simplexSet 4) := fun y _ => by
    simp only [Fin.sum_univ_two, w, mfs, Matrix.cons_val_zero, Matrix.cons_val_one]
    conv_rhs => rw [ksBdd]
    ring
  refine ⟨h6.1.congr_fun hS4 (measurableSet_simplexSet 4), ?_⟩
  rw [hP2, hM.2, setIntegral_congr_fun (measurableSet_simplexSet 5) hS6, h6.2]
  exact setIntegral_congr_fun (measurableSet_simplexSet 4) hS4

end Pieces

end QED.ChainProof.SetAKS

end
