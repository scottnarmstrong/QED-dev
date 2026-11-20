/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2VtxVPAlg

/-!
# A7 for the class `VP`: the denominators

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A7 for the vacuum-polarization vertex class `VP` at zero photon momentum.

After the change of loop momenta `mVP`, the ten line denominators of the terms `0, 1, 2` of `VP`
(`QED.TwoLoop.Bridge.vpDenom`, at `p' = p`) are those of the pieces `vD1`, `vD2`, `vD3` of the
self-energy class `V` with the open line doubled (`prod_vpDenom_zero`, …), and the nine
denominators left after cancelling line `8` or line `3` of term `3` are those of `vD4`, `vD5`
with the open line doubled (`prod_vpDenom_three_eight`, `prod_vpDenom_three_three`). The bubble
lines are matched up to the sign of their momenta.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.Bridge

theorem lineDenom_eq_of_or {m m' : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {q : Fin (m + 1) → Fin 4 → ℝ}
    {M : Fin (m + 1) → ℝ} {α' : Fin (m' + 1) → Fin 2 → ℝ} {q' : Fin (m' + 1) → Fin 4 → ℝ}
    {M' : Fin (m' + 1) → ℝ} {ε : ℝ} {i : Fin (m + 1)} {i' : Fin (m' + 1)}
    {ℓ ℓ' : Fin 2 → Fin 4 → ℝ}
    (hk : lineMomentum α q i ℓ = lineMomentum α' q' i' ℓ' ∨
      lineMomentum α q i ℓ = -lineMomentum α' q' i' ℓ') (hM : M i = M' i') :
    lineDenom α q M ε i ℓ = lineDenom α' q' M' ε i' ℓ' := by
  have hd : Minkowski.dot (lineMomentum α q i ℓ) (lineMomentum α q i ℓ) =
      Minkowski.dot (lineMomentum α' q' i' ℓ') (lineMomentum α' q' i' ℓ') := by
    rcases hk with h | h <;> rw [h]
    simp [Minkowski.dot]
  simp only [lineDenom, hd, hM]

variable {n : ℕ} (hn : 6 ≤ n) (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
  (E : Finset (Fin (n + 1))) (hw : IntNoSubdivergenceRefined 2 E fun i => awV (sh i))

/-- The insertion numerator of a piece of `V` on its open line. -/
theorem slotV_vData_apply (Q : Params) (s0 : sh 0 = 0)
    (c : Fin 4 × Fin 4 × Fin 4 × Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ) (p r : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (α β : Fin 4) :
    (vData hn sh Ms E hw).slotV 0 Q.m aSlotV bSlotV c p r ℓ α β = ∑ l, c l ℓ *
      (aSlotV l * insVP Q p r ℓ * bSlotV l) α β := by
  have hk : lineMomentum (vData hn sh Ms E hw).α ((vData hn sh Ms E hw).mom p) 0 ℓ = p - ℓ 0 := by
    have h := lineMomentum_vData hn sh Ms E hw p 0 ℓ
    rw [s0, (bm_loopAff_mV p ℓ).1] at h
    exact h
  have hr : (vData hn sh Ms E hw).mom r 0 = r := by
    change csV (sh 0) • r = r
    rw [s0]
    simp [csV]
  simp only [SEData.slotV, SEData.slotE, hk, hr, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, insVP]

/-- Matches a line momentum of `VP` with a line momentum of a piece of `V`, up to sign. -/
macro "vp_mom" : tactic => `(tactic|
  first
  | (left; funext μ
     simp [QED.Integration.TwoLoop.lineMomentum, loopAff, mVP, Fin.sum_univ_two,
       castLoopMatrix, vpShapeMatrix, vpShapeLines, class5LoopMatrix, vpShapeMomenta,
       classVPMomenta, vD1, vD2, vD3, vD4, vD5, vData, awV, csV, sh1, sh2, sh3, sh4, sh5,
       SEData.mom]
     try ring
     done)
  | (right; funext μ
     simp [QED.Integration.TwoLoop.lineMomentum, loopAff, mVP, Fin.sum_univ_two,
       castLoopMatrix, vpShapeMatrix, vpShapeLines, class5LoopMatrix, vpShapeMomenta,
       classVPMomenta, vD1, vD2, vD3, vD4, vD5, vData, awV, csV, sh1, sh2, sh3, sh4, sh5,
       SEData.mom]
     try ring))

/-- The vertex lines of the terms `0, 1, 2` as lines of the piece of `V`. -/
def τVP : Fin 10 → Fin 9 := ![0, 0, 1, 2, 5, 7, 6, 8, 3, 4]

/-- The vertex lines of the terms `0, 1, 2` as lines of the piece with line `0` doubled. -/
noncomputable def σVP : Equiv.Perm (Fin 10) :=
  Equiv.ofBijective ![0, 9, 1, 2, 5, 7, 6, 8, 3, 4] (by decide)

/-- The vertex lines of term `3` other than line `8`. -/
def ι8 : Fin 9 → Fin 10 := ![0, 1, 2, 3, 4, 5, 6, 7, 9]

/-- The vertex lines of term `3` other than line `3`. -/
def ι3 : Fin 9 → Fin 10 := ![0, 1, 2, 4, 5, 6, 7, 8, 9]

theorem succAbove_eight : Fin.succAbove (8 : Fin 10) = ι8 := by
  funext j
  fin_cases j <;> rfl

theorem succAbove_three : Fin.succAbove (3 : Fin 10) = ι3 := by
  funext j
  fin_cases j <;> rfl

/-- The lines `ι8` as lines of `vD4`. -/
def τ4 : Fin 9 → Fin 8 := ![0, 0, 1, 2, 4, 6, 5, 7, 3]

/-- The lines `ι8` as lines of `vD4` with line `0` doubled. -/
noncomputable def σ4 : Equiv.Perm (Fin 9) :=
  Equiv.ofBijective ![0, 8, 1, 2, 4, 6, 5, 7, 3] (by decide)

/-- The lines `ι3` as lines of `vD5`. -/
def τ5 : Fin 9 → Fin 8 := ![0, 0, 1, 4, 6, 5, 7, 3, 2]

/-- The lines `ι3` as lines of `vD5` with line `0` doubled. -/
noncomputable def σ5 : Equiv.Perm (Fin 9) :=
  Equiv.ofBijective ![0, 8, 1, 4, 6, 5, 7, 3, 2] (by decide)

section Den

variable (Q : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)

theorem lineDenom_vp_zero (i : Fin 10) :
    vpDenom { Q with ε := ε } 0 p p i ℓ =
      lineDenom (vD1 Q).α ((vD1 Q).mom p) (vD1 Q).M ε (τVP i) (loopAff mVP 0 ℓ) := by
  refine lineDenom_eq_of_or ?_ ?_
  · fin_cases i <;> simp only [τVP] <;> vp_mom
  · fin_cases i <;> rfl

theorem lineDenom_vp_one (i : Fin 10) :
    vpDenom { Q with ε := ε } 1 p p i ℓ =
      lineDenom (vD2 Q).α ((vD2 Q).mom p) (vD2 Q).M ε (τVP i) (loopAff mVP 0 ℓ) := by
  refine lineDenom_eq_of_or ?_ ?_
  · fin_cases i <;> simp only [τVP] <;> vp_mom
  · fin_cases i <;> rfl

theorem lineDenom_vp_two (i : Fin 10) :
    vpDenom { Q with ε := ε } 2 p p i ℓ =
      lineDenom (vD3 Q).α ((vD3 Q).mom p) (vD3 Q).M ε (τVP i) (loopAff mVP 0 ℓ) := by
  refine lineDenom_eq_of_or ?_ ?_
  · fin_cases i <;> simp only [τVP] <;> vp_mom
  · fin_cases i <;> rfl

theorem lineDenom_vp_three_eight (j : Fin 9) :
    vpDenom { Q with ε := ε } 3 p p (ι8 j) ℓ =
      lineDenom (vD4 Q).α ((vD4 Q).mom p) (vD4 Q).M ε (τ4 j) (loopAff mVP 0 ℓ) := by
  refine lineDenom_eq_of_or ?_ ?_
  · fin_cases j <;> simp only [τ4, ι8] <;> vp_mom
  · fin_cases j <;> rfl

theorem lineDenom_vp_three_three (j : Fin 9) :
    vpDenom { Q with ε := ε } 3 p p (ι3 j) ℓ =
      lineDenom (vD5 Q).α ((vD5 Q).mom p) (vD5 Q).M ε (τ5 j) (loopAff mVP 0 ℓ) := by
  refine lineDenom_eq_of_or ?_ ?_
  · fin_cases j <;> simp only [τ5, ι3] <;> vp_mom
  · fin_cases j <;> rfl

/-- The denominators of the piece `D` of `V` with the open line doubled, at `mVP ℓ`. -/
noncomputable abbrev dupDen (D : SEData) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∏ j, lineDenom (D.dup 0).α (dbl 0 (D.mom p)) (D.dup 0).M ε j (loopAff mVP 0 ℓ)

theorem prod_vpDenom_zero :
    ∏ i, vpDenom { Q with ε := ε } 0 p p i ℓ = dupDen (vD1 Q) p ε ℓ := by
  refine Fintype.prod_equiv σVP _ _ fun i => ?_
  rw [lineDenom_vp_zero]
  refine Eq.trans ?_ (lineDenom_dbl (vD1 Q).α ((vD1 Q).mom p) (vD1 Q).M ε 0 (σVP i) _).symm
  congr 1
  fin_cases i <;> rfl

theorem prod_vpDenom_one :
    ∏ i, vpDenom { Q with ε := ε } 1 p p i ℓ = dupDen (vD2 Q) p ε ℓ := by
  refine Fintype.prod_equiv σVP _ _ fun i => ?_
  rw [lineDenom_vp_one]
  refine Eq.trans ?_ (lineDenom_dbl (vD2 Q).α ((vD2 Q).mom p) (vD2 Q).M ε 0 (σVP i) _).symm
  congr 1
  fin_cases i <;> rfl

theorem prod_vpDenom_two :
    ∏ i, vpDenom { Q with ε := ε } 2 p p i ℓ = dupDen (vD3 Q) p ε ℓ := by
  refine Fintype.prod_equiv σVP _ _ fun i => ?_
  rw [lineDenom_vp_two]
  refine Eq.trans ?_ (lineDenom_dbl (vD3 Q).α ((vD3 Q).mom p) (vD3 Q).M ε 0 (σVP i) _).symm
  congr 1
  fin_cases i <;> rfl

theorem prod_vpDenom_three_eight :
    ∏ j, vpDenom { Q with ε := ε } 3 p p (ι8 j) ℓ = dupDen (vD4 Q) p ε ℓ := by
  refine Fintype.prod_equiv σ4 _ _ fun j => ?_
  rw [lineDenom_vp_three_eight]
  refine Eq.trans ?_ (lineDenom_dbl (vD4 Q).α ((vD4 Q).mom p) (vD4 Q).M ε 0 (σ4 j) _).symm
  congr 1
  fin_cases j <;> rfl

theorem prod_vpDenom_three_three :
    ∏ j, vpDenom { Q with ε := ε } 3 p p (ι3 j) ℓ = dupDen (vD5 Q) p ε ℓ := by
  refine Fintype.prod_equiv σ5 _ _ fun j => ?_
  rw [lineDenom_vp_three_three]
  refine Eq.trans ?_ (lineDenom_dbl (vD5 Q).α ((vD5 Q).mom p) (vD5 Q).M ε 0 (σ5 j) _).symm
  congr 1
  fin_cases j <;> rfl

/-- **Term `3` of `VP` after cancelling one denominator**, at `ε > 0`. -/
theorem vpDenom_three_split (hε : 0 < ε) :
    (vpDenom { Q with ε := ε } 3 p p 8 ℓ + vpDenom { Q with ε := ε } 3 p p 3 ℓ) *
        ∏ i, (vpDenom { Q with ε := ε } 3 p p i ℓ)⁻¹ =
      (dupDen (vD4 Q) p ε ℓ)⁻¹ + (dupDen (vD5 Q) p ε ℓ)⁻¹ := by
  have h0 : ∀ i, vpDenom { Q with ε := ε } 3 p p i ℓ ≠ 0 := fun i =>
    lineDenom_ne_zero _ _ _ hε i ℓ
  rw [add_mul]
  congr 1
  · rw [Fin.prod_univ_succAbove _ (8 : Fin 10), succAbove_eight, ← mul_assoc,
      mul_inv_cancel₀ (h0 8), one_mul, ← prod_vpDenom_three_eight, Finset.prod_inv_distrib]
  · rw [Fin.prod_univ_succAbove _ (3 : Fin 10), succAbove_three, ← mul_assoc,
      mul_inv_cancel₀ (h0 3), one_mul, ← prod_vpDenom_three_three, Finset.prod_inv_distrib]

end Den

end QED.GradedProof.WI2

end
