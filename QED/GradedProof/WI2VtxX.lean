/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2VtxR

/-!
# A7 for the classes `C₊`, `X`, `C₋`: insertions on the crossed graph `X`

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A7. As `QED/GradedProof/WI2VtxR.lean` for the crossed self-energy `X` (`dX`): the open vertex
classes `C₊`, `X`, `C₋` at `p' = p`, contracted with `r`, are `e · cRX P` times the parametric
values of the chain of `X` with the insertion `(m - k̸) r̸ (m - k̸)` on the electron line `0`,
`1`, `2` (`sum_lower_classLimitV_Cp`, `_X`, `_Cm`), the terms of `hasDerivAt_repX_wt`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.ClassLimit
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.TwoLoop.ClassIntegrable (openClasses)

/-! ### `Cp`: slot `0` of `X` -/

theorem mem_openClasses_Cp : Class5.Cp ∈ openClasses := by decide

/-- The change of loop momenta from the class routing of `Cp` to the routing of `dX`. -/
def mCp : Matrix (Fin 2) (Fin 2) ℤ := !![-1, -1; -1, 0]

theorem isUnit_det_mCp : IsUnit mCp.det := by simp [mCp, Matrix.det_fin_two]

/-- The lines of the Pauli–Villars form of `Cp` as lines of `dX` with line `0` doubled. -/
noncomputable def σCp : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![0, 7, 1, 2, 3, 5, 4, 6] (by decide)

theorem classMomE_Cp_wt (P : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (k : Fin 4) :
    classMomE .Cp p p ℓ (.inl (lineCp k)) =
      QED.Integration.TwoLoop.lineMomentum (dX P).α ((dX P).mom p)
        (eRX (![0, 0, 1, 2] k)) (loopAff mCp 0 ℓ) := by
  fin_cases k <;> funext μ <;>
    simp [classMomE, QED.Integration.TwoLoop.lineMomentum, loopAff, mCp, Fin.sum_univ_two,
      castLoopMatrix, class5LoopMatrix, SEData.mom, dX, wtData, aXw, cswRX, eRX, extMomenta,
      classCpSpMomenta, lineIdx_Cp] <;> ring

theorem lineDenom_vtx_Cp (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (i : Fin 8) :
    lineDenom (vtxData mem_openClasses_Cp P).α ((vtxData mem_openClasses_Cp P).mom p)
        (vtxData mem_openClasses_Cp P).M ε i ℓ =
      lineDenom (dX P).α ((dX P).mom p) (dX P).M ε (![0, 0, 1, 2, 3, 5, 4, 6] i)
        (loopAff mCp 0 ℓ) := by
  refine lineDenom_eq_of ?_ ?_
  · fin_cases i <;> funext μ <;>
      simp [QED.Integration.TwoLoop.lineMomentum, loopAff, mCp, Fin.sum_univ_two, vtxData,
        castLoopMatrix, class5LoopMatrixPV, class5LoopMatrix, SEData.mom, dX, wtData, aXw,
        cswRX, csVtx] <;> ring
  · fin_cases i <;> rfl

theorem prod_lineDenom_vtx_Cp (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, lineDenom (vtxData mem_openClasses_Cp P).α ((vtxData mem_openClasses_Cp P).mom p)
        (vtxData mem_openClasses_Cp P).M ε i ℓ =
      ∏ i, lineDenom ((dX P).dup (eRX 0)).α (dbl (eRX 0) ((dX P).mom p))
        ((dX P).dup (eRX 0)).M ε i (loopAff mCp 0 ℓ) := by
  refine Fintype.prod_equiv σCp _ _ fun i => ?_
  rw [lineDenom_vtx_Cp]
  refine Eq.trans ?_
    (lineDenom_dbl (dX P).α ((dX P).mom p) (dX P).M ε (eRX 0) (σCp i) _).symm
  congr 1
  fin_cases i <;> rfl

theorem chV_Cp (P : Params) (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (dX P).chV eRX (wX P) P.m p r (loopAff mCp 0 ℓ) 0 =
      chainAt (wX P) ![vtxE .Cp lineCp P p ℓ 1 * Dirac.slash r * vtxE .Cp lineCp P p ℓ 0,
        vtxE .Cp lineCp P p ℓ 2,
        vtxE .Cp lineCp P p ℓ 3] := by
  simp only [SEData.chV]
  congr 1
  funext j
  fin_cases j <;>
    simp [Function.update, SEData.chE, SEData.mom, dX, wtData, cswRX, eRX, vtxE, classMomE_Cp_wt P]

theorem num_Cp (P : Params) (p r : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * (twoLoopNorm * classNumeratorE .Cp P (fun _ => p)
      (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ) =
        P.e * cRX P * (dX P).chV eRX (wX P) P.m p r (loopAff mCp 0 ℓ) 0 α β := by
  have hch := congrFun (congrFun (sum_lower_smul_chainNum_Cp P (vtxE .Cp lineCp P p ℓ) r) α) β
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hch
  have hc : ∀ μ, classNumeratorE .Cp P (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α)
      (fun _ => β) (fun _ => μ) ℓ =
        (I * P.e) ^ 5 * (1 / I) ^ 4 * chainNum P permCp (vtxE .Cp lineCp P p ℓ) μ α β :=
    fun μ => chain_Cp P _ _ _ _ _ _ ℓ
  rw [chV_Cp, ← hch, ← twoLoopNorm_mul_openCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hc]
  ring

/-- **A7 for `Cp`**: the contracted limit of `Cp` at `p' = p` is `e · cRX` times the
parametric value of the chain of `X` with the insertion `(m - k̸) r̸ (m - k̸)` on line `0`. -/
theorem sum_lower_classLimitV_Cp (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * classLimitV .Cp P p p μ α β =
      P.e * cRX P * ((dX P).dup (eRX 0)).pvF
        (fun ℓ => (dX P).chV eRX (wX P) P.m p r ℓ 0 α β) (dbl (eRX 0) ((dX P).mom p)) :=
  sum_lower_classLimitV_eq mem_openClasses_Cp P hm hmγ hΛ hp r α β
    ((dX P).good_chV (wX P) P.m eRX_injective (mem_E_eRX intCrit_Xw P) p r 0 α β)
    ((vpos_dX_onShell P hm hmγ hΛ hp).dup (eRX 0)) mCp isUnit_det_mCp 0 _ (num_Cp P p r α β)
    fun ε _ ℓ => prod_lineDenom_vtx_Cp P p ε ℓ

/-! ### `X`: slot `1` of `X` -/

theorem mem_openClasses_X : Class5.X ∈ openClasses := by decide

/-- The change of loop momenta from the class routing of `X` to the routing of `dX`. -/
def mX : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; -1, 0]

theorem isUnit_det_mX : IsUnit mX.det := by simp [mX, Matrix.det_fin_two]

/-- The lines of the Pauli–Villars form of `X` as lines of `dX` with line `1` doubled. -/
noncomputable def σX : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![0, 1, 7, 2, 3, 5, 4, 6] (by decide)

theorem classMomE_X_wt (P : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (k : Fin 4) :
    classMomE .X p p ℓ (.inl (lineX k)) =
      QED.Integration.TwoLoop.lineMomentum (dX P).α ((dX P).mom p)
        (eRX (![0, 1, 1, 2] k)) (loopAff mX 0 ℓ) := by
  fin_cases k <;> funext μ <;>
    simp [classMomE, QED.Integration.TwoLoop.lineMomentum, loopAff, mX, Fin.sum_univ_two,
      castLoopMatrix, class5LoopMatrix, SEData.mom, dX, wtData, aXw, cswRX, eRX, extMomenta,
      classLXMomenta, lineIdx_X, add_comm]

theorem lineDenom_vtx_X (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (i : Fin 8) :
    lineDenom (vtxData mem_openClasses_X P).α ((vtxData mem_openClasses_X P).mom p)
        (vtxData mem_openClasses_X P).M ε i ℓ =
      lineDenom (dX P).α ((dX P).mom p) (dX P).M ε (![0, 1, 1, 2, 3, 5, 4, 6] i)
        (loopAff mX 0 ℓ) := by
  refine lineDenom_eq_of ?_ ?_
  · fin_cases i <;> funext μ <;>
      simp [QED.Integration.TwoLoop.lineMomentum, loopAff, mX, Fin.sum_univ_two, vtxData,
        castLoopMatrix, class5LoopMatrixPV, class5LoopMatrix, SEData.mom, dX, wtData, aXw,
        cswRX, csVtx, add_comm]
  · fin_cases i <;> rfl

theorem prod_lineDenom_vtx_X (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, lineDenom (vtxData mem_openClasses_X P).α ((vtxData mem_openClasses_X P).mom p)
        (vtxData mem_openClasses_X P).M ε i ℓ =
      ∏ i, lineDenom ((dX P).dup (eRX 1)).α (dbl (eRX 1) ((dX P).mom p))
        ((dX P).dup (eRX 1)).M ε i (loopAff mX 0 ℓ) := by
  refine Fintype.prod_equiv σX _ _ fun i => ?_
  rw [lineDenom_vtx_X]
  refine Eq.trans ?_
    (lineDenom_dbl (dX P).α ((dX P).mom p) (dX P).M ε (eRX 1) (σX i) _).symm
  congr 1
  fin_cases i <;> rfl

theorem chV_X (P : Params) (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (dX P).chV eRX (wX P) P.m p r (loopAff mX 0 ℓ) 1 =
      chainAt (wX P) ![vtxE .X lineX P p ℓ 0,
        vtxE .X lineX P p ℓ 2 * Dirac.slash r * vtxE .X lineX P p ℓ 1,
        vtxE .X lineX P p ℓ 3] := by
  simp only [SEData.chV]
  congr 1
  funext j
  fin_cases j <;>
    simp [Function.update, SEData.chE, SEData.mom, dX, wtData, cswRX, eRX, vtxE, classMomE_X_wt P]

theorem num_X (P : Params) (p r : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * (twoLoopNorm * classNumeratorE .X P (fun _ => p)
      (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ) =
        P.e * cRX P * (dX P).chV eRX (wX P) P.m p r (loopAff mX 0 ℓ) 1 α β := by
  have hch := congrFun (congrFun (sum_lower_smul_chainNum_X P (vtxE .X lineX P p ℓ) r) α) β
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hch
  have hc : ∀ μ, classNumeratorE .X P (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α)
      (fun _ => β) (fun _ => μ) ℓ =
        (I * P.e) ^ 5 * (1 / I) ^ 4 * chainNum P permX (vtxE .X lineX P p ℓ) μ α β :=
    fun μ => chain_X P _ _ _ _ _ _ ℓ
  rw [chV_X, ← hch, ← twoLoopNorm_mul_openCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hc]
  ring

/-- **A7 for `X`**: the contracted limit of `X` at `p' = p` is `e · cRX` times the
parametric value of the chain of `X` with the insertion `(m - k̸) r̸ (m - k̸)` on line `1`. -/
theorem sum_lower_classLimitV_X (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * classLimitV .X P p p μ α β =
      P.e * cRX P * ((dX P).dup (eRX 1)).pvF
        (fun ℓ => (dX P).chV eRX (wX P) P.m p r ℓ 1 α β) (dbl (eRX 1) ((dX P).mom p)) :=
  sum_lower_classLimitV_eq mem_openClasses_X P hm hmγ hΛ hp r α β
    ((dX P).good_chV (wX P) P.m eRX_injective (mem_E_eRX intCrit_Xw P) p r 1 α β)
    ((vpos_dX_onShell P hm hmγ hΛ hp).dup (eRX 1)) mX isUnit_det_mX 0 _ (num_X P p r α β)
    fun ε _ ℓ => prod_lineDenom_vtx_X P p ε ℓ

/-! ### `Cm`: slot `2` of `X` -/

theorem mem_openClasses_Cm : Class5.Cm ∈ openClasses := by decide

/-- The change of loop momenta from the class routing of `Cm` to the routing of `dX`. -/
def mCm : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 1; -1, 0]

theorem isUnit_det_mCm : IsUnit mCm.det := by simp [mCm, Matrix.det_fin_two]

/-- The lines of the Pauli–Villars form of `Cm` as lines of `dX` with line `2` doubled. -/
noncomputable def σCm : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![0, 1, 2, 7, 3, 5, 4, 6] (by decide)

theorem classMomE_Cm_wt (P : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (k : Fin 4) :
    classMomE .Cm p p ℓ (.inl (lineCm k)) =
      QED.Integration.TwoLoop.lineMomentum (dX P).α ((dX P).mom p)
        (eRX (![0, 1, 2, 2] k)) (loopAff mCm 0 ℓ) := by
  fin_cases k <;> funext μ <;>
    simp [classMomE, QED.Integration.TwoLoop.lineMomentum, loopAff, mCm, Fin.sum_univ_two,
      castLoopMatrix, class5LoopMatrix, SEData.mom, dX, wtData, aXw, cswRX, eRX, extMomenta,
      classCmSmMomenta, lineIdx_Cm, add_comm]

theorem lineDenom_vtx_Cm (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (i : Fin 8) :
    lineDenom (vtxData mem_openClasses_Cm P).α ((vtxData mem_openClasses_Cm P).mom p)
        (vtxData mem_openClasses_Cm P).M ε i ℓ =
      lineDenom (dX P).α ((dX P).mom p) (dX P).M ε (![0, 1, 2, 2, 3, 5, 4, 6] i)
        (loopAff mCm 0 ℓ) := by
  refine lineDenom_eq_of ?_ ?_
  · fin_cases i <;> funext μ <;>
      simp [QED.Integration.TwoLoop.lineMomentum, loopAff, mCm, Fin.sum_univ_two, vtxData,
        castLoopMatrix, class5LoopMatrixPV, class5LoopMatrix, SEData.mom, dX, wtData, aXw,
        cswRX, csVtx, add_comm]
  · fin_cases i <;> rfl

theorem prod_lineDenom_vtx_Cm (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, lineDenom (vtxData mem_openClasses_Cm P).α ((vtxData mem_openClasses_Cm P).mom p)
        (vtxData mem_openClasses_Cm P).M ε i ℓ =
      ∏ i, lineDenom ((dX P).dup (eRX 2)).α (dbl (eRX 2) ((dX P).mom p))
        ((dX P).dup (eRX 2)).M ε i (loopAff mCm 0 ℓ) := by
  refine Fintype.prod_equiv σCm _ _ fun i => ?_
  rw [lineDenom_vtx_Cm]
  refine Eq.trans ?_
    (lineDenom_dbl (dX P).α ((dX P).mom p) (dX P).M ε (eRX 2) (σCm i) _).symm
  congr 1
  fin_cases i <;> rfl

theorem chV_Cm (P : Params) (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (dX P).chV eRX (wX P) P.m p r (loopAff mCm 0 ℓ) 2 =
      chainAt (wX P) ![vtxE .Cm lineCm P p ℓ 0,
        vtxE .Cm lineCm P p ℓ 1,
        vtxE .Cm lineCm P p ℓ 3 * Dirac.slash r * vtxE .Cm lineCm P p ℓ 2] := by
  simp only [SEData.chV]
  congr 1
  funext j
  fin_cases j <;>
    simp [Function.update, SEData.chE, SEData.mom, dX, wtData, cswRX, eRX, vtxE, classMomE_Cm_wt P]

theorem num_Cm (P : Params) (p r : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * (twoLoopNorm * classNumeratorE .Cm P (fun _ => p)
      (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ) =
        P.e * cRX P * (dX P).chV eRX (wX P) P.m p r (loopAff mCm 0 ℓ) 2 α β := by
  have hch := congrFun (congrFun (sum_lower_smul_chainNum_Cm P (vtxE .Cm lineCm P p ℓ) r) α) β
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hch
  have hc : ∀ μ, classNumeratorE .Cm P (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α)
      (fun _ => β) (fun _ => μ) ℓ =
        (I * P.e) ^ 5 * (1 / I) ^ 4 * chainNum P permCm (vtxE .Cm lineCm P p ℓ) μ α β :=
    fun μ => chain_Cm P _ _ _ _ _ _ ℓ
  rw [chV_Cm, ← hch, ← twoLoopNorm_mul_openCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hc]
  ring

/-- **A7 for `Cm`**: the contracted limit of `Cm` at `p' = p` is `e · cRX` times the
parametric value of the chain of `X` with the insertion `(m - k̸) r̸ (m - k̸)` on line `2`. -/
theorem sum_lower_classLimitV_Cm (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * classLimitV .Cm P p p μ α β =
      P.e * cRX P * ((dX P).dup (eRX 2)).pvF
        (fun ℓ => (dX P).chV eRX (wX P) P.m p r ℓ 2 α β) (dbl (eRX 2) ((dX P).mom p)) :=
  sum_lower_classLimitV_eq mem_openClasses_Cm P hm hmγ hΛ hp r α β
    ((dX P).good_chV (wX P) P.m eRX_injective (mem_E_eRX intCrit_Xw P) p r 2 α β)
    ((vpos_dX_onShell P hm hmγ hΛ hp).dup (eRX 2)) mCm isUnit_det_mCm 0 _ (num_Cm P p r α β)
    fun ε _ ℓ => prod_lineDenom_vtx_Cm P p ε ℓ

end QED.GradedProof.WI2

end
