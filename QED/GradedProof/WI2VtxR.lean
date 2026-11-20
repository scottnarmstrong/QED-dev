/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.WI2RX
public import QED.GradedProof.WI2VtxChain
public import QED.GradedProof.WI2VtxOpen

/-!
# A7 for the classes `S₊`, `L`, `S₋`: insertions on the rainbow `R`

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A7. At zero photon momentum (`p' = p`, on shell), the open vertex classes `S₊`, `L`, `S₋`
contracted with `r` (`∑_μ r_μ V^μ`) are, up to `e · cRX P`, the parametric values of the chain of
the rainbow `R` in its Ward–Takahashi routing (`dR`) with the zero-momentum insertion
`(m - k̸) r̸ (m - k̸)` on the electron line `0`, `1`, `2` respectively, over the data with that
line doubled (`sum_lower_classLimitV_Sp`, `_L`, `_Sm`). These are the terms of the
Ward–Takahashi derivative of `R` (`hasDerivAt_repR_wt`).

The identity holds pointwise for the joint integrands at every `ε > 0` after the change of loop
momenta `ℓ ↦ mₓ ℓ` (`mSp`, `mL`, `mSm`, determinant `±1`): the class numerator is the chain form
(`chain_Sp`, …), the contraction merges the two electron numerators next to the external vertex
(`sum_lower_smul_chainNum_Sp`, …), and the eight denominators are those of the doubled data in
the order `σSp`, … (checked numerically before formalizing: `check_a7_open.py`, relative defect
`≤ 1.1e-15`). Then `sum_lower_classLimitV_eq`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.WI2

open QED.GradedProof.SE2 QED.Integration.TwoLoop QED.WickModel QED.TwoLoop.ClassLimit
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.TwoLoop.ClassIntegrable (openClasses)

theorem lineDenom_eq_of {m m' : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {q : Fin (m + 1) → Fin 4 → ℝ}
    {M : Fin (m + 1) → ℝ} {α' : Fin (m' + 1) → Fin 2 → ℝ} {q' : Fin (m' + 1) → Fin 4 → ℝ}
    {M' : Fin (m' + 1) → ℝ} {ε : ℝ} {i : Fin (m + 1)} {i' : Fin (m' + 1)}
    {ℓ ℓ' : Fin 2 → Fin 4 → ℝ}
    (hk : QED.Integration.TwoLoop.lineMomentum α q i ℓ =
      QED.Integration.TwoLoop.lineMomentum α' q' i' ℓ') (hM : M i = M' i') :
    lineDenom α q M ε i ℓ = lineDenom α' q' M' ε i' ℓ' := by
  simp only [lineDenom, hk, hM]

/-- The electron numerators of an open class at `p' = p`. -/
noncomputable def vtxE (c : Class5) (line : Fin 4 → FermionLine c.rep) (P : Params)
    (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun i => electronNumerator P.m (classMomE c p p ℓ (.inl (line i)))

theorem openCoeff_eq (e : ℝ) :
    (I * e) ^ 5 * (1 / I) ^ 4 = e * ((I * e) ^ 4 * (1 / I) ^ 3) := by
  field_simp

theorem twoLoopNorm_mul_openCoeff (Q : Params) :
    twoLoopNorm * ((I * Q.e) ^ 5 * (1 / I) ^ 4) = Q.e * cRX Q := by
  rw [openCoeff_eq, cRX, twoLoopNorm]
  ring

theorem vpos_dR_onShell (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) : (dR P).VPos ((dR P).mom p) := by
  have hν : 0 < min P.mγ P.Λ := lt_min hmγ hΛ
  exact vpos_dR P hm hν le_rfl (by rw [hp]; nlinarith)

theorem vpos_dX_onShell (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) : (dX P).VPos ((dX P).mom p) := by
  have hν : 0 < min (min P.mγ P.Λ) (2 * P.m) := lt_min (lt_min hmγ hΛ) (by linarith)
  exact vpos_dX P hm hν (min_le_left _ _) (min_le_right _ _) (by rw [hp]; nlinarith)

/-! ### `Sp`: slot `0` of `R` -/

theorem mem_openClasses_Sp : Class5.Sp ∈ openClasses := by decide

/-- The change of loop momenta from the class routing of `Sp` to the routing of `dR`. -/
def mSp : Matrix (Fin 2) (Fin 2) ℤ := !![-1, -1; -1, 0]

theorem isUnit_det_mSp : IsUnit mSp.det := by simp [mSp, Matrix.det_fin_two]

/-- The lines of the Pauli–Villars form of `Sp` as lines of `dR` with line `0` doubled. -/
noncomputable def σSp : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![0, 7, 1, 2, 3, 5, 4, 6] (by decide)

theorem classMomE_Sp_wt (P : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (k : Fin 4) :
    classMomE .Sp p p ℓ (.inl (lineSp k)) =
      QED.Integration.TwoLoop.lineMomentum (dR P).α ((dR P).mom p)
        (eRX (![0, 0, 1, 2] k)) (loopAff mSp 0 ℓ) := by
  fin_cases k <;> funext μ <;>
    simp [classMomE, QED.Integration.TwoLoop.lineMomentum, loopAff, mSp, Fin.sum_univ_two,
      castLoopMatrix, class5LoopMatrix, SEData.mom, dR, wtData, aRw, cswRX, eRX, extMomenta,
      classCpSpMomenta, lineIdx_Sp] <;> ring

theorem lineDenom_vtx_Sp (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (i : Fin 8) :
    lineDenom (vtxData mem_openClasses_Sp P).α ((vtxData mem_openClasses_Sp P).mom p)
        (vtxData mem_openClasses_Sp P).M ε i ℓ =
      lineDenom (dR P).α ((dR P).mom p) (dR P).M ε (![0, 0, 1, 2, 3, 5, 4, 6] i)
        (loopAff mSp 0 ℓ) := by
  refine lineDenom_eq_of ?_ ?_
  · fin_cases i <;> funext μ <;>
      simp [QED.Integration.TwoLoop.lineMomentum, loopAff, mSp, Fin.sum_univ_two, vtxData,
        castLoopMatrix, class5LoopMatrixPV, class5LoopMatrix, SEData.mom, dR, wtData, aRw,
        cswRX, csVtx] <;> ring
  · fin_cases i <;> rfl

theorem prod_lineDenom_vtx_Sp (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, lineDenom (vtxData mem_openClasses_Sp P).α ((vtxData mem_openClasses_Sp P).mom p)
        (vtxData mem_openClasses_Sp P).M ε i ℓ =
      ∏ i, lineDenom ((dR P).dup (eRX 0)).α (dbl (eRX 0) ((dR P).mom p))
        ((dR P).dup (eRX 0)).M ε i (loopAff mSp 0 ℓ) := by
  refine Fintype.prod_equiv σSp _ _ fun i => ?_
  rw [lineDenom_vtx_Sp]
  refine Eq.trans ?_
    (lineDenom_dbl (dR P).α ((dR P).mom p) (dR P).M ε (eRX 0) (σSp i) _).symm
  congr 1
  fin_cases i <;> rfl

theorem chV_Sp (P : Params) (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (dR P).chV eRX (wR P) P.m p r (loopAff mSp 0 ℓ) 0 =
      chainAt (wR P) ![vtxE .Sp lineSp P p ℓ 1 * Dirac.slash r * vtxE .Sp lineSp P p ℓ 0,
        vtxE .Sp lineSp P p ℓ 2,
        vtxE .Sp lineSp P p ℓ 3] := by
  simp only [SEData.chV]
  congr 1
  funext j
  fin_cases j <;>
    simp [Function.update, SEData.chE, SEData.mom, dR, wtData, cswRX, eRX, vtxE, classMomE_Sp_wt P]

theorem num_Sp (P : Params) (p r : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * (twoLoopNorm * classNumeratorE .Sp P (fun _ => p)
      (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ) =
        P.e * cRX P * (dR P).chV eRX (wR P) P.m p r (loopAff mSp 0 ℓ) 0 α β := by
  have hch := congrFun (congrFun (sum_lower_smul_chainNum_Sp P (vtxE .Sp lineSp P p ℓ) r) α) β
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hch
  have hc : ∀ μ, classNumeratorE .Sp P (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α)
      (fun _ => β) (fun _ => μ) ℓ =
        (I * P.e) ^ 5 * (1 / I) ^ 4 * chainNum P permSp (vtxE .Sp lineSp P p ℓ) μ α β :=
    fun μ => chain_Sp P _ _ _ _ _ _ ℓ
  rw [chV_Sp, ← hch, ← twoLoopNorm_mul_openCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hc]
  ring

/-- **A7 for `Sp`**: the contracted limit of `Sp` at `p' = p` is `e · cRX` times the
parametric value of the chain of `R` with the insertion `(m - k̸) r̸ (m - k̸)` on line `0`. -/
theorem sum_lower_classLimitV_Sp (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * classLimitV .Sp P p p μ α β =
      P.e * cRX P * ((dR P).dup (eRX 0)).pvF
        (fun ℓ => (dR P).chV eRX (wR P) P.m p r ℓ 0 α β) (dbl (eRX 0) ((dR P).mom p)) :=
  sum_lower_classLimitV_eq mem_openClasses_Sp P hm hmγ hΛ hp r α β
    ((dR P).good_chV (wR P) P.m eRX_injective (mem_E_eRX intCrit_Rw P) p r 0 α β)
    ((vpos_dR_onShell P hm hmγ hΛ hp).dup (eRX 0)) mSp isUnit_det_mSp 0 _ (num_Sp P p r α β)
    fun ε _ ℓ => prod_lineDenom_vtx_Sp P p ε ℓ

/-! ### `L`: slot `1` of `R` -/

theorem mem_openClasses_L : Class5.L ∈ openClasses := by decide

/-- The change of loop momenta from the class routing of `L` to the routing of `dR`. -/
def mL : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; -1, 0]

theorem isUnit_det_mL : IsUnit mL.det := by simp [mL, Matrix.det_fin_two]

/-- The lines of the Pauli–Villars form of `L` as lines of `dR` with line `1` doubled. -/
noncomputable def σL : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![0, 1, 7, 2, 3, 5, 4, 6] (by decide)

theorem classMomE_L_wt (P : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (k : Fin 4) :
    classMomE .L p p ℓ (.inl (lineL k)) =
      QED.Integration.TwoLoop.lineMomentum (dR P).α ((dR P).mom p)
        (eRX (![0, 1, 1, 2] k)) (loopAff mL 0 ℓ) := by
  fin_cases k <;> funext μ <;>
    simp [classMomE, QED.Integration.TwoLoop.lineMomentum, loopAff, mL, Fin.sum_univ_two,
      castLoopMatrix, class5LoopMatrix, SEData.mom, dR, wtData, aRw, cswRX, eRX, extMomenta,
      classLXMomenta, lineIdx_L]

theorem lineDenom_vtx_L (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (i : Fin 8) :
    lineDenom (vtxData mem_openClasses_L P).α ((vtxData mem_openClasses_L P).mom p)
        (vtxData mem_openClasses_L P).M ε i ℓ =
      lineDenom (dR P).α ((dR P).mom p) (dR P).M ε (![0, 1, 1, 2, 3, 5, 4, 6] i)
        (loopAff mL 0 ℓ) := by
  refine lineDenom_eq_of ?_ ?_
  · fin_cases i <;> funext μ <;>
      simp [QED.Integration.TwoLoop.lineMomentum, loopAff, mL, Fin.sum_univ_two, vtxData,
        castLoopMatrix, class5LoopMatrixPV, class5LoopMatrix, SEData.mom, dR, wtData, aRw,
        cswRX, csVtx] <;> ring
  · fin_cases i <;> rfl

theorem prod_lineDenom_vtx_L (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, lineDenom (vtxData mem_openClasses_L P).α ((vtxData mem_openClasses_L P).mom p)
        (vtxData mem_openClasses_L P).M ε i ℓ =
      ∏ i, lineDenom ((dR P).dup (eRX 1)).α (dbl (eRX 1) ((dR P).mom p))
        ((dR P).dup (eRX 1)).M ε i (loopAff mL 0 ℓ) := by
  refine Fintype.prod_equiv σL _ _ fun i => ?_
  rw [lineDenom_vtx_L]
  refine Eq.trans ?_
    (lineDenom_dbl (dR P).α ((dR P).mom p) (dR P).M ε (eRX 1) (σL i) _).symm
  congr 1
  fin_cases i <;> rfl

theorem chV_L (P : Params) (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (dR P).chV eRX (wR P) P.m p r (loopAff mL 0 ℓ) 1 =
      chainAt (wR P) ![vtxE .L lineL P p ℓ 0,
        vtxE .L lineL P p ℓ 2 * Dirac.slash r * vtxE .L lineL P p ℓ 1,
        vtxE .L lineL P p ℓ 3] := by
  simp only [SEData.chV]
  congr 1
  funext j
  fin_cases j <;>
    simp [Function.update, SEData.chE, SEData.mom, dR, wtData, cswRX, eRX, vtxE, classMomE_L_wt P]

theorem num_L (P : Params) (p r : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * (twoLoopNorm * classNumeratorE .L P (fun _ => p)
      (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ) =
        P.e * cRX P * (dR P).chV eRX (wR P) P.m p r (loopAff mL 0 ℓ) 1 α β := by
  have hch := congrFun (congrFun (sum_lower_smul_chainNum_L P (vtxE .L lineL P p ℓ) r) α) β
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hch
  have hc : ∀ μ, classNumeratorE .L P (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α)
      (fun _ => β) (fun _ => μ) ℓ =
        (I * P.e) ^ 5 * (1 / I) ^ 4 * chainNum P permL (vtxE .L lineL P p ℓ) μ α β :=
    fun μ => chain_L P _ _ _ _ _ _ ℓ
  rw [chV_L, ← hch, ← twoLoopNorm_mul_openCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hc]
  ring

/-- **A7 for `L`**: the contracted limit of `L` at `p' = p` is `e · cRX` times the
parametric value of the chain of `R` with the insertion `(m - k̸) r̸ (m - k̸)` on line `1`. -/
theorem sum_lower_classLimitV_L (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * classLimitV .L P p p μ α β =
      P.e * cRX P * ((dR P).dup (eRX 1)).pvF
        (fun ℓ => (dR P).chV eRX (wR P) P.m p r ℓ 1 α β) (dbl (eRX 1) ((dR P).mom p)) :=
  sum_lower_classLimitV_eq mem_openClasses_L P hm hmγ hΛ hp r α β
    ((dR P).good_chV (wR P) P.m eRX_injective (mem_E_eRX intCrit_Rw P) p r 1 α β)
    ((vpos_dR_onShell P hm hmγ hΛ hp).dup (eRX 1)) mL isUnit_det_mL 0 _ (num_L P p r α β)
    fun ε _ ℓ => prod_lineDenom_vtx_L P p ε ℓ

/-! ### `Sm`: slot `2` of `R` -/

theorem mem_openClasses_Sm : Class5.Sm ∈ openClasses := by decide

/-- The change of loop momenta from the class routing of `Sm` to the routing of `dR`. -/
def mSm : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; -1, 1]

theorem isUnit_det_mSm : IsUnit mSm.det := by simp [mSm, Matrix.det_fin_two]

/-- The lines of the Pauli–Villars form of `Sm` as lines of `dR` with line `2` doubled. -/
noncomputable def σSm : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective ![0, 1, 2, 7, 3, 5, 4, 6] (by decide)

theorem classMomE_Sm_wt (P : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (k : Fin 4) :
    classMomE .Sm p p ℓ (.inl (lineSm k)) =
      QED.Integration.TwoLoop.lineMomentum (dR P).α ((dR P).mom p)
        (eRX (![0, 1, 2, 2] k)) (loopAff mSm 0 ℓ) := by
  fin_cases k <;> funext μ <;>
    simp [classMomE, QED.Integration.TwoLoop.lineMomentum, loopAff, mSm, Fin.sum_univ_two,
      castLoopMatrix, class5LoopMatrix, SEData.mom, dR, wtData, aRw, cswRX, eRX, extMomenta,
      classCmSmMomenta, lineIdx_Sm, add_comm]

theorem lineDenom_vtx_Sm (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (i : Fin 8) :
    lineDenom (vtxData mem_openClasses_Sm P).α ((vtxData mem_openClasses_Sm P).mom p)
        (vtxData mem_openClasses_Sm P).M ε i ℓ =
      lineDenom (dR P).α ((dR P).mom p) (dR P).M ε (![0, 1, 2, 2, 3, 5, 4, 6] i)
        (loopAff mSm 0 ℓ) := by
  refine lineDenom_eq_of ?_ ?_
  · fin_cases i <;> funext μ <;>
      simp [QED.Integration.TwoLoop.lineMomentum, loopAff, mSm, Fin.sum_univ_two, vtxData,
        castLoopMatrix, class5LoopMatrixPV, class5LoopMatrix, SEData.mom, dR, wtData, aRw,
        cswRX, csVtx, add_comm]
  · fin_cases i <;> rfl

theorem prod_lineDenom_vtx_Sm (P : Params) (p : Fin 4 → ℝ) (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ i, lineDenom (vtxData mem_openClasses_Sm P).α ((vtxData mem_openClasses_Sm P).mom p)
        (vtxData mem_openClasses_Sm P).M ε i ℓ =
      ∏ i, lineDenom ((dR P).dup (eRX 2)).α (dbl (eRX 2) ((dR P).mom p))
        ((dR P).dup (eRX 2)).M ε i (loopAff mSm 0 ℓ) := by
  refine Fintype.prod_equiv σSm _ _ fun i => ?_
  rw [lineDenom_vtx_Sm]
  refine Eq.trans ?_
    (lineDenom_dbl (dR P).α ((dR P).mom p) (dR P).M ε (eRX 2) (σSm i) _).symm
  congr 1
  fin_cases i <;> rfl

theorem chV_Sm (P : Params) (p r : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    (dR P).chV eRX (wR P) P.m p r (loopAff mSm 0 ℓ) 2 =
      chainAt (wR P) ![vtxE .Sm lineSm P p ℓ 0,
        vtxE .Sm lineSm P p ℓ 1,
        vtxE .Sm lineSm P p ℓ 3 * Dirac.slash r * vtxE .Sm lineSm P p ℓ 2] := by
  simp only [SEData.chV]
  congr 1
  funext j
  fin_cases j <;>
    simp [Function.update, SEData.chE, SEData.mom, dR, wtData, cswRX, eRX, vtxE, classMomE_Sm_wt P]

theorem num_Sm (P : Params) (p r : Fin 4 → ℝ) (α β : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * (twoLoopNorm * classNumeratorE .Sm P (fun _ => p)
      (fun _ => p) (fun _ => p - p) (fun _ => α) (fun _ => β) (fun _ => μ) ℓ) =
        P.e * cRX P * (dR P).chV eRX (wR P) P.m p r (loopAff mSm 0 ℓ) 2 α β := by
  have hch := congrFun (congrFun (sum_lower_smul_chainNum_Sm P (vtxE .Sm lineSm P p ℓ) r) α) β
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hch
  have hc : ∀ μ, classNumeratorE .Sm P (fun _ => p) (fun _ => p) (fun _ => p - p) (fun _ => α)
      (fun _ => β) (fun _ => μ) ℓ =
        (I * P.e) ^ 5 * (1 / I) ^ 4 * chainNum P permSm (vtxE .Sm lineSm P p ℓ) μ α β :=
    fun μ => chain_Sm P _ _ _ _ _ _ ℓ
  rw [chV_Sm, ← hch, ← twoLoopNorm_mul_openCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hc]
  ring

/-- **A7 for `Sm`**: the contracted limit of `Sm` at `p' = p` is `e · cRX` times the
parametric value of the chain of `R` with the insertion `(m - k̸) r̸ (m - k̸)` on line `2`. -/
theorem sum_lower_classLimitV_Sm (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    {p : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (r : Fin 4 → ℝ) (α β : Fin 4) :
    ∑ μ, ((Minkowski.lower r μ : ℝ) : ℂ) * classLimitV .Sm P p p μ α β =
      P.e * cRX P * ((dR P).dup (eRX 2)).pvF
        (fun ℓ => (dR P).chV eRX (wR P) P.m p r ℓ 2 α β) (dbl (eRX 2) ((dR P).mom p)) :=
  sum_lower_classLimitV_eq mem_openClasses_Sm P hm hmγ hΛ hp r α β
    ((dR P).good_chV (wR P) P.m eRX_injective (mem_E_eRX intCrit_Rw P) p r 2 α β)
    ((vpos_dR_onShell P hm hmγ hΛ hp).dup (eRX 2)) mSm isUnit_det_mSm 0 _ (num_Sm P p r α β)
    fun ε _ ℓ => prod_lineDenom_vtx_Sm P p ε ℓ

end QED.GradedProof.WI2

end
