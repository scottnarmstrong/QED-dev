/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCRegXGeom
public import QED.ChainProof.SetCUnitMPauli
public import QED.TwoLoop.UnitSCGraphSpMain
public import QED.TwoLoop.UnitSCGraphSmMain
public import QED.TwoLoop.UnitSCGraphCpMain
public import QED.TwoLoop.UnitSCGraphCmMain

/-!
# Grouped Pauli numerators for the set (c) electron chains

The chain decomposition from `QED/TwoLoop/UnitSCGraph.lean` carries over to the
unit with extra photon denominators. Grouping their parameters preserves the
three trace contractions. The enlarged simplex supplies the factorials, and
the extra masses occur in the second Symanzik function.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.TwoLoop.LimitCovariance
open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.ChainProof.SetCUnit
open QED.TwoLoop.PauliZero QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit
open QED.TwoLoop.ParamNumEval QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitSCGraph
open QED.TwoLoop.UnitLGraphTrace QED.TwoLoop.ClassIntegrable
open QED.Integration.Feynman (simplexPoint)
open QED.Integration.TwoLoop

variable {r : ℕ}

private theorem unitMMomenta_emb (c : Class5) (s : Fin 8) (p p' : Fin 4 → ℝ) (i : Fin 8) :
    unitMMomenta c s (fun _ : Fin r => 1) p p' (mEmb r i) = pvMomentaE c p p' i := by
  simp [unitMMomenta, mScale, mLine, mExt_mEmb]

private theorem unitM_lineMomentum_emb (c : Class5) (s : Fin 8) (p p' : Fin 4 → ℝ) (i : Fin 8)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    Integration.TwoLoop.lineMomentum (unitMMatrix c s (fun _ : Fin r => 1))
      (unitMMomenta c s (fun _ : Fin r => 1) p p') (mEmb r i) ℓ =
      Integration.TwoLoop.lineMomentum (classAlpha c) (pvMomentaE c p p') i ℓ := by
  funext ν
  unfold Integration.TwoLoop.lineMomentum
  simp only [unitMMatrix_mEmb, unitMMomenta_emb]

private theorem classChain_unitM (c : Class5) (P : Params) (s : Fin 8) (u : ℝ) (μ : Fin 4)
    (l : Fin 5 → Fin 4) :
    classChain c P u μ l =
      elecChain (unitMMatrix c s (fun _ : Fin r => 1))
        (unitMMomenta c s (fun _ : Fin r => 1) (restMomentum P.m) (curveMomentum P.m u))
        (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
        (fun _ => P.m) (mEmb r ∘ ladderLines) := by
  funext ℓ
  simp only [classChain, elecChain, Function.comp_apply, unitM_lineMomentum_emb]

private theorem unitMPauliNum_chain {c : Class5} {pa : Equiv.Perm (Fin 5)}
    {line : Fin 4 → FermionLine c.rep} (hch : IsChainForm c pa line)
    (hmom : IsLineRouting c line) (hc : c ∈ openClasses) (P : Params) (s : Fin 8)
    (M : Fin (r + 8) → ℝ)
    (x : Fin (r + 7) → ℝ) (u : ℝ) :
    unitMPauliNum c P s (fun _ => 1) M x u =
      -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4,
        classWeight pa P μ l * paramNumOf (classChain c P u μ l)
          (unitMMatrix c s (fun _ => 1))
          (unitMMomenta c s (fun _ => 1) (restMomentum P.m) (curveMomentum P.m u)) M x := by
  set α := unitMMatrix c s (fun _ : Fin r => 1)
  set pm := unitMMomenta c s (fun _ : Fin r => 1) (restMomentum P.m) (curveMomentum P.m u)
  have hq : ∀ μ l, ∃ Q : LoopQuartic, Q.eval = classChain c P u μ l := fun μ l =>
    exists_quartic_elecChain _ _ _ _ _
  have hqμ : ∀ μ, ∃ Q : LoopQuartic,
      Q.eval = fun ℓ => ∑ l : Fin 5 → Fin 4, classWeight pa P μ l * classChain c P u μ l ℓ :=
    fun μ => exists_quartic_sum _ _ (hq μ)
  have h1 : unitMPauliNum c P s (fun _ => 1) M x u = -((π : ℂ) ^ 4) *
      paramNumOf (fun ℓ => ∑ j : Idx,
        pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
          openF c P (curveMomentum P.m u) j ℓ) α pm M x := by
    rw [paramNumOf_sum _ _ _ _ _ _ fun j => exists_quartic_openF hc P _ j, unitMPauliNum,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (fun ℓ => ∑ j : Idx,
      pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
        openF c P (curveMomentum P.m u) j ℓ) =
      fun ℓ => ladderConst P * ∑ μ, (1 : ℂ) *
        ∑ l : Fin 5 → Fin 4, classWeight pa P μ l * classChain c P u μ l ℓ := by
    funext ℓ
    rw [sum_pauliWt_openF_of_chain hch hmom]
    simp only [one_mul]
    rfl
  rw [h1, h2, paramNumOf_const_mul _ _ _ _ _ (exists_quartic_sum _ _ hqμ),
    paramNumOf_sum _ _ _ _ _ _ hqμ]
  simp only [one_mul]
  rw [mul_assoc]
  congr 2
  exact Finset.sum_congr rfl fun μ _ => paramNumOf_sum _ _ _ _ _ _ (hq μ)

/-- The three electron-chain trace terms retain their shape under grouping, with the
factorials of the enlarged simplex. -/
theorem unitMPauliNum_eq_T_of_chain {c : Class5} {pa : Equiv.Perm (Fin 5)}
    {line : Fin 4 → FermionLine c.rep} (hch : IsChainForm c pa line) (hmom : IsLineRouting c line)
    (hc : c ∈ openClasses) (P : Params) (s : Fin 8) (M : Fin (r + 8) → ℝ)
    (x : Fin (r + 7) → ℝ) (u : ℝ) :
    let w := groupExtra s (simplexPoint x)
    let V : ℂ := ↑(symanzikV (unitMMatrix c s (fun _ : Fin r => 1))
      (unitMMomenta c s (fun _ : Fin r => 1) (restMomentum P.m) (curveMomentum P.m u))
      M (simplexPoint x))
    unitMPauliNum c P s (fun _ => 1) M x u =
      ((r + 3).factorial : ℂ) / 6 * classT1 c pa P w u +
      ((r + 2).factorial : ℂ) / 2 * classT2 c pa P w u * V +
      ((r + 1).factorial : ℂ) * classT3 c pa P w u * V ^ 2 := by
  dsimp only
  rw [unitMPauliNum_chain hch hmom hc]
  have eAt (B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :=
    @paramNumOf_elecChain (r + 7) (unitMMatrix c s (fun _ : Fin r => 1))
      (unitMMomenta c s (fun _ : Fin r => 1) (restMomentum P.m) (curveMomentum P.m u))
      M x B (fun _ => P.m) (mEmb r ∘ ladderLines)
  simp only [classChain_unitM (r := r) c P s, eAt, symanzikMatrix_unitM_group,
    symanzikU_unitM_group, loopShift_unitM_group]
  have he :
      elecAt (unitMMatrix c s (fun _ : Fin r => 1))
        (unitMMomenta c s (fun _ : Fin r => 1) (restMomentum P.m) (curveMomentum P.m u))
        (fun _ => P.m) (mEmb r ∘ ladderLines)
        (-loopShift (classAlpha c) (pvMomentaE c (restMomentum P.m) (curveMomentum P.m u))
          (groupExtra s (simplexPoint x))) =
      classE c P (groupExtra s (simplexPoint x)) u := by
    funext k
    simp only [classE, QED.TwoLoop.UnitSCGraph.classMom, elecAt, Function.comp_apply,
      unitM_lineMomentum_emb]
  have e2 (B E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
      chainTwo (unitMMatrix c s (fun _ : Fin r => 1)) B E (mEmb r ∘ ladderLines) A =
        chainTwo (classAlpha c) B E ladderLines A := by
    simp only [chainTwo, contrC, Function.comp_apply, unitMMatrix_mEmb]
  have e3 (B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
      chainFour (unitMMatrix c s (fun _ : Fin r => 1)) B (mEmb r ∘ ladderLines) A =
        chainFour (classAlpha c) B ladderLines A := by
    simp only [chainFour, contrC, Function.comp_apply, unitMMatrix_mEmb]
  have h4 : r + 7 - 4 = r + 3 := by omega
  have h5 : r + 7 - 5 = r + 2 := by omega
  have h6 : r + 7 - 6 = r + 1 := by omega
  simp only [he, e2, e3, h4, h5, h6, classT1, classT2, classT3]
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring

private theorem continuous_unitMMomenta_apply (c : Class5) (s : Fin 8)
    (κ : Fin r → ℝ) (p : Fin 4 → ℝ) (i : Fin (r + 8)) (μ : Fin 4) :
    Continuous fun p' : Fin 4 → ℝ => unitMMomenta c s κ p p' i μ := by
  rcases extMomenta_cases c p (pvLines (mLine s i)) with h | h | h
  · simp only [unitMMomenta, pvMomentaE, Pi.smul_apply, smul_eq_mul, h]
    exact continuous_const
  · simp only [unitMMomenta, pvMomentaE, Pi.smul_apply, smul_eq_mul, h]
    exact continuous_const.mul (continuous_apply μ)
  · simp only [unitMMomenta, pvMomentaE, Pi.smul_apply, smul_eq_mul, h]
    exact continuous_const

attribute [local fun_prop] continuous_unitMMomenta_apply

private theorem tendsto_unitM_remainder (c : Class5) (P : Params) (s : Fin 8)
    (κ : Fin r → ℝ) (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ) :
    Tendsto (fun u => (symanzikV (unitMMatrix c s κ)
      (unitMMomenta c s κ (restMomentum P.m) (curveMomentum P.m u)) M (simplexPoint x) : ℂ))
      (𝓝 0) (𝓝 (unitMV0 c P s κ M x : ℂ)) := by
  have h : Continuous fun p' : Fin 4 → ℝ =>
      symanzikV (unitMMatrix c s κ) (unitMMomenta c s κ (restMomentum P.m) p')
        M (simplexPoint x) := by
    unfold symanzikV symanzikVector QED.Minkowski.dot
    fun_prop
  exact (Complex.continuous_ofReal.tendsto _).comp
    ((h.tendsto (restMomentum P.m)).comp (tendsto_curveMomentum P.m))

/-- A jet of the extended Pauli numerator from the three ordinary trace jets. -/
theorem hasJet2_unitMPauliNum_of_chain {c : Class5} {pa : Equiv.Perm (Fin 5)}
    {line : Fin 4 → FermionLine c.rep} (hch : IsChainForm c pa line) (hmom : IsLineRouting c line)
    (hc : c ∈ openClasses) (P : Params) (s : Fin 8) (M : Fin (r + 8) → ℝ)
    (x : Fin (r + 7) → ℝ) {A B : ℂ}
    (h₁ : HasJet2 (classT1 c pa P (groupExtra s (simplexPoint x))) 0 0 A)
    (h₂ : HasJet2 (classT2 c pa P (groupExtra s (simplexPoint x))) 0 0 B)
    (h₃ : HasJet2 (classT3 c pa P (groupExtra s (simplexPoint x))) 0 0 0) :
    HasJet2 (unitMPauliNum c P s (fun _ => 1) M x) 0 0
      (((r + 3).factorial : ℂ) / 6 * A +
        ((r + 2).factorial : ℂ) / 2 * B * (unitMV0 c P s (fun _ => 1) M x : ℂ)) := by
  have hV := tendsto_unitM_remainder c P s (fun _ => 1) M x
  have j₁ := h₁.const_mul (((r + 3).factorial : ℂ) / 6)
  have j₂ := h₂.const_mul (((r + 2).factorial : ℂ) / 2)
  have j₃ := h₃.const_mul ((r + 1).factorial : ℂ)
  simp only [mul_zero] at j₁ j₂ j₃
  have j₂ := hasJet2_mul_tendsto j₂ hV
  have j₃ := hasJet2_mul_tendsto j₃ (hV.pow 2)
  have H := ((j₁.add j₂).add j₃).congr (fun u => unitMPauliNum_eq_T_of_chain hch hmom hc P s M x u)
  simpa only [mul_zero, zero_mul, zero_add, add_zero] using H

/-- The grouped second-order Pauli coefficient of the `L` skeleton. -/
theorem secondCoeff_unitMPauliNum_L {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (s : Fin 8) (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ)
    (hU : lU (groupExtra s (simplexPoint x)) ≠ 0) :
    let w := groupExtra s (simplexPoint x)
    secondCoeff (unitMPauliNum .L P s (fun _ => 1) M x) =
      ((r + 3).factorial : ℂ) / 6 * secondCoeff (ladderT1 P w) +
        ((r + 2).factorial : ℂ) / 2 * secondCoeff (ladderT2 P w) *
          (unitMV0 .L P s (fun _ => 1) M x : ℂ) := by
  dsimp only
  have j₁ := hasJet2_ladderT1 hm he hU
  have j₂ := hasJet2_ladderT2 hm he hU
  have j₃ := hasJet2_ladderT3 hm (groupExtra s (simplexPoint x))
  rw [j₁.secondCoeff_eq, j₂.secondCoeff_eq]
  exact (hasJet2_unitMPauliNum_of_chain chain_L (fun p p' ℓ k => classMomE_L_eq p p' k ℓ)
    (by decide : Class5.L ∈ openClasses) P s M x j₁ j₂ j₃).secondCoeff_eq

/-- The grouped second-order Pauli coefficient of the `Sp` skeleton. -/
theorem secondCoeff_unitMPauliNum_Sp {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (s : Fin 8) (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ)
    (hU : spU (groupExtra s (simplexPoint x)) ≠ 0) :
    let w := groupExtra s (simplexPoint x)
    secondCoeff (unitMPauliNum .Sp P s (fun _ => 1) M x) =
      ((r + 3).factorial : ℂ) / 6 * secondCoeff (classT1 .Sp permSp P w) +
        ((r + 2).factorial : ℂ) / 2 * secondCoeff (classT2 .Sp permSp P w) *
          (unitMV0 .Sp P s (fun _ => 1) M x : ℂ) := by
  dsimp only
  have j₁ := hasJet2_spT1 hm he hU
  have j₂ := hasJet2_spT2 hm he hU
  have j₃ := hasJet2_spT3 hm (groupExtra s (simplexPoint x))
  rw [j₁.secondCoeff_eq, j₂.secondCoeff_eq]
  exact (hasJet2_unitMPauliNum_of_chain isChainForm_Sp classMomE_Sp_eq
    Sp_mem_openClasses P s M x j₁ j₂ j₃).secondCoeff_eq

/-- The grouped second-order Pauli coefficient of the `Sm` skeleton. -/
theorem secondCoeff_unitMPauliNum_Sm {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (s : Fin 8) (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ)
    (hU : smU (groupExtra s (simplexPoint x)) ≠ 0) :
    let w := groupExtra s (simplexPoint x)
    secondCoeff (unitMPauliNum .Sm P s (fun _ => 1) M x) =
      ((r + 3).factorial : ℂ) / 6 * secondCoeff (classT1 .Sm permSm P w) +
        ((r + 2).factorial : ℂ) / 2 * secondCoeff (classT2 .Sm permSm P w) *
          (unitMV0 .Sm P s (fun _ => 1) M x : ℂ) := by
  dsimp only
  have j₁ := hasJet2_smT1 hm he hU
  have j₂ := hasJet2_smT2 hm he hU
  have j₃ := hasJet2_smT3 hm (groupExtra s (simplexPoint x))
  rw [j₁.secondCoeff_eq, j₂.secondCoeff_eq]
  exact (hasJet2_unitMPauliNum_of_chain isChainForm_Sm classMomE_Sm_eq
    Sm_mem_openClasses P s M x j₁ j₂ j₃).secondCoeff_eq

/-- The grouped second-order Pauli coefficient of the `Cp` skeleton. -/
theorem secondCoeff_unitMPauliNum_Cp {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (s : Fin 8) (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ)
    (hU : cpU (groupExtra s (simplexPoint x)) ≠ 0) :
    let w := groupExtra s (simplexPoint x)
    secondCoeff (unitMPauliNum .Cp P s (fun _ => 1) M x) =
      ((r + 3).factorial : ℂ) / 6 * secondCoeff (classT1 .Cp permCp P w) +
        ((r + 2).factorial : ℂ) / 2 * secondCoeff (classT2 .Cp permCp P w) *
          (unitMV0 .Cp P s (fun _ => 1) M x : ℂ) := by
  dsimp only
  have j₁ := hasJet2_cpT1 hm he hU
  have j₂ := hasJet2_cpT2 hm he hU
  have j₃ := hasJet2_cpT3 hm (groupExtra s (simplexPoint x))
  rw [j₁.secondCoeff_eq, j₂.secondCoeff_eq]
  exact (hasJet2_unitMPauliNum_of_chain isChainForm_Cp classMomE_Cp_eq
    Cp_mem_openClasses P s M x j₁ j₂ j₃).secondCoeff_eq

/-- The grouped second-order Pauli coefficient of the `Cm` skeleton. -/
theorem secondCoeff_unitMPauliNum_Cm {P : Params} (hm : P.m = 1) (he : P.e = 1)
    (s : Fin 8) (M : Fin (r + 8) → ℝ) (x : Fin (r + 7) → ℝ)
    (hU : cmU (groupExtra s (simplexPoint x)) ≠ 0) :
    let w := groupExtra s (simplexPoint x)
    secondCoeff (unitMPauliNum .Cm P s (fun _ => 1) M x) =
      ((r + 3).factorial : ℂ) / 6 * secondCoeff (classT1 .Cm permCm P w) +
        ((r + 2).factorial : ℂ) / 2 * secondCoeff (classT2 .Cm permCm P w) *
          (unitMV0 .Cm P s (fun _ => 1) M x : ℂ) := by
  dsimp only
  have j₁ := hasJet2_cmT1 hm he hU
  have j₂ := hasJet2_cmT2 hm he hU
  have j₃ := hasJet2_cmT3 hm (groupExtra s (simplexPoint x))
  rw [j₁.secondCoeff_eq, j₂.secondCoeff_eq]
  exact (hasJet2_unitMPauliNum_of_chain isChainForm_Cm classMomE_Cm_eq
    Cm_mem_openClasses P s M x j₁ j₂ j₃).secondCoeff_eq

end QED.ChainProof.SetCUnitM

end
