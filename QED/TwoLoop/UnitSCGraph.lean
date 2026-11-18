/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLGraphTraceMain
import Mathlib.Tactic.Ring

/-!
# The projected parametric numerator of an open-line class as a combination of chains

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage 1 of the `S + C` link, graph half. This file is the
class-independent part of the ladder's `QED/TwoLoop/UnitLGraph.lean` and
`QED/TwoLoop/UnitLGraphTraceSum.lean`, for an open-line class `c` whose numerator has the chain
form with the photon pairing `π` (`QED.TwoLoop.LimitCovariance.chain_Sp`, …: external photon at
vertex `π 0`, internal photons `(π 1, π 2)`, `(π 3, π 4)`):

* `sum_pauliWt_openF_of_chain`: the Pauli projection of the class numerator is
  `κ ∑_μ ∑_l c^π_{μ,l} tr(B_{μ,l,0} E₃ B_{μ,l,1} E₂ B_{μ,l,2} E₁ B_{μ,l,3} E₀)`, with the photon
  weights `c^π_{μ,l} = [l_{π 0} = μ] η'_{l_{π 1} l_{π 2}} η'_{l_{π 3} l_{π 4}}` (`classWeight`) and
  the chain matrices `B` of the ladder (`QED.TwoLoop.UnitLGraph.ladderB`, which do not depend on
  the pairing);
* `openNum_eq_T_of_chain`: hence `N(x, u) = T₁ + T₂ V + T₃ V²` with the coefficients
  `classT1`, `classT2`, `classT3` (Wick's rule, `QED.TwoLoop.ParamNumEval.paramNumOf_elecChain`);
* `classT1_eq_of_pat`, `classT2_eq_of_pat`, `classT3_eq_of_pat`: if the photon-weight sum of the
  chain traces is `η² pat(P; Y)` for a contraction pattern `pat`, the three coefficients are
  `-π⁴ κ η² U⁻²` times `6 pat(P; Ē)`, the six single contractions of slots of `pat`, and the
  three double contractions.

The four facts of the classes `S₊, S₋, C₊, C₋` used here (the slot momenta are the routed line
momenta of the Pauli–Villars form) are `classMomE_Sp_eq`, `classMomE_Sm_eq`, `classMomE_Cp_eq`,
`classMomE_Cm_eq`.
-/

@[expose] public section

open Complex Matrix
open scoped Real

namespace QED.TwoLoop.UnitSCGraph

open QED.Dirac QED.WickModel QED.TwoLoop.LimitCovariance QED.TwoLoop.PauliZero
open QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.TwoLoop.PauliZeroLimit QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.ParamNumEval
open QED.TwoLoop.UnitLGraph QED.TwoLoop.UnitLGraphTrace
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.TwoLoop (LoopQuartic castLoopMatrix class5LoopMatrixPV symanzikV symanzikU
  symanzikMatrix lineMomentum loopShift)

/-! ### The chain form of the Pauli projection -/

/-- The loop matrix of the Pauli–Villars form of the class `c`. -/
noncomputable abbrev classAlpha (c : Class5) : Fin 8 → Fin 2 → ℝ :=
  castLoopMatrix (class5LoopMatrixPV c)

/-- The photon weight of the pairing `pa`:
`c^π_{μ,l} = [l_{π 0} = μ] η'_{l_{π 1} l_{π 2}} η'_{l_{π 3} l_{π 4}}`. -/
noncomputable def classWeight (pa : Equiv.Perm (Fin 5)) (P : Params) (μ : Fin 4)
    (l : Fin 5 → Fin 4) : ℂ :=
  kron μ (l (pa 0)) * pvEta P (l (pa 1)) (l (pa 2)) * pvEta P (l (pa 3)) (l (pa 4))

/-- The chain form of the numerator of the class `c` with the pairing `pa` and fermion lines
`line` (the hypothesis of `QED.TwoLoop.LimitCovariance.classNumM_cov_of_chain`). -/
def IsChainForm (c : Class5) (pa : Equiv.Perm (Fin 5)) (line : Fin 4 → FermionLine c.rep) : Prop :=
  ∀ (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ),
    classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
      chainNum P pa (fun i => electronNumerator P.m
        (classMomE c (pIn 0) (pOut 0) ℓ (.inl (line i)))) (μ 0) (αOut 0) (βIn 0)

/-- The momenta of the fermion lines are the routed momenta of the lines `0, 1, 2, 3` of the
Pauli–Villars form, the chain slot `k` carrying the line `3 - k`. -/
def IsLineRouting (c : Class5) (line : Fin 4 → FermionLine c.rep) : Prop :=
  ∀ (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (k : Fin 4),
    classMomE c p p' ℓ (.inl (line k)) =
      lineMomentum (classAlpha c) (pvMomentaE c p p') (ladderLines (3 - k)) ℓ

theorem isChainForm_Sp : IsChainForm .Sp permSp lineSp := chain_Sp
theorem isChainForm_Sm : IsChainForm .Sm permSm lineSm := chain_Sm
theorem isChainForm_Cp : IsChainForm .Cp permCp lineCp := chain_Cp
theorem isChainForm_Cm : IsChainForm .Cm permCm lineCm := chain_Cm

theorem classMomE_Sp_eq : IsLineRouting .Sp lineSp := fun p p' ℓ k => by fin_cases k <;> rfl
theorem classMomE_Sm_eq : IsLineRouting .Sm lineSm := fun p p' ℓ k => by fin_cases k <;> rfl
theorem classMomE_Cp_eq : IsLineRouting .Cp lineCp := fun p p' ℓ k => by fin_cases k <;> rfl
theorem classMomE_Cm_eq : IsLineRouting .Cm lineCm := fun p p' ℓ k => by fin_cases k <;> rfl

section Chain

variable {c : Class5} {pa : Equiv.Perm (Fin 5)} {line : Fin 4 → FermionLine c.rep}
  (hch : IsChainForm c pa line)
include hch

/-- **The projected class numerator as a combination of electron chains.** -/
theorem sum_pauliWt_openF_of_chain (hmom : IsLineRouting c line) (P : Params)
    (p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∑ j : Idx, pauliWt P.m p' (restMomentum P.m) j.1 j.2.1 j.2.2 * openF c P p' j ℓ =
      ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, classWeight pa P μ l *
        elecChain (classAlpha c) (pvMomentaE c (restMomentum P.m) p')
          (ladderB P.m p' (restMomentum P.m) μ l) (fun _ => P.m) ladderLines ℓ := by
  have hF : ∀ j : Idx, openF c P p' j ℓ = ladderConst P *
      ∑ l : Fin 5 → Fin 4, classWeight pa P j.1 l *
        openChain (fun t => gamma (l t))
          (fun i => electronNumerator P.m (classMomE c (restMomentum P.m) p' ℓ (.inl (line i))))
          j.2.1 j.2.2 := fun j => by
    simp only [openF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul, hch P,
      chainNum, Matrix.sum_apply, ladderConst, classWeight]
    ring
  simp only [hF, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : ∀ i j, pauliWt P.m p' (restMomentum P.m) μ i j * (ladderConst P *
      ∑ l : Fin 5 → Fin 4, classWeight pa P μ l *
        openChain (fun t => gamma (l t))
          (fun i => electronNumerator P.m (classMomE c (restMomentum P.m) p' ℓ (.inl (line i))))
          i j) =
      ladderConst P * ∑ l : Fin 5 → Fin 4, classWeight pa P μ l *
        (pauliWt P.m p' (restMomentum P.m) μ i j *
          openChain (fun t => gamma (l t))
            (fun i => electronNumerator P.m (classMomE c (restMomentum P.m) p' ℓ (.inl (line i))))
            i j) := fun i j => by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [e, ← Finset.mul_sum]
  congr 1
  rw [sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [← Finset.mul_sum, sum_pauliWt_mul, trace_openChain_mul,
    hmom _ _ _ 0, hmom _ _ _ 1, hmom _ _ _ 2, hmom _ _ _ 3]
  rfl

omit hch in
theorem exists_quartic_openF {c : Class5} (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses)
    (P : Params) (p' : Fin 4 → ℝ) (j : Idx) :
    ∃ Q : LoopQuartic, Q.eval = openF c P p' j := by
  obtain ⟨Q, hQ⟩ := ((QED.TwoLoop.ClassIntegrable.isLoopPoly_classNumeratorE hc P
    (fun _ => p') (fun _ => restMomentum P.m) (fun _ => p' - restMomentum P.m) (fun _ => j.2.1)
    (fun _ => j.2.2) (fun _ => j.1)).const_mul twoLoopNorm).exists_loopQuartic
  refine ⟨Q, hQ.trans (funext fun ℓ => ?_)⟩
  simp only [openF, Matrix.smul_apply, classNumM, Matrix.of_apply, smul_eq_mul]

omit hch in
/-- The chain of the class `c` at the Pauli index `μ` and Lorentz indices `l`, along the curve. -/
noncomputable def classChain (c : Class5) (P : Params) (u : ℝ) (μ : Fin 4) (l : Fin 5 → Fin 4) :
    (Fin 2 → Fin 4 → ℝ) → ℂ :=
  elecChain (classAlpha c) (pvMomentaE c (restMomentum P.m) (curveMomentum P.m u))
    (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l) (fun _ => P.m) ladderLines

/-- **The projected parametric numerator as a combination of chain numerators**:
`N(x, u) = -π⁴ κ ∑_μ ∑_l c^π_{μ,l} paramNumOf (chain_{μ,l})`. -/
theorem openNum_eq_of_chain (hmom : IsLineRouting c line)
    (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses) (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    openNum c P x u = -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4,
      classWeight pa P μ l * paramNumOf (classChain c P u μ l) (classAlpha c)
        (pvMomentaE c (restMomentum P.m) (curveMomentum P.m u)) (pvMasses P) x := by
  set α := classAlpha c
  set pm := pvMomentaE c (restMomentum P.m) (curveMomentum P.m u)
  have hq : ∀ μ l, ∃ Q : LoopQuartic, Q.eval = classChain c P u μ l := fun μ l =>
    exists_quartic_elecChain _ _ _ _ _
  have hqμ : ∀ μ, ∃ Q : LoopQuartic,
      Q.eval = fun ℓ => ∑ l : Fin 5 → Fin 4, classWeight pa P μ l * classChain c P u μ l ℓ :=
    fun μ => exists_quartic_sum _ _ (hq μ)
  have h1 : openNum c P x u = -((π : ℂ) ^ 4) * paramNumOf (fun ℓ => ∑ j : Idx,
      pauliWt P.m (curveMomentum P.m u) (restMomentum P.m) j.1 j.2.1 j.2.2 *
        openF c P (curveMomentum P.m u) j ℓ) α pm (pvMasses P) x := by
    rw [paramNumOf_sum _ _ _ _ _ _ fun j => exists_quartic_openF hc P _ j, openNum,
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

end Chain

/-! ### The three coefficients -/

section Coeff

variable (c : Class5) (pa : Equiv.Perm (Fin 5)) (P : Params) (z : Fin 8 → ℝ) (u : ℝ)

/-- The external momenta of the Pauli–Villars form of the class along the curve. -/
noncomputable abbrev classMom : Fin 8 → Fin 4 → ℝ :=
  pvMomentaE c (restMomentum P.m) (curveMomentum P.m u)

/-- The four electron numerators of the class at the shifted loop momenta, at the point `z`. -/
noncomputable def classE : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  elecAt (classAlpha c) (classMom c P u) (fun _ => P.m) ladderLines
    (-loopShift (classAlpha c) (classMom c P u) z)

/-- The coefficient `T₁` of `V⁰` in the projected numerator, at the point `z`. -/
noncomputable def classT1 : ℂ :=
  -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, classWeight pa P μ l *
    (((symanzikU (classAlpha c) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * ch (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l) (classE c P z u 0)
        (classE c P z u 1) (classE c P z u 2) (classE c P z u 3)))

/-- The coefficient `T₂` of `V¹` in the projected numerator, at the point `z`. -/
noncomputable def classT2 : ℂ :=
  -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, classWeight pa P μ l *
    (((symanzikU (classAlpha c) z ^ 2 : ℝ) : ℂ)⁻¹ *
      chainTwo (classAlpha c) (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
        (classE c P z u) ladderLines (symanzikMatrix (classAlpha c) z))

/-- The coefficient `T₃` of `V²` in the projected numerator, at the point `z`. -/
noncomputable def classT3 : ℂ :=
  -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4, classWeight pa P μ l *
    (((symanzikU (classAlpha c) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * chainFour (classAlpha c) (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
        ladderLines (symanzikMatrix (classAlpha c) z)))

end Coeff

/-- **The projected parametric numerator, explicit** (Wick's rule), as
`QED.TwoLoop.UnitLGraph.openNum_L_explicit`. -/
theorem openNum_explicit_of_chain {c : Class5} {pa : Equiv.Perm (Fin 5)}
    {line : Fin 4 → FermionLine c.rep} (hch : IsChainForm c pa line) (hmom : IsLineRouting c line)
    (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses) (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    openNum c P x u = -((π : ℂ) ^ 4) * ladderConst P * ∑ μ, ∑ l : Fin 5 → Fin 4,
      classWeight pa P μ l *
        (((symanzikU (classAlpha c) (simplexPoint x) ^ 2 : ℝ) : ℂ)⁻¹ *
          (6 * ch (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
              (classE c P (simplexPoint x) u 0) (classE c P (simplexPoint x) u 1)
              (classE c P (simplexPoint x) u 2) (classE c P (simplexPoint x) u 3) +
            chainTwo (classAlpha c) (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
                (classE c P (simplexPoint x) u) ladderLines
                (symanzikMatrix (classAlpha c) (simplexPoint x)) *
              ((symanzikV (classAlpha c) (classMom c P u) (pvMasses P) (simplexPoint x) : ℝ) : ℂ) +
            1 / 4 * chainFour (classAlpha c)
                (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l)
                ladderLines (symanzikMatrix (classAlpha c) (simplexPoint x)) *
              ((symanzikV (classAlpha c) (classMom c P u) (pvMasses P) (simplexPoint x) : ℝ) :
                ℂ) ^ 2)) := by
  rw [openNum_eq_of_chain hch hmom hc]
  simp only [classChain, paramNumOf_elecChain, classE]
  norm_num [Nat.factorial]

/-- **The projected numerator is `T₁ + T₂ V + T₃ V²`.** -/
theorem openNum_eq_T_of_chain {c : Class5} {pa : Equiv.Perm (Fin 5)}
    {line : Fin 4 → FermionLine c.rep} (hch : IsChainForm c pa line) (hmom : IsLineRouting c line)
    (hc : c ∈ QED.TwoLoop.ClassIntegrable.openClasses) (P : Params) (x : Fin 7 → ℝ) (u : ℝ) :
    openNum c P x u = classT1 c pa P (simplexPoint x) u +
      classT2 c pa P (simplexPoint x) u *
        ((symanzikV (classAlpha c) (classMom c P u) (pvMasses P) (simplexPoint x) : ℝ) : ℂ) +
      classT3 c pa P (simplexPoint x) u *
        ((symanzikV (classAlpha c) (classMom c P u) (pvMasses P) (simplexPoint x) : ℝ) : ℂ) ^ 2 := by
  rw [openNum_explicit_of_chain hch hmom hc]
  simp only [classT1, classT2, classT3, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
  · exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring

/-! ### The coefficients through a contraction pattern -/

section Pattern

variable (pa : Equiv.Perm (Fin 5)) (P : Params)
  (pat : (Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) → Matrix (Fin 4) (Fin 4) ℂ →
    Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 4) (Fin 4) ℂ → Matrix (Fin 4) (Fin 4) ℂ → ℂ)

/-- The photon-weight sum of the chain traces is `η² pat(P; Y)`. -/
def IsWeightPattern : Prop :=
  ∀ (p' p : Fin 4 → ℝ) (Y₀ Y₁ Y₂ Y₃ : Matrix (Fin 4) (Fin 4) ℂ),
    ∑ μ, ∑ l : Fin 5 → Fin 4, classWeight pa P μ l * ch (ladderB P.m p' p μ l) Y₀ Y₁ Y₂ Y₃ =
      pvConst P ^ 2 * pat (pauliMat P.m p' p) Y₀ Y₁ Y₂ Y₃

variable {pa P pat} (hpat : IsWeightPattern pa P pat)
include hpat

theorem sum_classWeight_sum_ch (p' p : Fin 4 → ℝ) (Y₀ Y₁ Y₂ Y₃ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, classWeight pa P μ l *
        ∑ ν, ch (ladderB P.m p' p μ l) (Y₀ ν) (Y₁ ν) (Y₂ ν) (Y₃ ν) =
      pvConst P ^ 2 * ∑ ν, pat (pauliMat P.m p' p) (Y₀ ν) (Y₁ ν) (Y₂ ν) (Y₃ ν) := by
  simp only [Finset.mul_sum]
  rw [sum_sum_sum_comm]
  exact Finset.sum_congr rfl fun ν _ => hpat p' p _ _ _ _

theorem sum_classWeight_sum_sum_ch (p' p : Fin 4 → ℝ)
    (Y₀ Y₁ Y₂ Y₃ : Fin 4 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ μ, ∑ l : Fin 5 → Fin 4, classWeight pa P μ l *
        ∑ ν, ∑ ρ, ch (ladderB P.m p' p μ l) (Y₀ ν ρ) (Y₁ ν ρ) (Y₂ ν ρ) (Y₃ ν ρ) =
      pvConst P ^ 2 * ∑ ν, ∑ ρ, pat (pauliMat P.m p' p) (Y₀ ν ρ) (Y₁ ν ρ) (Y₂ ν ρ) (Y₃ ν ρ) := by
  simp only [Finset.mul_sum]
  rw [sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [sum_sum_sum_comm]
  exact Finset.sum_congr rfl fun ρ _ => by rw [← hpat p' p]

variable (c : Class5) (z : Fin 8 → ℝ) (u : ℝ)

/-- The contraction coefficient `C_{kl}` of the slots `k, l` of the chain of the class `c`. -/
noncomputable abbrev classC (c : Class5) (A : Matrix (Fin 2) (Fin 2) ℝ) (k l : Fin 4) : ℂ :=
  (contrC (classAlpha c) A (ladderLines k) (ladderLines l) : ℂ)

/-- **`T₁` through the pattern**: `T₁ = -π⁴ κ η² U⁻² · 6 pat(P; Ē)`. -/
theorem classT1_eq_of_pat : classT1 c pa P z u =
    ladderK P * ((symanzikU (classAlpha c) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (6 * pat (ladderPauli P u) (classE c P z u 0) (classE c P z u 1) (classE c P z u 2)
        (classE c P z u 3)) := by
  have h := hpat (curveMomentum P.m u) (restMomentum P.m) (classE c P z u 0)
    (classE c P z u 1) (classE c P z u 2) (classE c P z u 3)
  calc classT1 c pa P z u = -((π : ℂ) ^ 4) * ladderConst P *
      (((symanzikU (classAlpha c) z ^ 2 : ℝ) : ℂ)⁻¹ * 6 * ∑ μ,
          ∑ l : Fin 5 → Fin 4, classWeight pa P μ l *
        ch (ladderB P.m (curveMomentum P.m u) (restMomentum P.m) μ l) (classE c P z u 0)
          (classE c P z u 1) (classE c P z u 2) (classE c P z u 3)) := by
        rw [classT1]
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
    _ = _ := by
        rw [h, ladderK]
        ring

/-- **`T₂` through the pattern**: the six single contractions of slots. -/
theorem classT2_eq_of_pat : classT2 c pa P z u =
    ladderK P * ((symanzikU (classAlpha c) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (classC c (symanzikMatrix (classAlpha c) z) 0 1 * ∑ ν, pat (ladderPauli P u)
          (gammaLower ν) (gamma ν) (classE c P z u 2) (classE c P z u 3) +
        classC c (symanzikMatrix (classAlpha c) z) 0 2 * ∑ ν, pat (ladderPauli P u)
          (gammaLower ν) (classE c P z u 1) (gamma ν) (classE c P z u 3) +
        classC c (symanzikMatrix (classAlpha c) z) 0 3 * ∑ ν, pat (ladderPauli P u)
          (gammaLower ν) (classE c P z u 1) (classE c P z u 2) (gamma ν) +
        classC c (symanzikMatrix (classAlpha c) z) 1 2 * ∑ ν, pat (ladderPauli P u)
          (classE c P z u 0) (gammaLower ν) (gamma ν) (classE c P z u 3) +
        classC c (symanzikMatrix (classAlpha c) z) 1 3 * ∑ ν, pat (ladderPauli P u)
          (classE c P z u 0) (gammaLower ν) (classE c P z u 2) (gamma ν) +
        classC c (symanzikMatrix (classAlpha c) z) 2 3 * ∑ ν, pat (ladderPauli P u)
          (classE c P z u 0) (classE c P z u 1) (gammaLower ν) (gamma ν)) := by
  set E := classE c P z u
  set A := symanzikMatrix (classAlpha c) z
  set p' := curveMomentum P.m u
  set p := restMomentum P.m
  have hT : classT2 c pa P z u = -((π : ℂ) ^ 4) * ladderConst P *
      ((symanzikU (classAlpha c) z ^ 2 : ℝ) : ℂ)⁻¹ * ∑ μ, ∑ l : Fin 5 → Fin 4,
        classWeight pa P μ l * chainTwo (classAlpha c) (ladderB P.m p' p μ l) E ladderLines A := by
    rw [classT2]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
  have h : ∀ μ (l : Fin 5 → Fin 4), classWeight pa P μ l *
      chainTwo (classAlpha c) (ladderB P.m p' p μ l) E ladderLines A =
      classC c A 0 1 * (classWeight pa P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (gammaLower ν)
          (gamma ν) (E 2) (E 3)) +
      classC c A 0 2 * (classWeight pa P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (gammaLower ν) (E 1)
          (gamma ν) (E 3)) +
      classC c A 0 3 * (classWeight pa P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (gammaLower ν) (E 1)
          (E 2) (gamma ν)) +
      classC c A 1 2 * (classWeight pa P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (E 0) (gammaLower ν)
          (gamma ν) (E 3)) +
      classC c A 1 3 * (classWeight pa P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (E 0) (gammaLower ν)
          (E 2) (gamma ν)) +
      classC c A 2 3 * (classWeight pa P μ l * ∑ ν, ch (ladderB P.m p' p μ l) (E 0) (E 1)
          (gammaLower ν) (gamma ν)) :=
    fun μ l => by
      simp only [chainTwo]
      ring
  rw [hT]
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [sum_classWeight_sum_ch hpat]
  rw [ladderK]
  ring

/-- **`T₃` through the pattern**: the three double contractions. -/
theorem classT3_eq_of_pat : classT3 c pa P z u =
    ladderK P * ((symanzikU (classAlpha c) z ^ 2 : ℝ) : ℂ)⁻¹ *
      (1 / 4 * (classC c (symanzikMatrix (classAlpha c) z) 0 1 *
          classC c (symanzikMatrix (classAlpha c) z) 2 3 * ∑ ν, ∑ ρ,
            pat (ladderPauli P u) (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ) +
        classC c (symanzikMatrix (classAlpha c) z) 0 2 *
          classC c (symanzikMatrix (classAlpha c) z) 1 3 * ∑ ν, ∑ ρ,
            pat (ladderPauli P u) (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ) +
        classC c (symanzikMatrix (classAlpha c) z) 0 3 *
          classC c (symanzikMatrix (classAlpha c) z) 1 2 * ∑ ν, ∑ ρ,
            pat (ladderPauli P u) (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν))) := by
  set A := symanzikMatrix (classAlpha c) z
  set p' := curveMomentum P.m u
  set p := restMomentum P.m
  have hT : classT3 c pa P z u = -((π : ℂ) ^ 4) * ladderConst P *
      ((symanzikU (classAlpha c) z ^ 2 : ℝ) : ℂ)⁻¹ * (1 / 4) * ∑ μ, ∑ l : Fin 5 → Fin 4,
        classWeight pa P μ l * chainFour (classAlpha c) (ladderB P.m p' p μ l) ladderLines A := by
    rw [classT3]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun l _ => by ring
  have h : ∀ μ (l : Fin 5 → Fin 4), classWeight pa P μ l *
      chainFour (classAlpha c) (ladderB P.m p' p μ l) ladderLines A =
      classC c A 0 1 * classC c A 2 3 * (classWeight pa P μ l * ∑ ν, ∑ ρ,
          ch (ladderB P.m p' p μ l) (gammaLower ν) (gamma ν) (gammaLower ρ) (gamma ρ)) +
      classC c A 0 2 * classC c A 1 3 * (classWeight pa P μ l * ∑ ν, ∑ ρ,
          ch (ladderB P.m p' p μ l) (gammaLower ν) (gammaLower ρ) (gamma ν) (gamma ρ)) +
      classC c A 0 3 * classC c A 1 2 * (classWeight pa P μ l * ∑ ν, ∑ ρ,
          ch (ladderB P.m p' p μ l) (gammaLower ν) (gammaLower ρ) (gamma ρ) (gamma ν)) :=
    fun μ l => by
      simp only [chainFour]
      ring
  rw [hT]
  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [sum_classWeight_sum_sum_ch hpat]
  rw [ladderK]
  ring

end Pattern

end QED.TwoLoop.UnitSCGraph

end
