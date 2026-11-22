/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCMainDChain
public import QED.ChainProof.SetCUnitMCov

/-!
# Set (c), the `δ₃` classes: the transverse part as a unit, and the class links

Helper level for the per-class links `QED.ChainProof.SetCPauli.SetCClassLim`, `SetCClassCov` of
the 24 classes `repD i s` (`QED.ChainProof.SetCPauli.mainVal (.inr (i, s))`). The value is the
transverse plus the longitudinal part (`QED.ChainProof.SetCMain.mainVal_inr_split`).

**The transverse part is a multi-denominator unit.** With the open-line chain of
`QED.ChainProof.SetCMain.dG_repD_chain`:

* the class numerators in one chain form (`chainPermD`, `classNumeratorE_chainD`) and the photon
  pairing of `repD i s` matched to that of its class (`chainPermD_repD`, kernel evaluation);
* the change from the `repD` routing to the class routing, `ℓ ↦ M ℓ + a(p, q)` with an integer
  unimodular `M` (`chgMD`, `chgAD`, `chgD`), checked on the integer momentum vectors of all lines
  of the twenty-four orbits (`mv_repD_fermion`, `mv_repD_photon`, kernel evaluation);
* the ten denominators (four electron lines; the element line twice with `(m_γ, Λ)`; the other
  photon line once) are those of the unit with element slot `repBSlot i`, two unscaled extra
  lines of masses `m_γ`, `Λ` and one power `k²` (`prod_dProd_repD`, `prod_lineDenom_unitM_two`);
* **`dGIntegrand_repD_eq_unit`**, **`dG_repD_value`**: the integrand and the value are
  `wD = -(i/2) δ₃ (1/i)(Λ² - m_γ²)` times those of the unit;
* **`tendsto_dG_repD`**, **`dGLimD_map`**: the `ε → 0⁺` limit `dGLimD` (from
  `QED.ChainProof.SetCUnitM.unitM_pow`) and its covariance (from `unitMLimitV_map`).

**The class links.** `DKLimLink`, `DKCovLink` (open) are the limit and covariance links of the
longitudinal part (`k^a k^b`) at the set (c) data;
**`setCClassLim_inr_of_dK`**, **`setCClassCov_inr_of_dK`** give `SetCClassLim` and
`SetCClassCov` of `mainFam` at `.inr (i, t)` from them.
-/

@[expose] public section
open Complex Matrix Filter Topology
open QED.WickModel (Params Contraction FermionLine PhotonLine Line lineMomentum₂
  photonMomentum₂)

namespace QED.ChainProof.SetCMain

open QED.TwoLoop.Enumeration QED.ChainProof.SetCLink QED.ChainProof.SetALink
open QED.ChainProof.SetCUnitM QED.TwoLoop.LimitCovariance QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable (openClasses)
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix
  class5LoopMatrixPV pvLines classPVMasses)
open QED.ChainProof.Enum (pc)
open QED.GradedProof.X0 (dProd)
open QED.ChainProof.SetCUnit (unitNum unitMasses MassesGe)

/-! ### The class routing in integer vectors -/

/-- The external momenta of the class lines as integer combinations of `p` and `q = p' - p`. -/
def extCoefD : Class5 → Fin 6 → Fin 2 → ℤ
  | .Cp => ![![1, 0], ![1, 1], ![1, 1], ![1, 1], ![0, 0], ![0, 0]]
  | .Sp => ![![1, 0], ![1, 1], ![1, 1], ![1, 1], ![0, 0], ![0, 0]]
  | .Cm => ![![1, 0], ![1, 0], ![1, 0], ![1, 1], ![0, 0], ![0, 0]]
  | .Sm => ![![1, 0], ![1, 0], ![1, 0], ![1, 1], ![0, 0], ![0, 0]]
  | .VP => ![![1, 0], ![1, 1], ![0, 0], ![0, 0], ![0, 0], ![0, 0]]
  | _ => ![![1, 0], ![1, 0], ![1, 1], ![1, 1], ![0, 0], ![0, 0]]

theorem extMomenta_eq_coef (c : Class5) (p p' : Fin 4 → ℝ) (j : Fin 6) :
    extMomenta c p p' j =
      ((extCoefD c j 0 : ℤ) : ℝ) • p + ((extCoefD c j 1 : ℤ) : ℝ) • (p' - p) := by
  cases c <;> fin_cases j <;>
    simp [extMomenta, extCoefD, QED.Integration.TwoLoop.classLXMomenta,
      QED.Integration.TwoLoop.classCpSpMomenta, QED.Integration.TwoLoop.classCmSmMomenta,
      QED.Integration.TwoLoop.classVPMomenta]

/-- The change of loop momenta `ℓ ↦ M ℓ + a(p, q)`. -/
def chgD (M : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → Fin 2 → ℤ) (p q : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  (fun s => ∑ r, M s r • ℓ r) + fun b => ((a b 0 : ℤ) : ℝ) • p + ((a b 1 : ℤ) : ℝ) • q

/-- The integer vector of class line `j` after the change `chgD M a`. -/
def classVecD (c : Class5) (M : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → Fin 2 → ℤ) (j : Fin 6) :
    Fin 4 → ℤ :=
  ![∑ b, class5LoopMatrix c j b * M b 0, ∑ b, class5LoopMatrix c j b * M b 1,
    ∑ b, class5LoopMatrix c j b * a b 0 + extCoefD c j 0,
    ∑ b, class5LoopMatrix c j b * a b 1 + extCoefD c j 1]

theorem lineMomentum_chgD (c : Class5) (M : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → Fin 2 → ℤ)
    (p p' : Fin 4 → ℝ) (j : Fin 6) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (castLoopMatrix (class5LoopMatrix c)) (extMomenta c p p') j
        (chgD M a p (p' - p) ℓ) = mvReal ℓ p (p' - p) (classVecD c M a j) := by
  funext μ
  simp only [lineMomentum, castLoopMatrix, chgD, extMomenta_eq_coef, mvReal, classVecD,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, zsmul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Int.cast_add, Int.cast_mul, Pi.sub_apply,
    Matrix.tail_cons, Pi.mul_apply, Pi.intCast_apply]
  ring

/-! ### The changes of loop momenta of the twenty-four orbits -/

/-- The loop matrix of the change from the `repD` routing to the class routing. -/
def chgMD : Fin 12 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![0, 1; 1, 0], !![0, 1; 1, 0], !![0, 1; 1, 0], !![0, 1; 1, 0], !![0, 1; 1, 0],
    !![0, 1; 1, 0], !![1, 0; 1, -1], !![1, 0; 1, -1], !![0, 1; -1, 0], !![0, 1; -1, 0],
    !![0, 1; 1, -1], !![0, 1; 1, -1]]

/-- The shift of the change, as coefficients of `p` and `q`. -/
def chgAD : Fin 12 → Fin 2 → Fin 2 → ℤ :=
  ![![![-1, -1], ![-1, -1]], ![![-1, -1], ![-1, -1]], ![![-1, -1], ![-1, -1]],
    ![![-1, -1], ![-1, -1]], ![![-1, 0], ![-1, -1]], ![![-1, 0], ![-1, -1]],
    ![![-1, -1], ![0, -1]], ![![-1, -1], ![0, -1]], ![![-1, -1], ![1, 1]],
    ![![-1, -1], ![1, 1]], ![![-1, -1], ![0, 0]], ![![-1, -1], ![0, 0]]]

theorem isUnit_det_chgMD : ∀ i, IsUnit (chgMD i).det := by
  intro i
  rw [Int.isUnit_iff]
  fin_cases i <;> simp [chgMD, Matrix.det_fin_two]

/-- The class line of the other photon line (the one without the element). -/
def oSlotD (i : Fin 12) : Fin 8 := if repBSlot i = 4 then 5 else 4

theorem mv_repD_fermion : ∀ i s (j : Fin 4), mv (repD i s) (.inl (lineRD i s j)) =
    classVecD (repBClass i) (chgMD i) (chgAD i) (Fin.castLE (by omega) j) := by
  decide +kernel

theorem mv_repD_photon : ∀ i s,
    (mv (repD i s) (.inr (photD i s 0)) =
        classVecD (repBClass i) (chgMD i) (chgAD i) (pvLines (repBSlot i)) ∨
      mv (repD i s) (.inr (photD i s 0)) =
        -classVecD (repBClass i) (chgMD i) (chgAD i) (pvLines (repBSlot i))) ∧
    (mv (repD i s) (.inr (photD i s 1)) =
        classVecD (repBClass i) (chgMD i) (chgAD i) (pvLines (repBSlot i)) ∨
      mv (repD i s) (.inr (photD i s 1)) =
        -classVecD (repBClass i) (chgMD i) (chgAD i) (pvLines (repBSlot i))) ∧
    (mv (repD i s) (.inr (photD i s 2)) =
        classVecD (repBClass i) (chgMD i) (chgAD i) (pvLines (oSlotD i)) ∨
      mv (repD i s) (.inr (photD i s 2)) =
        -classVecD (repBClass i) (chgMD i) (chgAD i) (pvLines (oSlotD i))) ∧
    (pmv (repD i s) (pc kD 5 0) =
        classVecD (repBClass i) (chgMD i) (chgAD i) (pvLines (repBSlot i)) ∨
      pmv (repD i s) (pc kD 5 0) =
        -classVecD (repBClass i) (chgMD i) (chgAD i) (pvLines (repBSlot i))) := by
  decide +kernel

/-! ### The class numerators in one chain form -/

/-- The photon pairing of an open class as a permutation. -/
noncomputable def chainPermD : Class5 → Equiv.Perm (Fin 5)
  | .L => permL
  | .X => permX
  | .Cp => permCp
  | .Cm => permCm
  | .Sp => permSp
  | .Sm => permSm
  | _ => 1

theorem lineIdx_lines : (∀ j, lineIdx (.inl (lineL j) : Line cL) = Fin.castLE (by omega) j) ∧
    (∀ j, lineIdx (.inl (lineX j) : Line cX) = Fin.castLE (by omega) j) ∧
    (∀ j, lineIdx (.inl (lineCp j) : Line cCp) = Fin.castLE (by omega) j) ∧
    (∀ j, lineIdx (.inl (lineCm j) : Line cCm) = Fin.castLE (by omega) j) ∧
    (∀ j, lineIdx (.inl (lineSp j) : Line cSp) = Fin.castLE (by omega) j) ∧
    (∀ j, lineIdx (.inl (lineSm j) : Line cSm) = Fin.castLE (by omega) j) := by
  decide +kernel

/-- **The numerator of an open class in chain form**, the electron momenta those of the rows
`0, …, 3` of the class routing. -/
theorem classNumeratorE_chainD {c : Class5} (hc : c ∈ openClasses) (P : Params)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    classNumeratorE c P pOut pIn kIn αOut βIn μ ℓ = (I * P.e) ^ 5 * (1 / I) ^ 4 *
      chainNum P (chainPermD c) (fun j => electronNumerator P.m
        (lineMomentum (castLoopMatrix (class5LoopMatrix c)) (extMomenta c (pIn 0) (pOut 0))
          (Fin.castLE (by omega) j) ℓ)) (μ 0) (αOut 0) (βIn 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lineIdx_lines
  simp only [openClasses, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [chain_L]; simp only [classMomE, h1]; rfl
  · rw [chain_X]; simp only [classMomE, h2]; rfl
  · rw [chain_Cp]; simp only [classMomE, h3]; rfl
  · rw [chain_Cm]; simp only [classMomE, h4]; rfl
  · rw [chain_Sp]; simp only [classMomE, h5]; rfl
  · rw [chain_Sm]; simp only [classMomE, h6]; rfl

/-- The photon pairing of `repD i s` is that of its class, up to the order within and of the
two internal pairs. -/
theorem chainPermD_repD : ∀ (i : Fin 12) (s : Fin 2),
    chainPermD (repBClass i) 0 = Fin.rev (skE i) ∧
      ((((chainPermD (repBClass i) 1 = ctEndA i s ∧ chainPermD (repBClass i) 2 = ctEndB i s) ∨
          (chainPermD (repBClass i) 1 = ctEndB i s ∧ chainPermD (repBClass i) 2 = ctEndA i s)) ∧
        ((chainPermD (repBClass i) 3 = Fin.rev (skR i) ∧
            chainPermD (repBClass i) 4 = Fin.rev (skT i)) ∨
          (chainPermD (repBClass i) 3 = Fin.rev (skT i) ∧
            chainPermD (repBClass i) 4 = Fin.rev (skR i)))) ∨
      (((chainPermD (repBClass i) 3 = ctEndA i s ∧ chainPermD (repBClass i) 4 = ctEndB i s) ∨
          (chainPermD (repBClass i) 3 = ctEndB i s ∧ chainPermD (repBClass i) 4 = ctEndA i s)) ∧
        ((chainPermD (repBClass i) 1 = Fin.rev (skR i) ∧
            chainPermD (repBClass i) 2 = Fin.rev (skT i)) ∨
          (chainPermD (repBClass i) 1 = Fin.rev (skT i) ∧
            chainPermD (repBClass i) 2 = Fin.rev (skR i))))) := by
  decide +kernel


/-- An entry of the chain form, for a photon pairing given up to the order of the pairs. -/
theorem chainNum_apply_pairsD (P : Params) (π : Equiv.Perm (Fin 5))
    (E : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ α β : Fin 4) {e a b c d : Fin 5} (h0 : π 0 = e)
    (hp : (((π 1 = a ∧ π 2 = b) ∨ (π 1 = b ∧ π 2 = a)) ∧
        ((π 3 = c ∧ π 4 = d) ∨ (π 3 = d ∧ π 4 = c))) ∨
      (((π 3 = a ∧ π 4 = b) ∨ (π 3 = b ∧ π 4 = a)) ∧
        ((π 1 = c ∧ π 2 = d) ∨ (π 1 = d ∧ π 2 = c)))) :
    chainNum P π E μ α β = ∑ l : Fin 5 → Fin 4, kron μ (l e) * pvEta P (l a) (l b) *
      pvEta P (l c) (l d) * openChain (fun u => Dirac.gamma (l u)) E α β := by
  simp only [chainNum, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h0]
  have hη := pvEta_symm P
  rcases hp with ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩ |
      ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩ <;>
    rw [h1, h2, h3, h4] <;> (try simp only [hη (l b) (l a), hη (l d) (l c)]) <;> ring

/-! ### The denominators -/

/-- The denominator `x + M² - iε` as a function of the momentum square `x`. -/
noncomputable def dnD (x M ε : ℝ) : ℂ := ((x + M ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I

/-- The momentum square of class line `j` in the class routing. -/
noncomputable def sqD (c : Class5) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (j : Fin 6) : ℝ :=
  Minkowski.dot (lineMomentum (castLoopMatrix (class5LoopMatrix c)) (extMomenta c p p') j ℓ)
    (lineMomentum (castLoopMatrix (class5LoopMatrix c)) (extMomenta c p p') j ℓ)

theorem lineMomentum_unitM_one (c : Class5) (s : Fin 8) {r : ℕ} {κ : Fin r → ℝ}
    (hκ : ∀ j, κ j = 1) (p p' : Fin 4 → ℝ) (k : Fin (r + 8)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (unitMMatrix c s κ) (unitMMomenta c s κ p p') k ℓ =
      lineMomentum (castLoopMatrix (class5LoopMatrix c)) (extMomenta c p p') (pvLines (mLine s k))
        ℓ := by
  have h1 : mScale κ k = 1 := by
    rcases mem_mEmb_or_mExtra k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · simp [mScale, mExt_mEmb]
    · simp [mScale, mExt_mExtra, hκ]
  unfold QED.Integration.TwoLoop.lineMomentum
  simp only [unitMMatrix, unitMMomenta, h1, one_smul]
  rfl

theorem prod_fin_ten {M : Type*} [CommMonoid M] (f : Fin 10 → M) :
    ∏ k, f k = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, Fin.prod_univ_eight]
  rfl

/-- **The ten denominators of the unit with two unscaled extra lines.** -/
theorem prod_lineDenom_unitM_two (c : Class5) (s : Fin 8) (p p' : Fin 4 → ℝ)
    (m a A b B u v ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ∏ k, (lineDenom (unitMMatrix c s ![1, 1]) (unitMMomenta c s ![1, 1] p p')
        (unitMMasses m a A b B ![u, v]) ε k ℓ)⁻¹ =
      (dnD (sqD c p p' ℓ 0) m ε)⁻¹ * (dnD (sqD c p p' ℓ 1) m ε)⁻¹ *
        (dnD (sqD c p p' ℓ 2) m ε)⁻¹ * (dnD (sqD c p p' ℓ 3) m ε)⁻¹ *
        (dnD (sqD c p p' ℓ 4) a ε)⁻¹ * (dnD (sqD c p p' ℓ 5) b ε)⁻¹ *
        (dnD (sqD c p p' ℓ 4) A ε)⁻¹ * (dnD (sqD c p p' ℓ 5) B ε)⁻¹ *
        (dnD (sqD c p p' ℓ (pvLines s)) u ε)⁻¹ * (dnD (sqD c p p' ℓ (pvLines s)) v ε)⁻¹ := by
  have hκ : ∀ j, (![1, 1] : Fin 2 → ℝ) j = 1 := by intro j; fin_cases j <;> rfl
  have hD : ∀ k, lineDenom (unitMMatrix c s ![1, 1]) (unitMMomenta c s ![1, 1] p p')
      (unitMMasses m a A b B ![u, v]) ε k ℓ =
      dnD (sqD c p p' ℓ (pvLines (mLine s k))) (unitMMasses m a A b B ![u, v] k) ε := by
    intro k
    simp only [lineDenom, lineMomentum_unitM_one c s hκ, dnD, sqD]
  simp only [hD]
  refine (prod_fin_ten _).trans ?_
  rfl


theorem dot_mvReal_of_pm {ℓ : Fin 2 → Fin 4 → ℝ} {p q : Fin 4 → ℝ} {v w : Fin 4 → ℤ}
    (h : v = w ∨ v = -w) :
    Minkowski.dot (mvReal ℓ p q v) (mvReal ℓ p q v) =
      Minkowski.dot (mvReal ℓ p q w) (mvReal ℓ p q w) := by
  rcases h with rfl | rfl
  · rfl
  · rw [map_neg, dot_neg_neg_D]

theorem castLE_four : (Fin.castLE (by omega) (0 : Fin 4) : Fin 6) = 0 ∧
    (Fin.castLE (by omega) (1 : Fin 4) : Fin 6) = 1 ∧
    (Fin.castLE (by omega) (2 : Fin 4) : Fin 6) = 2 ∧
    (Fin.castLE (by omega) (3 : Fin 4) : Fin 6) = 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem propDenom_eq_dnD (M ε : ℝ) (k : Fin 4 → ℝ) :
    propDenom M ε k = dnD (Minkowski.dot k k) M ε := rfl

section Routing

variable (i : Fin 12) (s : Fin 2) (p p' : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)

/-- The line momenta of `repD i s` as class line momenta after the change of loop momenta. -/
theorem lineMomentum₂_repD_fermion (j : Fin 4) :
    lineMomentum₂ (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ
        (.inl (lineRD i s j)) =
      lineMomentum (castLoopMatrix (class5LoopMatrix (repBClass i)))
        (extMomenta (repBClass i) p p') (Fin.castLE (by omega) j)
        (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) := by
  rw [lineMomentum₂_eq_mv _ _ _ _ (by simp), lineMomentum_chgD, mv_repD_fermion]

theorem sqD_repD (v : Fin 4 → ℤ) (j : Fin 6)
    (h : v = classVecD (repBClass i) (chgMD i) (chgAD i) j ∨
      v = -classVecD (repBClass i) (chgMD i) (chgAD i) j) :
    Minkowski.dot (mvReal ℓ p (p' - p) v) (mvReal ℓ p (p' - p) v) =
      sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) j := by
  rw [dot_mvReal_of_pm h, sqD, lineMomentum_chgD]

/-- **The ten denominators of `repD i s`** in the class routing. -/
theorem prod_dProd_repD (Q : Params) {F : Type} (Φ : Lepton.Flavors F) :
    ∏ l, dProd Q.ε (dMs Q Φ l)
        (lineMomentum₂ (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ l) =
      (dnD (sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) 0)
          (Φ.mass Φ.openLine) Q.ε)⁻¹ *
        (dnD (sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) 1)
          (Φ.mass Φ.openLine) Q.ε)⁻¹ *
        (dnD (sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) 2)
          (Φ.mass Φ.openLine) Q.ε)⁻¹ *
        (dnD (sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) 3)
          (Φ.mass Φ.openLine) Q.ε)⁻¹ *
        ((dnD (sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ)
          (pvLines (repBSlot i))) Q.mγ Q.ε)⁻¹ *
          (dnD (sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ)
            (pvLines (repBSlot i))) Q.Λ Q.ε)⁻¹) *
        ((dnD (sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ)
          (pvLines (repBSlot i))) Q.mγ Q.ε)⁻¹ *
          (dnD (sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ)
            (pvLines (repBSlot i))) Q.Λ Q.ε)⁻¹) *
        ((dnD (sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ)
          (pvLines (oSlotD i))) Q.mγ Q.ε)⁻¹ *
          (dnD (sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ)
            (pvLines (oSlotD i))) Q.Λ Q.ε)⁻¹) := by
  have hk := lineMomentum₂_eq_mv (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p)
    (by simp) ℓ
  have hf : ∀ j : Fin 4, Minkowski.dot
      (lineMomentum₂ (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ
        (.inl (lineRD i s j)))
      (lineMomentum₂ (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ
        (.inl (lineRD i s j))) =
      sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) (Fin.castLE (by omega) j) :=
    fun j => by rw [lineMomentum₂_repD_fermion, sqD]
  obtain ⟨g0, g1, g2, -⟩ := mv_repD_photon i s
  obtain ⟨c0, c1, c2, c3⟩ := castLE_four
  have f0 := hf 0
  have f1 := hf 1
  have f2 := hf 2
  have f3 := hf 3
  rw [c0] at f0
  rw [c1] at f1
  rw [c2] at f2
  rw [c3] at f3
  rw [Fintype.prod_sum_type, prod_lineRD, prod_photD]
  simp only [dMs, dProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    propDenom_eq_dnD]
  rw [f0, f1, f2, f3, hk, hk, hk, sqD_repD i p p' ℓ _ _ g0, sqD_repD i p p' ℓ _ _ g1,
    sqD_repD i p p' ℓ _ _ g2]
  ring

end Routing


/-! ### The transverse part as a unit -/

/-- The constant of the transverse part: `-(i/2) δ₃ · (1/i)(Λ² - m_γ²)`. -/
noncomputable def wD (P : Params) (δ₃ : ℝ) : ℂ :=
  -(I / 2) * (δ₃ : ℂ) * ((1 / I) * ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ))

theorem slotD_cases : ∀ i : Fin 12, (pvLines (repBSlot i) = 4 ∧ pvLines (oSlotD i) = 5) ∨
    (pvLines (repBSlot i) = 5 ∧ pvLines (oSlotD i) = 4) := by
  decide

theorem photonMomentum₂_repD_sq (i : Fin 12) (s : Fin 2) (p p' : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    Minkowski.dot (photonMomentum₂ (repD i s) (fun _ => p' - p)
        (lineMomentum₂ (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ) (pc kD 5 0))
      (photonMomentum₂ (repD i s) (fun _ => p' - p)
        (lineMomentum₂ (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) ℓ) (pc kD 5 0)) =
      sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) (pvLines (repBSlot i)) := by
  rw [photonMomentum₂_eq_pmv _ _ _ _ (by simp), sqD_repD i p p' ℓ _ _ (mv_repD_photon i s).2.2.2]

/-- **The transverse part of `repD i s` is a multi-denominator unit**: at every loop momentum,
the integrand is `wD` times the integrand of the unit of the class of `repB i` with the element
slot `repBSlot i`, two unscaled extra lines of masses `m_γ`, `Λ` and one power `k²`, at the
changed loop momenta (the unit parameters `P` sharing `e`, `m_γ`, `Λ` and the electron mass). -/
theorem dGIntegrand_repD_eq_unit (Q P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (hm : Φ.mass Φ.openLine = P.m) (he : P.e = Q.e) (hγ : P.mγ = Q.mγ)
    (hΛ : P.Λ = Q.Λ) (δ₃ : ℝ) (i : Fin 12) (s : Fin 2) (p p' : Fin 4 → ℝ) (μ α β : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    dGIntegrand Q Φ δ₃ (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
        (fun _ => β) (fun _ => μ) ℓ =
      wD Q δ₃ * unitMIntegrand (repBClass i) P (repBSlot i) ![1, 1]
        (unitMMasses P.m Q.mγ Q.Λ Q.mγ Q.Λ ![Q.mγ, Q.Λ]) Q.ε p p' 1 μ α β
        (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) := by
  unfold dGIntegrand
  rw [dG_repD_chain, prod_dProd_repD, photonMomentum₂_repD_sq]
  unfold unitMIntegrand unitNum
  rw [classNumeratorE_chainD (repBClass_mem i), prod_lineDenom_unitM_two]
  obtain ⟨h0, hp⟩ := chainPermD_repD i s
  rw [chainNum_apply_pairsD _ _ _ _ _ _ h0 hp]
  have hE : (fun j => electronNumerator P.m (lineMomentum (castLoopMatrix
      (class5LoopMatrix (repBClass i))) (extMomenta (repBClass i) p p') (Fin.castLE (by omega) j)
        (chgD (chgMD i) (chgAD i) p (p' - p) ℓ))) =
      fun j => electronNumerator (Φ.mass Φ.openLine) (lineMomentum₂ (repD i s) (fun _ => p')
        (fun _ => p) (fun _ => p' - p) ℓ (.inl (lineRD i s j))) := by
    funext j
    rw [hm, lineMomentum₂_repD_fermion]
  have hη : pvEta P = pvEta Q := by
    funext x y
    simp only [pvEta, hγ, hΛ]
  have hsq : elemSq (repBClass i) (repBSlot i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) =
      ((sqD (repBClass i) p p' (chgD (chgMD i) (chgAD i) p (p' - p) ℓ) (pvLines (repBSlot i)) :
        ℝ) : ℂ) := rfl
  simp only [hE, hη, hsq, he, hm]
  rcases slotD_cases i with ⟨h4, h5⟩ | ⟨h5, h4⟩ <;> rw [h4, h5] <;> unfold wD <;> ring


/-- **The transverse value of `repD i s` is a unit value** (every `ε`). -/
theorem dG_repD_value (Q P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (hm : Φ.mass Φ.openLine = P.m) (he : P.e = Q.e) (hγ : P.mγ = Q.mγ)
    (hΛ : P.Λ = Q.Λ) (δ₃ : ℝ) (i : Fin 12) (s : Fin 2) (p p' : Fin 4 → ℝ) (μ α β : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (dGIntegrand Q Φ δ₃ (repD i s) (fun _ => p')
        (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)) =
      wD Q δ₃ * unitMValue (repBClass i) P (repBSlot i) ![1, 1]
        (unitMMasses P.m Q.mγ Q.Λ Q.mγ Q.Λ ![Q.mγ, Q.Λ]) Q.ε p p' 1 μ α β := by
  unfold unitMValue
  rw [← QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_const_mul]
  exact QED.TwoLoop.ClassLimit.jointEnergyFirstIntegral_eq_of_comp (chgMD i) (isUnit_det_chgMD i)
    _ fun ℓ => dGIntegrand_repD_eq_unit Q P Φ hm he hγ hΛ δ₃ i s p p' μ α β ℓ

/-- **The `ε → 0⁺` limit of the transverse part of `repD i s`**: `wD` times the unit limit. -/
noncomputable def dGLimD (R : Params) (δ₃ : ℝ) (i : Fin 12) (p p' : Fin 4 → ℝ) :
    Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  fun μ => wD R δ₃ • unitMLimitV (repBClass i) R (repBSlot i) ![1, 1]
    (unitMMasses R.m R.mγ R.Λ R.mγ R.Λ ![R.mγ, R.Λ]) p p' 1 μ

theorem trailOne_one_two : TrailOne 1 (![1, 1] : Fin 2 → ℝ) := by
  intro j hj
  fin_cases j
  · simp at hj
  · rfl

theorem extraGe_two {a b : ℝ} (hab : a ≤ b) : ExtraGe a (![1, 1] : Fin 2 → ℝ) ![a, b] := by
  intro j
  fin_cases j
  · exact ⟨one_pos, le_rfl, le_rfl⟩
  · exact ⟨one_pos, le_rfl, hab⟩

section Limit

variable {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -R.m ^ 2) (hp' : Minkowski.dot p' p' = -R.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hm hγ hγΛ hp hp' hq

/-- **The transverse part of `repD i s` converges** as `ε → 0⁺`, to `dGLimD`. -/
theorem tendsto_dG_repD {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (hΦ : Φ.mass Φ.openLine = R.m) (δ₃ : ℝ) (i : Fin 12) (s : Fin 2) (μ α β : Fin 4) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (dGIntegrand { R with ε := ε } Φ δ₃
        (repD i s) (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
        (fun _ => μ))) (𝓝[>] 0) (𝓝 (dGLimD R δ₃ i p p' μ α β)) := by
  have hM : MassesGe R.mγ R.mγ R.Λ R.mγ R.Λ := ⟨le_rfl, hγΛ, le_rfl, hγΛ⟩
  have key := ((unitM_pow (repBClass_mem i) R hm (four_le_repBSlot i) hγ hM hp hp' hq 1
    (r := 2) (κ := ![1, 1]) (cs := ![R.mγ, R.Λ]) (by norm_num) trailOne_one_two
    (extraGe_two hγΛ)).2 μ α β).const_mul (wD R δ₃)
  refine key.congr fun ε => ?_
  rw [dG_repD_value { R with ε := ε } R Φ hΦ rfl rfl rfl δ₃ i s p p' μ α β]
  rfl

end Limit

/-- **Covariance of the transverse limit** of `repD i s` under every spinor-lifted `L`, the
external momenta moved. -/
theorem dGLimD_map {R : Params} (hm : 0 < R.m) (hγ : 0 < R.mγ) (hγΛ : R.mγ ≤ R.Λ)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -R.m ^ 2)
    (hp' : Minkowski.dot p' p' = -R.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ} (h : IsSpinLift L S T)
    (δ₃ : ℝ) (i : Fin 12) (μ : Fin 4) :
    S * dGLimD R δ₃ i (L *ᵥ p) (L *ᵥ p') μ * T = QED.Dirac.vecAct L (dGLimD R δ₃ i p p') μ := by
  have hM : MassesGe R.mγ R.mγ R.Λ R.mγ R.Λ := ⟨le_rfl, hγΛ, le_rfl, hγΛ⟩
  simp only [dGLimD, Matrix.mul_smul, Matrix.smul_mul]
  rw [unitMLimitV_map (repBClass_mem i) R hm (four_le_repBSlot i) hγ hM hp hp' hq h 1
    (by norm_num) trailOne_one_two (extraGe_two hγΛ) μ, ← QED.Dirac.vecAct_smul]
  rfl


/-! ### The class links of `repD` from the longitudinal part -/

section Links

open QED.ChainProof.SetCPauli
open QED.ChainProof.SetAPauli (regParams regFlavors)

variable {P₀ : Params}

/-- The longitudinal part of `repD i t` at the set (c) data, at `ε`. -/
noncomputable abbrev dKValD (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (s : ℝ × ℝ × ℝ)
    (i : Fin 12) (t : Fin 2) (p' p : Fin 4 → ℝ) (μ α β : Fin 4) (ε : ℝ) : ℂ :=
  QED.TwoLoop.jointEnergyFirstIntegral 2 (dKIntegrand { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) (repD i t) (fun _ => p')
    (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ))

/-- **The limit link of the longitudinal part of `repD i t`** (open): at the set (c) data, the
longitudinal part has an `ε → 0⁺` limit at every on-shell positive-energy pair with `q² > 0`. -/
def DKLimLink (P₀ : Params) (i : Fin 12) (t : Fin 2) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ p' p, IsPairQ P₀.m p' p → ∃ Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ, ∀ μ α β,
      Tendsto (dKValD P₀ M₁ M₂ c₁ c₂ mγ Λ D s i t p' p μ α β) (𝓝[>] 0) (𝓝 (Y μ α β))

/-- **The covariance link of the longitudinal part of `repD i t`** (open). -/
def DKCovLink (P₀ : Params) (i : Fin 12) (t : Fin 2) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
    ∀ p' p, IsPairQ P₀.m p' p → 0 < (L *ᵥ p') 0 → 0 < (L *ᵥ p) 0 →
    ∀ Y Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ,
      (∀ μ α β, Tendsto (dKValD P₀ M₁ M₂ c₁ c₂ mγ Λ D s i t p' p μ α β) (𝓝[>] 0)
        (𝓝 (Y μ α β))) →
      (∀ μ α β, Tendsto (dKValD P₀ M₁ M₂ c₁ c₂ mγ Λ D s i t (L *ᵥ p') (L *ᵥ p) μ α β) (𝓝[>] 0)
        (𝓝 (Z μ α β))) →
      ∀ μ, S * Z μ * T = QED.Dirac.vecAct L Y μ

theorem setCAdm_masses {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) : 0 < P₀.m ∧ 0 < mγ ∧ mγ ≤ Λ := by
  obtain ⟨-, -, -, -, hmγ, -, hmΛ, hm2, -⟩ := hA
  exact ⟨by linarith, hmγ, hmΛ.le⟩

/-- At `ε > 0` the class value of `repD i t` is the transverse plus the longitudinal value. -/
theorem mainVal_inr_eq_dG_add {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ} {ε : ℝ}
    (hε : 0 < ε) (p' p : Fin 4 → ℝ) (μ : Fin 4) (i : Fin 12) (t : Fin 2) (α β : Fin 4) :
    mainFam { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) p' p μ (.inr (i, t)) α β =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (dGIntegrand
          { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
          (P₀.e ^ 2 * (shareCt D s).d₃ 0) (repD i t) (fun _ => p') (fun _ => p) (fun _ => p' - p)
          (fun _ => α) (fun _ => β) (fun _ => μ)) +
        dKValD P₀ M₁ M₂ c₁ c₂ mγ Λ D s i t p' p μ α β ε :=
  mainVal_inr_split _ _ _ hε p' p μ i t α β

/-- The transverse part at the set (c) data converges to `dGLimD`. -/
theorem tendsto_dG_setC {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}
    (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) {p' p : Fin 4 → ℝ} (hpq : IsPairQ P₀.m p' p)
    (i : Fin 12) (t : Fin 2) (μ α β : Fin 4) :
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (dGIntegrand
        { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (P₀.e ^ 2 * (shareCt D s).d₃ 0) (repD i t) (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => α) (fun _ => β) (fun _ => μ))) (𝓝[>] 0)
      (𝓝 (dGLimD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) i p p'
        μ α β)) := by
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  exact tendsto_dG_repD (R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) hm hγ hγΛ hp hp' hq.le _ rfl _ i t
    μ α β

/-- **The limit link of `repD i t` from that of its longitudinal part.** -/
theorem setCClassLim_inr_of_dK {i : Fin 12} {t : Fin 2} (hK : DKLimLink P₀ i t) :
    SetCClassLim mainFam P₀ (.inr (i, t)) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  obtain ⟨Y, hY⟩ := hK M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  refine ⟨fun μ => dGLimD (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (P₀.e ^ 2 * (shareCt D s).d₃ 0) i p p' μ +
    Y μ, fun μ α β => ?_⟩
  refine ((tendsto_dG_setC hA hpq i t μ α β).add (hY μ α β)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (mainVal_inr_eq_dG_add hε p' p μ i t α β).symm

/-- **The covariance link of `repD i t` from that of its longitudinal part.** -/
theorem setCClassCov_inr_of_dK {i : Fin 12} {t : Fin 2} (hK : DKCovLink P₀ i t) :
    SetCClassCov mainFam P₀ (.inr (i, t)) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA L S T h p' p hpq h0 h1 Y Z hY hZ μ
  have hpq' := isPairQ_map h hpq h0 h1
  set R := regParams P₀ M₁ M₂ c₁ c₂ mγ Λ
  set δ₃ := P₀.e ^ 2 * (shareCt D s).d₃ 0
  have hKY : ∀ μ α β, Tendsto (dKValD P₀ M₁ M₂ c₁ c₂ mγ Λ D s i t p' p μ α β) (𝓝[>] 0)
      (𝓝 (Y μ α β - dGLimD R δ₃ i p p' μ α β)) := fun μ α β => by
    refine ((hY μ α β).sub (tendsto_dG_setC hA hpq i t μ α β)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [mainVal_inr_eq_dG_add hε p' p μ i t α β]
    ring
  have hKZ : ∀ μ α β, Tendsto (dKValD P₀ M₁ M₂ c₁ c₂ mγ Λ D s i t (L *ᵥ p') (L *ᵥ p) μ α β)
      (𝓝[>] 0) (𝓝 (Z μ α β - dGLimD R δ₃ i (L *ᵥ p) (L *ᵥ p') μ α β)) := fun μ α β => by
    refine ((hZ μ α β).sub (tendsto_dG_setC hA hpq' i t μ α β)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [mainVal_inr_eq_dG_add hε _ _ μ i t α β]
    ring
  have hcov := hK M₁ M₂ c₁ c₂ mγ Λ D s hA L S T h p' p hpq h0 h1
    (fun μ => Y μ - dGLimD R δ₃ i p p' μ)
    (fun μ => Z μ - dGLimD R δ₃ i (L *ᵥ p) (L *ᵥ p') μ) (fun μ α β => by simpa using hKY μ α β)
    (fun μ α β => by simpa using hKZ μ α β) μ
  obtain ⟨hm, hγ, hγΛ⟩ := setCAdm_masses hA
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hG := dGLimD_map (R := R) hm hγ hγΛ hp hp' hq.le h δ₃ i μ
  have hZ' : Z μ = (Z μ - dGLimD R δ₃ i (L *ᵥ p) (L *ᵥ p') μ) +
      dGLimD R δ₃ i (L *ᵥ p) (L *ᵥ p') μ := by abel
  rw [hZ', Matrix.mul_add, Matrix.add_mul, hcov, hG]
  simp only [QED.Dirac.vecAct, ← Finset.sum_add_distrib, ← smul_add, sub_add_cancel]

end Links

end QED.ChainProof.SetCMain

end
