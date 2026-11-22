/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLimCtS
public import QED.ChainProof.SetCLimCtKind

/-!
# Set (c): limits and covariance of the six `δ₃` classes `CD2`–`CD4`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The classes
`repCD2 s`, `repCD3 s`, `repCD4 s` are the one-loop vertex with a level-`0` `gaugeCt` vertex on its
open line and a level-`0` `photonCt` vertex on the photon line. The graded value (G₅) is the T1
value at the open-line parameters with the level-`0` counterterms
(`QED.ChainProof.SetCPauli.contractionValue_eq_ctLevel`); changing the `gaugeCt` vertex into a
`gauge` vertex (`QED.ChainProof.SetCPauli.contractionValue₂_toGK`) gives `δ₁` times the value of
a relabelling of the order-`e⁵` `δ₃` class representative of slot `s.rev` (`toGK_repCD2`, …,
kernel evaluation):

* `cdVal_apply`: the value of `CDₖ s` (`k = 2, 3, 4`) is `δ₁` times the value of
  `QED.TwoLoop.Relabel.CtClass.rep (d3Cls s)` at the open-line parameters `cdParams`.

Hence the limits exist and are `δ₁` times the `δ₃` class limits
`QED.TwoLoop.LimitCovariance.ctLimitV`, whose covariance is `QED.TwoLoop.PauliZero.ctLimitV_map`.

* **`setCClassLim_CD`**, **`setCClassCov_CD`**: the limit and covariance links of the classes
  `.inr (.inl (k, s))` of `QED.ChainProof.SetCPauli.ctFam`, `2 ≤ k`;
* **`setCLimitLink_of_main_cb_cd01`**, **`setCCovLink_of_main_cb_cd01`**: the limit and
  covariance links of (HS₆) from the per-class links of the 36 two-loop-outer classes, the five
  classes `CBₖ` and the four classes `CD0 s`, `CD1 s` (open).
-/

@[expose] public section

open Complex Matrix Filter Topology
open QED.WickModel (Params IsOnePI Contraction contractionValue₂ loopCount)

namespace QED.ChainProof.SetCPauli

open QED.TwoLoop.LimitCovariance QED.ChainProof.SetCLink QED.TwoLoop.Relabel
open QED.TwoLoop.Enumeration
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### The relabellings -/

/-- The relabelling exchanging the end vertices `0`, `2` of the open line. -/
def permCD : Equiv.Perm (Fin 4) := permK ![2, 1, 0, 3] ![2, 1, 0, 3]

/-- The `δ₃` class of `CDₖ s`: slot `s.rev` of the `photonCt` vertex towards `v₁`. -/
def d3Cls : Fin 2 → CtClass := ![.d3Slot1, .d3Slot0]

theorem kinds_CD2 : ∀ t, gKinds kCD2 (permCD t) = k_gggp t := by decide +kernel

theorem kinds_CD3 : ∀ t, gKinds kCD3 (permCD t) = k_gggp t := by decide +kernel

theorem kinds_CD4 : ∀ t, gKinds kCD4 (permCD t) = k_gggp t := by decide +kernel

theorem toGK_repCD2 : toGK (repCD2 0) = relabelK permCD kinds_CD2 repD3Slot1 ∧
    toGK (repCD2 1) = relabelK permCD kinds_CD2 repD3Slot0 := by
  decide +kernel

theorem toGK_repCD3 : toGK (repCD3 0) = relabelK permCD kinds_CD3 repD3Slot1 ∧
    toGK (repCD3 1) = relabelK permCD kinds_CD3 repD3Slot0 := by
  decide +kernel

theorem toGK_repCD4 : toGK (repCD4 0) = relabelK permCD kinds_CD4 repD3Slot1 ∧
    toGK (repCD4 1) = relabelK permCD kinds_CD4 repD3Slot0 := by
  decide +kernel

theorem ctWK_kCD (δ₁ : ℝ) : ctWK δ₁ kCD2 = δ₁ ∧ ctWK δ₁ kCD3 = δ₁ ∧ ctWK δ₁ kCD4 = δ₁ := by
  simp [ctWK, Fin.prod_univ_four, kCD2, kCD3, kCD4]

theorem loopCount_repD3 : loopCount repD3Slot0 = 1 ∧ loopCount repD3Slot1 = 1 := by
  simp only [loopCount_eq_card]
  decide +kernel

/-! ### The values -/

/-- The value of an open-line contraction `C` with one `gaugeCt` vertex whose kind change is a
relabelling of a 1PI contraction `R` of `k_gggp`: `δ₁` times the value of `R`. -/
theorem value_of_toGK_eq (Q : Params) {κ : Fin 4 → Wick.VertexKind} {C : Contraction 1 1 κ}
    (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (hC : IsOnePI C)
    {R : Contraction 1 1 k_gggp} (hR : IsOnePI R) (hκ : ∀ t, gKinds κ (permCD t) = k_gggp t)
    (hG : toGK C = relabelK permCD hκ R) (hLC : loopCount C = 1) (hLR : loopCount R = 1)
    (hw : ctWK Q.δ₁ κ = Q.δ₁) (p' p : Fin 4 → ℝ) (i j μ : Fin 4) :
    contractionValue₂ Q C (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ) =
      Q.δ₁ * contractionValue₂ Q R (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hV' : QED.WickModel.VerticesConnected (toGK C) := by
    rw [hG]
    exact (verticesConnected_relabelK_iff permCD hκ R).mpr hR.2.1
  have hL : loopCount (toGK C) = loopCount C := by
    rw [hG, loopCount_relabelK permCD hκ R hR.2.1, hLR, hLC]
  have hsum : ∑ v, QED.WickModel.externalMomentum C (fun _ => p') (fun _ => p)
      (fun _ => p' - p) v = 0 := by
    rw [QED.TwoLoop.Relabel.sum_externalMomentum hC.1]
    simp
  rw [contractionValue₂_toGK Q hcyc hC.2.1 hV' hL hsum, hw, hG, value_relabelK Q hmom hR]

/-- **The values of the `δ₃` classes `CD2`–`CD4`**: `δ₁` times the value of the `δ₃` class
representative of slot `s.rev`, at the open-line parameters with the level-`0` counterterms. -/
theorem cdVal_apply (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (s : Fin 2) (k : Fin 5) (hk : 2 ≤ k) (i j : Fin 4) :
    cdVal P Φ D p' p μ s k i j = (ctParamsLevel P Φ D 0).δ₁ *
      contractionValue₂ (ctParamsLevel P Φ D 0) (d3Cls s).rep (fun _ => p') (fun _ => p)
        (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) := by
  fin_cases k
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  all_goals fin_cases s
  · change Graded.contractionValue P Φ D (repCD2 0) (fun _ => 0) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ (cycle_repCD2 0)]
    exact value_of_toGK_eq _ (cycle_repCD2 0) (isOnePI_repCD2 0) repD3Slot1_isOnePI kinds_CD2
      toGK_repCD2.1 (loopCount_repCD.1 0) loopCount_repD3.2 (ctWK_kCD _).1 p' p i j μ
  · change Graded.contractionValue P Φ D (repCD2 1) (fun _ => 0) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ (cycle_repCD2 1)]
    exact value_of_toGK_eq _ (cycle_repCD2 1) (isOnePI_repCD2 1) repD3Slot0_isOnePI kinds_CD2
      toGK_repCD2.2 (loopCount_repCD.1 1) loopCount_repD3.1 (ctWK_kCD _).1 p' p i j μ
  · change Graded.contractionValue P Φ D (repCD3 0) (fun _ => 0) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ (cycle_repCD3 0)]
    exact value_of_toGK_eq _ (cycle_repCD3 0) (isOnePI_repCD3 0) repD3Slot1_isOnePI kinds_CD3
      toGK_repCD3.1 (loopCount_repCD.2.1 0) loopCount_repD3.2 (ctWK_kCD _).2.1 p' p i j μ
  · change Graded.contractionValue P Φ D (repCD3 1) (fun _ => 0) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ (cycle_repCD3 1)]
    exact value_of_toGK_eq _ (cycle_repCD3 1) (isOnePI_repCD3 1) repD3Slot0_isOnePI kinds_CD3
      toGK_repCD3.2 (loopCount_repCD.2.1 1) loopCount_repD3.1 (ctWK_kCD _).2.1 p' p i j μ
  · change Graded.contractionValue P Φ D (repCD4 0) (fun _ => 0) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ (cycle_repCD4 0)]
    exact value_of_toGK_eq _ (cycle_repCD4 0) (isOnePI_repCD4 0) repD3Slot1_isOnePI kinds_CD4
      toGK_repCD4.1 (loopCount_repCD.2.2 0) loopCount_repD3.2 (ctWK_kCD _).2.2 p' p i j μ
  · change Graded.contractionValue P Φ D (repCD4 1) (fun _ => 0) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ (cycle_repCD4 1)]
    exact value_of_toGK_eq _ (cycle_repCD4 1) (isOnePI_repCD4 1) repD3Slot0_isOnePI kinds_CD4
      toGK_repCD4.2 (loopCount_repCD.2.2 1) loopCount_repD3.1 (ctWK_kCD _).2.2 p' p i j μ

/-! ### Limits and covariance -/

/-- The open-line parameters with the level-`0` counterterms at the set (c) data. -/
abbrev cdParams (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (s : ℝ × ℝ × ℝ) : Params :=
  ctParamsLevel (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s) 0

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-- The class values of `CDₖ s` along `ε` are `δ₁` times the `δ₃` class values along `ε`. -/
theorem ctFam_CD_eq (k : Fin 5) (hk : 2 ≤ k) (t : Fin 2) (p' p : Fin 4 → ℝ) (μ i j : Fin 4)
    (ε : ℝ) :
    ctFam { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) p' p μ (.inr (.inl (k, t))) i j =
      (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).δ₁ *
        contractionValue₂ { cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s with ε := ε } (d3Cls t).rep
          (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) :=
  cdVal_apply _ _ _ p' p μ t k hk i j

theorem cdParams_m : (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).m = P₀.m := rfl

theorem cdParams_mγ : (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).mγ = mγ := rfl

theorem cdParams_Λ : (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).Λ = Λ := rfl

/-- The limit of the class `CDₖ s`. -/
noncomputable def cdLim (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (s : ℝ × ℝ × ℝ)
    (t : Fin 2) (p' p : Fin 4 → ℝ) : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ :=
  ((cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).δ₁ : ℂ) •
    ctLimitV (d3Cls t) (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) p p'

/-- At admissible data and an on-shell positive-energy pair, the class `CDₖ s` (`2 ≤ k`)
converges to `δ₁` times the `δ₃` class limit. -/
theorem isClassLimC_CD (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (k : Fin 5) (hk : 2 ≤ k)
    (t : Fin 2) {p' p : Fin 4 → ℝ} (hpq : IsPairQ P₀.m p' p) :
    IsClassLimC ctFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inr (.inl (k, t))) p' p
      (cdLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s t p' p) := by
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  intro μ i j
  rw [← cdParams_m (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂) (mγ := mγ) (Λ := Λ) (D := D)
    (s := s)] at hm hp hp'
  exact ((tendsto_ctLimitV (d3Cls t) (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) hm
    (cdParams_mγ.symm ▸ hmγ) (cdParams_Λ.symm ▸ hΛ) hp' hp hp0' hp0 hq.le μ i j).const_mul
      _).congr fun ε => (ctFam_CD_eq k hk t p' p μ i j ε).symm

/-- **The limit links of the six classes `CD2`–`CD4`.** -/
theorem setCClassLim_CD (k : Fin 5) (hk : 2 ≤ k) (t : Fin 2) :
    SetCClassLim ctFam P₀ (.inr (.inl (k, t))) :=
  fun _ _ _ _ _ _ _ _ hA _ _ hpq => ⟨_, isClassLimC_CD hA k hk t hpq⟩

/-- `vecAct L` of a constant multiple. -/
theorem vecAct_const_smul (L : Matrix (Fin 4) (Fin 4) ℝ) (c : ℂ)
    (Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    QED.Dirac.vecAct L (c • Y) μ = c • QED.Dirac.vecAct L Y μ := by
  simp only [QED.Dirac.vecAct, Pi.smul_apply, Finset.smul_sum, smul_comm _ c]

/-- **The covariance links of the six classes `CD2`–`CD4`.** -/
theorem setCClassCov_CD (k : Fin 5) (hk : 2 ≤ k) (t : Fin 2) :
    SetCClassCov ctFam P₀ (.inr (.inl (k, t))) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA L S T h p' p hpq h0 h1 Y Z hY hZ μ
  have hpq' := isPairQ_map h hpq h0 h1
  have eY : Y = cdLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s t p' p := by
    funext ν
    ext i j
    exact tendsto_nhds_unique (hY ν i j) (isClassLimC_CD hA k hk t hpq ν i j)
  have eZ : Z = cdLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s t (L *ᵥ p') (L *ᵥ p) := by
    funext ν
    ext i j
    exact tendsto_nhds_unique (hZ ν i j) (isClassLimC_CD hA k hk t hpq' ν i j)
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  rw [← cdParams_m (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂) (mγ := mγ) (Λ := Λ) (D := D)
    (s := s)] at hm hp hp'
  rw [eY, eZ, cdLim, cdLim, vecAct_const_smul, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
  rw [QED.TwoLoop.PauliZero.ctLimitV_map (d3Cls t) (cdParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) hm
    (cdParams_mγ.symm ▸ hmγ) (cdParams_Λ.symm ▸ hΛ) h hp hp' hp0 hp0' h1 h0 hq.le μ]

/-! ### The links of (HS₆) with the classes `CD2`–`CD4` discharged -/

/-- The limit links of the ten classes `CDₖ s`, from those of `CD0`, `CD1`. -/
theorem setCClassLim_CD_all (hCD : ∀ k s, k < 2 → SetCClassLim ctFam P₀ (.inr (.inl (k, s)))) :
    ∀ k s, SetCClassLim ctFam P₀ (.inr (.inl (k, s))) := fun k s =>
  if hk : 2 ≤ k then setCClassLim_CD k hk s else hCD k s (not_le.mp hk)

/-- The covariance links of the ten classes `CDₖ s`, from those of `CD0`, `CD1`. -/
theorem setCClassCov_CD_all (hCD : ∀ k s, k < 2 → SetCClassCov ctFam P₀ (.inr (.inl (k, s)))) :
    ∀ k s, SetCClassCov ctFam P₀ (.inr (.inl (k, s))) := fun k s =>
  if hk : 2 ≤ k then setCClassCov_CD k hk s else hCD k s (not_le.mp hk)

/-- **The limit link of (HS₆)** from the limit links of the 36 two-loop-outer classes, of the
five classes `CBₖ` and of the four classes `CD0 s`, `CD1 s`. -/
theorem setCLimitLink_of_main_cb_cd01 (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hCB : ∀ k, SetCClassLim ctFam P₀ (.inl k))
    (hCD : ∀ k s, k < 2 → SetCClassLim ctFam P₀ (.inr (.inl (k, s)))) : SetCLimitLink P₀ :=
  setCLimitLink_of_main_cbcd hM hCB (setCClassLim_CD_all hCD)

/-- **The covariance link of (HS₆)** from the limit and covariance links of the 36
two-loop-outer classes, of the five classes `CBₖ` and of the four classes `CD0 s`, `CD1 s`. -/
theorem setCCovLink_of_main_cb_cd01 (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hCB : ∀ k, SetCClassLim ctFam P₀ (.inl k))
    (hCD : ∀ k s, k < 2 → SetCClassLim ctFam P₀ (.inr (.inl (k, s))))
    (hMc : ∀ r, SetCClassCov mainFam P₀ r) (hCBc : ∀ k, SetCClassCov ctFam P₀ (.inl k))
    (hCDc : ∀ k s, k < 2 → SetCClassCov ctFam P₀ (.inr (.inl (k, s)))) : SetCCovLink P₀ :=
  setCCovLink_of_main_cbcd hM hCB (setCClassLim_CD_all hCD) hMc hCBc (setCClassCov_CD_all hCDc)

end QED.ChainProof.SetCPauli

end
