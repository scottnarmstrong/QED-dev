/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCCovClasses
public import QED.ChainProof.SetCLinkIntOne
public import QED.TwoLoop.PauliZeroCovariance

/-!
# Set (c): limits and covariance of the five VP-share classes `S0`–`S4`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The VP-share
classes `repS0`, …, `repS4` are the one-loop vertex with one level-`1` counterterm on its open
line and no element. Every fermion field lies on the cycle of the external field and the grading
is the constant `1`, so the graded value (G₅) is the T1 value (T₁₀) at the open-line parameters
with the level-`1` counterterms `e⁴ d(1)` (`QED.ChainProof.SetCLink.ctParamsLevel`):
`contractionValue_eq_ctLevel`. Each representative is a relabelling of a representative of the
order-`e⁵` counterterm classes `QED.TwoLoop.Relabel.CtClass` (`repS0_eq`, …, kernel evaluation):

* `S0`, `S1`: `δ₂`, `δ_m` on the outgoing, incoming internal line (`d2Out`, `d2In`);
* `S2`, `S3`, `S4`: `δ₁` at the three vertices (`d1At3`, `d1At2`, `d1At1`).

Hence the limits exist (`QED.TwoLoop.CountertermLimit.exists_tendsto_contractionValue₂_ctClass`)
and are the counterterm-class limits `QED.TwoLoop.LimitCovariance.ctLimitV`, whose covariance is
`QED.TwoLoop.PauliZero.ctLimitV_map`.

* **`setCClassLim_S`**, **`setCClassCov_S`**: the limit and covariance links of the classes
  `.inr (.inr k)` of `QED.ChainProof.SetCPauli.ctFam`;
* **`setCLimitLink_of_main_cbcd`**, **`setCCovLink_of_main_cbcd`**: the limit and covariance
  links of (HS₆) from the per-class links of the 36 two-loop-outer classes and of the 15
  classes `CBₖ`, `CDₖ s` (open).
-/

@[expose] public section

open Complex Matrix Filter Topology
open QED.WickModel (Params IsOnePI Contraction contractionValue₂)

namespace QED.ChainProof.SetCPauli

open QED.TwoLoop.LimitCovariance QED.ChainProof.SetCLink QED.TwoLoop.Relabel
open QED.TwoLoop.Enumeration
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-- **The graded value of an open-line contraction at a constant grading** is the T1 value at
the open-line parameters with the level-`n` counterterms. -/
theorem contractionValue_eq_ctLevel (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) (hcyc : ∀ x, Equiv.Perm.SameCycle C.1.1 x (.inl 0)) (n : ℕ)
    (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    Graded.contractionValue P Φ D C (fun _ => n) pOut pIn kIn αOut βIn μ =
      contractionValue₂ (ctParamsLevel P Φ D n) C pOut pIn kIn αOut βIn μ := by
  unfold Graded.contractionValue contractionValue₂
  congr 1
  funext ℓ
  rw [regulatedAmplitude_eq_ctLevel P Φ D C hcyc n,
    QED.TwoLoop.Insertion.regulatedAmplitude₂_eq_zeroFlavoring _ hcyc]

/-! ### The relabellings -/

theorem repS0_eq : repS0 = relabelK (permK ![3, 2, 0, 1] ![2, 3, 1, 0]) (by decide +kernel)
    repD2Out := by
  decide +kernel

theorem repS1_eq : repS1 = relabelK (permK ![3, 1, 0, 2] ![2, 1, 3, 0]) (by decide +kernel)
    repD2In := by
  decide +kernel

theorem repS2_eq : repS2 = relabelK (permK ![2, 1, 0] ![2, 1, 0]) (by decide +kernel)
    repD1At3 := by
  decide +kernel

theorem repS3_eq : repS3 = relabelK (permK ![2, 0, 1] ![1, 2, 0]) (by decide +kernel)
    repD1At2 := by
  decide +kernel

theorem repS4_eq : repS4 = relabelK (permK ![1, 0, 2] ![1, 0, 2]) (by decide +kernel)
    repD1At1 := by
  decide +kernel

/-- The counterterm class of the VP-share class `Sₖ`. -/
def sCls : Fin 5 → CtClass := ![.d2Out, .d2In, .d1At3, .d1At2, .d1At1]

/-- **The VP-share class values are counterterm-class values** at the open-line parameters with
the level-`1` counterterms. -/
theorem sVal_apply (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (k : Fin 5) (i j : Fin 4) :
    sVal P Φ D p' p μ k i j = contractionValue₂ (ctParamsLevel P Φ D 1) (sCls k).rep
      (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  fin_cases k
  · change Graded.contractionValue P Φ D repS0 (fun _ => 1) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ cycle_repS0, repS0_eq,
      value_relabelK _ hmom repD2Out_isOnePI]
    rfl
  · change Graded.contractionValue P Φ D repS1 (fun _ => 1) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ cycle_repS1, repS1_eq,
      value_relabelK _ hmom repD2In_isOnePI]
    rfl
  · change Graded.contractionValue P Φ D repS2 (fun _ => 1) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ cycle_repS2, repS2_eq,
      value_relabelK _ hmom repD1At3_isOnePI]
    rfl
  · change Graded.contractionValue P Φ D repS3 (fun _ => 1) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ cycle_repS3, repS3_eq,
      value_relabelK _ hmom repD1At2_isOnePI]
    rfl
  · change Graded.contractionValue P Φ D repS4 (fun _ => 1) _ _ _ _ _ _ = _
    rw [contractionValue_eq_ctLevel P Φ D _ cycle_repS4, repS4_eq,
      value_relabelK _ hmom repD1At1_isOnePI]
    rfl

/-! ### Limits and covariance -/

/-- The open-line parameters with the level-`1` counterterms at the set (c) data. -/
abbrev sParams (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt) (s : ℝ × ℝ × ℝ) : Params :=
  ctParamsLevel (regParams P₀ M₁ M₂ c₁ c₂ mγ Λ) (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s) 1

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-- The class values of `Sₖ` along `ε` are the counterterm-class values along `ε`. -/
theorem ctFam_S_eq (k : Fin 5) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) (ε : ℝ) :
    ctFam { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε } (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ)
        (shareCt D s) p' p μ (.inr (.inr k)) i j =
      contractionValue₂ { sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s with ε := ε } (sCls k).rep
        (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ) :=
  sVal_apply _ _ _ p' p μ k i j

/-- The counterterm-class values converge to `ctLimitV`. -/
theorem tendsto_ctLimitV (c : CtClass) (Q : Params) (hm : 0 < Q.m) (hmγ : 0 < Q.mγ)
    (hΛ : 0 < Q.Λ) {p' p : Fin 4 → ℝ} (hp' : Minkowski.dot p' p' = -Q.m ^ 2)
    (hp : Minkowski.dot p p = -Q.m ^ 2) (hp0' : 0 < p' 0) (hp0 : 0 < p 0)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (μ i j : Fin 4) :
    Tendsto (fun ε => contractionValue₂ { Q with ε := ε } c.rep (fun _ => p') (fun _ => p)
      (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)) (𝓝[>] 0)
      (𝓝 (ctLimitV c Q p p' μ i j)) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  exact tendsto_nhds_limUnder
    (QED.TwoLoop.CountertermLimit.exists_tendsto_contractionValue₂_ctClass c Q hm hmγ hΛ hmom hp
      hp' hp0 hp0' hq (fun _ => i) (fun _ => j) (fun _ => μ))

theorem sParams_m : (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).m = P₀.m := rfl

theorem sParams_mγ : (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).mγ = mγ := rfl

theorem sParams_Λ : (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s).Λ = Λ := rfl

/-- At admissible data and an on-shell positive-energy pair, the class `Sₖ` converges to the
counterterm-class limit. -/
theorem isClassLimC_S (hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (k : Fin 5) {p' p : Fin 4 → ℝ}
    (hpq : IsPairQ P₀.m p' p) :
    IsClassLimC ctFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inr (.inr k)) p' p
      (ctLimitV (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) p p') := by
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  intro μ i j
  rw [← sParams_m (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂) (mγ := mγ) (Λ := Λ) (D := D)
    (s := s)] at hm hp hp'
  exact (tendsto_ctLimitV (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) hm
    (sParams_mγ.symm ▸ hmγ) (sParams_Λ.symm ▸ hΛ) hp' hp hp0' hp0 hq.le μ i j).congr
    fun ε => (ctFam_S_eq k p' p μ i j ε).symm

/-- **The limit links of the five VP-share classes.** -/
theorem setCClassLim_S (k : Fin 5) : SetCClassLim ctFam P₀ (.inr (.inr k)) :=
  fun _ _ _ _ _ _ _ _ hA _ _ hpq => ⟨_, isClassLimC_S hA k hpq⟩

/-- **The covariance links of the five VP-share classes.** -/
theorem setCClassCov_S (k : Fin 5) : SetCClassCov ctFam P₀ (.inr (.inr k)) := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA L S T h p' p hpq h0 h1 Y Z hY hZ μ
  have hpq' := isPairQ_map h hpq h0 h1
  have eY : Y = ctLimitV (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) p p' := by
    funext ν
    ext i j
    exact tendsto_nhds_unique (hY ν i j) (isClassLimC_S hA k hpq ν i j)
  have eZ : Z = ctLimitV (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) (L *ᵥ p) (L *ᵥ p') := by
    funext ν
    ext i j
    exact tendsto_nhds_unique (hZ ν i j) (isClassLimC_S hA k hpq' ν i j)
  obtain ⟨-, -, -, -, hmγ, hΛ, -, hm2, -, -⟩ := hA
  obtain ⟨hp', hp, hp0', hp0, hq⟩ := hpq
  have hm : 0 < P₀.m := by linarith
  rw [← sParams_m (M₁ := M₁) (M₂ := M₂) (c₁ := c₁) (c₂ := c₂) (mγ := mγ) (Λ := Λ) (D := D)
    (s := s)] at hm hp hp'
  rw [eY, eZ]
  exact QED.TwoLoop.PauliZero.ctLimitV_map (sCls k) (sParams P₀ M₁ M₂ c₁ c₂ mγ Λ D s) hm
    (sParams_mγ.symm ▸ hmγ) (sParams_Λ.symm ▸ hΛ) h hp hp' hp0 hp0' h1 h0 hq.le μ

/-! ### The links of (HS₆) with the share classes discharged -/

/-- The limit links of the 20 counterterm and share classes, from those of `CB` and `CD`. -/
theorem setCClassLim_ct (hCB : ∀ k, SetCClassLim ctFam P₀ (.inl k))
    (hCD : ∀ k s, SetCClassLim ctFam P₀ (.inr (.inl (k, s)))) : ∀ r, SetCClassLim ctFam P₀ r
  | .inl k => hCB k
  | .inr (.inl (k, s)) => hCD k s
  | .inr (.inr k) => setCClassLim_S k

/-- The covariance links of the 20 counterterm and share classes, from those of `CB` and `CD`. -/
theorem setCClassCov_ct (hCB : ∀ k, SetCClassCov ctFam P₀ (.inl k))
    (hCD : ∀ k s, SetCClassCov ctFam P₀ (.inr (.inl (k, s)))) : ∀ r, SetCClassCov ctFam P₀ r
  | .inl k => hCB k
  | .inr (.inl (k, s)) => hCD k s
  | .inr (.inr k) => setCClassCov_S k

/-- **The limit link of (HS₆)** from the limit links of the 36 two-loop-outer classes and of the
15 classes `CBₖ`, `CDₖ s`; the five VP-share classes are discharged. -/
theorem setCLimitLink_of_main_cbcd (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hCB : ∀ k, SetCClassLim ctFam P₀ (.inl k))
    (hCD : ∀ k s, SetCClassLim ctFam P₀ (.inr (.inl (k, s)))) : SetCLimitLink P₀ :=
  setCLimitLink_of_classes hM (setCClassLim_ct hCB hCD)

/-- **The covariance link of (HS₆)** from the limit and covariance links of the 36
two-loop-outer classes and of the 15 classes `CBₖ`, `CDₖ s`; the five VP-share classes are
discharged. -/
theorem setCCovLink_of_main_cbcd (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hCB : ∀ k, SetCClassLim ctFam P₀ (.inl k))
    (hCD : ∀ k s, SetCClassLim ctFam P₀ (.inr (.inl (k, s))))
    (hMc : ∀ r, SetCClassCov mainFam P₀ r) (hCBc : ∀ k, SetCClassCov ctFam P₀ (.inl k))
    (hCDc : ∀ k s, SetCClassCov ctFam P₀ (.inr (.inl (k, s)))) : SetCCovLink P₀ :=
  setCCovLink_of_classes hM (setCClassLim_ct hCB hCD) hMc (setCClassCov_ct hCBc hCDc)

end QED.ChainProof.SetCPauli

end
