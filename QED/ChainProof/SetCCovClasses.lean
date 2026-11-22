/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCPauliLink
public import QED.ChainProof.SetCLinkVertex
public import QED.ChainProof.HCClasses

/-!
# The set (c) limit and covariance links from per-class links

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The set (c)
family vertex is `(1/i)` times the signed sum of the values of the 56 class representatives
(`QED.ChainProof.SetCLink.familyVertex_setC_eq_classes`). This file groups them into

* the 36 classes with a two-loop outer vertex (`MainIdx`): `-V(Bᵢ)` (12) and `+V(Dᵢₛ)` (24);
* the 20 counterterm and VP-share classes (`CtIdx`), with a one-loop outer vertex: `-V(CBₖ)` (5),
  `+V(CDₖₛ)` (10), `+V(Sₖ)` (5),

as signed matrix values `mainVal`, `ctVal` (`familyVertex_setC_eq_split`), and reduces the two
open links of `QED/ChainProof/SetCPauliLink.lean` to per-class statements at the set (c) data
(fixed admissible regulators, `D` renormalized through `e⁴`, `s` a VP share, counterterms
`shareCt D s`):

* `SetCClassLim V P₀ r`: the signed class value `V r` has an `ε → 0⁺` limit at every
  on-shell positive-energy pair with `q² > 0`;
* `SetCClassCov V P₀ r`: the class limits are covariant under every spinor-lifted `L` that keeps
  positive energies.

Proved: **`setCLimitLink_of_classes`** (`SetCLimitLink P₀` from the 56 limit links),
**`setCCovLink_of_classes`** (`SetCCovLink P₀` from the 56 limit and covariance links), and
`setCFixedLink_of_classes`, the fixed link of (HS₆) from these, the mirror identity (proved) and
the canonical Pauli limit.
-/

@[expose] public section

open Complex Matrix Filter Topology
open QED.WickModel (Params IsOnePI Contraction)

namespace QED.ChainProof.SetCPauli

open QED.TwoLoop.LimitCovariance QED.ChainProof.SetCLink
open QED.ChainProof.SetAPauli (regParams regFlavors)

/-! ### The split of the 56 classes -/

/-- The 36 classes with a two-loop outer vertex: `repB i` and `repD i s`. -/
abbrev MainIdx : Type := Fin 12 ⊕ Fin 12 × Fin 2

/-- The 20 counterterm and VP-share classes: `repCBₖ`, `repCDₖ s` and `repSₖ`. -/
abbrev CtIdx : Type := Fin 5 ⊕ Fin 5 × Fin 2 ⊕ Fin 5

/-- The graded value (G₅) of one contraction at the set (c) momenta, as a matrix. -/
noncomputable def clsVal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction 1 1 κ) (g : Graded.Grading κ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => Graded.contractionValue P Φ D C g (fun _ => p') (fun _ => p)
    (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ)

/-- **The signed values of the 36 two-loop-outer classes.** -/
noncomputable def mainVal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    MainIdx → Matrix (Fin 4) (Fin 4) ℂ
  | .inl i => -clsVal P Φ D (repB i) 0 p' p μ
  | .inr (i, s) => clsVal P Φ D (repD i s) 0 p' p μ

/-- The values of the five classes `CBₖ` (bubble on the photon). -/
noncomputable def cbVal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Fin 5 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![clsVal P Φ D repCB0 0 p' p μ, clsVal P Φ D repCB1 0 p' p μ, clsVal P Φ D repCB2 0 p' p μ,
    clsVal P Φ D repCB3 0 p' p μ, clsVal P Φ D repCB4 0 p' p μ]

/-- The values of the five classes `CDₖ s` (`δ₃` on the photon). -/
noncomputable def cdVal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (s : Fin 2) : Fin 5 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![clsVal P Φ D (repCD0 s) 0 p' p μ, clsVal P Φ D (repCD1 s) 0 p' p μ,
    clsVal P Φ D (repCD2 s) 0 p' p μ, clsVal P Φ D (repCD3 s) 0 p' p μ,
    clsVal P Φ D (repCD4 s) 0 p' p μ]

/-- The values of the five VP-share classes `Sₖ` (level-`1` counterterm, no element). -/
noncomputable def sVal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Fin 5 → Matrix (Fin 4) (Fin 4) ℂ :=
  ![clsVal P Φ D repS0 (gOne _) p' p μ, clsVal P Φ D repS1 (gOne _) p' p μ,
    clsVal P Φ D repS2 (gOne _) p' p μ, clsVal P Φ D repS3 (gOne _) p' p μ,
    clsVal P Φ D repS4 (gOne _) p' p μ]

/-- **The signed values of the 20 counterterm and VP-share classes.** -/
noncomputable def ctVal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    CtIdx → Matrix (Fin 4) (Fin 4) ℂ
  | .inl k => -cbVal P Φ D p' p μ k
  | .inr (.inl (k, s)) => cdVal P Φ D p' p μ s k
  | .inr (.inr k) => sVal P Φ D p' p μ k

/-- The signed values of all 56 classes. -/
noncomputable def allVal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    MainIdx ⊕ CtIdx → Matrix (Fin 4) (Fin 4) ℂ
  | .inl r => mainVal P Φ D p' p μ r
  | .inr r => ctVal P Φ D p' p μ r

/-- **The set (c) vertex is `(1/i)` times the sum of the signed class values**, split into the
36 two-loop-outer classes and the 20 counterterm and VP-share classes. -/
theorem familyVertex_setC_eq_split (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Graded.familyVertex P Φ D (fun C g => IsOnePI C ∧ ThreeLoop.IsSetC C g) 7 p' p μ =
      (1 / I) • (∑ r, mainVal P Φ D p' p μ r + ∑ r, ctVal P Φ D p' p μ r) := by
  rw [familyVertex_setC_eq_classes]
  ext α β
  simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply,
    smul_eq_mul, Fintype.sum_sum_type, Fintype.sum_prod_type, mainVal, ctVal, cbVal, cdVal,
    sVal, Fin.sum_univ_five, Matrix.neg_apply, clsVal, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Finset.sum_neg_distrib,
    Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_two]
  ring

/-- The sum over all 56 classes. -/
theorem sum_allVal (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    ∑ r, allVal P Φ D p' p μ r = ∑ r, mainVal P Φ D p' p μ r + ∑ r, ctVal P Φ D p' p μ r := by
  rw [Fintype.sum_sum_type]
  rfl

/-! ### Per-class links -/

/-- The type of a family of signed class values at the set (c) flavours. -/
abbrev ClsFam (ι : Type) : Type :=
  Params → Lepton.Flavors (Fin 3 ⊕ Fin 0 × Fin 3) → RegCt → (Fin 4 → ℝ) → (Fin 4 → ℝ) →
    Fin 4 → ι → Matrix (Fin 4) (Fin 4) ℂ

/-- `Y` is the `ε → 0⁺` limit of the class value `V · r` at the set (c) data, entrywise. -/
def IsClassLimC {ι : Type} (V : ClsFam ι) (P₀ : Params) (M₁ M₂ c₁ c₂ mγ Λ : ℝ) (D : RegCt)
    (s : ℝ × ℝ × ℝ) (r : ι) (p' p : Fin 4 → ℝ) (Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ μ i j, Tendsto (fun ε => V { regParams P₀ M₁ M₂ c₁ c₂ mγ Λ with ε := ε }
    (regFlavors P₀ M₁ M₂ c₁ c₂ mγ Λ) (shareCt D s) p' p μ r i j) (𝓝[>] 0) (𝓝 (Y μ i j))

/-- **The limit link of one class** (O-lim per class): at the set (c) data, the class value has
an `ε → 0⁺` limit at every on-shell positive-energy pair with `q² > 0`. -/
def SetCClassLim {ι : Type} (V : ClsFam ι) (P₀ : Params) (r : ι) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ p' p, IsPairQ P₀.m p' p → ∃ Y, IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p Y

/-- **The covariance link of one class**: the class limits are covariant under every
spinor-lifted `L` that keeps positive energies. -/
def SetCClassCov {ι : Type} (V : ClsFam ι) (P₀ : Params) (r : ι) : Prop :=
  ∀ M₁ M₂ c₁ c₂ mγ Λ D s, SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s →
    ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S T : Matrix (Fin 4) (Fin 4) ℂ), IsSpinLift L S T →
    ∀ p' p, IsPairQ P₀.m p' p → 0 < (L *ᵥ p') 0 → 0 < (L *ᵥ p) 0 →
    ∀ Y Z, IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p Y →
      IsClassLimC V P₀ M₁ M₂ c₁ c₂ mγ Λ D s r (L *ᵥ p') (L *ᵥ p) Z →
      ∀ μ, S * Z μ * T = QED.Dirac.vecAct L Y μ

/-- The 36 two-loop-outer class values as a family. -/
noncomputable abbrev mainFam : ClsFam MainIdx := fun Q Φ D => mainVal Q Φ D

/-- The 20 counterterm and VP-share class values as a family. -/
noncomputable abbrev ctFam : ClsFam CtIdx := fun Q Φ D => ctVal Q Φ D

/-- All 56 class values as a family. -/
noncomputable abbrev allFam : ClsFam (MainIdx ⊕ CtIdx) := fun Q Φ D => allVal Q Φ D

/-! ### Assembly -/

/-- `vecAct L` of a multiple of a finite sum. -/
theorem vecAct_smul_sum {ι : Type*} [Fintype ι] (L : Matrix (Fin 4) (Fin 4) ℝ) (c : ℂ)
    (Y : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    QED.Dirac.vecAct L (c • ∑ r, Y r) μ = c • ∑ r, QED.Dirac.vecAct L (Y r) μ := by
  simp only [QED.Dirac.vecAct, Pi.smul_apply, Finset.sum_apply, Finset.smul_sum, smul_comm _ c]
  exact Finset.sum_comm

variable {P₀ : Params} {M₁ M₂ c₁ c₂ mγ Λ : ℝ} {D : RegCt} {s : ℝ × ℝ × ℝ}

/-- **The sum of the class limits is a limit of the set (c) family vertex.** -/
theorem setCLim_sum {p' p : Fin 4 → ℝ} {Y : MainIdx ⊕ CtIdx → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ r, IsClassLimC allFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p (Y r)) :
    setCLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s p' p ((1 / I) • ∑ r, Y r) := by
  intro μ i j
  have hsum := (tendsto_finsetSum (Finset.univ : Finset (MainIdx ⊕ CtIdx))
    fun r _ => hY r μ i j).const_mul (1 / I)
  have hval : ((1 / I) • ∑ r, Y r) μ i j = (1 / I) * ∑ r, Y r μ i j := by
    simp only [Pi.smul_apply, Finset.sum_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [hval]
  refine hsum.congr fun ε => ?_
  rw [familyVertex_setC_eq_split, ← sum_allVal]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]

/-- **The limit of the set (c) family vertex is the sum of the class limits.** -/
theorem setCLim_eq_sum {p' p : Fin 4 → ℝ}
    {Y : MainIdx ⊕ CtIdx → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ r, IsClassLimC allFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p (Y r)) {V}
    (hV : setCLim P₀ M₁ M₂ c₁ c₂ mγ Λ D s p' p V) : V = (1 / I) • ∑ r, Y r := by
  funext μ
  ext i j
  exact tendsto_nhds_unique (hV μ i j) (setCLim_sum hY μ i j)

/-- The class limits of the split families are those of the joint family. -/
theorem isClassLimC_all_inl {r : MainIdx} {p' p : Fin 4 → ℝ} {Y}
    (h : IsClassLimC mainFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p Y) :
    IsClassLimC allFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inl r) p' p Y := h

/-- See `isClassLimC_all_inl`. -/
theorem isClassLimC_all_inr {r : CtIdx} {p' p : Fin 4 → ℝ} {Y}
    (h : IsClassLimC ctFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s r p' p Y) :
    IsClassLimC allFam P₀ M₁ M₂ c₁ c₂ mγ Λ D s (.inr r) p' p Y := h

/-- The limit links of the 56 classes, from those of the two groups. -/
theorem setCClassLim_all (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hC : ∀ r, SetCClassLim ctFam P₀ r) : ∀ r, SetCClassLim allFam P₀ r
  | .inl r => hM r
  | .inr r => hC r

/-- The covariance links of the 56 classes, from those of the two groups. -/
theorem setCClassCov_all (hM : ∀ r, SetCClassCov mainFam P₀ r)
    (hC : ∀ r, SetCClassCov ctFam P₀ r) : ∀ r, SetCClassCov allFam P₀ r
  | .inl r => hM r
  | .inr r => hC r

/-- **The limit link of (HS₆) from the limit links of the 56 classes.** -/
theorem setCLimitLink_of_classes (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hC : ∀ r, SetCClassLim ctFam P₀ r) : SetCLimitLink P₀ := by
  intro M₁ M₂ c₁ c₂ mγ Λ hM₁ hM₂ hPV₁ hPV₂ hmγ hΛ hmΛ hm2 D hD s hs p' p hp' hp hp0' hp0 hq
  have hA : SetCAdm P₀ M₁ M₂ c₁ c₂ mγ Λ D s := ⟨hM₁, hM₂, hPV₁, hPV₂, hmγ, hΛ, hmΛ, hm2, hD, hs⟩
  choose Y hY using fun r => setCClassLim_all hM hC r M₁ M₂ c₁ c₂ mγ Λ D s hA p' p
    ⟨hp', hp, hp0', hp0, hq⟩
  exact ⟨_, setCLim_sum hY⟩

/-- **The covariance link of (HS₆) from the limit and covariance links of the 56 classes.** -/
theorem setCCovLink_of_classes (hM : ∀ r, SetCClassLim mainFam P₀ r)
    (hC : ∀ r, SetCClassLim ctFam P₀ r) (hMc : ∀ r, SetCClassCov mainFam P₀ r)
    (hCc : ∀ r, SetCClassCov ctFam P₀ r) : SetCCovLink P₀ := by
  intro M₁ M₂ c₁ c₂ mγ Λ D s hA L S T h p' p hpq h0 h1 V W hV hW μ
  have hpq' := isPairQ_map h hpq h0 h1
  have hL := setCClassLim_all hM hC
  choose Y hY using fun r => hL r M₁ M₂ c₁ c₂ mγ Λ D s hA p' p hpq
  choose Z hZ using fun r => hL r M₁ M₂ c₁ c₂ mγ Λ D s hA _ _ hpq'
  rw [setCLim_eq_sum hY hV, setCLim_eq_sum hZ hW, vecAct_smul_sum,
    Pi.smul_apply, Finset.sum_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum,
    Matrix.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun r _ =>
    setCClassCov_all hMc hCc r M₁ M₂ c₁ c₂ mγ Λ D s hA L S T h p' p hpq h0 h1 (Y r) (Z r)
      (hY r) (hZ r) μ

/-- **The fixed link of (HS₆) from the per-class links**, the mirror identity (proved,
`QED.ChainProof.SetCMirror.setCMirrorAt`, passed as `hMA`) and the canonical Pauli limit. -/
theorem setCFixedLink_of_classes {b : ℝ → ℝ → ℝ → ℝ → ℝ} (he : P₀.e ≠ 0) (hm : 0 < P₀.m)
    (hM : ∀ r, SetCClassLim mainFam P₀ r) (hC : ∀ r, SetCClassLim ctFam P₀ r)
    (hMc : ∀ r, SetCClassCov mainFam P₀ r) (hCc : ∀ r, SetCClassCov ctFam P₀ r)
    (hMA : SetCMirrorAt P₀) (hB : SetCPauliAt P₀ b) :
    SetCFixedLink P₀ (setCPauliValue P₀ b) :=
  setCFixedLink_of_pauliAt he hm (setCLimitLink_of_classes hM hC)
    (setCCovLink_of_classes hM hC hMc hCc) hMA hB

end QED.ChainProof.SetCPauli

end
