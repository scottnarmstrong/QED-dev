/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMPow
public import QED.ChainProof.SetCUnitCov

/-!
# Multi-denominator two-loop vertex units: covariance

Helper level for set (c) (stage L2). The multi-denominator units of
`QED/ChainProof/SetCUnitMUnit.lean` are covariant exactly as the two-mass units
(`QED.ChainProof.SetCUnit.isLittleGroupCovariant_unitLimitV`, `…unitLimitV_map`): at `n = 0` the
limit entries are parametric values (`IsParamValue`) of the class numerator for the `r + 8`
lines, and the extra lines carry the momenta `κⱼ p_s`, which transform as the line momentum `p_s`.
With powers `(k²)ⁿ` the limits are linear combinations of `n = 0` limits
(`QED.ChainProof.SetCUnitM.unitMLimitV_succ`), and covariance is linear.

* `unitMData`, `isParamValue_unitMLimitV`: the parametric data and values at `n = 0`;
* **`isLittleGroupCovariant_unitMLimitV`**: little-group covariance, every `n` with the last `n`
  extra lines unscaled;
* **`unitMLimitV_map`**: `S W^μ T = L^μ_ν V^ν` for the limits `V` at `(p, p')` and `W` at
  `(L p, L p')`, every spinor-lifted `L`, every such `n`.
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge
open QED.TwoLoop.ClassIntegrable QED.TwoLoop.ClassLimit QED.TwoLoop.LimitCovariance
open QED.TwoLoop.ReflCovariance QED.ChainProof.SetCUnit
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix class5LoopMatrixPV)

variable {r : ℕ} {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-! ### Linearity -/

theorem vecAct_sub_smul (L : Matrix (Fin 4) (Fin 4) ℝ) (V W : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (a : ℂ) (μ : Fin 4) :
    vecAct L (fun ν => V ν - a • W ν) μ = vecAct L V μ - a • vecAct L W μ := by
  simp only [vecAct, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_comm _ a]

theorem conj_sub_smul (V W : Matrix (Fin 4) (Fin 4) ℂ) (a : ℂ) :
    S * (V - a • W) * T = S * V * T - a • (S * W * T) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The recursion of `unitMLimitV_succ` for the matrices. -/
theorem unitMLimitV_succ_mat {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
    (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    {n : ℕ} {κ cs : Fin (r + 1) → ℝ} (hnr : n + 1 ≤ r + 1) (hT : TrailOne (n + 1) κ)
    (hX : ExtraGe μ₀ κ cs) (μ : Fin 4) :
    unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' (n + 1) μ =
      unitMLimitV c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) p p' n μ -
        ((cs (Fin.last r) ^ 2 : ℝ) : ℂ) • unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p'
          n μ := by
  ext i j
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact unitMLimitV_succ hc P hm hs hμ₀ hM hp hp' hq hnr hT hX μ i j

/-! ### The parametric data at `n = 0` -/

/-- The parametric data of the multi-denominator unit. -/
noncomputable def unitMData {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m)
    {s : Fin 8} (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
    {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) : ParamData where
  m := r + 7
  α := unitMMatrix c s κ
  p := unitMMomenta c s κ p p'
  M := unitMMasses P.m a A b B cs
  E := unitME r
  hm := by omega
  hcrit := noSubdivergenceRefined_unitM hc s hX.ne_zero
  c := unitConst P.m μ₀
  hc := unitConst_pos hm hμ₀
  hV := fun _ hz hz1 hU => symanzikV_unitM_ge hc hs hμ₀ hM hX hp hp' hq hz hz1 hU

theorem unitMMomenta_map (c : Class5) (s : Fin 8) (κ : Fin r → ℝ) (p p' : Fin 4 → ℝ) :
    unitMMomenta c s κ (L *ᵥ p) (L *ᵥ p') = fun i => L *ᵥ unitMMomenta c s κ p p' i := by
  funext i
  simp only [unitMMomenta, pvMomentaE_map, Matrix.mulVec_smul]

theorem mulVec_unitMMomenta {p p' : Fin 4 → ℝ} (hLp : L *ᵥ p = p) (hLp' : L *ᵥ p' = p')
    (c : Class5) (s : Fin 8) (κ : Fin r → ℝ) (i : Fin (r + 8)) :
    L *ᵥ unitMMomenta c s κ p p' i = unitMMomenta c s κ p p' i := by
  simp only [unitMMomenta, pvMomentaE, Matrix.mulVec_smul, mulVec_extMomenta hLp hLp']

section Cov

variable {c : Class5} (hc : c ∈ openClasses) (P : Params) (hm : 0 < P.m) {s : Fin 8}
  (hs : 4 ≤ (s : ℕ)) {μ₀ a A b B : ℝ} (hμ₀ : 0 < μ₀) (hM : MassesGe μ₀ a A b B)
  {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
include hc hm hs hμ₀ hM hp hp' hq

/-- The unit limit at `n = 0` as a quartic parametric integral. -/
theorem exists_quartic_unitMLimitV {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) (μ i j : Fin 4) :
    ∃ Q : LoopQuartic, Q.eval = (fun ℓ => (twoLoopNorm • classNumM c P p p' μ ℓ) i j) ∧
      MeasureTheory.IntegrableOn (paramIntegrand Q (unitMMatrix c s κ) (unitMMomenta c s κ p p')
        (unitMMasses P.m a A b B cs) 0) (QED.Integration.Feynman.simplexSet (r + 7)) ∧
      unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' 0 μ i j =
        -((π : ℂ) ^ 4) * ∫ x in QED.Integration.Feynman.simplexSet (r + 7),
          paramIntegrand Q (unitMMatrix c s κ) (unitMMomenta c s κ p p')
            (unitMMasses P.m a A b B cs) 0 x := by
  obtain ⟨Q, hQ⟩ := exists_unitQuartic hc P p p' μ i j
  refine ⟨Q, hQ.trans (unitNum_eq_classNumM c P p p' μ i j), ?_, ?_⟩
  · exact (tendsto_unitMValue hc P hm hs hμ₀ hM hX hp hp' hq μ i j hQ).1
  · exact unitMLimitV_eq hc P hm hs hμ₀ hM hX hp hp' hq μ i j hQ

/-- Each entry of the unit limit at `n = 0` is the parametric value of its numerator. -/
theorem isParamValue_unitMLimitV {κ cs : Fin r → ℝ} (hX : ExtraGe μ₀ κ cs) (μ i j : Fin 4) :
    IsParamValue (unitMData hc P hm hs hμ₀ hM hX hp hp' hq)
      (fun ℓ => (twoLoopNorm • classNumM c P p p' μ ℓ) i j)
      (unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' 0 μ i j) := by
  obtain ⟨Q, hQ, -, hv⟩ := exists_quartic_unitMLimitV hc P hm hs hμ₀ hM hp hp' hq hX μ i j
  refine ⟨Q, hQ, ?_, hv⟩
  rw [← unitNum_eq_classNumM]
  exact refinedBound_unitM hc P s κ p p' μ i j

/-- **Little-group covariance of the multi-denominator unit limits**, for every power `n` with the
last `n ≤ r` extra lines unscaled. -/
theorem isLittleGroupCovariant_unitMLimitV (n : ℕ) :
    ∀ {r : ℕ} {κ cs : Fin r → ℝ}, n ≤ r → TrailOne n κ → ExtraGe μ₀ κ cs →
      IsLittleGroupCovariant p' p (unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n) := by
  induction n with
  | zero =>
    intro r κ cs _ _ hX
    exact isLittleGroupCovariant_of_paramValue (unitMData hc P hm hs hμ₀ hM hX hp hp' hq)
      (fun L S T _ hLp hLp' i => mulVec_unitMMomenta hLp hLp' c s κ i)
      (fun μ ℓ => twoLoopNorm • classNumM c P p p' μ ℓ)
      (fun L S T h hLp hLp' μ ℓ => by
        rw [Matrix.mul_smul, Matrix.smul_mul, classNumM_cov hc h hLp hLp', vecAct_smul]) _
      fun μ i j => isParamValue_unitMLimitV hc P hm hs hμ₀ hM hp hp' hq hX μ i j
  | succ n ih =>
    intro r κ cs hnr hT hX
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have h₁ := ih (by omega) hT.init hX.init
    have h₂ := ih (by omega) hT.of_succ hX
    intro L S T hST hγ hLp hLp' μ
    rw [unitMLimitV_succ_mat hc P hm hs hμ₀ hM hp hp' hq hnr hT hX, conj_sub_smul,
      h₁ L S T hST hγ hLp hLp' μ, h₂ L S T hST hγ hLp hLp' μ]
    rw [show unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' (n + 1) =
        fun ν => unitMLimitV c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) p p' n ν -
          ((cs (Fin.last r) ^ 2 : ℝ) : ℂ) • unitMLimitV c P s κ (unitMMasses P.m a A b B cs)
            p p' n ν from funext fun ν =>
        unitMLimitV_succ_mat hc P hm hs hμ₀ hM hp hp' hq hnr hT hX ν]
    exact (vecAct_sub_smul L _ _ _ μ).symm

/-- **Covariance of the multi-denominator unit limits with the external momenta moved**:
`S W^μ T = L^μ_ν V^ν`, `V` at `(p, p')`, `W` at `(L p, L p')`, the line masses unchanged, every
power `n` with the last `n ≤ r` extra lines unscaled. -/
theorem unitMLimitV_map (h : IsSpinLift L S T) (n : ℕ) :
    ∀ {r : ℕ} {κ cs : Fin r → ℝ}, n ≤ r → TrailOne n κ → ExtraGe μ₀ κ cs → ∀ μ : Fin 4,
      S * unitMLimitV c P s κ (unitMMasses P.m a A b B cs) (L *ᵥ p) (L *ᵥ p') n μ * T =
        vecAct L (unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' n) μ := by
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [dot_mulVec_sub h]; exact hq
  induction n with
  | zero =>
    intro r κ cs _ _ hX μ
    exact conj_eq_vecAct_of_paramValue (unitMData hc P hm hs hμ₀ hM hX hp hp' hq) h
      (unitMMomenta c s κ (L *ᵥ p) (L *ᵥ p')) (unitMMomenta_map c s κ p p')
      (fun μ ℓ => twoLoopNorm • classNumM c P p p' μ ℓ)
      (fun μ ℓ => twoLoopNorm • classNumM c P (L *ᵥ p) (L *ᵥ p') μ ℓ)
      (fun μ ℓ => by rw [Matrix.mul_smul, Matrix.smul_mul, classNumM_map hc h, vecAct_smul]) _ _
      (fun μ i j => isParamValue_unitMLimitV hc P hm hs hμ₀ hM hp hp' hq hX μ i j)
      (fun μ i j => exists_quartic_unitMLimitV hc P hm hs hμ₀ hM hpL hpL' hqL hX μ i j) μ
  | succ n ih =>
    intro r κ cs hnr hT hX μ
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [unitMLimitV_succ_mat hc P hm hs hμ₀ hM hpL hpL' hqL hnr hT hX, conj_sub_smul,
      ih (by omega) hT.init hX.init μ, ih (by omega) hT.of_succ hX μ]
    rw [show unitMLimitV c P s κ (unitMMasses P.m a A b B cs) p p' (n + 1) =
        fun ν => unitMLimitV c P s (Fin.init κ) (unitMMasses P.m a A b B (Fin.init cs)) p p' n ν -
          ((cs (Fin.last r) ^ 2 : ℝ) : ℂ) • unitMLimitV c P s κ (unitMMasses P.m a A b B cs)
            p p' n ν from funext fun ν =>
        unitMLimitV_succ_mat hc P hm hs hμ₀ hM hp hp' hq hnr hT hX ν]
    exact (vecAct_sub_smul L _ _ _ μ).symm

end Cov

end QED.ChainProof.SetCUnitM

end
