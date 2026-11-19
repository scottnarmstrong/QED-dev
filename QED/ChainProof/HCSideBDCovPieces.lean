/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDRepLimit
public import QED.TwoLoop.ReflCovarianceClasses

/-!
# Parametric pieces of the bubble–`δ₃` and `δ₃`–bubble limits

Helper for the covariance of the limits of `QED.ChainProof.Enum.repBD s` and `repDB s`. The
`ε → 0⁺` limit of each class integrand is a combination of parametric values
(`QED.TwoLoop.LimitCovariance.IsParamValue`) of pieces on rows of the `VP` class matrix. This
file provides:

* `JointLimV F v`: `F ε` is eventually jointly integrable and its joint integral tends to `v`;
  closed under sums, convergent scalar factors and eventual pointwise equality;
* `rowsData`: the parametric data of a piece on rows of the `VP` matrix, and
  `jointLimV_of_paramValue`: a parametric value is the limit of its piece;
* `conj_rowsData`: covariance of the values of such pieces, at the pair `(p, p')` and at
  `(L p, L p')`, for numerators covariant under `L`;
* `longM`, `bdN_eq_longM`, `dbN_eq_longM`, `longM_map`: the numerators of the longitudinal
  pieces as vertex chains with the tensor `u_ν w_ρ` (lowered), and their covariance;
* `bdPiece_bounds`, `dbPiece_bounds`: the polynomial and refined bounds of those numerators.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Matrix
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit
  QED.ChainProof.Enum QED.ChainProof.RepsInt QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.LimitCovariance QED.TwoLoop.ReflCovariance QED.Dirac
open QED.Integration.TwoLoop (lineDenom castLoopMatrix class5LoopMatrix classVPMomenta
  RefinedBound IntNoSubdivergenceRefined symanzikU symanzikV
  noSubdivergenceRefined_castLoopMatrix_iff
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined)
open QED.TwoLoop.ClassLimit (jointEnergyFirstIntegral_add jointEnergyFirstIntegral_const_mul
  jointEnergyFirstIntegrable_const_mul)

/-! ### Convergent families with a given limit -/

/-- For `ε → 0⁺`, `F ε` is eventually integrable in both stages and its joint energy-first
integral tends to `v`. -/
def JointLimV (F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ) (v : ℂ) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), QED.TwoLoop.jointEnergyFirstIntegrable 2 (F ε)) ∧
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (F ε)) (𝓝[>] 0) (𝓝 v)

namespace JointLimV

variable {F G : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ} {v w : ℂ}

theorem add (hF : JointLimV F v) (hG : JointLimV G w) :
    JointLimV (fun ε ℓ => F ε ℓ + G ε ℓ) (v + w) := by
  refine ⟨?_, (hF.2.add hG.2).congr' ?_⟩
  · filter_upwards [hF.1, hG.1] with ε h1 h2
    exact QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add h1 h2
  · filter_upwards [hF.1, hG.1] with ε h1 h2
    exact (jointEnergyFirstIntegral_add h1 h2).symm

theorem mul_left {a : ℝ → ℂ} {a₀ : ℂ} (ha : Tendsto a (𝓝[>] 0) (𝓝 a₀)) (hF : JointLimV F v) :
    JointLimV (fun ε ℓ => a ε * F ε ℓ) (a₀ * v) := by
  refine ⟨?_, (ha.mul hF.2).congr' (Eventually.of_forall fun ε => ?_)⟩
  · filter_upwards [hF.1] with ε h1
    exact jointEnergyFirstIntegrable_const_mul _ h1
  · exact (jointEnergyFirstIntegral_const_mul _ _).symm

theorem const_mul (c : ℂ) (hF : JointLimV F v) : JointLimV (fun ε ℓ => c * F ε ℓ) (c * v) :=
  mul_left tendsto_const_nhds hF

theorem eps_mul (hF : JointLimV F v) : JointLimV (fun ε ℓ => (ε : ℂ) * F ε ℓ) 0 := by
  have ha : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝 0) (𝓝 ((0 : ℝ) : ℂ)) :=
      continuous_ofReal.tendsto 0
    rw [ofReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  simpa only [zero_mul] using mul_left ha hF

theorem congr (hF : JointLimV F v) (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ℓ, F ε ℓ = G ε ℓ) :
    JointLimV G v := by
  have hfun : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε = G ε := h.mono fun ε hε => funext hε
  refine ⟨?_, hF.2.congr' ?_⟩
  · filter_upwards [hF.1, hfun] with ε h1 h2
    rwa [← h2]
  · filter_upwards [hfun] with ε h2
    rw [h2]

theorem of_jointHasLim (h : JointHasLim F) : ∃ v, JointLimV F v := by
  obtain ⟨h1, v, h2⟩ := h
  exact ⟨v, h1, h2⟩

theorem unique (hv : JointLimV F v) (hw : JointLimV F w) : v = w :=
  tendsto_nhds_unique hv.2 hw.2

end JointLimV

/-! ### Parametric data on rows of the `VP` matrix -/

/-- **The parametric data of a piece on rows `σ` of the `VP` class matrix**, with masses `Ms`,
external momenta of `VP` at `(p, p')`, numerator lines `E`, and a lower bound `c` for `V`. -/
noncomputable def rowsData {m : ℕ} (hm : 7 ≤ m) (σ : Fin (m + 1) → Fin 6) (Ms : Fin (m + 1) → ℝ)
    (p p' : Fin 4 → ℝ) (E : Finset (Fin (m + 1)))
    (hcrit : IntNoSubdivergenceRefined 2 E fun i => class5LoopMatrix .VP (σ i)) {c : ℝ}
    (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (castLoopMatrix fun i => class5LoopMatrix .VP (σ i)) z ≠ 0 →
      c ≤ symanzikV (castLoopMatrix fun i => class5LoopMatrix .VP (σ i))
        (fun i => classVPMomenta p p' (σ i)) Ms z) : ParamData where
  m := m
  α := castLoopMatrix fun i => class5LoopMatrix .VP (σ i)
  p := fun i => classVPMomenta p p' (σ i)
  M := Ms
  E := E
  hm := hm
  hcrit := (noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr hcrit
  c := c
  hc := hc
  hV := hV

/-- **A parametric value is the limit of its piece.** -/
theorem jointLimV_of_paramValue {D : ParamData} {F : (Fin 2 → Fin 4 → ℝ) → ℂ} {v : ℂ}
    (h : IsParamValue D F v) :
    JointLimV (fun ε ℓ => F ℓ * ∏ i, (lineDenom D.α D.p D.M ε i ℓ)⁻¹) v := by
  refine ⟨?_, h.tendsto⟩
  obtain ⟨Q, rfl, hB, -⟩ := h
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined Q D.α D.p D.M
    D.hm hε D.hcrit hB

/-- A numerator with the polynomial and refined bounds has a parametric value. -/
theorem exists_paramValue (D : ParamData) {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hpoly : IsLoopPoly 2 4 F)
    (hB : RefinedBound D.α D.E 4 F) : ∃ v, IsParamValue D F v := by
  obtain ⟨Q, rfl⟩ := hpoly.exists_loopQuartic
  exact ⟨_, Q, rfl, hB, rfl⟩

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-- **Covariance of the values of a piece on rows of the `VP` matrix**, between the pairs
`(p, p')` and `(L p, L p')`. -/
theorem conj_rowsData (h : IsSpinLift L S T) {m : ℕ} (hm : 7 ≤ m) (σ : Fin (m + 1) → Fin 6)
    (Ms : Fin (m + 1) → ℝ) (p p' : Fin 4 → ℝ) (E : Finset (Fin (m + 1)))
    (hcrit : IntNoSubdivergenceRefined 2 E fun i => class5LoopMatrix .VP (σ i)) {c : ℝ}
    (hc : 0 < c) (hV hV₂)
    (N N₂ : Fin 4 → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hN : ∀ μ ℓ, S * N₂ μ (loopAct L ℓ) * T = vecAct L (fun ν => N ν ℓ) μ)
    (W W₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hW : ∀ μ i j, IsParamValue (rowsData hm σ Ms p p' E hcrit hc hV) (fun ℓ => N μ ℓ i j)
      (W μ i j))
    (hW₂ : ∀ μ i j, IsParamValue (rowsData hm σ Ms (L *ᵥ p) (L *ᵥ p') E hcrit hc hV₂)
      (fun ℓ => N₂ μ ℓ i j) (W₂ μ i j)) (μ : Fin 4) :
    S * W₂ μ * T = vecAct L W μ :=
  conj_eq_vecAct_of_paramValue (rowsData hm σ Ms p p' E hcrit hc hV) h
    (fun i => classVPMomenta (L *ᵥ p) (L *ᵥ p') (σ i))
    (funext fun i => classVPMomenta_map p p' (σ i)) N N₂ hN W W₂ hW
    (fun μ i j => QED.TwoLoop.ReflCovariance.IsParamValue.exists_integrableOn (hW₂ μ i j)) μ

/-! ### The numerators of the longitudinal pieces -/

/-- The open-line chain with the photon tensor `u_ν w_ρ` (both lowered) at `γ^ν`, `γ^ρ`. -/
noncomputable def longM (P : Params) (p kext k u w : Fin 4 → ℝ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  IsSpinLift.chain (fun ν ρ => ((Minkowski.lower u ν : ℝ) : ℂ) * ((Minkowski.lower w ρ : ℝ) : ℂ))
    (electronNumerator P.m (p + kext - k)) (electronNumerator P.m (p - k)) μ

theorem sum_metric_mul_ofReal (v : Fin 4 → ℝ) (ρ : Fin 4) :
    ∑ c : Fin 4, ((Minkowski.metric ρ c : ℝ) : ℂ) * ((v c : ℝ) : ℂ) =
      ((Minkowski.lower v ρ : ℝ) : ℂ) := by
  simp only [Minkowski.lower, ofReal_sum, ofReal_mul]

theorem bdN_eq_longM (P : Params) (p kext : Fin 4 → ℝ) (μ α β : Fin 4) (k v : Fin 4 → ℝ) :
    bdN P p kext μ α β k v = longM P p kext k k v μ α β := by
  simp only [longM, IsSpinLift.chain, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, bdN, bdON]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ => ?_
  rw [← sum_metric_mul_ofReal v l2]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l3 _ => ?_
  ring

theorem dbN_eq_longM (P : Params) (p kext : Fin 4 → ℝ) (μ α β : Fin 4) (k v : Fin 4 → ℝ) :
    dbN P p kext μ α β k v = longM P p kext k v k μ α β := by
  simp only [longM, IsSpinLift.chain, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, dbN, bdON]
  refine Finset.sum_congr rfl fun l0 _ => Finset.sum_congr rfl fun l2 _ => ?_
  rw [← sum_metric_mul_ofReal v l0]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l5 _ => ?_
  ring

theorem tensorAct_lowerPair (h : IsSpinLift L S T) (u w : Fin 4 → ℝ) :
    IsSpinLift.tensorAct L (fun ν ρ => ((Minkowski.lower (L *ᵥ u) ν : ℝ) : ℂ) *
      ((Minkowski.lower (L *ᵥ w) ρ : ℝ) : ℂ)) =
      fun ν ρ => ((Minkowski.lower u ν : ℝ) : ℂ) * ((Minkowski.lower w ρ : ℝ) : ℂ) := by
  funext ν' ρ'
  rw [← h.lower_mulVec_contract u ν', ← h.lower_mulVec_contract w ρ']
  simp only [IsSpinLift.tensorAct, ofReal_sum, ofReal_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Covariance of the longitudinal numerators.** -/
theorem longM_map (h : IsSpinLift L S T) (P : Params) (p kext k u w : Fin 4 → ℝ) (μ : Fin 4) :
    S * longM P (L *ᵥ p) (L *ᵥ kext) (L *ᵥ k) (L *ᵥ u) (L *ᵥ w) μ * T =
      vecAct L (fun ν => longM P p kext k u w ν) μ := by
  have e1 : L *ᵥ p + L *ᵥ kext - L *ᵥ k = L *ᵥ (p + kext - k) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_add]
  have e2 : L *ᵥ p - L *ᵥ k = L *ᵥ (p - k) := by rw [Matrix.mulVec_sub]
  simp only [longM, h.mul_chain_mul, e1, e2, h.mul_electronNumerator_mul, tensorAct_lowerPair h]

/-! ### Bounds of the longitudinal numerators -/

section Bounds

variable (P : Params) {m : ℕ} (σ : Fin (m + 1) → Fin 6) (p kext : Fin 4 → ℝ) (μ α β : Fin 4)
  (eV : Fin (m + 1)) {V : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ}

include σ in
/-- The bounds of the numerator of a longitudinal piece of `repBD`. -/
theorem bdPiece_bounds (hV : IsLoopAffine V) (h0 : σ 0 = 0) (h1 : σ 1 = 1) (h2 : σ 2 = 4)
    (hVe : ∀ ℓ, V ℓ = classLineVP p (p + kext) (σ eV) ℓ) (h10 : (1 : Fin (m + 1)) ≠ 0)
    (h2E : (2 : Fin (m + 1)) ∉ ({1, 0} : Finset (Fin (m + 1))))
    (hVE : eV ∉ ({1, 0} : Finset (Fin (m + 1)))) (h2V : (2 : Fin (m + 1)) ≠ eV) :
    IsLoopPoly 2 4 (fun ℓ => bdN P p kext μ α β (-ℓ 1) (V ℓ)) ∧
      RefinedBound (castLoopMatrix fun i => class5LoopMatrix .VP (σ i)) ({1, 0} ∪ {2} ∪ {eV}) 4
        (fun ℓ => bdN P p kext μ α β (-ℓ 1) (V ℓ)) := by
  set al := castLoopMatrix fun i => class5LoopMatrix .VP (σ i)
  set pp : Fin (m + 1) → Fin 4 → ℝ := fun i => classVPMomenta p (p + kext) (σ i)
  have hlm : ∀ e ℓ, QED.Integration.TwoLoop.lineMomentum al pp e ℓ =
      classLineVP p (p + kext) (σ e) ℓ := fun _ _ => rfl
  have r0 : ∀ ℓ, classLineVP p (p + kext) 0 ℓ = p - -ℓ 1 := fun ℓ => (classLineVP_rows _ _ ℓ).1
  have r1 : ∀ ℓ, classLineVP p (p + kext) 1 ℓ = p + kext - -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.1
  have r4 : ∀ ℓ, classLineVP p (p + kext) 4 ℓ = -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.2.2.2.1
  refine ⟨?_, ?_⟩
  · unfold bdN bdON
    exact isLoopPoly_contract P.m isLoopAffine_neg_one hV
      (IsLoopAffine.const_sub' isLoopAffine_neg_one (p + kext))
      (IsLoopAffine.const_sub' isLoopAffine_neg_one p)
      Dirac.gamma Dirac.gamma (Dirac.gamma μ) α β
  · unfold bdN bdON
    refine refinedBound_contract' al pp h2E hVE h2V (fun ℓ => -ℓ 1) V
      (fun ℓ => by rw [hlm, h2, r4]) (fun ℓ => by rw [hlm, hVe]) _ fun l0 l2 => ?_
    exact refinedBound_openNum al pp h10 P.m (fun ℓ => p + kext - -ℓ 1) (fun ℓ => p - -ℓ 1)
      (fun ℓ => by rw [hlm, h1, r1]) (fun ℓ => by rw [hlm, h0, r0]) _ _ _ α β

include σ in
/-- The bounds of the numerator of a longitudinal piece of `repDB`. -/
theorem dbPiece_bounds (hV : IsLoopAffine V) (h0 : σ 0 = 0) (h1 : σ 1 = 1) (h2 : σ 2 = 4)
    (hVe : ∀ ℓ, V ℓ = classLineVP p (p + kext) (σ eV) ℓ) (h10 : (1 : Fin (m + 1)) ≠ 0)
    (h2E : (2 : Fin (m + 1)) ∉ ({1, 0} : Finset (Fin (m + 1))))
    (hVE : eV ∉ ({1, 0} : Finset (Fin (m + 1)))) (h2V : (2 : Fin (m + 1)) ≠ eV) :
    IsLoopPoly 2 4 (fun ℓ => dbN P p kext μ α β (-ℓ 1) (V ℓ)) ∧
      RefinedBound (castLoopMatrix fun i => class5LoopMatrix .VP (σ i)) ({1, 0} ∪ {2} ∪ {eV}) 4
        (fun ℓ => dbN P p kext μ α β (-ℓ 1) (V ℓ)) := by
  set al := castLoopMatrix fun i => class5LoopMatrix .VP (σ i)
  set pp : Fin (m + 1) → Fin 4 → ℝ := fun i => classVPMomenta p (p + kext) (σ i)
  have hlm : ∀ e ℓ, QED.Integration.TwoLoop.lineMomentum al pp e ℓ =
      classLineVP p (p + kext) (σ e) ℓ := fun _ _ => rfl
  have r0 : ∀ ℓ, classLineVP p (p + kext) 0 ℓ = p - -ℓ 1 := fun ℓ => (classLineVP_rows _ _ ℓ).1
  have r1 : ∀ ℓ, classLineVP p (p + kext) 1 ℓ = p + kext - -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.1
  have r4 : ∀ ℓ, classLineVP p (p + kext) 4 ℓ = -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.2.2.2.1
  simp only [dbN_eq_contract]
  refine ⟨?_, ?_⟩
  · refine isLoopPoly_contract' isLoopAffine_neg_one hV _ fun a b => ?_
    unfold bdON
    have hm : IsLoopPolyMat 2 (0 + 1 + 0 + 1 + 0) fun ℓ : Fin 2 → Fin 4 → ℝ =>
        Dirac.gamma a * electronNumerator P.m (p + kext - -ℓ 1) * Dirac.gamma μ *
          electronNumerator P.m (p - -ℓ 1) * Dirac.gamma b :=
      ((((IsLoopPolyMat.const _).mul ((IsLoopAffine.const_sub' isLoopAffine_neg_one
        (p + kext)).isLoopPolyMat_electronNumerator P.m)).mul (IsLoopPolyMat.const _)).mul
          ((IsLoopAffine.const_sub' isLoopAffine_neg_one p).isLoopPolyMat_electronNumerator
            P.m)).mul (IsLoopPolyMat.const _)
    exact hm α β
  · refine refinedBound_contract' al pp h2E hVE h2V (fun ℓ => -ℓ 1) V
      (fun ℓ => by rw [hlm, h2, r4]) (fun ℓ => by rw [hlm, hVe])
      (fun ℓ a b => bdON P p kext (-ℓ 1) μ b a α β) fun a b => ?_
    unfold bdON
    exact refinedBound_openNum al pp h10 P.m (fun ℓ => p + kext - -ℓ 1) (fun ℓ => p - -ℓ 1)
      (fun ℓ => by rw [hlm, h1, r1]) (fun ℓ => by rw [hlm, h0, r0]) _ _ _ α β

end Bounds

end QED.ChainProof.HCSide

end
