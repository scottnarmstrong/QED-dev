/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LimitCovarianceClasses
public import QED.TwoLoop.ClassLimitVP
import Mathlib.Tactic.Ring

/-!
# Covariance of the `ε → 0⁺` limit of the vacuum-polarization class

Part of obligation O2-20 (`docs/TWO-LOOP-DERIVATION.md`, section 5.4). The numerator of `VP`
(`QED.TwoLoop.Bridge.vpNumer`) is a vertex chain (`QED.TwoLoop.LimitCovariance.IsSpinLift.chain`)
of the open line whose photon tensor contracts the two Pauli–Villars photon factors with the
fermion-loop trace `Tr[γ^σ (M - q̸) γ^τ (M - (q + k)̸)]` (`vpNumer_eq`), resp. with
`Tr[γ^σ γ^τ]` for the coefficient of `M²` (`vpNumer2_eq`). Under `ℓ ↦ L ℓ` the trace transforms
on both indices (`traceT_conj`), and the photon tensor then transforms back (`tensorAct_lowered`),
so the matrices of the five ε-independent piece numerators are covariant (`vpPieceM_cov`). With
the limit of `QED.TwoLoop.ClassLimit.tendsto_contractionValue₂_VP` as a sum of five parametric
values, the limit vertex of `VP` is little-group covariant (`isLittleGroupCovariant_classLimitV_VP`).
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real

namespace QED.TwoLoop.LimitCovariance

open QED.Dirac QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit
open QED.Integration.TwoLoop (LoopQuartic RefinedBound castLoopMatrix lineDenom lineMomentum)

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-! ### Traces and photon tensors -/

/-- `Tr[γ^a A γ^b B]`. -/
noncomputable def traceT (A B : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) : ℂ :=
  (gamma a * A * gamma b * B).trace

/-- The action of `L` on both (upper) indices of a tensor. -/
noncomputable def upperAct (L : Matrix (Fin 4) (Fin 4) ℝ) (X : Fin 4 → Fin 4 → ℂ)
    (a b : Fin 4) : ℂ :=
  ∑ a', ∑ b', ((L a a' : ℝ) : ℂ) * ((L b b' : ℝ) : ℂ) * X a' b'

theorem electronNumerator_mulVec (h : IsSpinLift L S T) (m : ℝ) (u : Fin 4 → ℝ) :
    electronNumerator m (L *ᵥ u) = T * electronNumerator m u * S := by
  rw [← h.mul_electronNumerator_mul m u]
  simp only [← Matrix.mul_assoc]
  rw [h.mul_eq_one', Matrix.one_mul, Matrix.mul_assoc, h.mul_eq_one', Matrix.mul_one]

theorem traceT_conj (h : IsSpinLift L S T) (A B : Matrix (Fin 4) (Fin 4) ℂ) (a b : Fin 4) :
    traceT (T * A * S) (T * B * S) a b = upperAct L (traceT A B) a b := by
  have e : gamma a * (T * A * S) * gamma b * (T * B * S) =
      (gamma a * (T * A * S) * gamma b * (T * B)) * S := by
    simp only [Matrix.mul_assoc]
  rw [traceT, e, Matrix.trace_mul_comm]
  have e2 : S * (gamma a * (T * A * S) * gamma b * (T * B)) =
      (S * gamma a * T) * A * (S * gamma b * T) * B := by
    simp only [Matrix.mul_assoc]
  rw [e2, h.mul_gamma_mul, h.mul_gamma_mul]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, upperAct, traceT]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The Pauli–Villars photon factor `g_{xy} (Λ² - m_γ²)`. -/
noncomputable def pvG (P : Params) (x y : Fin 4) : ℂ :=
  ((Minkowski.metric x y * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)

theorem pvG_pair (h : IsSpinLift L S T) (P : Params) (u v : Fin 4) :
    ∑ x, ∑ y, pvG P x y * (((L x u : ℝ) : ℂ) * ((L y v : ℝ) : ℂ)) = pvG P u v := by
  have hr := h.lorentz_right u v
  have hc : ((∑ a, ∑ b, L a u * L b v * Minkowski.metric a b : ℝ) : ℂ) =
      ((Minkowski.metric u v : ℝ) : ℂ) := by rw [hr]
  simp only [pvG, ofReal_mul, ofReal_sum] at hc ⊢
  simp only [← hc, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- The photon tensor of `VP`: the two photon factors contracted with the loop tensor `X`. -/
noncomputable def lowered (P : Params) (X : Fin 4 → Fin 4 → ℂ) (ν ρ : Fin 4) : ℂ :=
  ∑ a, ∑ b, pvG P ν a * pvG P ρ b * X a b

theorem tensorAct_lowered (h : IsSpinLift L S T) (P : Params) (X : Fin 4 → Fin 4 → ℂ) :
    IsSpinLift.tensorAct L (lowered P (upperAct L X)) = lowered P X := by
  funext ν' ρ'
  simp only [IsSpinLift.tensorAct, lowered, upperAct, Finset.sum_mul, Finset.mul_sum]
  rw [sum_out4]
  refine (Finset.sum_congr rfl fun a' _ => sum_out4 _ _).trans ?_
  have e : ∀ a' b', pvG P ν' a' * pvG P ρ' b' * X a' b' =
      ∑ x, ∑ y, ∑ x', ∑ y', pvG P x y * (((L x ν' : ℝ) : ℂ) * ((L y a' : ℝ) : ℂ)) *
        (pvG P x' y' * (((L x' ρ' : ℝ) : ℂ) * ((L y' b' : ℝ) : ℂ))) * X a' b' := by
    intro a' b'
    rw [← pvG_pair h P ν' a', ← pvG_pair h P ρ' b']
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [sum_block2]
  simp only [e]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ =>
    Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring


/-! ### The chain form of the `VP` numerators -/

/-- The `VP` numerator matrix with loop tensor `X`, open-line momentum `p`, external photon
momentum `kext` and internal photon momentum `k`. -/
noncomputable def vpChainM (P : Params) (p kext k : Fin 4 → ℝ) (X : Fin 4 → Fin 4 → ℂ)
    (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  IsSpinLift.chain (lowered P X) (electronNumerator P.m (p + kext - k))
    (electronNumerator P.m (p - k)) μ

theorem vpNumer_eq (P : Params) (M : ℝ) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (q k : Fin 4 → ℝ) :
    vpNumer P M p kext α β μ q k = (I * P.e) ^ 5 * (1 / I) ^ 6 *
      vpChainM P p kext k (traceT (electronNumerator M q) (electronNumerator M (q + k))) μ α β := by
  simp only [vpNumer, vpChainM, IsSpinLift.chain, lowered, outerNum, loopTrace, traceT, pvG,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem vpNumer2_eq (P : Params) (p kext : Fin 4 → ℝ) (α β μ : Fin 4) (k : Fin 4 → ℝ) :
    vpNumer2 P p kext α β μ k = (I * P.e) ^ 5 * (1 / I) ^ 6 *
      vpChainM P p kext k (traceT 1 1) μ α β := by
  simp only [vpNumer2, vpChainM, IsSpinLift.chain, lowered, outerNum, traceT, Matrix.mul_one, pvG,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem vpChainM_cov (h : IsSpinLift L S T) (P : Params) {p kext : Fin 4 → ℝ}
    (hp : L *ᵥ p = p) (hk : L *ᵥ kext = kext) (k : Fin 4 → ℝ) (X : Fin 4 → Fin 4 → ℂ)
    (μ : Fin 4) :
    S * vpChainM P p kext (L *ᵥ k) (upperAct L X) μ * T =
      vecAct L (vpChainM P p kext k X) μ := by
  have e1 : p + kext - L *ᵥ k = L *ᵥ (p + kext - k) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_add, hp, hk]
  have e2 : p - L *ᵥ k = L *ᵥ (p - k) := by rw [Matrix.mulVec_sub, hp]
  simp only [vpChainM, h.mul_chain_mul, tensorAct_lowered h, e1, e2, h.mul_electronNumerator_mul]
  rfl

/-! ### The piece numerators -/

/-- The matrix of `E₀` at the on-shell pair `(p', p)`. -/
noncomputable def vpE0M (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => vpE0 P (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
    (fun _ => μ) ℓ

/-- The matrix of `E₂` at the on-shell pair `(p', p)`. -/
noncomputable def vpE2M (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => vpE2 P (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β)
    (fun _ => μ) ℓ

theorem vpE0M_eq (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpE0M P p p' μ ℓ = ((I * P.e) ^ 5 * (1 / I) ^ 6) • vpChainM P p (p' - p) (-ℓ 1)
      (traceT (electronNumerator 0 (ℓ 0)) (electronNumerator 0 (ℓ 0 + -ℓ 1))) μ := by
  ext α β
  simp only [vpE0M, vpE0, vpNumerator, Matrix.of_apply, vpNumer_eq, Matrix.smul_apply,
    smul_eq_mul]

theorem vpE2M_eq (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpE2M P p p' μ ℓ = ((I * P.e) ^ 5 * (1 / I) ^ 6) •
      vpChainM P p (p' - p) (-ℓ 1) (traceT 1 1) μ := by
  ext α β
  simp only [vpE2M, vpE2, Matrix.of_apply, vpNumer2_eq, Matrix.smul_apply, smul_eq_mul]

theorem neg_loopAct_one (ℓ : Fin 2 → Fin 4 → ℝ) : -loopAct L ℓ 1 = L *ᵥ (-ℓ 1) := by
  simp [loopAct, Matrix.mulVec_neg]

theorem vpE0M_cov (h : IsSpinLift L S T) (P : Params) {p p' : Fin 4 → ℝ} (hp : L *ᵥ p = p)
    (hp' : L *ᵥ p' = p') (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * vpE0M P p p' μ (loopAct L ℓ) * T = vecAct L (fun ν => vpE0M P p p' ν ℓ) μ := by
  have hk : L *ᵥ (p' - p) = p' - p := by rw [Matrix.mulVec_sub, hp, hp']
  have e : loopAct L ℓ 0 + -loopAct L ℓ 1 = L *ᵥ (ℓ 0 + -ℓ 1) := by
    simp [loopAct, Matrix.mulVec_add, Matrix.mulVec_neg]
  have hX : traceT (electronNumerator 0 (loopAct L ℓ 0))
      (electronNumerator 0 (loopAct L ℓ 0 + -loopAct L ℓ 1)) =
      upperAct L (traceT (electronNumerator 0 (ℓ 0)) (electronNumerator 0 (ℓ 0 + -ℓ 1))) := by
    funext a b
    rw [e, show loopAct L ℓ 0 = L *ᵥ ℓ 0 from rfl, electronNumerator_mulVec h,
      electronNumerator_mulVec h, traceT_conj h]
  simp only [vpE0M_eq]
  rw [hX, neg_loopAct_one]
  simp only [Matrix.mul_smul, Matrix.smul_mul, vpChainM_cov h P hp hk]
  rw [vecAct_smul]

theorem vpE2M_cov (h : IsSpinLift L S T) (P : Params) {p p' : Fin 4 → ℝ} (hp : L *ᵥ p = p)
    (hp' : L *ᵥ p' = p') (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * vpE2M P p p' μ (loopAct L ℓ) * T = vecAct L (fun ν => vpE2M P p p' ν ℓ) μ := by
  have hk : L *ᵥ (p' - p) = p' - p := by rw [Matrix.mulVec_sub, hp, hp']
  have hX : traceT 1 1 = upperAct L (traceT 1 1) := by
    funext a b
    rw [← traceT_conj h, Matrix.mul_one, h.mul_eq_one']
  have hX' : vpChainM P p (p' - p) (-loopAct L ℓ 1) (traceT 1 1) =
      vpChainM P p (p' - p) (L *ᵥ (-ℓ 1)) (upperAct L (traceT 1 1)) := by
    rw [neg_loopAct_one, ← hX]
  simp only [vpE2M_eq, hX', Matrix.mul_smul, Matrix.smul_mul, vpChainM_cov h P hp hk]
  rw [vecAct_smul]

theorem lineDenom_zero_loopAct (h : IsSpinLift L S T) {m : ℕ} (α : Fin (m + 1) → Fin 2 → ℝ)
    (q : Fin (m + 1) → Fin 4 → ℝ) (M : Fin (m + 1) → ℝ) (i : Fin (m + 1))
    (hq : L *ᵥ q i = q i) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom α q M 0 i (loopAct L ℓ) = lineDenom α q M 0 i ℓ := by
  simp only [lineDenom, lineMomentum_loopAct α q i hq, h.dot_mulVec]

theorem mulVec_classVPMomenta {p p' : Fin 4 → ℝ} (hp : L *ᵥ p = p) (hp' : L *ᵥ p' = p')
    (i : Fin 6) : L *ᵥ QED.Integration.TwoLoop.classVPMomenta p p' i =
      QED.Integration.TwoLoop.classVPMomenta p p' i := by
  fin_cases i <;> simp [QED.Integration.TwoLoop.classVPMomenta, hp, hp']

/-- The matrix of the `j`-th piece numerator at the on-shell pair `(p', p)`. -/
noncomputable def vpPieceM (P : Params) (p p' : Fin 4 → ℝ) (j : Fin 5) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => vpPieceNumer P (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α)
    (fun _ => β) (fun _ => μ) j ℓ

/-- The coefficient of `E₀` in the `j`-th piece. -/
noncomputable def vpCoeff0 (P : Params) (j : Fin 5) : ℂ :=
  if j = 3 ∨ j = 4 then 0 else twoLoopNorm * vpBubbleCoeff P

/-- The coefficient of `E₂` in the `j`-th piece. -/
noncomputable def vpCoeff2 (P : Params) (p p' : Fin 4 → ℝ) (j : Fin 5) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ℂ :=
  if j = 3 then
    -(twoLoopNorm * vpBubbleCoeff P * lineDenom (castLoopMatrix (vpShapeMatrix 3))
      (vpShapeMomenta 3 p p') (vpShapeMasses P 3) 0 8 ℓ)
  else if j = 4 then
    -(twoLoopNorm * vpBubbleCoeff P * lineDenom (castLoopMatrix (vpShapeMatrix 3))
      (vpShapeMomenta 3 p p') (vpShapeMasses P 3) 0 3 ℓ)
  else twoLoopNorm * vpBubbleCoeff P * ((P.m ^ 2 : ℝ) : ℂ)

theorem vpPieceM_eq (P : Params) (p p' : Fin 4 → ℝ) (j : Fin 5) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpPieceM P p p' j μ ℓ = vpCoeff0 P j • vpE0M P p p' μ ℓ + vpCoeff2 P p p' j ℓ • vpE2M P p p' μ ℓ := by
  ext α β
  simp only [vpPieceM, vpE0M, vpE2M, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, vpPieceNumer, vpCoeff0, vpCoeff2]
  fin_cases j <;> simp <;> ring

theorem vpCoeff2_loopAct (h : IsSpinLift L S T) (P : Params) {p p' : Fin 4 → ℝ}
    (hp : L *ᵥ p = p) (hp' : L *ᵥ p' = p') (j : Fin 5) (ℓ : Fin 2 → Fin 4 → ℝ) :
    vpCoeff2 P p p' j (loopAct L ℓ) = vpCoeff2 P p p' j ℓ := by
  have hq : ∀ i, L *ᵥ vpShapeMomenta 3 p p' i = vpShapeMomenta 3 p p' i := fun i =>
    mulVec_classVPMomenta hp hp' _
  simp only [vpCoeff2, lineDenom_zero_loopAct h _ _ _ _ (hq _) ℓ]

/-- **Covariance of the piece numerators of `VP`.** -/
theorem vpPieceM_cov (h : IsSpinLift L S T) (P : Params) {p p' : Fin 4 → ℝ} (hp : L *ᵥ p = p)
    (hp' : L *ᵥ p' = p') (j : Fin 5) (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * vpPieceM P p p' j μ (loopAct L ℓ) * T = vecAct L (fun ν => vpPieceM P p p' j ν ℓ) μ := by
  simp only [vpPieceM_eq, vpCoeff2_loopAct h P hp hp', Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, vpE0M_cov h P hp hp', vpE2M_cov h P hp hp']
  rw [vecAct_add, vecAct_smul, vecAct_smul]


/-! ### The limit of `VP` -/

/-- The parametric data of the `j`-th piece of `VP`. -/
noncomputable def vpData (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hm : 0 < P.m)
    (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (j : Fin 5) : ParamData where
  m := 9
  α := castLoopMatrix (vpShapeMatrix (vpPieceShape j))
  p := vpShapeMomenta (vpPieceShape j) p p'
  M := vpShapeMasses P (vpPieceShape j)
  E := vpPieceLines j
  hm := by norm_num
  hcrit := noSubdivergenceRefined_vpPiece j
  c := 3 / 4 * min (P.m ^ 2) (min P.mγ P.Λ ^ 2)
  hc := mul_pos (by norm_num) (lt_min (by positivity) (pow_pos (lt_min hmγ hΛ) 2))
  hV := fun _ hz hz1 hU => symanzikV_vpShape_ge_min P hmγ hΛ h₁ h₂ _ hp hp' hq hz hz1 hU

/-- **Covariance of the limit of `VP`.** -/
theorem isLittleGroupCovariant_classLimitV_VP (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) :
    IsLittleGroupCovariant p' p (classLimitV .VP P p p') := by
  have h₁ : P.m ^ 2 ≤ P.M₁ ^ 2 := pow_le_pow_left₀ hm.le hM₁ 2
  have h₂ : P.m ^ 2 ≤ P.M₂ ^ 2 := pow_le_pow_left₀ hm.le hM₂ 2
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hVP := fun (μ α β : Fin 4) => tendsto_contractionValue₂_VP P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂
    (pOut := fun _ => p') (pIn := fun _ => p) (kIn := fun _ => p' - p) hmom hp hp' hq
    (fun _ => α) (fun _ => β) (fun _ => μ)
  choose Q hQ _ hT using hVP
  set D := vpData P hmγ hΛ hm h₁ h₂ hp hp' hq with hD
  set W : Fin 5 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun j μ => Matrix.of fun α β =>
    -((π : ℂ) ^ 4) * ∫ x in QED.Integration.Feynman.simplexSet 9, paramIntegrand (Q μ α β j)
      (castLoopMatrix (vpShapeMatrix (vpPieceShape j)))
      (vpShapeMomenta (vpPieceShape j) p p') (vpShapeMasses P (vpPieceShape j)) 0 x with hW
  have hlim : classLimitV .VP P p p' = fun μ => ∑ j ∈ Finset.univ, (1 : ℂ) • W j μ := by
    funext μ
    ext α β
    simp only [classLimitV, Matrix.of_apply, (hT μ α β).limUnder_eq, one_smul, Matrix.sum_apply,
      hW]
  rw [hlim]
  refine VertexCovariance.isLittleGroupCovariant_sum _ _ fun j _ => ?_
  refine isLittleGroupCovariant_of_paramValue (D j)
    (fun L S T _ hLp hLp' i => mulVec_classVPMomenta hLp hLp' _)
    (fun μ ℓ => vpPieceM P p p' j μ ℓ) (fun L S T h hLp hLp' μ ℓ => vpPieceM_cov h P hLp hLp' j μ ℓ)
    (W j) fun μ α β => ?_
  have hF : (fun ℓ => vpPieceM P p p' j μ ℓ α β) = vpPieceNumer P (fun _ => p') (fun _ => p)
      (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ) j := by
    funext ℓ
    simp only [vpPieceM, Matrix.of_apply]
  rw [hF]
  exact ⟨Q μ α β j, hQ μ α β j, refinedBound_vpPieceNumer P _ _ _ _ _ _ j, rfl⟩

end QED.TwoLoop.LimitCovariance

end
