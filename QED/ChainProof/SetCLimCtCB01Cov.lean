/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLimCtCB01Lim
public import QED.TwoLoop.ReflCovarianceClasses

/-!
# Set (c): covariance of the limits of the classes `CB0`, `CB1`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The limit of
`CB0`, `CB1` is `-(∑ⱼ vAⱼ + c ∑ⱼ vBⱼ)` with parametric values `vA`, `vB` of the pieces
(`QED/ChainProof/SetCLimCtCB01Lim.lean`). Under a spinor-lifted `L` moving the external momenta,
each piece is covariant by `QED.TwoLoop.ReflCovariance.conj_eq_vecAct_of_paramValue`, since its
numerator is:

* `cbNumM_eq`, `cbNum2M_eq`: the numerators of the bubble vertex are vertex chains
  (`QED.TwoLoop.LimitCovariance.IsSpinLift.chain`) of the open-line matrices with the photon
  tensor of the bubble, as for `VP`;
* `cbNumM_map`, `cbNum2M_map`: so they are covariant when the open-line matrices are
  (`cbXa_map`: `A` and `Y` of the transformed momenta);
* `cbPieceM_map`: the pieces, whose coefficients are invariant
  (`QED.TwoLoop.ReflCovariance.vpCoeff2_map`).

* **`conj_cbLim`**: `S Z^μ T = L^μ_ν Y^ν` for the limits `Y` at `(p', p)` and `Z` at `(Lp', Lp)`;
* `cb_char`: every limit of the class value has this form.
-/

@[expose] public section

open Complex Matrix Filter Topology
open scoped Real

namespace QED.ChainProof.SetCPauli.CB01

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.ClassLimit QED.Dirac
open QED.TwoLoop.LimitCovariance QED.TwoLoop.ReflCovariance
open QED.ChainProof.SetCPauli (mergeY mergeC)
open QED.Integration.TwoLoop (lineDenom castLoopMatrix)

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-! ### The numerators as vertex chains -/

/-- The matrix of `cbNum` in the external spinor indices. -/
noncomputable def cbNumM (P : Params) (M : ℝ) (X1 X0 : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => cbNum P M X1 X0 α β μ ℓ

/-- The matrix of `cbNum2` in the external spinor indices. -/
noncomputable def cbNum2M (P : Params) (X1 X0 : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => cbNum2 P X1 X0 α β μ

theorem cbNumM_eq (P : Params) (M : ℝ) (X1 X0 : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbNumM P M X1 X0 μ ℓ = ((I * P.e) ^ 5 * (1 / I) ^ 6) • IsSpinLift.chain
      (lowered P (traceT (electronNumerator M (ℓ 0)) (electronNumerator M (ℓ 0 + -ℓ 1)))) X1 X0
        μ := by
  ext α β
  simp only [cbNumM, cbNum, Matrix.of_apply, IsSpinLift.chain, lowered, loopTrace, traceT, pvG,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem cbNum2M_eq (P : Params) (X1 X0 : Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    cbNum2M P X1 X0 μ = ((I * P.e) ^ 5 * (1 / I) ^ 6) •
      IsSpinLift.chain (lowered P (traceT 1 1)) X1 X0 μ := by
  ext α β
  simp only [cbNum2M, cbNum2, Matrix.of_apply, IsSpinLift.chain, lowered, traceT, pvG,
    Matrix.mul_one, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/-! ### Covariance of the numerators -/

/-- **Covariance of `cbNum`** for covariant open-line matrices. -/
theorem cbNumM_map (h : IsSpinLift L S T) (P : Params) (M : ℝ)
    {X1 X0 Y1 Y0 : Matrix (Fin 4) (Fin 4) ℂ} (h1 : S * Y1 * T = X1) (h0 : S * Y0 * T = X0)
    (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * cbNumM P M Y1 Y0 μ (loopAct L ℓ) * T = vecAct L (fun ν => cbNumM P M X1 X0 ν ℓ) μ := by
  have e : loopAct L ℓ 0 + -loopAct L ℓ 1 = L *ᵥ (ℓ 0 + -ℓ 1) := by
    simp [loopAct, Matrix.mulVec_add, Matrix.mulVec_neg]
  have hX : traceT (electronNumerator M (loopAct L ℓ 0))
      (electronNumerator M (loopAct L ℓ 0 + -loopAct L ℓ 1)) =
      upperAct L (traceT (electronNumerator M (ℓ 0)) (electronNumerator M (ℓ 0 + -ℓ 1))) := by
    funext a b
    rw [e, show loopAct L ℓ 0 = L *ᵥ ℓ 0 from rfl, electronNumerator_mulVec h,
      electronNumerator_mulVec h, traceT_conj h]
  simp only [cbNumM_eq]
  rw [hX]
  simp only [Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul, tensorAct_lowered h, h1, h0]
  rw [vecAct_smul]

/-- **Covariance of `cbNum2`** for covariant open-line matrices. -/
theorem cbNum2M_map (h : IsSpinLift L S T) (P : Params) {X1 X0 Y1 Y0 : Matrix (Fin 4) (Fin 4) ℂ}
    (h1 : S * Y1 * T = X1) (h0 : S * Y0 * T = X0) (μ : Fin 4) :
    S * cbNum2M P Y1 Y0 μ * T = vecAct L (fun ν => cbNum2M P X1 X0 ν) μ := by
  have hX : traceT 1 1 = upperAct L (traceT 1 1) := by
    funext a b
    rw [← traceT_conj h, Matrix.mul_one, h.mul_eq_one']
  have hT : IsSpinLift.tensorAct L (lowered P (traceT 1 1)) = lowered P (traceT 1 1) := by
    conv_lhs => rw [hX]
    exact tensorAct_lowered h P _
  simp only [cbNum2M_eq, Matrix.mul_smul, Matrix.smul_mul, h.mul_chain_mul, hT, h1, h0]
  rw [vecAct_smul]

theorem cbMom_map (p' p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (i : Fin 2) :
    cbMom (L *ᵥ p') (L *ᵥ p) (loopAct L ℓ) i = L *ᵥ cbMom p' p ℓ i := by
  fin_cases i <;> simp [cbMom, loopAct, Matrix.mulVec_add]

theorem mergeY_map (h : IsSpinLift L S T) (m δ₂ δm : ℝ) (u : Fin 4 → ℝ) :
    S * mergeY m δ₂ δm (L *ᵥ u) * T = mergeY m δ₂ δm u := by
  simp only [mergeY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    h.mul_electronNumerator_mul, Matrix.mul_one, h.mul_eq_one]

theorem cbXa_map (h : IsSpinLift L S T) (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) (i : Fin 2) :
    S * cbXa P d (L *ᵥ p') (L *ᵥ p) (loopAct L ℓ) i * T = cbXa P d p' p ℓ i := by
  unfold cbXa
  rw [cbMom_map]
  split_ifs
  · exact mergeY_map h _ _ _ _
  · exact h.mul_electronNumerator_mul _ _

theorem cbEa0M_map (h : IsSpinLift L S T) (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * Matrix.of (fun α β => cbEa0 P d (L *ᵥ p') (L *ᵥ p) α β μ (loopAct L ℓ)) * T =
      vecAct L (fun ν => Matrix.of fun α β => cbEa0 P d p' p α β ν ℓ) μ :=
  cbNumM_map h P 0 (cbXa_map h P d p' p ℓ 1) (cbXa_map h P d p' p ℓ 0) μ ℓ

theorem cbEa2M_map (h : IsSpinLift L S T) (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ)
    (μ : Fin 4) (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * Matrix.of (fun α β => cbEa2 P d (L *ᵥ p') (L *ᵥ p) α β μ (loopAct L ℓ)) * T =
      vecAct L (fun ν => Matrix.of fun α β => cbEa2 P d p' p α β ν ℓ) μ :=
  cbNum2M_map h P (cbXa_map h P d p' p ℓ 1) (cbXa_map h P d p' p ℓ 0) μ

theorem cbEv0M_map (h : IsSpinLift L S T) (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * Matrix.of (fun α β => cbEv0 P (L *ᵥ p') (L *ᵥ p) α β μ (loopAct L ℓ)) * T =
      vecAct L (fun ν => Matrix.of fun α β => cbEv0 P p' p α β ν ℓ) μ :=
  cbNumM_map h P 0 (by rw [cbMom_map]; exact h.mul_electronNumerator_mul _ _)
    (by rw [cbMom_map]; exact h.mul_electronNumerator_mul _ _) μ ℓ

theorem cbEv2M_map (h : IsSpinLift L S T) (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * Matrix.of (fun α β => cbEv2 P (L *ᵥ p') (L *ᵥ p) α β μ (loopAct L ℓ)) * T =
      vecAct L (fun ν => Matrix.of fun α β => cbEv2 P p' p α β ν ℓ) μ :=
  cbNum2M_map h P (by rw [cbMom_map]; exact h.mul_electronNumerator_mul _ _)
    (by rw [cbMom_map]; exact h.mul_electronNumerator_mul _ _) μ

/-- **Covariance of the pieces** of covariant numerator pairs. -/
theorem cbPieceM_map (h : IsSpinLift L S T) (P : Params) (p' p : Fin 4 → ℝ) (j : Fin 5)
    (F0 F2 : (Fin 4 → ℝ) → (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ)
    (h0 : ∀ μ ℓ, S * Matrix.of (fun α β => F0 (L *ᵥ p') (L *ᵥ p) α β μ (loopAct L ℓ)) * T =
      vecAct L (fun ν => Matrix.of fun α β => F0 p' p α β ν ℓ) μ)
    (h2 : ∀ μ ℓ, S * Matrix.of (fun α β => F2 (L *ᵥ p') (L *ᵥ p) α β μ (loopAct L ℓ)) * T =
      vecAct L (fun ν => Matrix.of fun α β => F2 p' p α β ν ℓ) μ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * Matrix.of (fun α β => cbPiece P (L *ᵥ p) (L *ᵥ p') (F0 (L *ᵥ p') (L *ᵥ p) α β μ)
        (F2 (L *ᵥ p') (L *ᵥ p) α β μ) j (loopAct L ℓ)) * T =
      vecAct L (fun ν => Matrix.of fun α β => cbPiece P p p' (F0 p' p α β ν) (F2 p' p α β ν) j ℓ)
        μ := by
  have e : ∀ (q q' : Fin 4 → ℝ) (G0 G2 : Fin 4 → Fin 4 → (Fin 2 → Fin 4 → ℝ) → ℂ)
      (k : Fin 2 → Fin 4 → ℝ),
      Matrix.of (fun α β => cbPiece P q q' (G0 α β) (G2 α β) j k) =
        vpCoeff0 P j • Matrix.of (fun α β => G0 α β k) +
          vpCoeff2 P q q' j k • Matrix.of (fun α β => G2 α β k) := fun _ _ _ _ _ => by
    ext α β
    simp only [cbPiece_eq, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [e (L *ᵥ p) (L *ᵥ p') (fun α β => F0 (L *ᵥ p') (L *ᵥ p) α β μ)
    (fun α β => F2 (L *ᵥ p') (L *ᵥ p) α β μ), vpCoeff2_map h P p p' j ℓ]
  simp only [e p p' (fun α β => F0 p' p α β _) (fun α β => F2 p' p α β _)]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, h0, h2, vecAct_add, vecAct_smul, vecAct_smul]

/-! ### Covariance of the limit -/

theorem cbShapeMomenta_map (d : Fin 2) (t : Fin 4) (p p' : Fin 4 → ℝ) :
    cbShapeMomenta d t (L *ᵥ p) (L *ᵥ p') = fun i => L *ᵥ cbShapeMomenta d t p p' i :=
  funext fun _ => classVPMomenta_map p p' _

theorem vecAct_sum_fun {ι : Type*} [Fintype ι] (L : Matrix (Fin 4) (Fin 4) ℝ)
    (V : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    vecAct L (fun ν => ∑ k, V k ν) μ = ∑ k, vecAct L (V k) μ := by
  simp only [vecAct, Finset.smul_sum]
  rw [Finset.sum_comm]

/-- **Covariance of the limit of `CB0` (`d = 1`), `CB1` (`d = 0`)**: if `Y` at `(p', p)` and `Z`
at `(Lp', Lp)` are sums `∑ vA + c ∑ vB` of parametric values of the pieces, then
`S Z^μ T = L^μ_ν Y^ν`. -/
theorem conj_cbLim (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hm : 0 < P.m)
    (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) (h : IsSpinLift L S T)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
    (hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2)
    (hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2)
    (hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p)) (d : Fin 2)
    (Y Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hY : ∀ μ i j, ∃ vA vB : Fin 5 → ℂ,
      (∀ k, IsParamValue (vpData P hmγ hΛ hm h₁ h₂ hp hp' hq k)
        (cbPiece P p p' (cbEa0 P d p' p i j μ) (cbEa2 P d p' p i j μ) k) (vA k)) ∧
      (∀ k, IsParamValue (cbData P hmγ hΛ hm h₁ h₂ hp hp' hq d k)
        (cbPiece P p p' (cbEv0 P p' p i j μ) (cbEv2 P p' p i j μ) k) (vB k)) ∧
      Y μ i j = ∑ k, vA k + mergeC P.m P.δ₂ P.δm * ∑ k, vB k)
    (hZ : ∀ μ i j, ∃ vA vB : Fin 5 → ℂ,
      (∀ k, IsParamValue (vpData P hmγ hΛ hm h₁ h₂ hpL hpL' hqL k)
        (cbPiece P (L *ᵥ p) (L *ᵥ p') (cbEa0 P d (L *ᵥ p') (L *ᵥ p) i j μ)
          (cbEa2 P d (L *ᵥ p') (L *ᵥ p) i j μ) k) (vA k)) ∧
      (∀ k, IsParamValue (cbData P hmγ hΛ hm h₁ h₂ hpL hpL' hqL d k)
        (cbPiece P (L *ᵥ p) (L *ᵥ p') (cbEv0 P (L *ᵥ p') (L *ᵥ p) i j μ)
          (cbEv2 P (L *ᵥ p') (L *ᵥ p) i j μ) k) (vB k)) ∧
      Z μ i j = ∑ k, vA k + mergeC P.m P.δ₂ P.δm * ∑ k, vB k)
    (μ : Fin 4) : S * Z μ * T = vecAct L Y μ := by
  choose vA vB hvA hvB hYv using hY
  choose wA wB hwA hwB hZv using hZ
  have eY : Y = fun μ => ∑ k, Matrix.of (fun i j => vA μ i j k) +
      mergeC P.m P.δ₂ P.δm • ∑ k, Matrix.of (fun i j => vB μ i j k) := by
    funext μ
    ext i j
    simp only [hYv, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply,
      smul_eq_mul]
  have eZ : Z = fun μ => ∑ k, Matrix.of (fun i j => wA μ i j k) +
      mergeC P.m P.δ₂ P.δm • ∑ k, Matrix.of (fun i j => wB μ i j k) := by
    funext μ
    ext i j
    simp only [hZv, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.of_apply,
      smul_eq_mul]
  have kA : ∀ k, S * Matrix.of (fun i j => wA μ i j k) * T =
      vecAct L (fun μ => Matrix.of fun i j => vA μ i j k) μ := fun k =>
    conj_eq_vecAct_of_paramValue (vpData P hmγ hΛ hm h₁ h₂ hp hp' hq k) h
      (vpShapeMomenta (vpPieceShape k) (L *ᵥ p) (L *ᵥ p')) (vpShapeMomenta_map _ p p')
      (fun μ ℓ => Matrix.of fun i j =>
        cbPiece P p p' (cbEa0 P d p' p i j μ) (cbEa2 P d p' p i j μ) k ℓ)
      (fun μ ℓ => Matrix.of fun i j => cbPiece P (L *ᵥ p) (L *ᵥ p')
        (cbEa0 P d (L *ᵥ p') (L *ᵥ p) i j μ) (cbEa2 P d (L *ᵥ p') (L *ᵥ p) i j μ) k ℓ)
      (fun μ ℓ => cbPieceM_map h P p' p k (cbEa0 P d) (cbEa2 P d) (cbEa0M_map h P d p' p)
        (cbEa2M_map h P d p' p) μ ℓ)
      (fun μ => Matrix.of fun i j => vA μ i j k) (fun μ => Matrix.of fun i j => wA μ i j k)
      (fun μ i j => hvA μ i j k) (fun μ i j => IsParamValue.exists_integrableOn (hwA μ i j k)) μ
  have kB : ∀ k, S * Matrix.of (fun i j => wB μ i j k) * T =
      vecAct L (fun μ => Matrix.of fun i j => vB μ i j k) μ := fun k =>
    conj_eq_vecAct_of_paramValue (cbData P hmγ hΛ hm h₁ h₂ hp hp' hq d k) h
      (cbShapeMomenta d (vpPieceShape k) (L *ᵥ p) (L *ᵥ p')) (cbShapeMomenta_map d _ p p')
      (fun μ ℓ => Matrix.of fun i j =>
        cbPiece P p p' (cbEv0 P p' p i j μ) (cbEv2 P p' p i j μ) k ℓ)
      (fun μ ℓ => Matrix.of fun i j => cbPiece P (L *ᵥ p) (L *ᵥ p')
        (cbEv0 P (L *ᵥ p') (L *ᵥ p) i j μ) (cbEv2 P (L *ᵥ p') (L *ᵥ p) i j μ) k ℓ)
      (fun μ ℓ => cbPieceM_map h P p' p k (cbEv0 P) (cbEv2 P) (cbEv0M_map h P p' p)
        (cbEv2M_map h P p' p) μ ℓ)
      (fun μ => Matrix.of fun i j => vB μ i j k) (fun μ => Matrix.of fun i j => wB μ i j k)
      (fun μ i j => hvB μ i j k) (fun μ i j => IsParamValue.exists_integrableOn (hwB μ i j k)) μ
  rw [eY, eZ, vecAct_add, vecAct_smul, vecAct_sum_fun, vecAct_sum_fun]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum,
    Finset.sum_mul, kA, kB]

/-- **Every limit of the class value** has the form of `conj_cbLim`, from `tendsto_cbIntegrand`
and the value in shape form. -/
theorem cb_char (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hm : 0 < P.m)
    (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (d : Fin 2) (V : ℝ → Fin 4 → Fin 4 → Fin 4 → ℂ)
    (hV : ∀ μ i j, ∀ ε : ℝ, 0 < ε → V ε μ i j = -QED.TwoLoop.jointEnergyFirstIntegral 2 fun ℓ =>
      (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * cbIntegrand { P with ε := ε } d p' p i j μ ℓ)
    {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ μ i j, Tendsto (fun ε => V ε μ i j) (𝓝[>] 0) (𝓝 (Y μ i j))) (μ i j : Fin 4) :
    ∃ vA vB : Fin 5 → ℂ,
      (∀ k, IsParamValue (vpData P hmγ hΛ hm h₁ h₂ hp hp' hq k)
        (cbPiece P p p' (cbEa0 P d p' p i j μ) (cbEa2 P d p' p i j μ) k) (vA k)) ∧
      (∀ k, IsParamValue (cbData P hmγ hΛ hm h₁ h₂ hp hp' hq d k)
        (cbPiece P p p' (cbEv0 P p' p i j μ) (cbEv2 P p' p i j μ) k) (vB k)) ∧
      Y μ i j = ∑ k, vA k + mergeC P.m P.δ₂ P.δm * ∑ k, vB k := by
  obtain ⟨vA, vB, hvA, hvB, hT⟩ := tendsto_cbIntegrand P hmγ hΛ hm h₁ h₂ hp hp' hq d i j μ
  refine ⟨vA, vB, hvA, hvB, tendsto_nhds_unique (hY μ i j) ?_⟩
  have h := hT.2.neg
  rw [neg_neg] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (hV μ i j ε hε).symm

end QED.ChainProof.SetCPauli.CB01

end
