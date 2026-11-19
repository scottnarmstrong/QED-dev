/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2FormRX
public import QED.GradedProof.SE2LimV
public import QED.TwoLoop.LoopPolySubst

/-!
# The class obligation of clause 2 for `V`

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), clause 2.

* The numerators of `V` are self-energy chains: `seE0 = seChain(E(k₀), D[T₀])`,
  `seE2 = seChain(E(k₀), D[T₂])` with `D[T]_{l₀ l₁} = ∑ g'_{l₀ l₂} g'_{l₁ l₃} T_{l₂ l₃}`
  (`g' = (Λ² - m_γ²) g`), `T₀ = tr(γ^σ E₀(u) γ^τ E₀(v))`, `T₂ = tr(γ^σ γ^τ)`.
* The traces transform contravariantly, `T(Lu, Lv) = L T(u, v) Lᵀ` (`trace_contra`), so
  `D[T]` transforms covariantly (`tensorCov_DV`), and the numerators are spinor covariant.
* `hasSEForm_vPiece`: a piece of `V` (eight or nine lines) with a covariant numerator has the
  covariant form; `classForm_repV` sums the five pieces (`contractionValue₂_repV_eq`).
-/

@[expose] public section

open Complex Filter Topology Matrix

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Routing QED.TwoLoop.Enumeration QED.TwoLoop.Insertion
open QED.TwoLoop.Relabel QED.TwoLoop.Bridge QED.TwoLoop.LimitCovariance
open QED.Integration.TwoLoop (lineDenom castLoopMatrix RefinedBound IntNoSubdivergenceRefined
  symanzikU symanzikV noSubdivergenceRefined_castLoopMatrix_iff)

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S S' : Matrix (Fin 4) (Fin 4) ℂ}

/-! ### Two-index tensors in matrix form -/

/-- The complexified Lorentz matrix. -/
noncomputable def lc (L : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  L.map fun x => (x : ℂ)

theorem tensorCov_of_matrix {D' D : Fin 4 → Fin 4 → ℂ}
    (hM : (lc L)ᵀ * Matrix.of D' * lc L = Matrix.of D) : TensorCov L D' D := by
  intro b a
  have e := congrFun (congrFun hM b) a
  simp only [Matrix.mul_apply, Matrix.transpose_apply, lc, Matrix.map_apply, Matrix.of_apply,
    Finset.sum_mul] at e
  rw [← e, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The scaled metric `(Λ² - m_γ²) g`. -/
noncomputable def gK (P : Params) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun a b => ((Minkowski.metric a b * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ)

theorem lc_gK_lc (h : IsSpinLift L S S') (P : Params) : (lc L)ᵀ * gK P * lc L = gK P := by
  ext b a
  have hr := h.lorentz_right b a
  have hc : ((∑ x, ∑ y, L x b * L y a * Minkowski.metric x y : ℝ) : ℂ) *
      ((P.Λ ^ 2 - P.mγ ^ 2 : ℝ) : ℂ) =
      ((Minkowski.metric b a * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) := by
    rw [hr]; push_cast; ring
  simp only [Matrix.mul_apply, Matrix.transpose_apply, lc, Matrix.map_apply, gK,
    Matrix.of_apply, Finset.sum_mul]
  rw [← hc]
  push_cast
  rw [Finset.sum_mul, Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem lc_gKT_lc (h : IsSpinLift L S S') (P : Params) :
    (lc L)ᵀ * (gK P)ᵀ * lc L = (gK P)ᵀ := by
  have e := congrArg Matrix.transpose (lc_gK_lc h P)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at e ⊢
  exact e

/-- The photon factor `D[T]` of the vacuum-polarization chain. -/
noncomputable def DV (P : Params) (T : Fin 4 → Fin 4 → ℂ) (l0 l1 : Fin 4) : ℂ :=
  ∑ l2, ∑ l3, ((Minkowski.metric l0 l2 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) *
    ((Minkowski.metric l1 l3 * (P.Λ ^ 2 - P.mγ ^ 2) : ℝ) : ℂ) * T l2 l3

theorem of_DV (P : Params) (T : Fin 4 → Fin 4 → ℂ) :
    Matrix.of (DV P T) = gK P * Matrix.of T * (gK P)ᵀ := by
  ext l0 l1
  simp only [DV, gK, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem tensorCov_DV (h : IsSpinLift L S S') (P : Params) {T' T : Fin 4 → Fin 4 → ℂ}
    (hT : Matrix.of T' = lc L * Matrix.of T * (lc L)ᵀ) : TensorCov L (DV P T') (DV P T) := by
  apply tensorCov_of_matrix
  rw [of_DV, of_DV, hT]
  calc (lc L)ᵀ * (gK P * (lc L * Matrix.of T * (lc L)ᵀ) * (gK P)ᵀ) * lc L =
      ((lc L)ᵀ * gK P * lc L) * Matrix.of T * ((lc L)ᵀ * (gK P)ᵀ * lc L) := by
        simp only [Matrix.mul_assoc]
    _ = gK P * Matrix.of T * (gK P)ᵀ := by rw [lc_gK_lc h, lc_gKT_lc h]

/-- **Traces of the closed loop transform contravariantly.** -/
theorem trace_contra (h : IsSpinLift L S S') {A B A' B' : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : S * A' * S' = A) (hB : S * B' * S' = B) :
    Matrix.of (fun σ τ => (Dirac.gamma σ * A' * Dirac.gamma τ * B').trace) =
      lc L * Matrix.of (fun σ τ => (Dirac.gamma σ * A * Dirac.gamma τ * B).trace) *
        (lc L)ᵀ := by
  ext σ τ
  have htr : ∀ X : Matrix (Fin 4) (Fin 4) ℂ, X.trace = (S * X * S').trace := fun X => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h.mul_eq_one', Matrix.one_mul]
  rw [Matrix.of_apply, htr, h.mul_mul_mul, h.mul_mul_mul, h.mul_mul_mul, h.mul_gamma_mul,
    h.mul_gamma_mul, hA, hB]
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_apply, lc, Matrix.map_apply, Matrix.of_apply,
    Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem trSE_contra (h : IsSpinLift L S S') (u v : Fin 4 → ℝ) :
    Matrix.of (trSE 0 (L *ᵥ u) (L *ᵥ v)) = lc L * Matrix.of (trSE 0 u v) * (lc L)ᵀ :=
  trace_contra h (h.mul_electronNumerator_mul 0 u) (h.mul_electronNumerator_mul 0 v)

/-- The trace `tr(γ^σ γ^τ)`. -/
noncomputable def trG (σ τ : Fin 4) : ℂ := (Dirac.gamma σ * Dirac.gamma τ).trace

theorem trG_contra (h : IsSpinLift L S S') :
    Matrix.of trG = lc L * Matrix.of trG * (lc L)ᵀ := by
  have h1 : S * (1 : Matrix (Fin 4) (Fin 4) ℂ) * S' = 1 := by rw [Matrix.mul_one, h.mul_eq_one]
  have e := trace_contra h h1 h1
  simp only [Matrix.mul_one] at e
  exact e

/-! ### The numerators of `V` as chains -/

theorem seE0_eq (P : Params) (α β : Fin 4) (ko u v : Fin 4 → ℝ) :
    seE0 P α β ko u v = seChain (electronNumerator P.m ko) (DV P (trSE 0 u v)) α β := by
  simp only [seE0, outerSE, seChain, DV, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem seE2_eq (P : Params) (α β : Fin 4) (ko : Fin 4 → ℝ) :
    seE2 P α β ko = seChain (electronNumerator P.m ko) (DV P trG) α β := by
  simp only [seE2, outerSE, seChain, DV, trG, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The numerator of the first three pieces of `V` as a matrix. -/
noncomputable def numV1 (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => vF1 Q p α β ℓ

/-- The numerator of the last two pieces of `V` as a matrix. -/
noncomputable def numV2 (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun α β => vF2 Q p α β ℓ

theorem numV1_eq (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    numV1 Q p ℓ = (vκ * vC Q * vK Q) •
      (seChain (electronNumerator Q.m (bm p ℓ 0)) (DV Q (trSE 0 (bm p ℓ 1) (bm p ℓ 2))) +
        ((Q.m ^ 2 : ℝ) : ℂ) • seChain (electronNumerator Q.m (bm p ℓ 0)) (DV Q trG)) := by
  ext α β
  simp only [numV1, vF1, Matrix.of_apply, seE0_eq, seE2_eq, Matrix.smul_apply,
    Matrix.add_apply, smul_eq_mul]

theorem numV2_eq (Q : Params) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    numV2 Q p ℓ = (-(vκ * vC Q * vK Q)) •
      seChain (electronNumerator Q.m (bm p ℓ 0)) (DV Q trG) := by
  ext α β
  simp only [numV2, vF2, Matrix.of_apply, seE2_eq, Matrix.smul_apply, smul_eq_mul]
  ring

theorem bm_loopAct (L : Matrix (Fin 4) (Fin 4) ℝ) (p : Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ)
    (j : Fin 5) : bm (L *ᵥ p) (loopAct L ℓ) j = L *ᵥ bm p ℓ j := by
  show QED.Integration.TwoLoop.lineMomentum _ (basePP (L *ᵥ p)) j (loopAct L ℓ) =
    L *ᵥ QED.Integration.TwoLoop.lineMomentum _ (basePP p) j ℓ
  rw [show basePP (L *ᵥ p) = fun j => aVc j • (L *ᵥ p) from funext (basePP_eq _),
    show basePP p = fun j => aVc j • p from funext (basePP_eq _)]
  exact lineMomentum_loopAct_smul L _ aVc j p ℓ

theorem cov_numV1 (Q : Params) (h : IsSpinLift L S S') (p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : S * numV1 Q (L *ᵥ p) (loopAct L ℓ) * S' = numV1 Q p ℓ := by
  rw [numV1_eq, numV1_eq, bm_loopAct, bm_loopAct, bm_loopAct, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_seChain_mul h _ (tensorCov_DV h Q (trSE_contra h _ _)),
    mul_seChain_mul h _ (tensorCov_DV h Q (trG_contra h)), h.mul_electronNumerator_mul]

theorem cov_numV2 (Q : Params) (h : IsSpinLift L S S') (p : Fin 4 → ℝ)
    (ℓ : Fin 2 → Fin 4 → ℝ) : S * numV2 Q (L *ᵥ p) (loopAct L ℓ) * S' = numV2 Q p ℓ := by
  rw [numV2_eq, numV2_eq, bm_loopAct, Matrix.mul_smul, Matrix.smul_mul,
    mul_seChain_mul h _ (tensorCov_DV h Q (trG_contra h)), h.mul_electronNumerator_mul]

/-! ### Polynomiality in the external momentum -/

theorem isLoopPoly_one_of_two {f : (Fin 4 → ℝ) → ℂ} {n : ℕ}
    (h : IsLoopPoly 2 n fun ℓ' => f (ℓ' 0)) : IsLoopPoly 1 n fun y => f (y 0) := by
  refine (congrArg (IsLoopPoly 1 n) (funext fun y => ?_)).mp
    (h.comp_affine ![![1], ![0]] 0)
  simp

theorem isLoopAffine_bm_p (ℓ : Fin 2 → Fin 4 → ℝ) (j : Fin 5) :
    IsLoopAffine fun ℓ' : Fin 2 → Fin 4 → ℝ => bm (ℓ' 0) ℓ j := by
  refine ⟨![aVc j, 0], QED.Integration.TwoLoop.lineMomentum (castLoopMatrix baseA) 0 j ℓ,
    fun ℓ' => ?_⟩
  funext μ
  simp [QED.Integration.TwoLoop.lineMomentum, basePP_eq, Fin.sum_univ_two]
  ring

theorem isLoopPoly_numV1_p (Q : Params) (ℓ : Fin 2 → Fin 4 → ℝ) (i j : Fin 4) :
    IsLoopPoly 1 4 fun y => numV1 Q (y 0) ℓ i j := by
  refine isLoopPoly_one_of_two (f := fun p => numV1 Q p ℓ i j) ?_
  have ha := isLoopAffine_bm_p ℓ
  have h2 := ((isLoopPoly_seE2 Q i j (ha 0)).mono (n' := 3) (by norm_num)).const_mul
    ((Q.m ^ 2 : ℝ) : ℂ)
  exact (((isLoopPoly_seE0 Q i j (ha 0) (ha 1) (ha 2)).add h2).const_mul
    (vκ * vC Q * vK Q)).mono (by norm_num)

theorem isLoopPoly_numV2_p (Q : Params) (ℓ : Fin 2 → Fin 4 → ℝ) (i j : Fin 4) :
    IsLoopPoly 1 4 fun y => numV2 Q (y 0) ℓ i j := by
  refine isLoopPoly_one_of_two (f := fun p => numV2 Q p ℓ i j) ?_
  have h := ((isLoopPoly_seE2 Q i j (isLoopAffine_bm_p ℓ 0)).const_mul
    (-(vκ * vC Q * vK Q))).mono (n' := 4) (by norm_num)
  refine (congrArg (IsLoopPoly 2 4) (funext fun ℓ' => ?_)).mp h
  simp only [numV2, vF2, Matrix.of_apply]
  ring

/-! ### The pieces and the class `V` -/

/-- **A piece of `V` with a covariant numerator has the covariant form.** -/
theorem hasSEForm_vPiece {n : ℕ} (hn : 7 ≤ n) (sh : Fin (n + 1) → Fin 5) (Ms : Fin (n + 1) → ℝ)
    {E : Finset (Fin (n + 1))} (hcrit : IntNoSubdivergenceRefined 2 E fun i => baseA (sh i))
    (F : (Fin 4 → ℝ) → (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ)
    (hpoly : ∀ p i j, IsLoopPoly 2 4 fun ℓ => F p ℓ i j)
    (hB : ∀ p i j, RefinedBound (castLoopMatrix fun i => baseA (sh i)) E 4 fun ℓ => F p ℓ i j)
    (hcov : ∀ (L : Matrix (Fin 4) (Fin 4) ℝ) (S S' : Matrix (Fin 4) (Fin 4) ℂ),
      IsSpinLift L S S' → ∀ p ℓ, S * F (L *ᵥ p) (loopAct L ℓ) * S' = F p ℓ)
    {d : ℕ} (hpolyp : ∀ ℓ i j, IsLoopPoly 1 d fun y => F (y 0) ℓ i j) {m m₀ ν : ℝ}
    (hm0 : 0 < m₀) (hmm : m₀ ≤ m) (hν0 : 0 < ν) (hν2 : ν ≤ 2 * m₀)
    (h0 : ∀ i, sh i = 0 → m ≤ Ms i) (h12 : ∀ i, sh i = 1 ∨ sh i = 2 → m₀ ≤ Ms i)
    (h34 : ∀ i, sh i = 3 ∨ sh i = 4 → ν ≤ Ms i) :
    HasSEForm (m + ν) fun ε p i j => QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => F p ℓ i j *
      ∏ k, (lineDenom (castLoopMatrix fun i => baseA (sh i)) (fun i => basePP p (sh i)) Ms ε k
        ℓ)⁻¹) := by
  have hm : 0 < m := hm0.trans_le hmm
  have hc : 0 < min (m₀ ^ 2) (ν ^ 2) := lt_min (by positivity) (by positivity)
  have hMc : ∀ i, min (m₀ ^ 2) (ν ^ 2) ≤ Ms i ^ 2 := by
    intro i
    rcases (by decide : ∀ j : Fin 5, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) (sh i) with
      h | h | h | h | h
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (hmm.trans (h0 i h)) 2)
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (h12 i (Or.inl h)) 2)
    · exact (min_le_left _ _).trans (pow_le_pow_left₀ hm0.le (h12 i (Or.inr h)) 2)
    · exact (min_le_right _ _).trans (pow_le_pow_left₀ hν0.le (h34 i (Or.inl h)) 2)
    · exact (min_le_right _ _).trans (pow_le_pow_left₀ hν0.le (h34 i (Or.inr h)) 2)
  have hpp : ∀ p : Fin 4 → ℝ, (fun i => basePP p (sh i)) = fun i => aVc (sh i) • p :=
    fun p => funext fun i => basePP_eq p (sh i)
  let D : SEData :=
    { m := n
      α := castLoopMatrix fun i => baseA (sh i)
      cs := fun i => aVc (sh i)
      M := Ms
      E := E
      hm := by omega
      hcrit := (noSubdivergenceRefined_castLoopMatrix_iff _ _ _).mpr hcrit }
  let P : SEPiece (m + ν) :=
    { D := D
      N := F
      hQ := fun p i j => by
        obtain ⟨Q', hQ'⟩ := (hpoly p i j).exists_loopQuartic
        exact ⟨Q', ⟨Or.inl hn, hQ' ▸ hB p i j⟩, hQ'⟩
      hV := fun p hp => ⟨_, min_one_mul_pos (by positivity) hc hp, fun z hz hz1 hU => by
        have e := symanzikV_vShape_ge sh Ms hm hν0 hν2 h0 h12 h34 hc hMc hp hz hz1 hU
        rw [hpp] at e
        exact e⟩
      hcov := hcov }
  refine P.hasSEForm (by nlinarith) (d := d) hpolyp (h := fun _ => 1) tendsto_const_nhds
    fun p _ i j => Eventually.of_forall fun ε => ?_
  show _ = 1 * QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => F p ℓ i j *
    ∏ k, (lineDenom (castLoopMatrix fun i => baseA (sh i)) (fun i => aVc (sh i) • p) Ms ε k
      ℓ)⁻¹)
  rw [one_mul, ← hpp]

theorem classForm_repV : ClassForm repV := by
  intro Q hQ m₀ ν hm0 hmm hM1 hM2 hν0 hν hν2
  have hγ : ν ≤ Q.mγ := hν.trans (min_le_left _ _)
  have hΛ : ν ≤ Q.Λ := hν.trans (min_le_right _ _)
  obtain ⟨c1, c2, c3, c4, c5⟩ := crit_sh
  obtain ⟨a1, b1, d1⟩ := cond_sh1 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a2, b2, d2⟩ := cond_sh2 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a3, b3, d3⟩ := cond_sh3 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a4, b4, d4⟩ := cond_sh4 Q hM1 hM2 hmm hγ hΛ
  obtain ⟨a5, b5, d5⟩ := cond_sh5 Q hM1 hM2 hmm hγ hΛ
  have p1 := fun p i j => isLoopPoly_vF1 Q p i j
  have p2 := fun p i j => isLoopPoly_vF2 Q p i j
  have cv1 := fun L S S' (h : IsSpinLift L S S') p ℓ => cov_numV1 Q h p ℓ
  have cv2 := fun L S S' (h : IsSpinLift L S S') p ℓ => cov_numV2 Q h p ℓ
  have h1 := hasSEForm_vPiece (by norm_num) sh1 (ms1 Q) c1 (numV1 Q) p1
    (fun p i j => refinedBound_vF1 Q p i j sh1 rfl rfl rfl) cv1 (isLoopPoly_numV1_p Q)
    hm0 hmm hν0 hν2 a1 b1 d1
  have h2 := hasSEForm_vPiece (by norm_num) sh2 (ms2 Q) c2 (numV1 Q) p1
    (fun p i j => refinedBound_vF1 Q p i j sh2 rfl rfl rfl) cv1 (isLoopPoly_numV1_p Q)
    hm0 hmm hν0 hν2 a2 b2 d2
  have h3 := hasSEForm_vPiece (by norm_num) sh3 (ms3 Q) c3 (numV1 Q) p1
    (fun p i j => refinedBound_vF1 Q p i j sh3 rfl rfl rfl) cv1 (isLoopPoly_numV1_p Q)
    hm0 hmm hν0 hν2 a3 b3 d3
  have h4 := hasSEForm_vPiece (by norm_num) sh4 (ms4 Q) c4 (numV2 Q) p2
    (fun p i j => refinedBound_vF2 Q p i j sh4 rfl) cv2 (isLoopPoly_numV2_p Q)
    hm0 hmm hν0 hν2 a4 b4 d4
  have h5 := hasSEForm_vPiece (by norm_num) sh5 (ms5 Q) c5 (numV2 Q) p2
    (fun p i j => refinedBound_vF2 Q p i j sh5 rfl) cv2 (isLoopPoly_numV2_p Q)
    hm0 hmm hν0 hν2 a5 b5 d5
  refine ((((h1.add h2).add h3).add h4).add h5).congr fun p _ α β => ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (contractionValue₂_repV_eq hQ.pv₁ hQ.pv₂ hε p α β).symm

end QED.GradedProof.SE2

end
