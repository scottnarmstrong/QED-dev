/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCSideBDCovLim
public import QED.ChainProof.HCSideLinks

/-!
# Covariance of the bubble–`δ₃` and `δ₃`–bubble class limits

For a real `L` with a spinor lift `(S, T)` and an admissible pair `(p', p)`, the limits `Y` at
`(p', p)` and `Z` at `(L p', L p)` of the class vertex
`QED.ChainProof.HCValue.classV (repBD s)` (resp. `repDB s`) satisfy `S Z^μ T = L^μ_ν Y^ν`
(`conj_classLimit_repBD`, `conj_classLimit_repDB`), hence **`repCov_repBD`**,
**`repCov_repDB`**. The limits are combinations of parametric values with coefficients
independent of the external momenta (`classLimit_repBD_eq`); the numerators transform covariantly
(`QED.TwoLoop.ReflCovariance.vpPieceM_map` for the `VP` pieces, `bdL1N_map`, … for the
longitudinal pieces, via `QED.ChainProof.HCSide.longM_map`), and so do their parametric values
(`QED.ChainProof.HCSide.conj_rowsData`). As for `repDD`, positive energies are not used.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Matrix
open scoped Real

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit
  QED.ChainProof.Enum QED.ChainProof.RepsInt QED.TwoLoop.ClassIntegrable
open QED.TwoLoop.LimitCovariance QED.TwoLoop.ReflCovariance QED.Dirac QED.ChainProof.HCValue
open QED.TwoLoop.ClassLimit (vpPieceShape vpPieceLines vpPieceNumer vpEpsNumer vpDenomProd
  integrand_VP_eq isLoopPoly_vpPieceNumer refinedBound_vpPieceNumer isLoopPoly_vpEpsNumer
  refinedBound_vpEpsNumer twoLoopNorm)
open QED.Integration.TwoLoop (lineDenom castLoopMatrix class5LoopMatrix classVPMomenta
  RefinedBound IntNoSubdivergenceRefined)

/-! ### Covariance -/

section Cov

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

theorem loopAct_zero_add_neg_one (ℓ : Fin 2 → Fin 4 → ℝ) :
    loopAct L ℓ 0 + -loopAct L ℓ 1 = L *ᵥ (ℓ 0 + -ℓ 1) := by
  simp [loopAct, Matrix.mulVec_add, Matrix.mulVec_neg]

/-- **Covariance of the longitudinal numerators** (here: `repBD`, loop `b₀ b₁ b₂`). -/
theorem bdL1N_map (h : IsSpinLift L S T) (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * bdL1N P (L *ᵥ p) (L *ᵥ p') μ (loopAct L ℓ) * T =
      vecAct L (fun ν => bdL1N P p p' ν ℓ) μ := by
  have e : ∀ q q' ν (l : Fin 2 → Fin 4 → ℝ),
      bdL1N P q q' ν l = longM P q (q' - q) (-l 1) (-l 1) (l 0) ν := fun q q' ν l => by
    ext α β
    simp only [bdL1N, Matrix.of_apply, bdN_eq_longM]
  simp only [e]
  rw [neg_loopAct_one, ← Matrix.mulVec_sub]
  exact longM_map h P p (p' - p) (-ℓ 1) (-ℓ 1) (ℓ 0) μ

theorem bdL2N_map (h : IsSpinLift L S T) (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * bdL2N P (L *ᵥ p) (L *ᵥ p') μ (loopAct L ℓ) * T =
      vecAct L (fun ν => bdL2N P p p' ν ℓ) μ := by
  have e : ∀ q q' ν (l : Fin 2 → Fin 4 → ℝ),
      bdL2N P q q' ν l = longM P q (q' - q) (-l 1) (-l 1) (l 0 + -l 1) ν := fun q q' ν l => by
    ext α β
    simp only [bdL2N, Matrix.of_apply, bdN_eq_longM]
  simp only [e]
  rw [loopAct_zero_add_neg_one, neg_loopAct_one, ← Matrix.mulVec_sub]
  exact longM_map h P p (p' - p) (-ℓ 1) (-ℓ 1) (ℓ 0 + -ℓ 1) μ

theorem dbL1N_map (h : IsSpinLift L S T) (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * dbL1N P (L *ᵥ p) (L *ᵥ p') μ (loopAct L ℓ) * T =
      vecAct L (fun ν => dbL1N P p p' ν ℓ) μ := by
  have e : ∀ q q' ν (l : Fin 2 → Fin 4 → ℝ),
      dbL1N P q q' ν l = longM P q (q' - q) (-l 1) (l 0) (-l 1) ν := fun q q' ν l => by
    ext α β
    simp only [dbL1N, Matrix.of_apply, dbN_eq_longM]
  simp only [e]
  rw [neg_loopAct_one, ← Matrix.mulVec_sub]
  exact longM_map h P p (p' - p) (-ℓ 1) (ℓ 0) (-ℓ 1) μ

theorem dbL2N_map (h : IsSpinLift L S T) (P : Params) (p p' : Fin 4 → ℝ) (μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    S * dbL2N P (L *ᵥ p) (L *ᵥ p') μ (loopAct L ℓ) * T =
      vecAct L (fun ν => dbL2N P p p' ν ℓ) μ := by
  have e : ∀ q q' ν (l : Fin 2 → Fin 4 → ℝ),
      dbL2N P q q' ν l = longM P q (q' - q) (-l 1) (l 0 + -l 1) (-l 1) ν := fun q q' ν l => by
    ext α β
    simp only [dbL2N, Matrix.of_apply, dbN_eq_longM]
  simp only [e]
  rw [loopAct_zero_add_neg_one, neg_loopAct_one, ← Matrix.mulVec_sub]
  exact longM_map h P p (p' - p) (-ℓ 1) (ℓ 0 + -ℓ 1) (-ℓ 1) μ

theorem vecAct_sum (L : Matrix (Fin 4) (Fin 4) ℝ) {ι : Type*} (s : Finset ι)
    (A : ι → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (μ : Fin 4) :
    vecAct L (fun ν => ∑ k ∈ s, A k ν) μ = ∑ k ∈ s, vecAct L (A k) μ := by
  simpa only [one_smul] using
    QED.TwoLoop.VertexCovariance.vecAct_finset_sum s L (fun _ => 1) A μ

/-- **The linear combination of the class limits**: covariance of the parts gives covariance of
the combination. -/
theorem conj_comb (c K₁ K₂ κ₁ κ₂ : ℂ) {A A' B B' : Fin 5 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    {C C' D D' : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hA : ∀ k μ, S * A' k μ * T = vecAct L (A k) μ) (hB : ∀ k μ, S * B' k μ * T = vecAct L (B k) μ)
    (hC : ∀ μ, S * C' μ * T = vecAct L C μ) (hD : ∀ μ, S * D' μ * T = vecAct L D μ) (μ : Fin 4) :
    S * (c • (K₁ • ∑ k, A' k μ + K₂ • ∑ k, B' k μ + κ₁ • C' μ + κ₂ • D' μ)) * T =
      vecAct L (fun ν => c • (K₁ • ∑ k, A k ν + K₂ • ∑ k, B k ν + κ₁ • C ν + κ₂ • D ν)) μ := by
  rw [vecAct_smul, vecAct_add, vecAct_add, vecAct_add, vecAct_smul, vecAct_smul, vecAct_smul,
    vecAct_smul, vecAct_sum, vecAct_sum]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum,
    Matrix.sum_mul, hA, hB, hC, hD]

/-- The class vertex of `repBD s` as the joint integral of `bdG`. -/
theorem classV_repBD_eq' (s : Fin 2) (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    classV (repBD s) P p' p μ i j = (1 / I) * QED.TwoLoop.jointEnergyFirstIntegral 2
      (bdG P (fun _ => i) (fun _ => j) (fun _ => μ) s (fun _ => p) (fun _ => p' - p)) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hΦ : chainFlavors P = (⟨P.mass, P.loopCoeff, 0⟩ : QED.Lepton.Flavors (Fin 3)) := rfl
  rw [classV, Matrix.of_apply, hΦ, contractionValue₂_params', contractionValue₂_repBD_eq _ s hmom]

/-- The class vertex of `repDB s` as the joint integral of `dbG`. -/
theorem classV_repDB_eq' (s : Fin 2) (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    classV (repDB s) P p' p μ i j = (1 / I) * QED.TwoLoop.jointEnergyFirstIntegral 2
      (dbG P (fun _ => i) (fun _ => j) (fun _ => μ) s (fun _ => p) (fun _ => p' - p)) := by
  have hmom : (fun _ : Fin 1 => p') 0 = (fun _ : Fin 1 => p) 0 + (fun _ : Fin 1 => p' - p) 0 := by
    simp
  have hΦ : chainFlavors P = (⟨P.mass, P.loopCoeff, 0⟩ : QED.Lepton.Flavors (Fin 3)) := rfl
  rw [classV, Matrix.of_apply, hΦ, contractionValue₂_params', contractionValue₂_repDB_eq _ s hmom]

variable {P : Params} (hA : ChainAdmissible P) {p p' : Fin 4 → ℝ}
  (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
  (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))

include hA hp hp' hq in
/-- **The limit of the class vertex of `repBD s` as a combination of parametric values.** -/
theorem classLimit_repBD_eq (s : Fin 2) {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ μ i j, Tendsto (fun ε => classV (repBD s) { P with ε := ε } p' p μ i j)
      (𝓝[>] 0) (𝓝 (Y μ i j))) :
    ∃ (V₁ V₂ : Fin 5 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (W₁ W₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ),
      (∀ k μ i j, IsParamValue (ext1Data hA hp hp' hq k) (fun ℓ => vpPieceM P p p' k μ ℓ i j)
        (V₁ k μ i j)) ∧
      (∀ k μ i j, IsParamValue (ext2Data hA hp hp' hq k) (fun ℓ => vpPieceM P p p' k μ ℓ i j)
        (V₂ k μ i j)) ∧
      (∀ μ i j, IsParamValue (L1Data hA hp hp' hq) (fun ℓ => bdL1N P p p' μ ℓ i j) (W₁ μ i j)) ∧
      (∀ μ i j, IsParamValue (L2Data hA hp hp' hq) (fun ℓ => bdL2N P p p' μ ℓ i j) (W₂ μ i j)) ∧
      ∀ μ, Y μ = (1 / I) • (bdK1 P • ∑ k, V₁ k μ + bdK2 P • ∑ k, V₂ k μ + bdκL P • W₁ μ +
        (-bdκL P) • W₂ μ) := by
  choose v1 v2 w1 w2 hv1 hv2 hw1 hw2 hlim using fun μ i j => bd_lim hA hp hp' hq s i j μ
  refine ⟨fun k μ => Matrix.of fun i j => v1 μ i j k, fun k μ => Matrix.of fun i j => v2 μ i j k,
    fun μ => Matrix.of fun i j => w1 μ i j, fun μ => Matrix.of fun i j => w2 μ i j,
    fun k μ i j => hv1 μ i j k, fun k μ i j => hv2 μ i j k, hw1, hw2, fun μ => ?_⟩
  ext i j
  have hY' : Tendsto (fun ε => (1 / I) * QED.TwoLoop.jointEnergyFirstIntegral 2
      (bdG { P with ε := ε } (fun _ => i) (fun _ => j) (fun _ => μ) s (fun _ => p)
        (fun _ => p' - p))) (𝓝[>] 0) (𝓝 (Y μ i j)) :=
    (hY μ i j).congr fun ε => classV_repBD_eq' s _ p' p μ i j
  rw [tendsto_nhds_unique hY' ((hlim μ i j).2.const_mul (1 / I))]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.of_apply, smul_eq_mul]

include hA hp hp' hq in
/-- **The limit of the class vertex of `repDB s` as a combination of parametric values.** -/
theorem classLimit_repDB_eq (s : Fin 2) {Y : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ μ i j, Tendsto (fun ε => classV (repDB s) { P with ε := ε } p' p μ i j)
      (𝓝[>] 0) (𝓝 (Y μ i j))) :
    ∃ (V₁ V₂ : Fin 5 → Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (W₁ W₂ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ),
      (∀ k μ i j, IsParamValue (ext1Data hA hp hp' hq k) (fun ℓ => vpPieceM P p p' k μ ℓ i j)
        (V₁ k μ i j)) ∧
      (∀ k μ i j, IsParamValue (ext2Data hA hp hp' hq k) (fun ℓ => vpPieceM P p p' k μ ℓ i j)
        (V₂ k μ i j)) ∧
      (∀ μ i j, IsParamValue (L1Data hA hp hp' hq) (fun ℓ => dbL1N P p p' μ ℓ i j) (W₁ μ i j)) ∧
      (∀ μ i j, IsParamValue (L2Data hA hp hp' hq) (fun ℓ => dbL2N P p p' μ ℓ i j) (W₂ μ i j)) ∧
      ∀ μ, Y μ = (1 / I) • (bdK1 P • ∑ k, V₁ k μ + bdK2 P • ∑ k, V₂ k μ + bdκL P • W₁ μ +
        (-bdκL P) • W₂ μ) := by
  choose v1 v2 w1 w2 hv1 hv2 hw1 hw2 hlim using fun μ i j => db_lim hA hp hp' hq s i j μ
  refine ⟨fun k μ => Matrix.of fun i j => v1 μ i j k, fun k μ => Matrix.of fun i j => v2 μ i j k,
    fun μ => Matrix.of fun i j => w1 μ i j, fun μ => Matrix.of fun i j => w2 μ i j,
    fun k μ i j => hv1 μ i j k, fun k μ i j => hv2 μ i j k, hw1, hw2, fun μ => ?_⟩
  ext i j
  have hY' : Tendsto (fun ε => (1 / I) * QED.TwoLoop.jointEnergyFirstIntegral 2
      (dbG { P with ε := ε } (fun _ => i) (fun _ => j) (fun _ => μ) s (fun _ => p)
        (fun _ => p' - p))) (𝓝[>] 0) (𝓝 (Y μ i j)) :=
    (hY μ i j).congr fun ε => classV_repDB_eq' s _ p' p μ i j
  rw [tendsto_nhds_unique hY' ((hlim μ i j).2.const_mul (1 / I))]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.of_apply, smul_eq_mul]

end Cov

/-! ### The covariance of the limits -/

section Final

variable {L : Matrix (Fin 4) (Fin 4) ℝ} {S T : Matrix (Fin 4) (Fin 4) ℂ}

/-- **Covariance of the bubble–`δ₃` class limits under `L`, with the external momenta moved.** -/
theorem conj_classLimit_repBD (s : Fin 2) {P : Params} (hA : ChainAdmissible P)
    (h : IsSpinLift L S T) {p' p : Fin 4 → ℝ} (hpq : IsPairQ P.m p' p)
    {Y Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ μ i j, Tendsto (fun ε => classV (repBD s) { P with ε := ε } p' p μ i j)
      (𝓝[>] 0) (𝓝 (Y μ i j)))
    (hZ : ∀ μ i j, Tendsto (fun ε => classV (repBD s) { P with ε := ε } (L *ᵥ p') (L *ᵥ p)
      μ i j) (𝓝[>] 0) (𝓝 (Z μ i j))) (μ : Fin 4) :
    S * Z μ * T = vecAct L Y μ := by
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [dot_mulVec_sub h]; exact hq.le
  obtain ⟨V₁, V₂, W₁, W₂, hV₁, hV₂, hW₁, hW₂, hYV⟩ := classLimit_repBD_eq hA hp hp' hq.le s hY
  obtain ⟨V₁', V₂', W₁', W₂', hV₁', hV₂', hW₁', hW₂', hZV⟩ :=
    classLimit_repBD_eq hA hpL hpL' hqL s hZ
  have c₁ : ∀ k μ, S * V₁' k μ * T = vecAct L (V₁ k) μ := fun k μ =>
    conj_rowsData h _ _ _ p p' _ _ _ _ _ (fun μ ℓ => vpPieceM P p p' k μ ℓ)
      (fun μ ℓ => vpPieceM P (L *ᵥ p) (L *ᵥ p') k μ ℓ) (fun μ ℓ => vpPieceM_map h P p p' k μ ℓ)
      (V₁ k) (V₁' k) (hV₁ k) (hV₁' k) μ
  have c₂ : ∀ k μ, S * V₂' k μ * T = vecAct L (V₂ k) μ := fun k μ =>
    conj_rowsData h _ _ _ p p' _ _ _ _ _ (fun μ ℓ => vpPieceM P p p' k μ ℓ)
      (fun μ ℓ => vpPieceM P (L *ᵥ p) (L *ᵥ p') k μ ℓ) (fun μ ℓ => vpPieceM_map h P p p' k μ ℓ)
      (V₂ k) (V₂' k) (hV₂ k) (hV₂' k) μ
  have d₁ : ∀ μ, S * W₁' μ * T = vecAct L W₁ μ := fun μ =>
    conj_rowsData h _ _ _ p p' _ _ _ _ _ (fun μ ℓ => bdL1N P p p' μ ℓ)
      (fun μ ℓ => bdL1N P (L *ᵥ p) (L *ᵥ p') μ ℓ) (fun μ ℓ => bdL1N_map h P p p' μ ℓ)
      W₁ W₁' hW₁ hW₁' μ
  have d₂ : ∀ μ, S * W₂' μ * T = vecAct L W₂ μ := fun μ =>
    conj_rowsData h _ _ _ p p' _ _ _ _ _ (fun μ ℓ => bdL2N P p p' μ ℓ)
      (fun μ ℓ => bdL2N P (L *ᵥ p) (L *ᵥ p') μ ℓ) (fun μ ℓ => bdL2N_map h P p p' μ ℓ)
      W₂ W₂' hW₂ hW₂' μ
  rw [hZV, show Y = _ from funext hYV]
  exact conj_comb _ _ _ _ _ c₁ c₂ d₁ d₂ μ

/-- **Covariance of the `δ₃`–bubble class limits under `L`, with the external momenta moved.** -/
theorem conj_classLimit_repDB (s : Fin 2) {P : Params} (hA : ChainAdmissible P)
    (h : IsSpinLift L S T) {p' p : Fin 4 → ℝ} (hpq : IsPairQ P.m p' p)
    {Y Z : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ}
    (hY : ∀ μ i j, Tendsto (fun ε => classV (repDB s) { P with ε := ε } p' p μ i j)
      (𝓝[>] 0) (𝓝 (Y μ i j)))
    (hZ : ∀ μ i j, Tendsto (fun ε => classV (repDB s) { P with ε := ε } (L *ᵥ p') (L *ᵥ p)
      μ i j) (𝓝[>] 0) (𝓝 (Z μ i j))) (μ : Fin 4) :
    S * Z μ * T = vecAct L Y μ := by
  obtain ⟨hp', hp, -, -, hq⟩ := hpq
  have hpL : Minkowski.dot (L *ᵥ p) (L *ᵥ p) = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp
  have hpL' : Minkowski.dot (L *ᵥ p') (L *ᵥ p') = -P.m ^ 2 := by rw [h.dot_mulVec]; exact hp'
  have hqL : 0 ≤ Minkowski.dot (L *ᵥ p' - L *ᵥ p) (L *ᵥ p' - L *ᵥ p) := by
    rw [dot_mulVec_sub h]; exact hq.le
  obtain ⟨V₁, V₂, W₁, W₂, hV₁, hV₂, hW₁, hW₂, hYV⟩ := classLimit_repDB_eq hA hp hp' hq.le s hY
  obtain ⟨V₁', V₂', W₁', W₂', hV₁', hV₂', hW₁', hW₂', hZV⟩ :=
    classLimit_repDB_eq hA hpL hpL' hqL s hZ
  have c₁ : ∀ k μ, S * V₁' k μ * T = vecAct L (V₁ k) μ := fun k μ =>
    conj_rowsData h _ _ _ p p' _ _ _ _ _ (fun μ ℓ => vpPieceM P p p' k μ ℓ)
      (fun μ ℓ => vpPieceM P (L *ᵥ p) (L *ᵥ p') k μ ℓ) (fun μ ℓ => vpPieceM_map h P p p' k μ ℓ)
      (V₁ k) (V₁' k) (hV₁ k) (hV₁' k) μ
  have c₂ : ∀ k μ, S * V₂' k μ * T = vecAct L (V₂ k) μ := fun k μ =>
    conj_rowsData h _ _ _ p p' _ _ _ _ _ (fun μ ℓ => vpPieceM P p p' k μ ℓ)
      (fun μ ℓ => vpPieceM P (L *ᵥ p) (L *ᵥ p') k μ ℓ) (fun μ ℓ => vpPieceM_map h P p p' k μ ℓ)
      (V₂ k) (V₂' k) (hV₂ k) (hV₂' k) μ
  have d₁ : ∀ μ, S * W₁' μ * T = vecAct L W₁ μ := fun μ =>
    conj_rowsData h _ _ _ p p' _ _ _ _ _ (fun μ ℓ => dbL1N P p p' μ ℓ)
      (fun μ ℓ => dbL1N P (L *ᵥ p) (L *ᵥ p') μ ℓ) (fun μ ℓ => dbL1N_map h P p p' μ ℓ)
      W₁ W₁' hW₁ hW₁' μ
  have d₂ : ∀ μ, S * W₂' μ * T = vecAct L W₂ μ := fun μ =>
    conj_rowsData h _ _ _ p p' _ _ _ _ _ (fun μ ℓ => dbL2N P p p' μ ℓ)
      (fun μ ℓ => dbL2N P (L *ᵥ p) (L *ᵥ p') μ ℓ) (fun μ ℓ => dbL2N_map h P p p' μ ℓ)
      W₂ W₂' hW₂ hW₂' μ
  rw [hZV, show Y = _ from funext hYV]
  exact conj_comb _ _ _ _ _ c₁ c₂ d₁ d₂ μ

/-- **The bubble–`δ₃` representatives are covariant.** -/
theorem repCov_repBD (s : Fin 2) : RepCov (repBD s) :=
  fun _ hA _ _ _ h _ _ hpq _ _ _ _ hY hZ μ => conj_classLimit_repBD s hA h hpq hY hZ μ

/-- **The `δ₃`–bubble representatives are covariant.** -/
theorem repCov_repDB (s : Fin 2) : RepCov (repDB s) :=
  fun _ hA _ _ _ h _ _ hpq _ _ _ _ hY hZ μ => conj_classLimit_repDB s hA h hpq hY hZ μ

end Final

end QED.ChainProof.HCSide

end
