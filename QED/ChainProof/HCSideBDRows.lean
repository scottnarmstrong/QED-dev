/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.RepsIntDBInt
public import QED.TwoLoop.ClassLimitVP
public import QED.TwoLoop.ClassLimitParametric

/-!
# Limits of two-loop pieces on the rows of the `VP` class matrix

Helper for obligation O3-6 for the bubble–`δ₃` and `δ₃`–bubble representatives. The value
integrands of `repBD s` and `repDB s` split into pieces whose lines are rows of the class loop
matrix of `VP` (`QED.ChainProof.RepsInt.bdG_eq`, `QED.ChainProof.RepsInt.dbG_eq`). This file
proves that each such piece has an `ε → 0⁺` limit of its joint energy-first integral.

* `JointHasLim F`: for `ε → 0⁺`, `F ε` is eventually integrable in both stages and its joint
  energy-first integral converges. It is closed under sums, multiplication by convergent scalar
  functions, and eventual pointwise equality.
* `jointHasLim_vpRows`: a piece `F ∏ᵢ D_{σ(i)}⁻¹` on rows of the `VP` matrix, with an
  `ε`-independent numerator of degree at most four that satisfies the refined criterion, and a
  uniform lower bound for the Symanzik polynomial `V`.
* `symanzikV_vpRows_ge`: that lower bound, `(3/4) min(m², m_γ²)`, for on-shell `p, p'` with
  `(p' - p)² ≥ 0` and masses at least those of `VP` with photon masses `m_γ`.
* `jointHasLim_vpSum_ext1`, `jointHasLim_vpSum_ext2`: the sums over the four `VP` shapes with one,
  resp. two, extra photon denominators. The numerator of shape `3` depends on `ε` and is split as
  in `QED.TwoLoop.ClassLimit.integrand_VP_eq`.
* `jointHasLim_bdPiece`, `jointHasLim_dbPiece`: the longitudinal pieces.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology

namespace QED.ChainProof.HCSide

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.Insertion QED.TwoLoop.CountertermLimit
  QED.ChainProof.Enum QED.ChainProof.RepsInt QED.TwoLoop.ClassIntegrable
open QED.Integration.TwoLoop (lineDenom lineMomentum castLoopMatrix class5LoopMatrix
  classVPMomenta classVPMasses RefinedBound IntNoSubdivergenceRefined symanzikU symanzikV
  noSubdivergenceRefined_castLoopMatrix_iff loopMatrixVP LoopQuartic
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined)
open QED.TwoLoop.ClassLimit (jointEnergyFirstIntegral_add jointEnergyFirstIntegral_const_mul
  jointEnergyFirstIntegrable_const_mul lineDenom_eps tendsto_jointEnergyFirstIntegral_of_refined)

/-! ### Convergent families of two-loop integrands -/

/-- For `ε → 0⁺`, `F ε` is eventually integrable in both stages of the joint energy-first
integral (T₉′), and its joint integral converges. -/
def JointHasLim (F : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), QED.TwoLoop.jointEnergyFirstIntegrable 2 (F ε)) ∧
    ∃ L : ℂ, Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (F ε)) (𝓝[>] 0) (𝓝 L)

namespace JointHasLim

variable {F G : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ}

theorem add (hF : JointHasLim F) (hG : JointHasLim G) :
    JointHasLim fun ε ℓ => F ε ℓ + G ε ℓ := by
  obtain ⟨hF1, L, hL⟩ := hF
  obtain ⟨hG1, K, hK⟩ := hG
  refine ⟨?_, L + K, (hL.add hK).congr' ?_⟩
  · filter_upwards [hF1, hG1] with ε h1 h2
    exact QED.TwoLoop.ClassIntegrable.jointEnergyFirstIntegrable_add h1 h2
  · filter_upwards [hF1, hG1] with ε h1 h2
    exact (jointEnergyFirstIntegral_add h1 h2).symm

theorem mul_left {a : ℝ → ℂ} {a₀ : ℂ} (ha : Tendsto a (𝓝[>] 0) (𝓝 a₀)) (hF : JointHasLim F) :
    JointHasLim fun ε ℓ => a ε * F ε ℓ := by
  obtain ⟨hF1, L, hL⟩ := hF
  refine ⟨?_, a₀ * L, (ha.mul hL).congr' (Eventually.of_forall fun ε => ?_)⟩
  · filter_upwards [hF1] with ε h1
    exact jointEnergyFirstIntegrable_const_mul _ h1
  · exact (jointEnergyFirstIntegral_const_mul _ _).symm

theorem const_mul (c : ℂ) (hF : JointHasLim F) : JointHasLim fun ε ℓ => c * F ε ℓ :=
  mul_left tendsto_const_nhds hF

theorem eps_mul (hF : JointHasLim F) : JointHasLim fun ε ℓ => (ε : ℂ) * F ε ℓ :=
  mul_left ((Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero).mono_left
    nhdsWithin_le_nhds) hF

theorem congr (hF : JointHasLim F) (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ℓ, F ε ℓ = G ε ℓ) :
    JointHasLim G := by
  obtain ⟨hF1, L, hL⟩ := hF
  have hFG : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε = G ε := h.mono fun ε hε => funext hε
  refine ⟨?_, L, hL.congr' ?_⟩
  · filter_upwards [hF1, hFG] with ε h1 h2
    rwa [← h2]
  · filter_upwards [hFG] with ε h2
    rw [h2]

end JointHasLim

/-! ### Pieces on rows of the `VP` matrix -/

/-- **The limit of a piece on rows of the `VP` matrix**: with at least eight lines, the refined
criterion for the numerator lines `E`, an `ε`-independent numerator of degree at most four with
the pointwise bound for `E`, and `V ≥ c > 0` on the simplex. -/
theorem jointHasLim_vpRows {m : ℕ} (hm : 7 ≤ m) (σ : Fin (m + 1) → Fin 6) (Ms : Fin (m + 1) → ℝ)
    (p p' : Fin 4 → ℝ) {E : Finset (Fin (m + 1))}
    (hcrit : IntNoSubdivergenceRefined 2 E fun i => class5LoopMatrix .VP (σ i))
    {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hpoly : IsLoopPoly 2 4 F)
    (hB : RefinedBound (castLoopMatrix fun i => class5LoopMatrix .VP (σ i)) E 4 F) {c : ℝ}
    (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (castLoopMatrix fun i => class5LoopMatrix .VP (σ i)) z ≠ 0 →
      c ≤ symanzikV (castLoopMatrix fun i => class5LoopMatrix .VP (σ i))
        (fun i => classVPMomenta p p' (σ i)) Ms z) :
    JointHasLim fun ε ℓ => F ℓ * ∏ i, (propDenom (Ms i) ε (classLineVP p p' (σ i) ℓ))⁻¹ := by
  refine ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact jointEnergyFirstIntegrable_vpRows hm σ Ms hε p p' hcrit hpoly hB
  · obtain ⟨Q, rfl⟩ := hpoly.exists_loopQuartic
    exact ⟨_, tendsto_jointEnergyFirstIntegral_of_refined Q
      (castLoopMatrix fun i => class5LoopMatrix .VP (σ i)) (fun i => classVPMomenta p p' (σ i)) Ms
      hm ((noSubdivergenceRefined_castLoopMatrix_iff 2 _ _).mpr hcrit) hB hc hV⟩

/-- **`V ≥ (3/4) min(m², m_γ²)` on rows of the `VP` matrix**, for on-shell `p, p'` with
`(p' - p)² ≥ 0` and masses at least those of `VP` with loop mass `m` and photon masses `m_γ`. -/
theorem symanzikV_vpRows_ge {m : ℕ} (σ : Fin (m + 1) → Fin 6) (Ms : Fin (m + 1) → ℝ)
    {mass mγ : ℝ} (hM : ∀ i, classVPMasses mass mass mγ mγ (σ i) ^ 2 ≤ Ms i ^ 2)
    {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -mass ^ 2) (hp' : Minkowski.dot p' p' = -mass ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (z : Fin (m + 1) → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hz1 : ∑ i, z i = 1)
    (hU : symanzikU (castLoopMatrix fun i => class5LoopMatrix .VP (σ i)) z ≠ 0) :
    3 / 4 * min (mass ^ 2) (mγ ^ 2) ≤ symanzikV (castLoopMatrix fun i => class5LoopMatrix .VP (σ i))
      (fun i => classVPMomenta p p' (σ i)) Ms z :=
  QED.Integration.TwoLoop.le_symanzikV_comp_of (σ := σ) (α := loopMatrixVP)
    (fun _ hw hw1 hU' =>
      QED.Integration.TwoLoop.symanzikV_classVP_ge le_rfl hp hp' hq le_rfl le_rfl hw hw1 hU')
    hM hz hz1 hU

/-! ### The `VP` shapes with extra photon denominators -/

section VPExt

variable (P : Params)

/-- The mass condition of `symanzikV_vpRows_ge` for the `VP` shapes with one extra photon line
of mass `M ≥ m_γ`. -/
theorem vpExt1Masses_ge (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2)
    (hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2) {M : ℝ} (hM : P.mγ ^ 2 ≤ M ^ 2) (t : Fin 4) (i : Fin 11) :
    classVPMasses P.m P.m P.mγ P.mγ (vpExt1Lines t i) ^ 2 ≤ vpExt1Masses P t M i ^ 2 := by
  fin_cases t <;> fin_cases i <;>
    simp [classVPMasses, vpExt1Lines, vpExt1Masses, vpShapeLines, vpShapeMasses, h₁, h₂, hΛ, hM]

/-- The mass condition for two extra photon lines of masses `M, M' ≥ m_γ`. -/
theorem vpExt2Masses_ge (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2)
    (hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2) {M M' : ℝ} (hM : P.mγ ^ 2 ≤ M ^ 2) (hM' : P.mγ ^ 2 ≤ M' ^ 2)
    (t : Fin 4) (i : Fin 12) :
    classVPMasses P.m P.m P.mγ P.mγ (vpExt2Lines t i) ^ 2 ≤ vpExt2Masses P t M M' i ^ 2 := by
  fin_cases t <;> fin_cases i <;>
    simp [classVPMasses, vpExt2Lines, vpExt2Masses, vpShapeLines, vpShapeMasses, h₁, h₂, hΛ, hM,
      hM']

end VPExt

/-! ### The sums over the `VP` shapes -/

section VPSum

variable (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4)

/-- The numerator of the `VP` shapes `0, 1, 2`. -/
noncomputable def vpLow (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  vpBubbleCoeff P * (vpE0 P pIn kIn αOut βIn μ ℓ +
    ((P.m ^ 2 : ℝ) : ℂ) * vpE2 P pIn kIn αOut βIn μ ℓ)

/-- The `ε`-independent part of the numerator of shape `3` with line `i` at `ε = 0`. -/
noncomputable def vpHigh (i : Fin 10) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  -(vpBubbleCoeff P * vpE2 P pIn kIn αOut βIn μ ℓ *
    vpDenom { P with ε := 0 } 3 (pIn 0) (pOut 0) i ℓ)

/-- The coefficient of `ε` in the numerator of shape `3`. -/
noncomputable def vpEps (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  2 * I * (vpBubbleCoeff P * vpE2 P pIn kIn αOut βIn μ ℓ)

/-- **The numerators of the four `VP` shapes in `ε`-independent parts.** -/
theorem vpTermNumer_split (ε : ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) (X : Fin 4 → ℂ) :
    ∑ t : Fin 4, vpTermNumer { P with ε := ε } pOut pIn kIn αOut βIn μ t ℓ * X t =
      vpLow P pIn kIn αOut βIn μ ℓ * X 0 + vpLow P pIn kIn αOut βIn μ ℓ * X 1 +
        vpLow P pIn kIn αOut βIn μ ℓ * X 2 + vpHigh P pOut pIn kIn αOut βIn μ 8 ℓ * X 3 +
        vpHigh P pOut pIn kIn αOut βIn μ 3 ℓ * X 3 +
        (ε : ℂ) * (vpEps P pIn kIn αOut βIn μ ℓ * X 3) := by
  have hD : ∀ i : Fin 10, vpDenom { P with ε := ε } 3 (pIn 0) (pOut 0) i ℓ =
      vpDenom { P with ε := 0 } 3 (pIn 0) (pOut 0) i ℓ - (ε : ℂ) * I := fun i =>
    lineDenom_eps _ _ _ ε i ℓ
  have hE0 : vpE0 { P with ε := ε } pIn kIn αOut βIn μ ℓ = vpE0 P pIn kIn αOut βIn μ ℓ := rfl
  have hE2 : vpE2 { P with ε := ε } pIn kIn αOut βIn μ ℓ = vpE2 P pIn kIn αOut βIn μ ℓ := rfl
  have hK : vpBubbleCoeff { P with ε := ε } = vpBubbleCoeff P := rfl
  simp only [Fin.sum_univ_four, vpTermNumer, Fin.reduceEq, ↓reduceIte, hD, hE0, hE2, hK, vpLow,
    vpHigh, vpEps]
  ring

/-- The numerator bounds of the parts. -/
theorem vpParts_bounds :
    (IsLoopPoly 2 4 (vpLow P pIn kIn αOut βIn μ) ∧ ∀ t : Fin 4,
      RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1, 2, 3} 4
        (vpLow P pIn kIn αOut βIn μ)) ∧
    (IsLoopPoly 2 4 (vpHigh P pOut pIn kIn αOut βIn μ 8) ∧
      RefinedBound (castLoopMatrix (vpShapeMatrix 3)) {0, 1, 2, 8} 4
        (vpHigh P pOut pIn kIn αOut βIn μ 8)) ∧
    (IsLoopPoly 2 4 (vpHigh P pOut pIn kIn αOut βIn μ 3) ∧
      RefinedBound (castLoopMatrix (vpShapeMatrix 3)) {0, 1, 3, 9} 4
        (vpHigh P pOut pIn kIn αOut βIn μ 3)) ∧
    (IsLoopPoly 2 4 (vpEps P pIn kIn αOut βIn μ) ∧
      RefinedBound (castLoopMatrix (vpShapeMatrix 3)) {0, 1, 2, 3} 4
        (vpEps P pIn kIn αOut βIn μ)) := by
  obtain ⟨hlow, hpoly3, hB8, hB3⟩ := vpTerm_bounds { P with ε := 0 } pOut pIn kIn αOut βIn μ 1
  simp only [one_mul] at hlow hpoly3 hB8 hB3
  refine ⟨⟨(hlow 0).1, fun t => (hlow t).2⟩, ⟨hpoly3 8, hB8⟩, ⟨hpoly3 3, hB3⟩, ?_, ?_⟩
  · exact (((isLoopPoly_vpE2 P pIn kIn αOut βIn μ).mono (by norm_num)).const_mul _).const_mul _
  · exact (((refinedBound_vpE2 3 P pIn kIn αOut βIn μ).mono (by decide) (by norm_num)).const_mul
      _).const_mul _

variable {P}

/-- **The `VP` shapes with one extra photon denominator converge**, for on-shell `p = pIn 0`,
`p' = pOut 0` with `(p' - p)² ≥ 0`, `m, m_γ > 0`, `M₁, M₂ ≥ m`, `Λ ≥ m_γ` and `M ≥ m_γ`. -/
theorem jointHasLim_vpSum_ext1 (hm : 0 < P.m) (hmγ : 0 < P.mγ) (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2)
    (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) (hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2) {M : ℝ} (hM : P.mγ ^ 2 ≤ M ^ 2)
    (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
    (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (pOut 0 - pIn 0) (pOut 0 - pIn 0)) :
    JointHasLim fun ε ℓ => ∑ t : Fin 4, vpTermNumer { P with ε := ε } pOut pIn kIn αOut βIn μ t ℓ *
      ((∏ i : Fin 10, (vpDenom { P with ε := ε } t (pIn 0) (pOut 0) i ℓ)⁻¹) *
        (propDenom M ε (ℓ 1))⁻¹) := by
  have hc : 0 < 3 / 4 * min (P.m ^ 2) (P.mγ ^ 2) :=
    mul_pos (by norm_num) (lt_min (by positivity) (by positivity))
  have piece : ∀ (t : Fin 4) {E : Finset (Fin 10)}
      (_ : IntNoSubdivergenceRefined 2 (E.map Fin.castSuccEmb)
        fun i => class5LoopMatrix .VP (vpExt1Lines t i))
      {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (_ : IsLoopPoly 2 4 F)
      (_ : RefinedBound (castLoopMatrix (vpShapeMatrix t)) E 4 F),
      JointHasLim fun ε ℓ => F ℓ * ((∏ i : Fin 10, (vpDenom { P with ε := ε } t (pIn 0) (pOut 0) i
        ℓ)⁻¹) * (propDenom M ε (ℓ 1))⁻¹) := by
    intro t E hcrit F hpoly hB
    refine (jointHasLim_vpRows (by norm_num) (vpExt1Lines t) (vpExt1Masses P t M) (pIn 0) (pOut 0)
      hcrit hpoly (RefinedBound.map_rows _ (vpExt1_rows t) hB) hc
      (symanzikV_vpRows_ge _ _ (vpExt1Masses_ge P h₁ h₂ hΛ hM t) hp hp' hq)).congr
      (Eventually.of_forall fun ε ℓ => ?_)
    exact congrArg (F ℓ * ·) (prod_vpExt1 { P with ε := ε } t M (pIn 0) (pOut 0) ℓ)
  obtain ⟨⟨hpL, hBL⟩, ⟨hp8, hB8⟩, ⟨hp3, hB3⟩, ⟨hpE, hBE⟩⟩ :=
    vpParts_bounds P pOut pIn kIn αOut βIn μ
  have h := (((((piece 0 (crit_vpExt1 0) hpL (hBL 0)).add (piece 1 (crit_vpExt1 1) hpL
    (hBL 1))).add (piece 2 (crit_vpExt1 2) hpL (hBL 2))).add
      (piece 3 crit_vpExt1_three.1 hp8 hB8)).add (piece 3 crit_vpExt1_three.2 hp3 hB3)).add
        (piece 3 (crit_vpExt1 3) hpE hBE).eps_mul
  refine h.congr (Eventually.of_forall fun ε ℓ => ?_)
  exact (vpTermNumer_split P pOut pIn kIn αOut βIn μ ε ℓ fun t =>
    (∏ i : Fin 10, (vpDenom { P with ε := ε } t (pIn 0) (pOut 0) i ℓ)⁻¹) *
      (propDenom M ε (ℓ 1))⁻¹).symm

/-- **The `VP` shapes with two extra photon denominators converge**, as
`jointHasLim_vpSum_ext1`, with `M, M' ≥ m_γ`. -/
theorem jointHasLim_vpSum_ext2 (hm : 0 < P.m) (hmγ : 0 < P.mγ) (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2)
    (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) (hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2) {M M' : ℝ} (hM : P.mγ ^ 2 ≤ M ^ 2)
    (hM' : P.mγ ^ 2 ≤ M' ^ 2) (hp : Minkowski.dot (pIn 0) (pIn 0) = -P.m ^ 2)
    (hp' : Minkowski.dot (pOut 0) (pOut 0) = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (pOut 0 - pIn 0) (pOut 0 - pIn 0)) :
    JointHasLim fun ε ℓ => ∑ t : Fin 4, vpTermNumer { P with ε := ε } pOut pIn kIn αOut βIn μ t ℓ *
      ((∏ i : Fin 10, (vpDenom { P with ε := ε } t (pIn 0) (pOut 0) i ℓ)⁻¹) *
        ((propDenom M ε (ℓ 1))⁻¹ * (propDenom M' ε (ℓ 1))⁻¹)) := by
  have hc : 0 < 3 / 4 * min (P.m ^ 2) (P.mγ ^ 2) :=
    mul_pos (by norm_num) (lt_min (by positivity) (by positivity))
  have piece : ∀ (t : Fin 4) {E : Finset (Fin 10)}
      (_ : IntNoSubdivergenceRefined 2 (E.map (Fin.castLEEmb (by norm_num : 10 ≤ 12)))
        fun i => class5LoopMatrix .VP (vpExt2Lines t i))
      {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (_ : IsLoopPoly 2 4 F)
      (_ : RefinedBound (castLoopMatrix (vpShapeMatrix t)) E 4 F),
      JointHasLim fun ε ℓ => F ℓ * ((∏ i : Fin 10, (vpDenom { P with ε := ε } t (pIn 0) (pOut 0) i
        ℓ)⁻¹) * ((propDenom M ε (ℓ 1))⁻¹ * (propDenom M' ε (ℓ 1))⁻¹)) := by
    intro t E hcrit F hpoly hB
    refine (jointHasLim_vpRows (by norm_num) (vpExt2Lines t) (vpExt2Masses P t M M') (pIn 0)
      (pOut 0) hcrit hpoly (RefinedBound.map_rows _ (vpExt2_rows t) hB) hc
      (symanzikV_vpRows_ge _ _ (vpExt2Masses_ge P h₁ h₂ hΛ hM hM' t) hp hp' hq)).congr
      (Eventually.of_forall fun ε ℓ => ?_)
    exact congrArg (F ℓ * ·) (prod_vpExt2 { P with ε := ε } t M M' (pIn 0) (pOut 0) ℓ)
  obtain ⟨⟨hpL, hBL⟩, ⟨hp8, hB8⟩, ⟨hp3, hB3⟩, ⟨hpE, hBE⟩⟩ :=
    vpParts_bounds P pOut pIn kIn αOut βIn μ
  have h := (((((piece 0 (crit_vpExt2 0) hpL (hBL 0)).add (piece 1 (crit_vpExt2 1) hpL
    (hBL 1))).add (piece 2 (crit_vpExt2 2) hpL (hBL 2))).add
      (piece 3 crit_vpExt2_three.1 hp8 hB8)).add (piece 3 crit_vpExt2_three.2 hp3 hB3)).add
        (piece 3 (crit_vpExt2 3) hpE hBE).eps_mul
  refine h.congr (Eventually.of_forall fun ε ℓ => ?_)
  exact (vpTermNumer_split P pOut pIn kIn αOut βIn μ ε ℓ fun t =>
    (∏ i : Fin 10, (vpDenom { P with ε := ε } t (pIn 0) (pOut 0) i ℓ)⁻¹) *
      ((propDenom M ε (ℓ 1))⁻¹ * (propDenom M' ε (ℓ 1))⁻¹)).symm

end VPSum

/-! ### The longitudinal pieces -/

section LPieces

/-- **The limit of a longitudinal piece of `repBD`** (the piece of
`QED.ChainProof.RepsInt.jointEnergyFirstIntegrable_bdPiece`), given `V ≥ c > 0`. -/
theorem jointHasLim_bdPiece (P : Params) {m : ℕ} (hm : 7 ≤ m)
    (σ : Fin (m + 1) → Fin 6) (Ms : Fin (m + 1) → ℝ) (p kext : Fin 4 → ℝ)
    (μ α β : Fin 4) (eV : Fin (m + 1)) {V : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hV : IsLoopAffine V)
    (h0 : σ 0 = 0) (h1 : σ 1 = 1) (h2 : σ 2 = 4)
    (hVe : ∀ ℓ, V ℓ = classLineVP p (p + kext) (σ eV) ℓ) (h10 : (1 : Fin (m + 1)) ≠ 0)
    (h2E : (2 : Fin (m + 1)) ∉ ({1, 0} : Finset (Fin (m + 1))))
    (hVE : eV ∉ ({1, 0} : Finset (Fin (m + 1)))) (h2V : (2 : Fin (m + 1)) ≠ eV)
    (hcrit : IntNoSubdivergenceRefined 2 ({1, 0} ∪ {2} ∪ {eV}) fun i => class5LoopMatrix .VP (σ i))
    (κ : ℂ) {c : ℝ} (hc : 0 < c)
    (hVs : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (castLoopMatrix fun i => class5LoopMatrix .VP (σ i)) z ≠ 0 →
      c ≤ symanzikV (castLoopMatrix fun i => class5LoopMatrix .VP (σ i))
        (fun i => classVPMomenta p (p + kext) (σ i)) Ms z) :
    JointHasLim fun ε ℓ =>
      (κ * bdN P p kext μ α β (-ℓ 1) (V ℓ)) *
        ∏ i, (propDenom (Ms i) ε (classLineVP p (p + kext) (σ i) ℓ))⁻¹ := by
  set al := castLoopMatrix fun i => class5LoopMatrix .VP (σ i)
  set pp : Fin (m + 1) → Fin 4 → ℝ := fun i => classVPMomenta p (p + kext) (σ i)
  have hlm : ∀ e ℓ, lineMomentum al pp e ℓ = classLineVP p (p + kext) (σ e) ℓ := fun _ _ => rfl
  have r0 : ∀ ℓ, classLineVP p (p + kext) 0 ℓ = p - -ℓ 1 := fun ℓ => (classLineVP_rows _ _ ℓ).1
  have r1 : ∀ ℓ, classLineVP p (p + kext) 1 ℓ = p + kext - -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.1
  have r4 : ∀ ℓ, classLineVP p (p + kext) 4 ℓ = -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.2.2.2.1
  have hpoly : IsLoopPoly 2 4 fun ℓ => κ * bdN P p kext μ α β (-ℓ 1) (V ℓ) := by
    refine IsLoopPoly.const_mul κ ?_
    unfold bdN bdON
    exact isLoopPoly_contract P.m isLoopAffine_neg_one hV
      (IsLoopAffine.const_sub' isLoopAffine_neg_one (p + kext))
      (IsLoopAffine.const_sub' isLoopAffine_neg_one p)
      Dirac.gamma Dirac.gamma (Dirac.gamma μ) α β
  have hB : RefinedBound al ({1, 0} ∪ {2} ∪ {eV}) 4 fun ℓ =>
      κ * bdN P p kext μ α β (-ℓ 1) (V ℓ) := by
    refine RefinedBound.const_mul κ ?_
    unfold bdN bdON
    refine refinedBound_contract' al pp h2E hVE h2V (fun ℓ => -ℓ 1) V
      (fun ℓ => by rw [hlm, h2, r4]) (fun ℓ => by rw [hlm, hVe]) _ fun l0 l2 => ?_
    exact refinedBound_openNum al pp h10 P.m (fun ℓ => p + kext - -ℓ 1) (fun ℓ => p - -ℓ 1)
      (fun ℓ => by rw [hlm, h1, r1]) (fun ℓ => by rw [hlm, h0, r0]) _ _ _ α β
  exact jointHasLim_vpRows hm σ Ms p (p + kext) hcrit hpoly hB hc hVs

/-- **The limit of a longitudinal piece of `repDB`**, as `jointHasLim_bdPiece` with the
numerator `dbN`. -/
theorem jointHasLim_dbPiece (P : Params) {m : ℕ} (hm : 7 ≤ m)
    (σ : Fin (m + 1) → Fin 6) (Ms : Fin (m + 1) → ℝ) (p kext : Fin 4 → ℝ)
    (μ α β : Fin 4) (eV : Fin (m + 1)) {V : (Fin 2 → Fin 4 → ℝ) → Fin 4 → ℝ} (hV : IsLoopAffine V)
    (h0 : σ 0 = 0) (h1 : σ 1 = 1) (h2 : σ 2 = 4)
    (hVe : ∀ ℓ, V ℓ = classLineVP p (p + kext) (σ eV) ℓ) (h10 : (1 : Fin (m + 1)) ≠ 0)
    (h2E : (2 : Fin (m + 1)) ∉ ({1, 0} : Finset (Fin (m + 1))))
    (hVE : eV ∉ ({1, 0} : Finset (Fin (m + 1)))) (h2V : (2 : Fin (m + 1)) ≠ eV)
    (hcrit : IntNoSubdivergenceRefined 2 ({1, 0} ∪ {2} ∪ {eV}) fun i => class5LoopMatrix .VP (σ i))
    (κ : ℂ) {c : ℝ} (hc : 0 < c)
    (hVs : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (castLoopMatrix fun i => class5LoopMatrix .VP (σ i)) z ≠ 0 →
      c ≤ symanzikV (castLoopMatrix fun i => class5LoopMatrix .VP (σ i))
        (fun i => classVPMomenta p (p + kext) (σ i)) Ms z) :
    JointHasLim fun ε ℓ =>
      (κ * dbN P p kext μ α β (-ℓ 1) (V ℓ)) *
        ∏ i, (propDenom (Ms i) ε (classLineVP p (p + kext) (σ i) ℓ))⁻¹ := by
  set al := castLoopMatrix fun i => class5LoopMatrix .VP (σ i)
  set pp : Fin (m + 1) → Fin 4 → ℝ := fun i => classVPMomenta p (p + kext) (σ i)
  have hlm : ∀ e ℓ, lineMomentum al pp e ℓ = classLineVP p (p + kext) (σ e) ℓ := fun _ _ => rfl
  have r0 : ∀ ℓ, classLineVP p (p + kext) 0 ℓ = p - -ℓ 1 := fun ℓ => (classLineVP_rows _ _ ℓ).1
  have r1 : ∀ ℓ, classLineVP p (p + kext) 1 ℓ = p + kext - -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.1
  have r4 : ∀ ℓ, classLineVP p (p + kext) 4 ℓ = -ℓ 1 := fun ℓ =>
    (classLineVP_rows _ _ ℓ).2.2.2.2.1
  simp only [dbN_eq_contract]
  have hpoly : IsLoopPoly 2 4 fun ℓ => κ * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      bdON P p kext (-ℓ 1) μ b a α β * ((Minkowski.metric b c : ℝ) : ℂ) *
        ((Minkowski.lower (-ℓ 1) a : ℝ) : ℂ) * ((V ℓ c : ℝ) : ℂ) := by
    refine IsLoopPoly.const_mul κ (isLoopPoly_contract' isLoopAffine_neg_one hV _ fun a b => ?_)
    unfold bdON
    have hm : IsLoopPolyMat 2 (0 + 1 + 0 + 1 + 0) fun ℓ : Fin 2 → Fin 4 → ℝ =>
        Dirac.gamma a * electronNumerator P.m (p + kext - -ℓ 1) * Dirac.gamma μ *
          electronNumerator P.m (p - -ℓ 1) * Dirac.gamma b :=
      ((((IsLoopPolyMat.const _).mul ((IsLoopAffine.const_sub' isLoopAffine_neg_one
        (p + kext)).isLoopPolyMat_electronNumerator P.m)).mul (IsLoopPolyMat.const _)).mul
          ((IsLoopAffine.const_sub' isLoopAffine_neg_one p).isLoopPolyMat_electronNumerator
            P.m)).mul (IsLoopPolyMat.const _)
    exact hm α β
  have hB : RefinedBound al ({1, 0} ∪ {2} ∪ {eV}) 4 fun ℓ => κ * ∑ a : Fin 4, ∑ b : Fin 4,
      ∑ c : Fin 4, bdON P p kext (-ℓ 1) μ b a α β * ((Minkowski.metric b c : ℝ) : ℂ) *
        ((Minkowski.lower (-ℓ 1) a : ℝ) : ℂ) * ((V ℓ c : ℝ) : ℂ) := by
    refine RefinedBound.const_mul κ ?_
    refine refinedBound_contract' al pp h2E hVE h2V (fun ℓ => -ℓ 1) V
      (fun ℓ => by rw [hlm, h2, r4]) (fun ℓ => by rw [hlm, hVe])
      (fun ℓ a b => bdON P p kext (-ℓ 1) μ b a α β) fun a b => ?_
    unfold bdON
    exact refinedBound_openNum al pp h10 P.m (fun ℓ => p + kext - -ℓ 1) (fun ℓ => p - -ℓ 1)
      (fun ℓ => by rw [hlm, h1, r1]) (fun ℓ => by rw [hlm, h0, r0]) _ _ _ α β
  exact jointHasLim_vpRows hm σ Ms p (p + kext) hcrit hpoly hB hc hVs

/-- The mass condition of `symanzikV_vpRows_ge` for the longitudinal pieces. -/
theorem massL_ge (P : Params) (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2)
    (hΛ : P.mγ ^ 2 ≤ P.Λ ^ 2) :
    (∀ i, classVPMasses P.m P.m P.mγ P.mγ (lineL1 i) ^ 2 ≤ massL1 P i ^ 2) ∧
    (∀ i, classVPMasses P.m P.m P.mγ P.mγ (lineL2 i) ^ 2 ≤ massL1 P i ^ 2) ∧
    (∀ i, classVPMasses P.m P.m P.mγ P.mγ (lineL3a i) ^ 2 ≤ massL3a P i ^ 2) ∧
    (∀ i, classVPMasses P.m P.m P.mγ P.mγ (lineL3b i) ^ 2 ≤ massL3b P i ^ 2) ∧
    (∀ i, classVPMasses P.m P.m P.mγ P.mγ (lineL3c i) ^ 2 ≤ massL3c P i ^ 2) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    simp [classVPMasses, lineL1, lineL2, lineL3a, lineL3b, lineL3c, massL1, massL3a, massL3b,
      massL3c, h₁, h₂, hΛ]

end LPieces

end QED.ChainProof.HCSide

end
