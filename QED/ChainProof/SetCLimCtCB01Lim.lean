/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLimCtCB01Bnd
public import QED.TwoLoop.LimitCovarianceVP

/-!
# Set (c): the `ε → 0⁺` limits of the classes `CB0`, `CB1`

Helper level for (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`. The integrand of
`CB0`, `CB1` in shape form (`QED.ChainProof.SetCPauli.CB01.cbIntegrand`) is
`-(T₁₀(N_a) + c T₁₁(N) + iε T₁₁(N_a))`, where `T₁₀(E)`, `T₁₁(E)` are the divided-difference sums
of a numerator pair `E = (E₀, E₂)` over the ten-line shapes of `VP` and over the eleven-line
doubled shapes (`integrand_cb_eq`). For any pair, as for `VP` (`cbTerm_split`, the pattern of
`QED.TwoLoop.ClassLimit.integrand_VP_eq`),

`(2π)⁻⁸ ∑ₜ Nₜ(E) ∏ D_{t,i}⁻¹ = ∑ⱼ cbPiece j (E) ∏ D_{sⱼ,i}⁻¹ + ε · cbEps (E) ∏ D_{3,i}⁻¹`,

with `ε`-independent pieces on the shapes `sⱼ = 0, 1, 2, 3, 3`. Each piece is a parametric value
(`QED.TwoLoop.LimitCovariance.IsParamValue`) on the data `vpData` (ten lines) or `cbData` (eleven
lines), so its integral converges, and the `ε` terms tend to `0`.

* `HasLimJ`: integrable at `ε > 0` with a limit of the joint integral; closed under sums,
  constant multiples and the factor `ε`;
* `hasLimJ_cbT10`, `hasLimJ_cbT11`: the two divided-difference sums of a bounded pair;
* **`tendsto_cbIntegrand`**: the joint integral of `(2π)⁻⁸ cbIntegrand` converges to
  `-(∑ⱼ vAⱼ + c ∑ⱼ vBⱼ)`, `vA` the values of the pieces of `N_a` on the ten-line shapes, `vB` those
  of `N` on the doubled shapes.
-/

@[expose] public section

open Complex Filter Topology
open scoped Real

namespace QED.ChainProof.SetCPauli.CB01

open QED.WickModel QED.TwoLoop.Bridge QED.TwoLoop.ClassIntegrable QED.TwoLoop.ClassLimit
open QED.TwoLoop.LimitCovariance (ParamData IsParamValue vpData)
open QED.ChainProof.SetCPauli (mergeY mergeC)
open QED.TwoLoop.CountertermLimit (isLoopPolyMat_add isLoopPolyMat_smul isLoopPolyMat_mono)
open QED.Integration.TwoLoop (lineDenom castLoopMatrix RefinedBound NoSubdivergenceRefined
  jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined)

/-! ### The `ε`-independent pieces of a numerator pair -/

/-- The `ε`-independent piece `j` of the numerator pair `(E₀, E₂)`, as `vpPieceNumer`:
`(2π)⁻⁸ K (E₀ + m² E₂)` on the shapes `0, 1, 2`, and `-(2π)⁻⁸ K E₂ D⁰_{3,8}`,
`-(2π)⁻⁸ K E₂ D⁰_{3,3}` on the shape `3`. -/
noncomputable def cbPiece (P : Params) (p p' : Fin 4 → ℝ) (E0 E2 : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (j : Fin 5) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  if j = 3 then
    twoLoopNorm * -(vpBubbleCoeff P * E2 ℓ * lineDenom (castLoopMatrix (vpShapeMatrix 3))
      (vpShapeMomenta 3 p p') (vpShapeMasses P 3) 0 8 ℓ)
  else if j = 4 then
    twoLoopNorm * -(vpBubbleCoeff P * E2 ℓ * lineDenom (castLoopMatrix (vpShapeMatrix 3))
      (vpShapeMomenta 3 p p') (vpShapeMasses P 3) 0 3 ℓ)
  else twoLoopNorm * (vpBubbleCoeff P * (E0 ℓ + ((P.m ^ 2 : ℝ) : ℂ) * E2 ℓ))

/-- The coefficient of `ε` in the shape-`3` numerator of the pair `(E₀, E₂)`: `2i (2π)⁻⁸ K E₂`. -/
noncomputable def cbEps (P : Params) (E2 : (Fin 2 → Fin 4 → ℝ) → ℂ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    ℂ :=
  2 * I * (twoLoopNorm * (vpBubbleCoeff P * E2 ℓ))

/-- **The divided-difference sum of a numerator pair in `ε`-independent pieces**, for any
denominator products `Dp`. -/
theorem cbTerm_split (P : Params) (ε : ℝ) (p p' : Fin 4 → ℝ) (E0 E2 : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (Dp : Fin 4 → ℂ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    twoLoopNorm * ∑ t : Fin 4, cbTermNumer { P with ε := ε } p p' (E0 ℓ) (E2 ℓ) t ℓ * Dp t =
      ∑ j : Fin 5, cbPiece P p p' E0 E2 j ℓ * Dp (vpPieceShape j) +
        (ε : ℂ) * (cbEps P E2 ℓ * Dp 3) := by
  have hD : ∀ i : Fin 10, vpDenom { P with ε := ε } 3 p p' i ℓ =
      lineDenom (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMomenta 3 p p') (vpShapeMasses P 3) ε
        i ℓ := fun _ => rfl
  have hK : vpBubbleCoeff { P with ε := ε } = vpBubbleCoeff P := rfl
  simp only [Fin.sum_univ_four, Fin.sum_univ_five, cbTermNumer, Fin.reduceEq, ↓reduceIte, hD, hK,
    cbPiece, cbEps, vpPieceShape, Matrix.cons_val]
  rw [lineDenom_eps _ _ _ ε 8, lineDenom_eps _ _ _ ε 3]
  ring

theorem cbTermNumer_lin (P : Params) (p p' : Fin 4 → ℝ) (a b x0 x2 y0 y2 : ℂ) (t : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbTermNumer P p p' (a * x0 + b * y0) (a * x2 + b * y2) t ℓ =
      a * cbTermNumer P p p' x0 x2 t ℓ + b * cbTermNumer P p p' y0 y2 t ℓ := by
  unfold cbTermNumer
  split_ifs <;> ring

/-- The pieces in coefficient form (`QED.TwoLoop.LimitCovariance.vpCoeff0`, `vpCoeff2`). -/
theorem cbPiece_eq (P : Params) (p p' : Fin 4 → ℝ) (E0 E2 : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (j : Fin 5) (ℓ : Fin 2 → Fin 4 → ℝ) :
    cbPiece P p p' E0 E2 j ℓ = QED.TwoLoop.LimitCovariance.vpCoeff0 P j * E0 ℓ +
      QED.TwoLoop.LimitCovariance.vpCoeff2 P p p' j ℓ * E2 ℓ := by
  simp only [cbPiece, QED.TwoLoop.LimitCovariance.vpCoeff0,
    QED.TwoLoop.LimitCovariance.vpCoeff2]
  fin_cases j <;> simp <;> ring

/-! ### The divided-difference sums and the integrand -/

/-- The divided-difference sum of the pair `(E₀, E₂)` over the ten-line shapes at `ε`. -/
noncomputable def cbT10 (P : Params) (ε : ℝ) (p p' : Fin 4 → ℝ)
    (E0 E2 : (Fin 2 → Fin 4 → ℝ) → ℂ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  twoLoopNorm * ∑ t : Fin 4, cbTermNumer { P with ε := ε } p p' (E0 ℓ) (E2 ℓ) t ℓ *
    ∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹

/-- The divided-difference sum of the pair `(E₀, E₂)` over the doubled shapes `(d, t)` at `ε`. -/
noncomputable def cbT11 (P : Params) (d : Fin 2) (ε : ℝ) (p p' : Fin 4 → ℝ)
    (E0 E2 : (Fin 2 → Fin 4 → ℝ) → ℂ) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  twoLoopNorm * ∑ t : Fin 4, cbTermNumer { P with ε := ε } p p' (E0 ℓ) (E2 ℓ) t ℓ *
    ∏ i : Fin 11, (cbDenom P d t p p' ε i ℓ)⁻¹

/-- **The integrand of `CB0`, `CB1` at prescription `ε`** as three divided-difference sums. -/
theorem integrand_cb_eq (P : Params) (ε : ℝ) (d : Fin 2) (p' p : Fin 4 → ℝ) (α β μ : Fin 4)
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * cbIntegrand { P with ε := ε } d p' p α β μ ℓ =
      -(cbT10 P ε p p' (cbEa0 P d p' p α β μ) (cbEa2 P d p' p α β μ) ℓ +
        mergeC P.m P.δ₂ P.δm * cbT11 P d ε p p' (cbEv0 P p' p α β μ) (cbEv2 P p' p α β μ) ℓ +
        (ε : ℂ) * I * cbT11 P d ε p p' (cbEa0 P d p' p α β μ) (cbEa2 P d p' p α β μ) ℓ) := by
  have h : ∀ t, cbTermNumer { P with ε := ε } p p'
      (mergeC P.m P.δ₂ P.δm * cbEv0 P p' p α β μ ℓ + (ε : ℂ) * I * cbEa0 P d p' p α β μ ℓ)
      (mergeC P.m P.δ₂ P.δm * cbEv2 P p' p α β μ ℓ + (ε : ℂ) * I * cbEa2 P d p' p α β μ ℓ) t ℓ =
      mergeC P.m P.δ₂ P.δm * cbTermNumer { P with ε := ε } p p' (cbEv0 P p' p α β μ ℓ)
          (cbEv2 P p' p α β μ ℓ) t ℓ +
        (ε : ℂ) * I * cbTermNumer { P with ε := ε } p p' (cbEa0 P d p' p α β μ ℓ)
          (cbEa2 P d p' p α β μ ℓ) t ℓ := fun t => cbTermNumer_lin _ _ _ _ _ _ _ _ _ _ _
  change (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ * -(∑ t : Fin 4, cbTermNumer { P with ε := ε } p p'
      (cbEa0 P d p' p α β μ ℓ) (cbEa2 P d p' p α β μ ℓ) t ℓ *
        ∏ i : Fin 10, (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹ +
    ∑ t : Fin 4, cbTermNumer { P with ε := ε } p p'
        (mergeC P.m P.δ₂ P.δm * cbEv0 P p' p α β μ ℓ + (ε : ℂ) * I * cbEa0 P d p' p α β μ ℓ)
        (mergeC P.m P.δ₂ P.δm * cbEv2 P p' p α β μ ℓ +
          (ε : ℂ) * I * cbEa2 P d p' p α β μ ℓ) t ℓ *
      ∏ i : Fin 11, (cbDenom P d t p p' ε i ℓ)⁻¹) = _
  simp only [h]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, cbT10, cbT11]
  ring

/-! ### Joint integrals with a limit -/

/-- `H ε` is jointly integrable for `ε > 0` and its joint integral tends to `a` as `ε → 0⁺`. -/
def HasLimJ (H : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ) (a : ℂ) : Prop :=
  (∀ ε : ℝ, 0 < ε → QED.TwoLoop.jointEnergyFirstIntegrable 2 (H ε)) ∧
    Tendsto (fun ε => QED.TwoLoop.jointEnergyFirstIntegral 2 (H ε)) (𝓝[>] 0) (𝓝 a)

namespace HasLimJ

variable {F G : ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ} {a b : ℂ}

theorem add (hF : HasLimJ F a) (hG : HasLimJ G b) :
    HasLimJ (fun ε ℓ => F ε ℓ + G ε ℓ) (a + b) := by
  refine ⟨fun ε hε => jointEnergyFirstIntegrable_add (hF.1 ε hε) (hG.1 ε hε),
    (hF.2.add hG.2).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (jointEnergyFirstIntegral_add (hF.1 ε hε) (hG.1 ε hε)).symm

theorem const_mul (c : ℂ) (hF : HasLimJ F a) : HasLimJ (fun ε ℓ => c * F ε ℓ) (c * a) :=
  ⟨fun ε hε => jointEnergyFirstIntegrable_const_mul c (hF.1 ε hε),
    (hF.2.const_mul c).congr fun ε => (jointEnergyFirstIntegral_const_mul c (F ε)).symm⟩

theorem eps_mul (hF : HasLimJ F a) : HasLimJ (fun ε ℓ => (ε : ℂ) * F ε ℓ) 0 := by
  have hε0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    (Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero).mono_left nhdsWithin_le_nhds
  refine ⟨fun ε hε => jointEnergyFirstIntegrable_const_mul _ (hF.1 ε hε), ?_⟩
  have h := hε0.mul hF.2
  rw [zero_mul] at h
  exact h.congr fun ε => (jointEnergyFirstIntegral_const_mul _ (F ε)).symm

theorem congr (hF : HasLimJ F a) (h : ∀ ε : ℝ, 0 < ε → F ε = G ε) : HasLimJ G a := by
  refine ⟨fun ε hε => h ε hε ▸ hF.1 ε hε, hF.2.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [h ε hε]

theorem zero : HasLimJ (fun _ _ => 0) 0 := by
  refine ⟨fun _ _ => ⟨fun _ => MeasureTheory.integrable_zero _ _ _, ?_⟩, ?_⟩
  · simp only [MeasureTheory.integral_zero]
    exact MeasureTheory.integrable_zero _ _ _
  · simp only [QED.TwoLoop.jointEnergyFirstIntegral, MeasureTheory.integral_zero]
    exact tendsto_const_nhds

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → (Fin 2 → Fin 4 → ℝ) → ℂ} {a : ι → ℂ}
    (h : ∀ k ∈ s, HasLimJ (F k) (a k)) :
    HasLimJ (fun ε ℓ => ∑ k ∈ s, F k ε ℓ) (∑ k ∈ s, a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (h k (Finset.mem_insert_self k s)).add
      (ih fun k' hk' => h k' (Finset.mem_insert_of_mem hk'))

end HasLimJ

/-- A parametric value gives a joint integral with a limit. -/
theorem hasLimJ_of_paramValue {D : ParamData} {F : (Fin 2 → Fin 4 → ℝ) → ℂ} {v : ℂ}
    (h : IsParamValue D F v) :
    HasLimJ (fun ε ℓ => F ℓ * ∏ i, (lineDenom D.α D.p D.M ε i ℓ)⁻¹) v := by
  refine ⟨fun ε hε => ?_, h.tendsto⟩
  obtain ⟨Q, rfl, hB, -⟩ := h
  exact jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
    Q D.α D.p D.M D.hm hε D.hcrit hB

/-- A bounded polynomial numerator has a parametric value. -/
theorem exists_paramValue (D : ParamData) {F : (Fin 2 → Fin 4 → ℝ) → ℂ} (hP : IsLoopPoly 2 4 F)
    (hB : RefinedBound D.α D.E 4 F) : ∃ v, IsParamValue D F v := by
  obtain ⟨Q, hQ⟩ := hP.exists_loopQuartic
  exact ⟨_, Q, hQ, hB, rfl⟩

/-! ### Bounds and degrees of the pieces -/

theorem isLoopPoly_cbPiece (P : Params) (p p' : Fin 4 → ℝ) {E0 E2 : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (hp0 : IsLoopPoly 2 4 E0) (hp2 : IsLoopPoly 2 2 E2) (j : Fin 5) :
    IsLoopPoly 2 4 (cbPiece P p p' E0 E2 j) := by
  have h3 : ∀ i : Fin 10, IsLoopPoly 2 4 fun ℓ => twoLoopNorm * -(vpBubbleCoeff P * E2 ℓ *
      lineDenom (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMomenta 3 p p') (vpShapeMasses P 3) 0
        i ℓ) := fun i => by
    have hD : IsLoopPoly 2 2 fun ℓ => lineDenom (castLoopMatrix (vpShapeMatrix 3))
        (vpShapeMomenta 3 p p') (vpShapeMasses P 3) 0 i ℓ :=
      isLoopPoly_vpDenom { P with ε := 0 } 3 p p' i
    have h := (((hp2.const_mul (vpBubbleCoeff P)).mul hD).const_mul (-twoLoopNorm)).mono
      (by norm_num : 2 + 2 ≤ 4)
    refine (congrArg (IsLoopPoly 2 4) (funext fun ℓ => ?_)).mp h
    ring
  unfold cbPiece
  split_ifs
  · exact h3 8
  · exact h3 3
  · exact (((hp0.add ((hp2.mono (by norm_num)).const_mul _)).const_mul _).const_mul _)

theorem isLoopPoly_cbEps (P : Params) {E2 : (Fin 2 → Fin 4 → ℝ) → ℂ} (hp2 : IsLoopPoly 2 2 E2) :
    IsLoopPoly 2 4 (cbEps P E2) :=
  (((hp2.mono (by norm_num)).const_mul _).const_mul _).const_mul _

/-- **The pointwise bound of the pieces** of a pair bounded as the numerators of `VP`. -/
theorem refinedBound_cbPiece (P : Params) (p p' : Fin 4 → ℝ) {E0 E2 : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h0 : ∀ t, RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1, 2, 3} 4 E0)
    (h2 : ∀ t, RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1} 2 E2) (j : Fin 5) :
    RefinedBound (castLoopMatrix (vpShapeMatrix (vpPieceShape j))) (vpPieceLines j) 4
      (cbPiece P p p' E0 E2 j) := by
  have hlow : ∀ t : Fin 4, RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1, 2, 3} 4
      fun ℓ => twoLoopNorm * (vpBubbleCoeff P * (E0 ℓ + ((P.m ^ 2 : ℝ) : ℂ) * E2 ℓ)) := fun t =>
    (((h0 t).add (((h2 t).mono (by decide) (by norm_num)).const_mul _)).const_mul _).const_mul _
  have hD8 : RefinedBound (castLoopMatrix (vpShapeMatrix 3)) ({8} ∪ {2}) 2
      fun ℓ => lineDenom (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMomenta 3 p p')
        (vpShapeMasses P 3) 0 8 ℓ :=
    refinedBound_lineDenom_of_eq _ _ _ 0 (by decide) fun ℓ => rfl
  have hD3 : RefinedBound (castLoopMatrix (vpShapeMatrix 3)) ({3} ∪ {9}) 2
      fun ℓ => lineDenom (castLoopMatrix (vpShapeMatrix 3)) (vpShapeMomenta 3 p p')
        (vpShapeMasses P 3) 0 3 ℓ :=
    refinedBound_lineDenom_of_eq _ _ _ 0 (by decide) fun ℓ => rfl
  fin_cases j
  · exact hlow 0
  · exact hlow 1
  · exact hlow 2
  · exact (((((h2 3).const_mul _).mul hD8 (by decide)).mono (by decide)
      (by norm_num)).neg).const_mul _
  · exact (((((h2 3).const_mul _).mul hD3 (by decide)).mono (by decide)
      (by norm_num)).neg).const_mul _

theorem refinedBound_cbEps (P : Params) {E2 : (Fin 2 → Fin 4 → ℝ) → ℂ}
    (h2 : RefinedBound (castLoopMatrix (vpShapeMatrix 3)) {0, 1} 2 E2) :
    RefinedBound (castLoopMatrix (vpShapeMatrix (vpPieceShape 3))) (vpPieceLines 3) 4
      (cbEps P E2) :=
  (((h2.mono (by decide) (by norm_num)).const_mul _).const_mul _).const_mul _

/-! ### The parametric data of the doubled shapes -/

theorem noSubdivergenceRefined_cbPiece (d : Fin 2) (j : Fin 5) :
    NoSubdivergenceRefined 2 ((vpPieceLines j).map Fin.castSuccEmb)
      (castLoopMatrix (cbShapeMatrix d (vpPieceShape j))) := by
  have key : ∀ (E E' : Finset (Fin 11)) (α : Fin 11 → Fin 2 → ℝ), E = E' →
      NoSubdivergenceRefined 2 E' α → NoSubdivergenceRefined 2 E α := fun _ _ _ h h' => h ▸ h'
  fin_cases j
  · exact key _ _ _ (by decide) (noSubdivergenceRefined_cbShape d 0)
  · exact key _ _ _ (by decide) (noSubdivergenceRefined_cbShape d 1)
  · exact key _ _ _ (by decide) (noSubdivergenceRefined_cbShape d 2)
  · exact key _ _ _ (by decide) (noSubdivergenceRefined_cbShape_three d).1
  · exact key _ _ _ (by decide) (noSubdivergenceRefined_cbShape_three d).2

/-- The parametric data of the `j`-th piece on the doubled shape `(d, sⱼ)`. -/
noncomputable def cbData (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hm : 0 < P.m)
    (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (d : Fin 2) (j : Fin 5) : ParamData where
  m := 10
  α := castLoopMatrix (cbShapeMatrix d (vpPieceShape j))
  p := cbShapeMomenta d (vpPieceShape j) p p'
  M := cbShapeMasses P (vpPieceShape j)
  E := (vpPieceLines j).map Fin.castSuccEmb
  hm := by norm_num
  hcrit := noSubdivergenceRefined_cbPiece d j
  c := 3 / 4 * min (P.m ^ 2) (min P.mγ P.Λ ^ 2)
  hc := mul_pos (by norm_num) (lt_min (by positivity) (pow_pos (lt_min hmγ hΛ) 2))
  hV := fun _ hz hz1 hU => symanzikV_cbShape_ge_min P hmγ hΛ h₁ h₂ d _ hp hp' hq hz hz1 hU

/-! ### The limits of the divided-difference sums -/

section Limits

variable (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hm : 0 < P.m) (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2)
  (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) {p p' : Fin 4 → ℝ} (hp : Minkowski.dot p p = -P.m ^ 2)
  (hp' : Minkowski.dot p' p' = -P.m ^ 2) (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p))
  {E0 E2 : (Fin 2 → Fin 4 → ℝ) → ℂ} (hp0 : IsLoopPoly 2 4 E0) (hp2 : IsLoopPoly 2 2 E2)
  (hB0 : ∀ t, RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1, 2, 3} 4 E0)
  (hB2 : ∀ t, RefinedBound (castLoopMatrix (vpShapeMatrix t)) {0, 1} 2 E2)
include hp0 hp2 hB0 hB2

/-- **The sum over the ten-line shapes**: its pieces are parametric values on `vpData`, and its
joint integral converges to their sum. -/
theorem hasLimJ_cbT10 :
    ∃ v : Fin 5 → ℂ, (∀ j, IsParamValue (vpData P hmγ hΛ hm h₁ h₂ hp hp' hq j)
        (cbPiece P p p' E0 E2 j) (v j)) ∧
      HasLimJ (fun ε => cbT10 P ε p p' E0 E2) (∑ j, v j) := by
  choose v hv using fun j => exists_paramValue (vpData P hmγ hΛ hm h₁ h₂ hp hp' hq j)
    (isLoopPoly_cbPiece P p p' hp0 hp2 j) (refinedBound_cbPiece P p p' hB0 hB2 j)
  obtain ⟨w, hw⟩ := exists_paramValue (vpData P hmγ hΛ hm h₁ h₂ hp hp' hq 3)
    (isLoopPoly_cbEps P hp2) (refinedBound_cbEps P (hB2 3))
  refine ⟨v, hv, ?_⟩
  have h := ((HasLimJ.sum Finset.univ fun j _ => hasLimJ_of_paramValue (hv j)).add
    (hasLimJ_of_paramValue hw).eps_mul)
  rw [add_zero] at h
  refine h.congr fun ε _ => funext fun ℓ => ?_
  rw [cbT10, cbTerm_split P ε p p' E0 E2 fun t => ∏ i : Fin 10,
    (vpDenom { P with ε := ε } t p p' i ℓ)⁻¹]
  rfl

/-- **The sum over the doubled shapes**: its pieces are parametric values on `cbData`, and its
joint integral converges to their sum. -/
theorem hasLimJ_cbT11 (d : Fin 2) :
    ∃ v : Fin 5 → ℂ, (∀ j, IsParamValue (cbData P hmγ hΛ hm h₁ h₂ hp hp' hq d j)
        (cbPiece P p p' E0 E2 j) (v j)) ∧
      HasLimJ (fun ε => cbT11 P d ε p p' E0 E2) (∑ j, v j) := by
  choose v hv using fun j => exists_paramValue (cbData P hmγ hΛ hm h₁ h₂ hp hp' hq d j)
    (isLoopPoly_cbPiece P p p' hp0 hp2 j)
    (refinedBound_cbShape d _ (refinedBound_cbPiece P p p' hB0 hB2 j))
  obtain ⟨w, hw⟩ := exists_paramValue (cbData P hmγ hΛ hm h₁ h₂ hp hp' hq d 3)
    (isLoopPoly_cbEps P hp2) (refinedBound_cbShape d _ (refinedBound_cbEps P (hB2 3)))
  refine ⟨v, hv, ?_⟩
  have h := ((HasLimJ.sum Finset.univ fun j _ => hasLimJ_of_paramValue (hv j)).add
    (hasLimJ_of_paramValue hw).eps_mul)
  rw [add_zero] at h
  refine h.congr fun ε _ => funext fun ℓ => ?_
  rw [cbT11, cbTerm_split P ε p p' E0 E2 fun t => ∏ i : Fin 11, (cbDenom P d t p p' ε i ℓ)⁻¹]
  rfl

end Limits

/-! ### Degrees of the numerator pairs -/

/-- The open-line matrices `A`, `Y` have degree one. -/
theorem isLoopPolyMat_cbLine (P : Params) (p' p : Fin 4 → ℝ) (i : Fin 2) :
    IsLoopPolyMat 2 1 (fun ℓ => electronNumerator P.m (cbMom p' p ℓ i)) ∧
      IsLoopPolyMat 2 1 (fun ℓ => mergeY P.m P.δ₂ P.δm (cbMom p' p ℓ i)) := by
  have hA : IsLoopAffine fun ℓ : Fin 2 → Fin 4 → ℝ => cbMom p' p ℓ i := by
    fin_cases i
    · refine (congrArg IsLoopAffine (funext fun ℓ => ?_)).mp (isLoopAffine_affine ![0, 1] p)
      simp [cbMom, add_comm]
    · refine (congrArg IsLoopAffine (funext fun ℓ => ?_)).mp (isLoopAffine_affine ![0, 1] p')
      simp [cbMom, add_comm]
  have hN := hA.isLoopPolyMat_electronNumerator P.m
  refine ⟨hN, ?_⟩
  unfold mergeY
  exact isLoopPolyMat_add (isLoopPolyMat_smul _ hN)
    (isLoopPolyMat_mono (isLoopPolyMat_smul _ (IsLoopPolyMat.const _)) (by norm_num))

theorem isLoopPolyMat_cbXa (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ) (i : Fin 2) :
    IsLoopPolyMat 2 1 (fun ℓ => cbXa P d p' p ℓ i) := by
  by_cases h : i = d
  · simp only [cbXa, h, ↓reduceIte]
    exact (isLoopPolyMat_cbLine P p' p d).2
  · simp only [cbXa, h, ↓reduceIte]
    exact (isLoopPolyMat_cbLine P p' p i).1

theorem isLoopPoly_cbNum0 (P : Params) {X1 X0 : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (hX1 : IsLoopPolyMat 2 1 X1) (hX0 : IsLoopPolyMat 2 1 X0) (α β μ : Fin 4) :
    IsLoopPoly 2 4 (fun ℓ => cbNum P 0 (X1 ℓ) (X0 ℓ) α β μ ℓ) := by
  obtain ⟨hq, hqk, -, -⟩ := isLoopAffine_vpLines 0 0
  unfold cbNum
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l3 _ =>
    IsLoopPoly.sum _ fun l4 _ => IsLoopPoly.sum _ fun l5 _ => ?_)
  have ht : IsLoopPoly 2 2 fun ℓ : Fin 2 → Fin 4 → ℝ => loopTrace 0 (ℓ 0) (-ℓ 1) l5 l4 :=
    ((((IsLoopPolyMat.const (L := 2) (Dirac.gamma l5)).mul
      (hq.isLoopPolyMat_electronNumerator 0)).mul (IsLoopPolyMat.const (Dirac.gamma l4))).mul
        (hqk.isLoopPolyMat_electronNumerator 0)).trace
  have hO := (((((IsLoopPolyMat.const (L := 2) (Dirac.gamma l0)).mul hX1).mul
    (IsLoopPolyMat.const (Dirac.gamma μ))).mul hX0).mul (IsLoopPolyMat.const (Dirac.gamma l3))) α β
  exact (((hO.mul (IsLoopPoly.const (n := 0) _)).mul (IsLoopPoly.const (n := 0) _)).mul ht).mono
    (by norm_num)

theorem isLoopPoly_cbNum2 (P : Params) {X1 X0 : (Fin 2 → Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ}
    (hX1 : IsLoopPolyMat 2 1 X1) (hX0 : IsLoopPolyMat 2 1 X0) (α β μ : Fin 4) :
    IsLoopPoly 2 2 (fun ℓ => cbNum2 P (X1 ℓ) (X0 ℓ) α β μ) := by
  unfold cbNum2
  refine IsLoopPoly.const_mul _ (IsLoopPoly.sum _ fun l0 _ => IsLoopPoly.sum _ fun l3 _ =>
    IsLoopPoly.sum _ fun l4 _ => IsLoopPoly.sum _ fun l5 _ => ?_)
  have hO := (((((IsLoopPolyMat.const (L := 2) (Dirac.gamma l0)).mul hX1).mul
    (IsLoopPolyMat.const (Dirac.gamma μ))).mul hX0).mul (IsLoopPolyMat.const (Dirac.gamma l3))) α β
  exact (((hO.mul (IsLoopPoly.const (n := 0) _)).mul (IsLoopPoly.const (n := 0) _)).mul
    (IsLoopPoly.const (n := 0) _)).mono (by norm_num)

theorem isLoopPoly_cbEa (P : Params) (d : Fin 2) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    IsLoopPoly 2 4 (cbEa0 P d p' p α β μ) ∧ IsLoopPoly 2 2 (cbEa2 P d p' p α β μ) :=
  ⟨isLoopPoly_cbNum0 P (isLoopPolyMat_cbXa P d p' p 1) (isLoopPolyMat_cbXa P d p' p 0) α β μ,
    isLoopPoly_cbNum2 P (isLoopPolyMat_cbXa P d p' p 1) (isLoopPolyMat_cbXa P d p' p 0) α β μ⟩

theorem isLoopPoly_cbEv (P : Params) (p' p : Fin 4 → ℝ) (α β μ : Fin 4) :
    IsLoopPoly 2 4 (cbEv0 P p' p α β μ) ∧ IsLoopPoly 2 2 (cbEv2 P p' p α β μ) :=
  ⟨isLoopPoly_cbNum0 P (isLoopPolyMat_cbLine P p' p 1).1 (isLoopPolyMat_cbLine P p' p 0).1 α β μ,
    isLoopPoly_cbNum2 P (isLoopPolyMat_cbLine P p' p 1).1 (isLoopPolyMat_cbLine P p' p 0).1 α β μ⟩

/-! ### The limit of the integrand -/

/-- **The limit of the integrand of `CB0`, `CB1`**: the pieces of the once-merged pair on the
ten-line shapes and of the bare pair on the doubled shapes are parametric values `vA`, `vB`, and
the joint integral of `(2π)⁻⁸ cbIntegrand` converges to `-(∑ vA + c ∑ vB)`. -/
theorem tendsto_cbIntegrand (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hm : 0 < P.m)
    (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (d : Fin 2) (α β μ : Fin 4) :
    ∃ vA vB : Fin 5 → ℂ,
      (∀ j, IsParamValue (vpData P hmγ hΛ hm h₁ h₂ hp hp' hq j)
        (cbPiece P p p' (cbEa0 P d p' p α β μ) (cbEa2 P d p' p α β μ) j) (vA j)) ∧
      (∀ j, IsParamValue (cbData P hmγ hΛ hm h₁ h₂ hp hp' hq d j)
        (cbPiece P p p' (cbEv0 P p' p α β μ) (cbEv2 P p' p α β μ) j) (vB j)) ∧
      HasLimJ (fun ε ℓ => (((2 * Real.pi) ^ (4 * 2) : ℝ) : ℂ)⁻¹ *
          cbIntegrand { P with ε := ε } d p' p α β μ ℓ)
        (-(∑ j, vA j + mergeC P.m P.δ₂ P.δm * ∑ j, vB j)) := by
  obtain ⟨hA0, hA2⟩ := isLoopPoly_cbEa P d p' p α β μ
  obtain ⟨hV0, hV2⟩ := isLoopPoly_cbEv P p' p α β μ
  obtain ⟨vA, hvA, hA⟩ := hasLimJ_cbT10 P hmγ hΛ hm h₁ h₂ hp hp' hq hA0 hA2
    (fun t => refinedBound_cbEa0 t P d p' p α β μ) (fun t => refinedBound_cbEa2 t P d p' p α β μ)
  obtain ⟨vB, hvB, hB⟩ := hasLimJ_cbT11 P hmγ hΛ hm h₁ h₂ hp hp' hq hV0 hV2
    (fun t => refinedBound_cbEv0 t P p' p α β μ) (fun t => refinedBound_cbEv2 t P p' p α β μ) d
  obtain ⟨vC, -, hC⟩ := hasLimJ_cbT11 P hmγ hΛ hm h₁ h₂ hp hp' hq hA0 hA2
    (fun t => refinedBound_cbEa0 t P d p' p α β μ) (fun t => refinedBound_cbEa2 t P d p' p α β μ) d
  refine ⟨vA, vB, hvA, hvB, ?_⟩
  have h := ((hA.add (hB.const_mul (mergeC P.m P.δ₂ P.δm))).add
    (hC.const_mul I).eps_mul).const_mul (-1)
  have e : -(∑ j, vA j + mergeC P.m P.δ₂ P.δm * ∑ j, vB j) =
      -1 * (∑ j, vA j + mergeC P.m P.δ₂ P.δm * ∑ j, vB j + 0) := by ring
  rw [e]
  refine h.congr fun ε _ => funext fun ℓ => ?_
  rw [integrand_cb_eq]
  ring

/-- **The value of `CB0` converges**, with the limit as in `tendsto_cbIntegrand` (`d = 1`). -/
theorem tendsto_cb0 (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hm : 0 < P.m)
    (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (α β μ : Fin 4) :
    ∃ vA vB : Fin 5 → ℂ,
      (∀ j, IsParamValue (vpData P hmγ hΛ hm h₁ h₂ hp hp' hq j)
        (cbPiece P p p' (cbEa0 P 1 p' p α β μ) (cbEa2 P 1 p' p α β μ) j) (vA j)) ∧
      (∀ j, IsParamValue (cbData P hmγ hΛ hm h₁ h₂ hp hp' hq 1 j)
        (cbPiece P p p' (cbEv0 P p' p α β μ) (cbEv2 P p' p α β μ) j) (vB j)) ∧
      Tendsto (fun ε => contractionValue₂ { P with ε := ε } QED.ChainProof.SetCLink.repCB0
          (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ))
        (𝓝[>] 0) (𝓝 (-(∑ j, vA j + mergeC P.m P.δ₂ P.δm * ∑ j, vB j))) := by
  obtain ⟨vA, vB, hvA, hvB, h⟩ := tendsto_cbIntegrand P hmγ hΛ hm h₁ h₂ hp hp' hq 1 α β μ
  refine ⟨vA, vB, hvA, hvB, h.2.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (contractionValue₂_cb0_shapes { P with ε := ε } hε.ne' hc₁ hc₂ p' p α β μ).symm

/-- **The value of `CB1` converges**, with the limit as in `tendsto_cbIntegrand` (`d = 0`). -/
theorem tendsto_cb1 (P : Params) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hm : 0 < P.m)
    (h₁ : P.m ^ 2 ≤ P.M₁ ^ 2) (h₂ : P.m ^ 2 ≤ P.M₂ ^ 2) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {p p' : Fin 4 → ℝ}
    (hp : Minkowski.dot p p = -P.m ^ 2) (hp' : Minkowski.dot p' p' = -P.m ^ 2)
    (hq : 0 ≤ Minkowski.dot (p' - p) (p' - p)) (α β μ : Fin 4) :
    ∃ vA vB : Fin 5 → ℂ,
      (∀ j, IsParamValue (vpData P hmγ hΛ hm h₁ h₂ hp hp' hq j)
        (cbPiece P p p' (cbEa0 P 0 p' p α β μ) (cbEa2 P 0 p' p α β μ) j) (vA j)) ∧
      (∀ j, IsParamValue (cbData P hmγ hΛ hm h₁ h₂ hp hp' hq 0 j)
        (cbPiece P p p' (cbEv0 P p' p α β μ) (cbEv2 P p' p α β μ) j) (vB j)) ∧
      Tendsto (fun ε => contractionValue₂ { P with ε := ε } QED.ChainProof.SetCLink.repCB1
          (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => α) (fun _ => β) (fun _ => μ))
        (𝓝[>] 0) (𝓝 (-(∑ j, vA j + mergeC P.m P.δ₂ P.δm * ∑ j, vB j))) := by
  obtain ⟨vA, vB, hvA, hvB, h⟩ := tendsto_cbIntegrand P hmγ hΛ hm h₁ h₂ hp hp' hq 0 α β μ
  refine ⟨vA, vB, hvA, hvB, h.2.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (contractionValue₂_cb1_shapes { P with ε := ε } hε.ne' hc₁ hc₂ p' p α β μ).symm

end QED.ChainProof.SetCPauli.CB01

end
