/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCUnitMLines
public import QED.ChainProof.SetAKSKBNHom
public import QED.Integration.ChengWu

/-!
# Multi-denominator units: a bound uniform in `ε` for a graph with one rescaled line

Helper level for set (c) (stage L2, the `ε`/`x` interchange of the `repB` classes). At the
Feynman parameter `x` of the inserted bubble, the transverse unit of `repB` contains the spectral
line `x(1-x) k² + M² - iε`: a line of the engine whose momentum is rescaled by `κ = √(x(1-x))`.
Its `ε → 0⁺` limit is `κ⁻²` times a unit with an unscaled line of mass `M/κ`
(`QED.ChainProof.SetCUnitM.unitMLimitV_spectral`), but at fixed `ε` the same rescaling produces
the prescription `ε/κ²` on that line, which the engine does not treat. This file bounds the
value at fixed `ε` directly, uniformly in `ε`, by `κ⁻²` times a constant of the unscaled graph:

* `absParam`: the absolute parametric integrand at a point of the orthant, `|V - iε|` replaced
  by `V`; **`absParam_smul`**: it is homogeneous of degree `-(m+1)`; **`absParam_scale`**: for
  rescaled lines (momenta `σᵢ kᵢ`, masses `σᵢ Mᵢ`) it is the original one at `σ² z`;
* `coordScale`, **`integral_chengWuSet_coordScale`**: rescaling a free coordinate of a Cheng–Wu
  domain;
* **`integral_simplex_lineWeights`**: for a homogeneous integrand `F`,
  `∫_Δ F(d ⊙ z) = a⁻¹ ∫_Δ F(z)`, `d` the weight `a > 0` on one line (Cheng–Wu twice,
  `QED.Integration.ChengWu.integral_simplex_chengWu`);
* `integrableOn_absParam`: integrability and the bound by `∫_Δ domFun` under the engine
  hypotheses;
* **`norm_jointEnergyFirstIntegral_scale_le`**, **`norm_jointEnergyFirstIntegral_scale_le'`**:
  for every `ε > 0`, the joint energy-first integral of the graph with one line rescaled by
  `κ ≠ 0` is at most `κ⁻² π⁴ ∫_Δ domFun`, a constant of the unscaled graph independent of `ε` and
  of the masses (from the parametric representation at `ε`, `|V - iε| ≥ V`, and the change of
  variables `z_line → κ² z_line`).
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace QED.ChainProof.SetCUnitM

open QED.Integration.TwoLoop (symanzikU symanzikV symanzikMatrix symanzikVector LoopQuartic
  NoSubdivergenceRefined RefinedBound lineDenom loopShift loopComp coefVec energyShift
  spatialShift jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_refined)
open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.ChengWu (chengWuSet integral_simplex_chengWu
  integrableOn_simplex_chengWu_iff measurableSet_chengWuSet)
open QED.TwoLoop.ClassLimit (paramIntegrand coeffOne coeffTwo coeffThree wBase)
open QED.ChainProof.SetAKS (ksN_symanzikU_smul ksN_loopShift_smul ksN_symanzikMatrix_smul
  ksN_contractTwo_smul ksN_contractFour_smul ksN_symanzikV_smul)

section Abs

variable {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ)

/-- The absolute parametric integrand at a point `z` of the orthant: the norms of the three
terms of `paramIntegrand`, with `|V - iε|` replaced by `V`. -/
noncomputable def absParam (z : Fin (m + 1) → ℝ) : ℝ :=
  ‖((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ * (((m - 4).factorial : ℂ) * Q.eval (-loopShift α p z))‖ *
      (symanzikV α p M z ^ (m - 3))⁻¹ +
    ‖((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ * (((m - 5).factorial : ℂ) / 2 *
      Q.contractTwo (symanzikMatrix α z) (loopComp (-loopShift α p z)))‖ *
      (symanzikV α p M z ^ (m - 4))⁻¹ +
    ‖((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ * (((m - 6).factorial : ℂ) / 4 *
      Q.contractFour (symanzikMatrix α z))‖ * (symanzikV α p M z ^ (m - 5))⁻¹

theorem absParam_simplexPoint (x : Fin m → ℝ) :
    absParam Q α p M (simplexPoint x) =
      ‖coeffOne Q α p x‖ * (symanzikV α p M (simplexPoint x) ^ (m - 3))⁻¹ +
        ‖coeffTwo Q α p x‖ * (symanzikV α p M (simplexPoint x) ^ (m - 4))⁻¹ +
        ‖coeffThree Q α x‖ * (symanzikV α p M (simplexPoint x) ^ (m - 5))⁻¹ := rfl

/-- **Homogeneity** of degree `-(m+1)`. -/
theorem absParam_smul (hm : 7 ≤ m) (z : Fin (m + 1) → ℝ) {t : ℝ} (ht : 0 < t) :
    absParam Q α p M (t • z) = (t ^ (m + 1))⁻¹ • absParam Q α p M z := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 7 := ⟨m - 7, by omega⟩
  have ht0 := ht.ne'
  have hU : ((symanzikU α (t • z) ^ 2 : ℝ) : ℂ)⁻¹ =
      (((t ^ 4)⁻¹ : ℝ) : ℂ) * ((symanzikU α z ^ 2 : ℝ) : ℂ)⁻¹ := by
    rw [ksN_symanzikU_smul]; push_cast; ring
  have e3 : n + 7 - 3 = n + 4 := by omega
  have e4 : n + 7 - 4 = n + 3 := by omega
  have e5 : n + 7 - 5 = n + 2 := by omega
  simp only [absParam, hU, ksN_loopShift_smul α p z ht0, ksN_symanzikMatrix_smul,
    ksN_contractTwo_smul ht0, ksN_contractFour_smul ht0, ksN_symanzikV_smul α p M z ht0, e3, e4,
    e5, smul_eq_mul]
  have h1 : ∀ X : ℂ, ‖(((t ^ 4)⁻¹ : ℝ) : ℂ) * X‖ = (t ^ 4)⁻¹ * ‖X‖ := fun X => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h2 : ∀ X Y Z : ℂ, (((t ^ 4)⁻¹ : ℝ) : ℂ) * X * (Y * ((t : ℂ)⁻¹ * Z)) =
      (((t ^ 5)⁻¹ : ℝ) : ℂ) * (X * (Y * Z)) := fun X Y Z => by push_cast; ring
  have h3 : ∀ X Y Z : ℂ, (((t ^ 4)⁻¹ : ℝ) : ℂ) * X * (Y * (((t : ℂ) ^ 2)⁻¹ * Z)) =
      (((t ^ 6)⁻¹ : ℝ) : ℂ) * (X * (Y * Z)) := fun X Y Z => by push_cast; ring
  have h5 : ∀ X : ℂ, ‖(((t ^ 5)⁻¹ : ℝ) : ℂ) * X‖ = (t ^ 5)⁻¹ * ‖X‖ := fun X => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h6 : ∀ X : ℂ, ‖(((t ^ 6)⁻¹ : ℝ) : ℂ) * X‖ = (t ^ 6)⁻¹ * ‖X‖ := fun X => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [h2, h3, mul_assoc, h1, h5, h6]
  simp only [mul_pow, mul_inv]
  ring

/-- `coefVec` of rescaled lines. -/
theorem coefVec_scale (σ : Fin (m + 1) → ℝ) (z q : Fin (m + 1) → ℝ) :
    coefVec (fun i => σ i • α i) z (fun i => σ i * q i) = coefVec α (fun i => σ i ^ 2 * z i) q := by
  funext s
  simp only [coefVec, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem loopShift_scale (σ : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) :
    loopShift (fun i => σ i • α i) (fun i => σ i • p i) z =
      loopShift α p fun i => σ i ^ 2 * z i := by
  have h : ∀ c : Fin 4, coefVec (fun i => σ i • α i) z (fun i => (σ i • p i) c) =
      coefVec α (fun i => σ i ^ 2 * z i) (fun i => p i c) := fun c => by
    rw [← coefVec_scale]
    rfl
  unfold loopShift energyShift spatialShift
  simp only [symanzikMatrix_scale, h]

theorem symanzikV_scale_mul (σ : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) :
    symanzikV (fun i => σ i • α i) (fun i => σ i • p i) (fun i => σ i * M i) z =
      symanzikV α p M fun i => σ i ^ 2 * z i := by
  unfold symanzikV
  rw [symanzikMatrix_scale, symanzikVector_scale]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [dot_smul_smul_sq]; ring

/-- **The absolute integrand of rescaled lines** is that of the original lines at `σ² z`. -/
theorem absParam_scale (σ : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) :
    absParam Q (fun i => σ i • α i) (fun i => σ i • p i) (fun i => σ i * M i) z =
      absParam Q α p M (fun i => σ i ^ 2 * z i) := by
  simp only [absParam, symanzikU_scale, symanzikMatrix_scale, loopShift_scale,
    symanzikV_scale_mul]

end Abs

/-! ### Rescaling one coordinate of a Cheng–Wu domain -/

section Coord

variable {m : ℕ}

/-- The linear map rescaling the coordinate `i` by `a`. -/
noncomputable def coordScale (i : Fin m) (a : ℝ) : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.diagonal (Function.update 1 i a)))

theorem coordScale_apply (i : Fin m) (a : ℝ) (w : Fin m → ℝ) (k : Fin m) :
    coordScale i a w k = Function.update (1 : Fin m → ℝ) i a k * w k := by
  simp [coordScale, Matrix.mulVec_diagonal]

theorem det_coordScale (i : Fin m) (a : ℝ) : (coordScale i a).det = a := by
  rw [ContinuousLinearMap.det, coordScale, LinearMap.coe_toContinuousLinearMap,
    LinearMap.det_toLin', Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

theorem coordScale_comp {i : Fin m} {a : ℝ} (ha : a ≠ 0) (w : Fin m → ℝ) :
    coordScale i a⁻¹ (coordScale i a w) = w := by
  funext k
  rw [coordScale_apply, coordScale_apply, ← mul_assoc]
  by_cases hk : k = i
  · subst hk; simp [ha]
  · simp [hk]

theorem coordScale_mem {i j : Fin m} (hij : i ≠ j) {a : ℝ} (ha : 0 < a) {w : Fin m → ℝ}
    (hw : w ∈ chengWuSet j) : coordScale i a w ∈ chengWuSet j := by
  rw [QED.Integration.ChengWu.mem_chengWuSet] at hw ⊢
  refine ⟨fun k => ?_, ?_⟩
  · rw [coordScale_apply]
    by_cases hk : k = i
    · subst hk; simpa using mul_pos ha (hw.1 k)
    · simpa [hk] using hw.1 k
  · rw [coordScale_apply, Function.update_of_ne hij.symm]
    simpa using hw.2

theorem image_coordScale {i j : Fin m} (hij : i ≠ j) {a : ℝ} (ha : 0 < a) :
    coordScale i a '' chengWuSet j = chengWuSet j := by
  refine Set.Subset.antisymm ?_ fun w hw => ⟨coordScale i a⁻¹ w,
    coordScale_mem hij (inv_pos.2 ha) hw, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact coordScale_mem hij ha hw
  · simpa using coordScale_comp (i := i) (inv_ne_zero ha.ne') w

theorem injective_coordScale (i : Fin m) {a : ℝ} (ha : a ≠ 0) :
    Function.Injective (coordScale i a) := fun w w' h => by
  rw [← coordScale_comp ha w, ← coordScale_comp ha w', h]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Rescaling a free coordinate**: `∫_{D_j} H(w with wᵢ → a wᵢ) dw = a⁻¹ ∫_{D_j} H`. -/
theorem integral_chengWuSet_coordScale {i j : Fin m} (hij : i ≠ j) {a : ℝ} (ha : 0 < a)
    (H : (Fin m → ℝ) → E) :
    ∫ w in chengWuSet j, H (coordScale i a w) = a⁻¹ • ∫ w in chengWuSet j, H w := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_chengWuSet j)
    (fun w _ => (coordScale i a).hasFDerivAt.hasFDerivWithinAt)
    ((injective_coordScale i ha.ne').injOn) H
  rw [image_coordScale hij ha, det_coordScale, abs_of_pos ha, integral_smul] at h
  rw [h, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]

theorem integrableOn_chengWuSet_coordScale_iff {i j : Fin m} (hij : i ≠ j) {a : ℝ} (ha : 0 < a)
    (H : (Fin m → ℝ) → E) :
    IntegrableOn (fun w => H (coordScale i a w)) (chengWuSet j) ↔
      IntegrableOn H (chengWuSet j) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (measurableSet_chengWuSet j) (fun w _ => (coordScale i a).hasFDerivAt.hasFDerivWithinAt)
    ((injective_coordScale i ha.ne').injOn) H
  rw [image_coordScale hij ha, det_coordScale, abs_of_pos ha] at h
  rw [h, IntegrableOn, IntegrableOn]
  exact (integrable_smul_iff ha.ne' (fun w => H (coordScale i a w))).symm

end Coord

/-! ### Rescaling one line in the simplex integral -/

section Simplex

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weights `d = (1, …, a, …, 1)`, `a` at the line `castSucc i`. -/
def lineWeights (i : Fin m) (a : ℝ) : Fin (m + 1) → ℝ :=
  Function.update 1 (Fin.castSucc i) a

theorem lineWeights_mul_snoc {i j : Fin m} (hij : i ≠ j) (a : ℝ) (w : Fin m → ℝ) :
    (fun k => lineWeights i a k * (Fin.snoc w (1 - w j) : Fin (m + 1) → ℝ) k) =
      Fin.snoc (coordScale i a w) (1 - coordScale i a w j) := by
  funext k
  have hj : coordScale i a w j = w j := by
    rw [coordScale_apply, Function.update_of_ne hij.symm]; simp
  induction k using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last, Fin.snoc_last, hj, lineWeights,
      Function.update_of_ne (Fin.castSucc_lt_last i).ne']
    simp
  | cast k =>
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc, coordScale_apply, lineWeights]
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne (fun h => hk (Fin.castSucc_injective _ h)),
        Function.update_of_ne hk]
      simp

variable (H : (Fin (m + 1) → ℝ) → E)
  (hH : ∀ z : Fin (m + 1) → ℝ, ∀ t : ℝ, 0 < t → H (t • z) = (t ^ (m + 1))⁻¹ • H z)
include hH

theorem homog_lineWeights (i : Fin m) (a : ℝ) (z : Fin (m + 1) → ℝ) (t : ℝ) (ht : 0 < t) :
    H (fun k => lineWeights i a k * (t • z) k) =
      (t ^ (m + 1))⁻¹ • H (fun k => lineWeights i a k * z k) := by
  rw [← hH _ t ht]
  congr 1
  funext k
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Rescaling one line of a homogeneous integrand**: for `F` homogeneous of degree `-(m+1)`,
`∫_Δ F(d ⊙ z) = a⁻¹ ∫_Δ F(z)` with `d` the weight `a > 0` on the line `castSucc i`. -/
theorem integral_simplex_lineWeights {i j : Fin m} (hij : i ≠ j) {a : ℝ} (ha : 0 < a) :
    ∫ x in simplexSet m, H (fun k => lineWeights i a k * simplexPoint x k) =
      a⁻¹ • ∫ x in simplexSet m, H (simplexPoint x) := by
  rw [integral_simplex_chengWu j (fun z => H (fun k => lineWeights i a k * z k))
      (fun z _ t ht => homog_lineWeights H hH i a z t ht),
    integral_simplex_chengWu j H (fun z _ t ht => hH z t ht)]
  simp only [lineWeights_mul_snoc hij]
  exact integral_chengWuSet_coordScale hij ha (fun w => H (Fin.snoc w (1 - w j)))

theorem integrableOn_simplex_lineWeights_iff {i j : Fin m} (hij : i ≠ j) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x => H (fun k => lineWeights i a k * simplexPoint x k)) (simplexSet m) ↔
      IntegrableOn (fun x => H (simplexPoint x)) (simplexSet m) := by
  rw [integrableOn_simplex_chengWu_iff j (fun z => H (fun k => lineWeights i a k * z k))
      (fun z _ t ht => homog_lineWeights H hH i a z t ht),
    integrableOn_simplex_chengWu_iff j H (fun z _ t ht => hH z t ht)]
  simp only [lineWeights_mul_snoc hij]
  exact integrableOn_chengWuSet_coordScale_iff hij ha (fun w => H (Fin.snoc w (1 - w j)))

end Simplex

/-! ### The value with one rescaled line at fixed `ε` -/

section Value

variable {m : ℕ} (Q : LoopQuartic) (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
  (M : Fin (m + 1) → ℝ)

theorem aestronglyMeasurable_absParam (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval) :
    AEStronglyMeasurable (fun x => absParam Q α p M (simplexPoint x))
      (volume.restrict (simplexSet m)) := by
  obtain ⟨hT₁, hT₂, hT₃⟩ := QED.TwoLoop.ClassLimit.integrableOn_coeff Q α p hm hcrit hB
  have hV : Measurable fun x : Fin m → ℝ => symanzikV α p M (simplexPoint x) :=
    (QED.Integration.TwoLoop.measurable_symanzikV α p M).comp
      QED.Integration.TwoLoop.continuous_simplexPoint'.measurable
  have hk : ∀ k : ℕ, AEStronglyMeasurable
      (fun x : Fin m → ℝ => (symanzikV α p M (simplexPoint x) ^ k)⁻¹)
      (volume.restrict (simplexSet m)) := fun k => ((hV.pow_const k).inv).aestronglyMeasurable
  exact ((hT₁.aestronglyMeasurable.norm.mul (hk _)).add
    (hT₂.aestronglyMeasurable.norm.mul (hk _))).add (hT₃.aestronglyMeasurable.norm.mul (hk _))

theorem absParam_le_domFun {c : ℝ} (hc : 0 < c) {x : Fin m → ℝ}
    (hV : c ≤ symanzikV α p M (simplexPoint x)) :
    absParam Q α p M (simplexPoint x) ≤ QED.ChainProof.SetCUnit.domFun Q α p c x := by
  have hk : ∀ k : ℕ, (symanzikV α p M (simplexPoint x) ^ k)⁻¹ ≤ (c ^ k)⁻¹ := fun k =>
    inv_anti₀ (pow_pos hc k) (pow_le_pow_left₀ hc.le hV k)
  rw [absParam_simplexPoint, QED.ChainProof.SetCUnit.domFun]
  gcongr

theorem absParam_nonneg_of {x : Fin m → ℝ} (hV : 0 ≤ symanzikV α p M (simplexPoint x)) :
    0 ≤ absParam Q α p M (simplexPoint x) := by
  rw [absParam_simplexPoint]
  positivity

variable {Q α p M}

/-- **Integrability of the absolute integrand** under the hypotheses of the engine. -/
theorem integrableOn_absParam (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z) :
    IntegrableOn (fun x => absParam Q α p M (simplexPoint x)) (simplexSet m) ∧
      ∫ x in simplexSet m, absParam Q α p M (simplexPoint x) ≤
        ∫ x in simplexSet m, QED.ChainProof.SetCUnit.domFun Q α p c x := by
  have hm0 : 0 < m := by omega
  have hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0 :=
    QED.Integration.TwoLoop.NoSubdivergence.span (α := α) fun i => by
      have := hcrit.noSubdivergenceOfOrder i; omega
  have hD := QED.ChainProof.SetCUnit.integrableOn_domFun (p := p) hm hcrit hB c
  have hae : ∀ᵐ x ∂(volume.restrict (simplexSet m)), 0 ≤ absParam Q α p M (simplexPoint x) ∧
      absParam Q α p M (simplexPoint x) ≤ QED.ChainProof.SetCUnit.domFun Q α p c x := by
    filter_upwards [QED.Integration.TwoLoop.ae_posDef α hm0 hspan] with x ⟨hxS, hPD⟩
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    have hVx := hV _ hz.1 hz.2 hPD.det_pos.ne'
    exact ⟨absParam_nonneg_of Q α p M (hc.le.trans hVx), absParam_le_domFun Q α p M hc hVx⟩
  have hI : IntegrableOn (fun x => absParam Q α p M (simplexPoint x)) (simplexSet m) :=
    hD.mono' (aestronglyMeasurable_absParam Q α p M hm hcrit hB) (by
      filter_upwards [hae] with x hx
      rw [Real.norm_of_nonneg hx.1]
      exact hx.2)
  exact ⟨hI, integral_mono_ae hI hD (by filter_upwards [hae] with x hx; exact hx.2)⟩

theorem noSubdivergenceRefined_lineScale {k : ℕ} {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined k E α) {σ : Fin (m + 1) → ℝ} (hσ0 : ∀ i, σ i ≠ 0) :
    NoSubdivergenceRefined k E (fun i => σ i • α i) := by
  have h := noSubdivergenceRefined_scale_comp hcrit id (Function.Embedding.refl _)
    (fun _ => rfl) σ hσ0
  simpa [Finset.map_refl] using h

theorem refinedBound_lineScale {E : Finset (Fin (m + 1))} (hB : RefinedBound α E 4 Q.eval)
    {σ : Fin (m + 1) → ℝ} (hσ : ∀ e ∈ E, σ e = 1) :
    RefinedBound (fun i => σ i • α i) E 4 Q.eval := by
  have h := refinedBound_map (α' := fun i => σ i • α i) (Function.Embedding.refl _)
    (fun e he => by simp [hσ e he]) hB
  simpa [Finset.map_refl] using h

/-- Both stages of the joint energy-first integral are integrable for rescaled lines with scale
`1` on the numerator lines. -/
theorem jointEnergyFirstIntegrable_lineScale (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval)
    {σ : Fin (m + 1) → ℝ} (hσ0 : ∀ i, σ i ≠ 0) (hσ : ∀ e ∈ E, σ e = 1) (M' : Fin (m + 1) → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    QED.TwoLoop.jointEnergyFirstIntegrable 2 (fun ℓ => Q.eval ℓ *
      ∏ k, (lineDenom (fun k => σ k • α k) (fun k => σ k • p k) M' ε k ℓ)⁻¹) :=
  QED.Integration.TwoLoop.jointEnergyFirstIntegrable_loopQuartic_mul_prod_inv_lineDenom_of_refined
    Q _ _ M' hm hε (noSubdivergenceRefined_lineScale hcrit hσ0) (refinedBound_lineScale hB hσ)

/-- **The joint energy-first integral with one rescaled line, bounded uniformly in `ε`.** Let the
line `castSucc i` be rescaled by `κ ≠ 0` (its momentum `κ k`, its mass `κ M`), the other lines
unchanged, and let the engine hypotheses hold for the original lines with `V ≥ c > 0`. Then for
every `ε > 0` the value of the rescaled graph is bounded by `κ⁻² π⁴ ∫_Δ domFun`, a constant
independent of `ε` and of the masses. -/
theorem norm_jointEnergyFirstIntegral_scale_le (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z)
    {i j : Fin m} (hij : i ≠ j) (hiE : Fin.castSucc i ∉ E) {κ : ℝ} (hκ : κ ≠ 0)
    {σ : Fin (m + 1) → ℝ} (hσi : σ (Fin.castSucc i) = κ) (hσ : ∀ k, k ≠ Fin.castSucc i → σ k = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ‖QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => Q.eval ℓ *
        ∏ k, (lineDenom (fun k => σ k • α k) (fun k => σ k • p k) (fun k => σ k * M k) ε k
          ℓ)⁻¹)‖ ≤
      (κ ^ 2)⁻¹ * (π ^ 4 * ∫ x in simplexSet m, QED.ChainProof.SetCUnit.domFun Q α p c x) := by
  have hm0 : 0 < m := by omega
  have hσ0 : ∀ k, σ k ≠ 0 := fun k => by
    by_cases hk : k = Fin.castSucc i
    · rw [hk, hσi]; exact hκ
    · rw [hσ k hk]; exact one_ne_zero
  set α' : Fin (m + 1) → Fin 2 → ℝ := fun k => σ k • α k
  set p' : Fin (m + 1) → Fin 4 → ℝ := fun k => σ k • p k
  set M' : Fin (m + 1) → ℝ := fun k => σ k * M k
  have hcrit' : NoSubdivergenceRefined 2 E α' := noSubdivergenceRefined_lineScale hcrit hσ0
  have hB' : RefinedBound α' E 4 Q.eval := refinedBound_lineScale hB fun e he =>
    hσ e fun h' => hiE (h' ▸ he)
  have hspan' : ∃ i j, α' i 0 * α' j 1 - α' i 1 * α' j 0 ≠ 0 :=
    QED.Integration.TwoLoop.NoSubdivergence.span (α := α') fun i => by
      have := hcrit'.noSubdivergenceOfOrder i; omega
  -- the weights `σ²`
  have ha : 0 < κ ^ 2 := by positivity
  have hd : (fun k => σ k ^ 2) = lineWeights i (κ ^ 2) := by
    funext k
    by_cases hk : k = Fin.castSucc i
    · rw [hk, hσi, lineWeights, Function.update_self]
    · rw [hσ k hk, lineWeights, Function.update_of_ne hk]; simp
  have hd' : ∀ z : Fin (m + 1) → ℝ,
      (fun k => σ k ^ 2 * z k) = fun k => lineWeights i (κ ^ 2) k * z k := fun z => by
    funext k; rw [← hd]
  have hsc : ∀ z : Fin (m + 1) → ℝ, absParam Q α' p' M' z =
      absParam Q α p M (fun k => lineWeights i (κ ^ 2) k * z k) := fun z => by
    rw [absParam_scale, ← hd]
  have hH : ∀ z : Fin (m + 1) → ℝ, ∀ t : ℝ, 0 < t →
      absParam Q α p M (t • z) = (t ^ (m + 1))⁻¹ • absParam Q α p M z :=
    fun z t ht => absParam_smul Q α p M hm z ht
  obtain ⟨hI, hle⟩ := integrableOn_absParam hm hcrit hB hc hV
  have hI' : IntegrableOn (fun x => absParam Q α' p' M' (simplexPoint x)) (simplexSet m) := by
    simp only [hsc]
    exact (integrableOn_simplex_lineWeights_iff _ hH hij ha).2 hI
  have hint : ∫ x in simplexSet m, absParam Q α' p' M' (simplexPoint x) =
      (κ ^ 2)⁻¹ * ∫ x in simplexSet m, absParam Q α p M (simplexPoint x) := by
    simp only [hsc]
    exact integral_simplex_lineWeights _ hH hij ha
  -- the pointwise bound of the rescaled parametric integrand
  have hpt : ∀ᵐ x ∂(volume.restrict (simplexSet m)),
      ‖paramIntegrand Q α' p' M' ε x‖ ≤ absParam Q α' p' M' (simplexPoint x) := by
    filter_upwards [QED.Integration.TwoLoop.ae_posDef α' hm0 hspan'] with x ⟨hxS, hPD⟩
    have hz := QED.Integration.Feynman.simplexPoint_mem_stdSimplex hxS
    set z := simplexPoint x
    set S := ∑ k, lineWeights i (κ ^ 2) k * z k
    have hw0 : ∀ k, 0 < lineWeights i (κ ^ 2) k := fun k => by
      have := hσ0 k
      rw [← hd]; positivity
    have hS : 0 < S := by
      have hU0 : symanzikU α' z ≠ 0 := hPD.det_pos.ne'
      by_contra hS0
      push Not at hS0
      have hz0 : ∀ k, lineWeights i (κ ^ 2) k * z k = 0 := fun k =>
        (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hw0 k).le (hz.1 k)).mp
          (le_antisymm hS0 (Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k).le (hz.1 k))) k
          (Finset.mem_univ k)
      have : (fun k => lineWeights i (κ ^ 2) k * z k) = (0 : ℝ) • z := by
        funext k; rw [hz0 k]; simp
      apply hU0
      rw [symanzikU_scale, hd' z, this, ksN_symanzikU_smul]
      ring
    set y : Fin (m + 1) → ℝ := S⁻¹ • fun k => lineWeights i (κ ^ 2) k * z k
    have hy : (fun k => lineWeights i (κ ^ 2) k * z k) = S • y := by
      simp only [y, smul_smul, mul_inv_cancel₀ hS.ne', one_smul]
    have hy0 : ∀ k, 0 ≤ y k := fun k => by
      simp only [y, Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 hS.le) (mul_nonneg (hw0 k).le (hz.1 k))
    have hy1 : ∑ k, y k = 1 := by
      simp only [y, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact inv_mul_cancel₀ hS.ne'
    have hUy : symanzikU α y ≠ 0 := by
      have hU0 : symanzikU α' z ≠ 0 := hPD.det_pos.ne'
      rw [symanzikU_scale, hd' z, hy, ksN_symanzikU_smul] at hU0
      exact right_ne_zero_of_mul hU0
    have hVpos : 0 < symanzikV α' p' M' z := by
      rw [symanzikV_scale_mul, hd' z, hy, ksN_symanzikV_smul α p M y hS.ne']
      exact mul_pos hS (hc.trans_le (hV y hy0 hy1 hUy))
    exact QED.TwoLoop.ClassLimit.norm_paramIntegrand_le Q α' p' M' hVpos ε le_rfl
  have hrep := (jointEnergyFirstIntegral_loopQuartic_mul_prod_inv_lineDenom_of_refined
    Q α' p' M' hm hε hcrit' hB').2.2
  change ‖QED.TwoLoop.jointEnergyFirstIntegral 2
    (fun ℓ => Q.eval ℓ * ∏ k, (lineDenom α' p' M' ε k ℓ)⁻¹)‖ ≤ _
  rw [hrep]
  change ‖-((π : ℂ) ^ 4) * ∫ x in simplexSet m, paramIntegrand Q α' p' M' ε x‖ ≤ _
  rw [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have h1 := norm_integral_le_of_norm_le hI' hpt
  rw [hint] at h1
  have hπ : 0 ≤ π ^ 4 := by positivity
  calc π ^ 4 * ‖∫ x in simplexSet m, paramIntegrand Q α' p' M' ε x‖
      ≤ π ^ 4 * ((κ ^ 2)⁻¹ * ∫ x in simplexSet m, absParam Q α p M (simplexPoint x)) :=
        mul_le_mul_of_nonneg_left h1 hπ
    _ ≤ π ^ 4 * ((κ ^ 2)⁻¹ * ∫ x in simplexSet m, QED.ChainProof.SetCUnit.domFun Q α p c x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by positivity)) hπ
    _ = _ := by ring

/-- The joint energy-first integral of a line product does not depend on the order of the
lines. -/
theorem jointEnergyFirstIntegral_prod_perm (τ : Equiv.Perm (Fin (m + 1))) (ε : ℝ) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => Q.eval ℓ *
        ∏ k, (lineDenom (fun k => α (τ k)) (fun k => p (τ k)) (fun k => M (τ k)) ε k ℓ)⁻¹) =
      QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => Q.eval ℓ *
        ∏ k, (lineDenom α p M ε k ℓ)⁻¹) := by
  congr 1
  funext ℓ
  congr 1
  exact Fintype.prod_equiv τ _ _ fun k => rfl

/-- **One rescaled line at any position** (`m ≥ 7`): the bound of
`norm_jointEnergyFirstIntegral_scale_le` after moving the rescaled line to the front. The
constant `∫_Δ domFun` is that of the reordered lines; it does not involve `ε` or the masses. -/
theorem norm_jointEnergyFirstIntegral_scale_le' (hm : 7 ≤ m) {E : Finset (Fin (m + 1))}
    (hcrit : NoSubdivergenceRefined 2 E α) (hB : RefinedBound α E 4 Q.eval) {c : ℝ} (hc : 0 < c)
    (hV : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α p M z)
    {i₀ : Fin (m + 1)} (hiE : i₀ ∉ E) {κ : ℝ} (hκ : κ ≠ 0)
    {σ : Fin (m + 1) → ℝ} (hσi : σ i₀ = κ) (hσ : ∀ k, k ≠ i₀ → σ k = 1) {ε : ℝ} (hε : 0 < ε) :
    ‖QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => Q.eval ℓ *
        ∏ k, (lineDenom (fun k => σ k • α k) (fun k => σ k • p k) (fun k => σ k * M k) ε k
          ℓ)⁻¹)‖ ≤
      (κ ^ 2)⁻¹ * (π ^ 4 * ∫ x in simplexSet m, QED.ChainProof.SetCUnit.domFun Q
        (fun k => α (Equiv.swap (Fin.castSucc ⟨0, by omega⟩) i₀ k))
        (fun k => p (Equiv.swap (Fin.castSucc ⟨0, by omega⟩) i₀ k)) c x) := by
  set i : Fin m := ⟨0, by omega⟩
  set j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  set τ := Equiv.swap (Fin.castSucc i) i₀
  rw [← jointEnergyFirstIntegral_prod_perm (Q := Q) (α := fun k => σ k • α k)
    (p := fun k => σ k • p k) (M := fun k => σ k * M k) τ ε]
  have hcrit' : NoSubdivergenceRefined 2 (E.map τ.symm.toEmbedding) (fun k => α (τ k)) := by
    have h := noSubdivergenceRefined_scale_comp hcrit τ τ.symm.toEmbedding
      (fun k => by simp) (fun _ => 1) (fun _ => one_ne_zero)
    simpa using h
  have hB' : RefinedBound (fun k => α (τ k)) (E.map τ.symm.toEmbedding) 4 Q.eval :=
    refinedBound_map τ.symm.toEmbedding (fun e _ => by simp) hB
  have hV' : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 →
      symanzikU (fun k => α (τ k)) z ≠ 0 →
      c ≤ symanzikV (fun k => α (τ k)) (fun k => p (τ k)) (fun k => M (τ k)) z :=
    fun z hz hz1 hU => QED.Integration.TwoLoop.le_symanzikV_comp_of hV (fun _ => le_rfl) hz hz1 hU
  have hiE' : Fin.castSucc i ∉ E.map τ.symm.toEmbedding := by
    simp only [Finset.mem_map_equiv, Equiv.symm_symm]
    simpa [τ] using hiE
  exact norm_jointEnergyFirstIntegral_scale_le hm hcrit' hB' hc hV' hij hiE' hκ
    (σ := fun k => σ (τ k)) (by simp [τ, hσi]) (fun k hk => hσ _ (by
      intro h; apply hk; simpa [τ] using congrArg τ h)) hε

end Value

end QED.ChainProof.SetCUnitM

end
