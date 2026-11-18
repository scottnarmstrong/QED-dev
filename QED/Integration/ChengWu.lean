/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SimplexMerge
public import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp

/-!
# The Cheng–Wu theorem on the simplex

For a function `F` on `ℝ^{m+1}` homogeneous of degree `-(m+1)` on the open positive orthant,
`F(t z) = t^{-(m+1)} F(z)` (`t > 0`), the integral over the simplex `Δₘ` of `F` at the barycentric
point equals the integral in which the simplex constraint is kept only on **two** coordinates,
`j` and the last one, while the others run over `(0, ∞)`:
`∫_{Δₘ} F(z) dx = ∫_{w ∈ D_j} F(w, 1 - w_j) dw`, `D_j = {w ∈ ℝᵐ : wᵢ > 0, w_j < 1}`
(`integral_simplex_chengWu`); the two integrands are integrable together
(`integrableOn_simplex_chengWu_iff`). This is the case of the Cheng–Wu theorem used in
`docs/TWO-LOOP-UNITS.md` (section 2.1): for the ladder, `j` is the inner electron `z_B = Y` and
the last coordinate the inner photon `z_b = 1 - Y`.

## Proof

The map `φ(w) = w / S(w)`, `S(w) = 1 + ∑_{i ≠ j} wᵢ`, is a bijection of `D_j` onto the open
simplex `{xᵢ > 0, ∑ x < 1}` (`image_chengWuMap`, `injOn_chengWuMap`), with barycentric point
`S⁻¹ (w, 1 - w_j)` (`simplexPoint_chengWuMap`). Its derivative is `S⁻¹ I - S⁻² w ⊗ ℓ`,
`ℓ(v) = ∑_{i ≠ j} vᵢ`, of determinant `S^{-(m+1)}` by the matrix determinant lemma
(`det_chengWuDeriv`), which homogeneity cancels. The closed and the open simplex differ by a null
set (the coordinate hyperplanes and the hyperplane `∑ x = 1`, the image of `x_j = 0` under the
measure-preserving `simplexSwap`).
-/

public section

open MeasureTheory Set Matrix

namespace QED.Integration.ChengWu

open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.TwoLoop (simplexSwap measurePreserving_simplexSwap simplexPoint_castSucc
  simplexPoint_last)
open QED.Integration.SimplexMerge (mem_simplexSet_iff_le)

variable {m : ℕ}

/-! ### The sets and the map -/

/-- The Cheng–Wu domain `D_j = {w : wᵢ > 0, w_j < 1}`. -/
def chengWuSet (j : Fin m) : Set (Fin m → ℝ) := {w | (∀ i, 0 < w i) ∧ w j < 1}

/-- The open simplex `{x : xᵢ > 0, ∑ x < 1}`. -/
def openSimplex (m : ℕ) : Set (Fin m → ℝ) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}

theorem mem_chengWuSet {j : Fin m} {w : Fin m → ℝ} :
    w ∈ chengWuSet j ↔ (∀ i, 0 < w i) ∧ w j < 1 := Iff.rfl

theorem mem_openSimplex {x : Fin m → ℝ} :
    x ∈ openSimplex m ↔ (∀ i, 0 < x i) ∧ ∑ i, x i < 1 := Iff.rfl

/-- The linear form `ℓ(v) = ∑ᵢ vᵢ - v_j`. -/
noncomputable def chengWuForm (j : Fin m) : (Fin m → ℝ) →L[ℝ] ℝ :=
  (∑ i : Fin m, (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)) -
    (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)

theorem chengWuForm_apply (j : Fin m) (w : Fin m → ℝ) :
    chengWuForm j w = ∑ i, w i - w j := by
  simp [chengWuForm]

/-- The scale `S(w) = 1 + ∑_{i ≠ j} wᵢ`. -/
noncomputable def chengWuScale (j : Fin m) (w : Fin m → ℝ) : ℝ := 1 + chengWuForm j w

/-- The Cheng–Wu map `φ(w) = w / S(w)`. -/
noncomputable def chengWuMap (j : Fin m) (w : Fin m → ℝ) : Fin m → ℝ :=
  (chengWuScale j w)⁻¹ • w

theorem isOpen_chengWuSet (j : Fin m) : IsOpen (chengWuSet j) := by
  have h1 : IsOpen {w : Fin m → ℝ | ∀ i, 0 < w i} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  exact h1.inter (isOpen_lt (continuous_apply j) continuous_const)

theorem measurableSet_chengWuSet (j : Fin m) : MeasurableSet (chengWuSet j) :=
  (isOpen_chengWuSet j).measurableSet

theorem chengWuScale_pos {j : Fin m} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    0 < chengWuScale j w := by
  rw [chengWuScale, chengWuForm_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have : 0 ≤ ∑ i ∈ Finset.univ.erase j, w i := Finset.sum_nonneg fun i _ => (hw i).le
  linarith

theorem sum_eq_chengWuScale (j : Fin m) (w : Fin m → ℝ) :
    ∑ i, w i = chengWuScale j w - 1 + w j := by
  rw [chengWuScale, chengWuForm_apply]
  ring

/-- **The barycentric point of `φ(w)`** is `S⁻¹ (w, 1 - w_j)`. -/
theorem simplexPoint_chengWuMap {j : Fin m} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    simplexPoint (chengWuMap j w) = (chengWuScale j w)⁻¹ • Fin.snoc w (1 - w j) := by
  have hS := (chengWuScale_pos (j := j) hw).ne'
  funext k
  induction k using Fin.lastCases with
  | last =>
    rw [simplexPoint_last, Pi.smul_apply, Fin.snoc_last, smul_eq_mul]
    simp only [chengWuMap, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_eq_chengWuScale j w]
    field_simp
    ring
  | cast i =>
    rw [simplexPoint_castSucc, Pi.smul_apply, Fin.snoc_castSucc]
    rfl

theorem chengWuMap_mem {j : Fin m} {w : Fin m → ℝ} (hw : w ∈ chengWuSet j) :
    chengWuMap j w ∈ openSimplex m := by
  have hS := chengWuScale_pos (j := j) hw.1
  refine ⟨fun i => ?_, ?_⟩
  · simp only [chengWuMap, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hS) (hw.1 i)
  · simp only [chengWuMap, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_eq_chengWuScale j w]
    rw [inv_mul_lt_iff₀ hS]
    linarith [hw.2]

/-- **`φ` maps `D_j` onto the open simplex.** -/
theorem image_chengWuMap (j : Fin m) : chengWuMap j '' chengWuSet j = openSimplex m := by
  refine Set.Subset.antisymm (fun x ⟨w, hw, hx⟩ => hx ▸ chengWuMap_mem hw) fun x hx => ?_
  set s := x j + (1 - ∑ i, x i) with hs_def
  have hs : 0 < s := by linarith [hx.1 j, hx.2]
  refine ⟨s⁻¹ • x, ⟨fun i => ?_, ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hs) (hx.1 i)
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_lt_iff₀ hs]
    linarith [hx.2]
  · have hS : chengWuScale j (s⁻¹ • x) = s⁻¹ := by
      rw [chengWuScale, chengWuForm_apply]
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      field_simp
      rw [hs_def]
      ring
    rw [chengWuMap, hS, inv_inv, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

/-- **`φ` is injective on `D_j`.** -/
theorem injOn_chengWuMap (j : Fin m) : InjOn (chengWuMap j) (chengWuSet j) := by
  intro w hw w' hw' h
  have hS := (chengWuScale_pos (j := j) hw.1).ne'
  have hS' := (chengWuScale_pos (j := j) hw'.1).ne'
  have hc : ∀ i, (chengWuScale j w)⁻¹ * w i = (chengWuScale j w')⁻¹ * w' i := fun i => by
    simpa [chengWuMap] using congrFun h i
  have hsum : (chengWuScale j w)⁻¹ * ∑ i, w i = (chengWuScale j w')⁻¹ * ∑ i, w' i := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hc i
  rw [sum_eq_chengWuScale j w, sum_eq_chengWuScale j w'] at hsum
  have hj := hc j
  have hSS : chengWuScale j w = chengWuScale j w' := by
    have e1 : (chengWuScale j w)⁻¹ * (chengWuScale j w - 1 + w j) =
        1 - (chengWuScale j w)⁻¹ + (chengWuScale j w)⁻¹ * w j := by field_simp
    have e2 : (chengWuScale j w')⁻¹ * (chengWuScale j w' - 1 + w' j) =
        1 - (chengWuScale j w')⁻¹ + (chengWuScale j w')⁻¹ * w' j := by field_simp
    rw [e1, e2, hj] at hsum
    have : (chengWuScale j w)⁻¹ = (chengWuScale j w')⁻¹ := by linarith
    exact inv_injective this
  funext i
  have := hc i
  rw [hSS] at this
  exact (mul_right_injective₀ (inv_ne_zero hS')) this

/-! ### The derivative and its determinant -/

/-- The derivative `S⁻¹ I - S⁻² w ⊗ ℓ` of the Cheng–Wu map. -/
noncomputable def chengWuDeriv (j : Fin m) (w : Fin m → ℝ) : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  (chengWuScale j w)⁻¹ • ContinuousLinearMap.id ℝ (Fin m → ℝ) +
    (-((chengWuScale j w ^ 2)⁻¹) • chengWuForm j).smulRight w

theorem hasFDerivAt_chengWuMap {j : Fin m} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    HasFDerivAt (chengWuMap j) (chengWuDeriv j w) w := by
  have hS : HasFDerivAt (chengWuScale j) (chengWuForm j) w :=
    ((chengWuForm j).hasFDerivAt).const_add 1
  have hinv := (hasFDerivAt_inv (chengWuScale_pos (j := j) hw).ne').comp w hS
  refine (hinv.smul (hasFDerivAt_id w)).congr_fderiv ?_
  ext v i
  simp [chengWuDeriv, mul_comm]

theorem toMatrix'_chengWuDeriv (j : Fin m) (w : Fin m → ℝ) :
    LinearMap.toMatrix' (chengWuDeriv j w : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) =
      (chengWuScale j w)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ) +
        replicateCol (Fin 1) w * replicateRow (Fin 1)
          (fun k => -((chengWuScale j w ^ 2)⁻¹) * chengWuForm j (Pi.single k 1)) := by
  ext i k
  rw [LinearMap.toMatrix'_apply]
  simp only [chengWuDeriv, ContinuousLinearMap.coe_coe]
  simp [Matrix.mul_apply, Pi.single_apply, Matrix.one_apply]
  ring

/-- **The Jacobian of the Cheng–Wu map**: `det φ'(w) = S(w)^{-(m+1)}`. -/
theorem det_chengWuDeriv {j : Fin m} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    (chengWuDeriv j w).det = (chengWuScale j w ^ (m + 1))⁻¹ := by
  have hS := (chengWuScale_pos (j := j) hw).ne'
  set S := chengWuScale j w
  set v : Fin m → ℝ := fun k => -((S ^ 2)⁻¹) * chengWuForm j (Pi.single k 1)
  have hdot : v ⬝ᵥ (S • w) = -(S⁻¹ * chengWuForm j w) := by
    have : chengWuForm j w = ∑ k, w k * chengWuForm j (Pi.single k 1) := by
      conv_lhs => rw [show w = ∑ k, w k • Pi.single k (1 : ℝ) from by
        ext i; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, map_smul]
    rw [this, Finset.mul_sum, ← Finset.sum_neg_distrib]
    simp only [dotProduct, v, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  have hM : (S⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ) + replicateCol (Fin 1) w * replicateRow (Fin 1) v) =
      S⁻¹ • (1 + replicateCol (Fin 1) (S • w) * replicateRow (Fin 1) v) := by
    ext i k
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, replicateCol_apply,
      replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', toMatrix'_chengWuDeriv, hM,
    Matrix.det_smul]
  have hdet : (1 + replicateCol (Fin 1) (S • w) * replicateRow (Fin 1) v).det =
      1 + v ⬝ᵥ (S • w) := by
    rw [det_one_add_mul_comm, Matrix.det_fin_one]
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
      replicateCol_apply, dotProduct]
  rw [hdet, hdot, Fintype.card_fin]
  have hℓ : chengWuForm j w = S - 1 := by simp only [S, chengWuScale]; ring
  rw [hℓ]
  field_simp
  rw [one_div, inv_pow, pow_succ]
  field_simp
  ring

/-! ### The null boundary -/

theorem volume_coord_eq_zero (i : Fin m) :
    volume {x : Fin m → ℝ | x i = 0} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane _ i 0

theorem volume_sum_eq_one (j : Fin m) :
    volume {x : Fin m → ℝ | ∑ i, x i = 1} = 0 := by
  have hset : {x : Fin m → ℝ | ∑ i, x i = 1} = simplexSwap j ⁻¹' {y | y j = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, simplexSwap, Function.update_self]
    constructor <;> intro h <;> linarith
  rw [hset, (measurePreserving_simplexSwap j).measure_preimage
    (measurableSet_eq_fun (measurable_pi_apply j) measurable_const).nullMeasurableSet]
  exact volume_coord_eq_zero j

theorem simplexSet_ae_eq_openSimplex (j : Fin m) :
    simplexSet m =ᵐ[volume] openSimplex m := by
  have hm : 0 < m := j.pos
  have hsub : openSimplex m ⊆ simplexSet m := fun x hx =>
    (mem_simplexSet_iff_le hm x).mpr ⟨fun i => (hx.1 i).le, hx.2.le⟩
  refine (ae_eq_set.mpr ⟨?_, by simp [Set.sdiff_eq_empty.mpr hsub]⟩)
  refine measure_mono_null (t := (⋃ i, {x : Fin m → ℝ | x i = 0}) ∪ {x | ∑ i, x i = 1})
    ?_ (measure_union_null (measure_iUnion_null fun i => volume_coord_eq_zero i)
      (volume_sum_eq_one j))
  intro x ⟨hx, hx'⟩
  rw [mem_simplexSet_iff_le hm] at hx
  by_contra hc
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists] at hc
  exact hx' ⟨fun i => lt_of_le_of_ne (hx.1 i) (Ne.symm (hc.1 i)), lt_of_le_of_ne hx.2 hc.2⟩

/-! ### The theorem -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem abs_det_smul_chengWu {j : Fin m} {F : (Fin (m + 1) → ℝ) → E}
    (hF : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      F (t • z) = (t ^ (m + 1))⁻¹ • F z)
    {w : Fin m → ℝ} (hw : w ∈ chengWuSet j) :
    |(chengWuDeriv j w).det| • F (simplexPoint (chengWuMap j w)) = F (Fin.snoc w (1 - w j)) := by
  have hS := chengWuScale_pos (j := j) hw.1
  have hz : ∀ i, 0 < (Fin.snoc w (1 - w j) : Fin (m + 1) → ℝ) i := fun i => by
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; linarith [hw.2]
    | cast i => simp only [Fin.snoc_castSucc]; exact hw.1 i
  rw [det_chengWuDeriv hw.1, simplexPoint_chengWuMap hw.1, hF _ hz _ (inv_pos.mpr hS), smul_smul,
    abs_of_pos (by positivity), inv_pow, inv_inv, inv_mul_cancel₀ (by positivity), one_smul]

/-- **The Cheng–Wu theorem on the simplex**: for `F` homogeneous of degree `-(m+1)` on the open
positive orthant, `∫_{Δₘ} F(z) dx = ∫_{D_j} F(w, 1 - w_j) dw`. -/
theorem integral_simplex_chengWu (j : Fin m) (F : (Fin (m + 1) → ℝ) → E)
    (hF : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      F (t • z) = (t ^ (m + 1))⁻¹ • F z) :
    ∫ x in simplexSet m, F (simplexPoint x) = ∫ w in chengWuSet j, F (Fin.snoc w (1 - w j)) := by
  rw [setIntegral_congr_set (simplexSet_ae_eq_openSimplex j), ← image_chengWuMap j,
    integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_chengWuSet j)
      (fun w hw => (hasFDerivAt_chengWuMap hw.1).hasFDerivWithinAt) (injOn_chengWuMap j)]
  exact setIntegral_congr_fun (measurableSet_chengWuSet j) fun w hw => abs_det_smul_chengWu hF hw

/-- **Integrability in the Cheng–Wu variables.** -/
theorem integrableOn_simplex_chengWu_iff (j : Fin m) (F : (Fin (m + 1) → ℝ) → E)
    (hF : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      F (t • z) = (t ^ (m + 1))⁻¹ • F z) :
    IntegrableOn (fun x => F (simplexPoint x)) (simplexSet m) ↔
      IntegrableOn (fun w => F (Fin.snoc w (1 - w j))) (chengWuSet j) := by
  rw [IntegrableOn, Measure.restrict_congr_set (simplexSet_ae_eq_openSimplex j), ← IntegrableOn,
    ← image_chengWuMap j,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (measurableSet_chengWuSet j)
      (fun w hw => (hasFDerivAt_chengWuMap hw.1).hasFDerivWithinAt) (injOn_chengWuMap j)]
  exact integrableOn_congr_fun (fun w hw => abs_det_smul_chengWu hF hw)
    (measurableSet_chengWuSet j)

end QED.Integration.ChengWu

end
