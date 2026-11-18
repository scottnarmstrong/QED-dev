/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.ChengWu
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp

/-!
# The Cheng–Wu theorem with the constraint on a set of coordinates

A generalization of `QED/Integration/ChengWu.lean` (which keeps the simplex constraint on two
coordinates `j` and the last), needed for the crossed ladder, whose inner simplex in section 2.2
of `docs/TWO-LOOP-UNITS.md` has three coordinates `(z₂, z₃, z_b)`. For a function `F` on
`ℝ^{m+1}` homogeneous of degree `-(m+1)` on the open positive orthant and a set `T` of the first
`m` coordinates,
`∫_{Δₘ} F(z) dx = ∫_{w ∈ D_T} F(w, 1 - ∑_{i ∈ T} wᵢ) dw`,
`D_T = {w ∈ ℝᵐ : wᵢ > 0, ∑_{i ∈ T} wᵢ < 1}` (`integral_simplex_chengWuSet`): the constraint is
kept on the coordinates of `T` and the last one, the others run over `(0, ∞)`. The two integrands
are integrable together (`integrableOn_simplex_chengWuSet_iff`).

The proof is that of `QED.Integration.ChengWu.integral_simplex_chengWu` with the linear form
`ℓ(v) = ∑_{i ∉ T} vᵢ`: the map `φ(w) = w / S(w)`, `S = 1 + ℓ(w)`, is a bijection of `D_T` onto the
open simplex with barycentric point `S⁻¹ (w, 1 - ∑_T w)`, and `det φ'(w) = S^{-(m+1)}` by the matrix
determinant lemma.
-/

public section

open MeasureTheory Set Matrix

namespace QED.TwoLoop.UnitXGraph

open QED.Integration.Feynman (simplexSet simplexPoint measurableSet_simplexSet)
open QED.Integration.TwoLoop (simplexPoint_castSucc simplexPoint_last)
open QED.Integration.ChengWu (openSimplex mem_openSimplex simplexSet_ae_eq_openSimplex)

variable {m : ℕ}

/-! ### The sets and the map -/

/-- The Cheng–Wu domain `D_T = {w : wᵢ > 0, ∑_{i ∈ T} wᵢ < 1}`. -/
def cwSet (T : Finset (Fin m)) : Set (Fin m → ℝ) := {w | (∀ i, 0 < w i) ∧ ∑ i ∈ T, w i < 1}

theorem mem_cwSet {T : Finset (Fin m)} {w : Fin m → ℝ} :
    w ∈ cwSet T ↔ (∀ i, 0 < w i) ∧ ∑ i ∈ T, w i < 1 := Iff.rfl

/-- The linear form `ℓ(v) = ∑_{i ∉ T} vᵢ`. -/
noncomputable def cwForm (T : Finset (Fin m)) : (Fin m → ℝ) →L[ℝ] ℝ :=
  ∑ i ∈ Tᶜ, (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ)

theorem cwForm_apply (T : Finset (Fin m)) (w : Fin m → ℝ) : cwForm T w = ∑ i ∈ Tᶜ, w i := by
  simp [cwForm]

/-- The scale `S(w) = 1 + ∑_{i ∉ T} wᵢ`. -/
noncomputable def cwScale (T : Finset (Fin m)) (w : Fin m → ℝ) : ℝ := 1 + cwForm T w

/-- The Cheng–Wu map `φ(w) = w / S(w)`. -/
noncomputable def cwMap (T : Finset (Fin m)) (w : Fin m → ℝ) : Fin m → ℝ := (cwScale T w)⁻¹ • w

theorem isOpen_cwSet (T : Finset (Fin m)) : IsOpen (cwSet T) := by
  have h1 : IsOpen {w : Fin m → ℝ | ∀ i, 0 < w i} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  exact h1.inter (isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i)
    continuous_const)

theorem measurableSet_cwSet (T : Finset (Fin m)) : MeasurableSet (cwSet T) :=
  (isOpen_cwSet T).measurableSet

theorem cwScale_pos {T : Finset (Fin m)} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    0 < cwScale T w := by
  rw [cwScale, cwForm_apply]
  have : 0 ≤ ∑ i ∈ Tᶜ, w i := Finset.sum_nonneg fun i _ => (hw i).le
  linarith

theorem sum_eq_cwScale (T : Finset (Fin m)) (w : Fin m → ℝ) :
    ∑ i, w i = cwScale T w - 1 + ∑ i ∈ T, w i := by
  rw [cwScale, cwForm_apply, ← Finset.sum_add_sum_compl T]
  ring

/-- **The barycentric point of `φ(w)`** is `S⁻¹ (w, 1 - ∑_T w)`. -/
theorem simplexPoint_cwMap {T : Finset (Fin m)} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    simplexPoint (cwMap T w) = (cwScale T w)⁻¹ • Fin.snoc w (1 - ∑ i ∈ T, w i) := by
  have hS := (cwScale_pos (T := T) hw).ne'
  funext k
  induction k using Fin.lastCases with
  | last =>
    rw [simplexPoint_last, Pi.smul_apply, Fin.snoc_last, smul_eq_mul]
    simp only [cwMap, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_eq_cwScale T w]
    field_simp
    ring
  | cast i =>
    rw [simplexPoint_castSucc, Pi.smul_apply, Fin.snoc_castSucc]
    rfl

theorem cwMap_mem {T : Finset (Fin m)} {w : Fin m → ℝ} (hw : w ∈ cwSet T) :
    cwMap T w ∈ openSimplex m := by
  have hS := cwScale_pos (T := T) hw.1
  refine mem_openSimplex.mpr ⟨fun i => ?_, ?_⟩
  · simp only [cwMap, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hS) (hw.1 i)
  · simp only [cwMap, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, sum_eq_cwScale T w]
    rw [inv_mul_lt_iff₀ hS]
    linarith [hw.2]

/-- **`φ` maps `D_T` onto the open simplex.** -/
theorem image_cwMap (T : Finset (Fin m)) : cwMap T '' cwSet T = openSimplex m := by
  refine Set.Subset.antisymm (fun x ⟨w, hw, hx⟩ => hx ▸ cwMap_mem hw) fun x hx₀ => ?_
  have hx := mem_openSimplex.mp hx₀
  set s := ∑ i ∈ T, x i + (1 - ∑ i, x i) with hs_def
  have hT : 0 ≤ ∑ i ∈ T, x i := Finset.sum_nonneg fun i _ => (hx.1 i).le
  have hs : 0 < s := by linarith [hx.2]
  refine ⟨s⁻¹ • x, ⟨fun i => ?_, ?_⟩, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hs) (hx.1 i)
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [inv_mul_lt_iff₀ hs]
    linarith [hx.2]
  · have hS : cwScale T (s⁻¹ • x) = s⁻¹ := by
      rw [cwScale, cwForm_apply]
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      have hsplit := Finset.sum_add_sum_compl T x
      field_simp
      rw [hs_def]
      linarith
    rw [cwMap, hS, inv_inv, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

/-- **`φ` is injective on `D_T`.** -/
theorem injOn_cwMap (T : Finset (Fin m)) : InjOn (cwMap T) (cwSet T) := by
  intro w hw w' hw' h
  have hS := (cwScale_pos (T := T) hw.1).ne'
  have hS' := (cwScale_pos (T := T) hw'.1).ne'
  have hc : ∀ i, (cwScale T w)⁻¹ * w i = (cwScale T w')⁻¹ * w' i := fun i => by
    simpa [cwMap] using congrFun h i
  have hsum : (cwScale T w)⁻¹ * ∑ i ∈ Tᶜ, w i = (cwScale T w')⁻¹ * ∑ i ∈ Tᶜ, w' i := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hc i
  have e : ∀ v : Fin m → ℝ, ∑ i ∈ Tᶜ, v i = cwScale T v - 1 := fun v => by
    rw [cwScale, cwForm_apply]; ring
  rw [e w, e w'] at hsum
  have hSS : cwScale T w = cwScale T w' := by
    have e1 : (cwScale T w)⁻¹ * (cwScale T w - 1) = 1 - (cwScale T w)⁻¹ := by field_simp
    have e2 : (cwScale T w')⁻¹ * (cwScale T w' - 1) = 1 - (cwScale T w')⁻¹ := by field_simp
    rw [e1, e2] at hsum
    have : (cwScale T w)⁻¹ = (cwScale T w')⁻¹ := by linarith
    exact inv_injective this
  funext i
  have := hc i
  rw [hSS] at this
  exact (mul_right_injective₀ (inv_ne_zero hS')) this

/-! ### The derivative and its determinant -/

/-- The derivative `S⁻¹ I - S⁻² w ⊗ ℓ` of the Cheng–Wu map. -/
noncomputable def cwDeriv (T : Finset (Fin m)) (w : Fin m → ℝ) :
    (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  (cwScale T w)⁻¹ • ContinuousLinearMap.id ℝ (Fin m → ℝ) +
    (-((cwScale T w ^ 2)⁻¹) • cwForm T).smulRight w

theorem hasFDerivAt_cwMap {T : Finset (Fin m)} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    HasFDerivAt (cwMap T) (cwDeriv T w) w := by
  have hS : HasFDerivAt (cwScale T) (cwForm T) w := ((cwForm T).hasFDerivAt).const_add 1
  have hinv := (hasFDerivAt_inv (cwScale_pos (T := T) hw).ne').comp w hS
  refine (hinv.smul (hasFDerivAt_id w)).congr_fderiv ?_
  ext v i
  simp [cwDeriv, mul_comm]

theorem toMatrix'_cwDeriv (T : Finset (Fin m)) (w : Fin m → ℝ) :
    LinearMap.toMatrix' (cwDeriv T w : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) =
      (cwScale T w)⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ) +
        replicateCol (Fin 1) w * replicateRow (Fin 1)
          (fun k => -((cwScale T w ^ 2)⁻¹) * cwForm T (Pi.single k 1)) := by
  ext i k
  rw [LinearMap.toMatrix'_apply]
  simp only [cwDeriv, ContinuousLinearMap.coe_coe]
  simp [Matrix.mul_apply, Pi.single_apply, Matrix.one_apply]
  ring

/-- **The Jacobian of the Cheng–Wu map**: `det φ'(w) = S(w)^{-(m+1)}`. -/
theorem det_cwDeriv {T : Finset (Fin m)} {w : Fin m → ℝ} (hw : ∀ i, 0 < w i) :
    (cwDeriv T w).det = (cwScale T w ^ (m + 1))⁻¹ := by
  have hS := (cwScale_pos (T := T) hw).ne'
  set S := cwScale T w
  set v : Fin m → ℝ := fun k => -((S ^ 2)⁻¹) * cwForm T (Pi.single k 1)
  have hdot : v ⬝ᵥ (S • w) = -(S⁻¹ * cwForm T w) := by
    have : cwForm T w = ∑ k, w k * cwForm T (Pi.single k 1) := by
      conv_lhs => rw [show w = ∑ k, w k • Pi.single k (1 : ℝ) from by
        ext i; simp [Finset.sum_apply, Pi.single_apply]]
      simp [map_sum, map_smul]
    rw [this, Finset.mul_sum, ← Finset.sum_neg_distrib]
    simp only [dotProduct, v, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  have hM : (S⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ) +
      replicateCol (Fin 1) w * replicateRow (Fin 1) v) =
      S⁻¹ • (1 + replicateCol (Fin 1) (S • w) * replicateRow (Fin 1) v) := by
    ext i k
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, replicateCol_apply,
      replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', toMatrix'_cwDeriv, hM,
    Matrix.det_smul]
  have hdet : (1 + replicateCol (Fin 1) (S • w) * replicateRow (Fin 1) v).det =
      1 + v ⬝ᵥ (S • w) := by
    rw [det_one_add_mul_comm, Matrix.det_fin_one]
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, replicateRow_apply,
      replicateCol_apply, dotProduct]
  rw [hdet, hdot, Fintype.card_fin]
  have hℓ : cwForm T w = S - 1 := by simp only [S, cwScale]; ring
  rw [hℓ]
  field_simp
  rw [one_div, inv_pow, pow_succ]
  field_simp
  ring

/-! ### The theorem -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem abs_det_smul_cw {T : Finset (Fin m)} {F : (Fin (m + 1) → ℝ) → E}
    (hF : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      F (t • z) = (t ^ (m + 1))⁻¹ • F z)
    {w : Fin m → ℝ} (hw : w ∈ cwSet T) :
    |(cwDeriv T w).det| • F (simplexPoint (cwMap T w)) = F (Fin.snoc w (1 - ∑ i ∈ T, w i)) := by
  have hS := cwScale_pos (T := T) hw.1
  have hz : ∀ i, 0 < (Fin.snoc w (1 - ∑ i ∈ T, w i) : Fin (m + 1) → ℝ) i := fun i => by
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; linarith [hw.2]
    | cast i => simp only [Fin.snoc_castSucc]; exact hw.1 i
  rw [det_cwDeriv hw.1, simplexPoint_cwMap hw.1, hF _ hz _ (inv_pos.mpr hS), smul_smul,
    abs_of_pos (by positivity), inv_pow, inv_inv, inv_mul_cancel₀ (by positivity), one_smul]

/-- **The Cheng–Wu theorem with the constraint on a set `T` of coordinates**: for `F`
homogeneous of degree `-(m+1)` on the open positive orthant,
`∫_{Δₘ} F(z) dx = ∫_{D_T} F(w, 1 - ∑_{i ∈ T} wᵢ) dw`. -/
theorem integral_simplex_chengWuSet (hm : 0 < m) (T : Finset (Fin m))
    (F : (Fin (m + 1) → ℝ) → E)
    (hF : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      F (t • z) = (t ^ (m + 1))⁻¹ • F z) :
    ∫ x in simplexSet m, F (simplexPoint x) =
      ∫ w in cwSet T, F (Fin.snoc w (1 - ∑ i ∈ T, w i)) := by
  rw [setIntegral_congr_set (simplexSet_ae_eq_openSimplex (⟨0, hm⟩ : Fin m)), ← image_cwMap T,
    integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_cwSet T)
      (fun w hw => (hasFDerivAt_cwMap hw.1).hasFDerivWithinAt) (injOn_cwMap T)]
  exact setIntegral_congr_fun (measurableSet_cwSet T) fun w hw => abs_det_smul_cw hF hw

/-- **Integrability in the Cheng–Wu variables.** -/
theorem integrableOn_simplex_chengWuSet_iff (hm : 0 < m) (T : Finset (Fin m))
    (F : (Fin (m + 1) → ℝ) → E)
    (hF : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 < z i) → ∀ t : ℝ, 0 < t →
      F (t • z) = (t ^ (m + 1))⁻¹ • F z) :
    IntegrableOn (fun x => F (simplexPoint x)) (simplexSet m) ↔
      IntegrableOn (fun w => F (Fin.snoc w (1 - ∑ i ∈ T, w i))) (cwSet T) := by
  rw [IntegrableOn, Measure.restrict_congr_set (simplexSet_ae_eq_openSimplex (⟨0, hm⟩ : Fin m)),
    ← IntegrableOn, ← image_cwMap T,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (measurableSet_cwSet T)
      (fun w hw => (hasFDerivAt_cwMap hw.1).hasFDerivWithinAt) (injOn_cwMap T)]
  exact integrableOn_congr_fun (fun w hw => abs_det_smul_cw hF hw) (measurableSet_cwSet T)

end QED.TwoLoop.UnitXGraph

end
