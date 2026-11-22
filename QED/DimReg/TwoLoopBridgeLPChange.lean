/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Basic
public import QED.Integration.ChengWu
public import QED.Integration.TwoLoopParametricAlgebra
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The orthant as a cone over the open simplex

The change of variables `z = s · (x, 1 - ∑ x)` maps `(0, ∞) × Δₘ°` (with `Δₘ°` the open simplex
`QED.Integration.ChengWu.openSimplex m`) bijectively onto the open orthant `(0, ∞)^(m+1)`, with
Jacobian `s^m`. This is the step that turns the Lee–Pomeransky integral over the orthant
(`QED.DimReg.lpIntegral`) into the projective integral over the simplex.

We realize it on `ℝ^(m+1)` as `rayMap y = y_m · simplexPoint (y_0, …, y_{m-1})` on the set
`raySet m = {y : (y_0, …, y_{m-1}) ∈ Δₘ°, y_m > 0}`. Its derivative factors as a lower
unitriangular shear after an upper triangular map with diagonal `(y_m, …, y_m, 1)`, so its
determinant is `y_m ^ m` (`det_rayDeriv`). Splitting off the last coordinate
(`MeasurableEquiv.piFinSuccAbove`) and Fubini give the cone formula.

## Main results

* `QED.DimReg.LPChange.integral_posOrthant_eq_raySet`: `∫_{(0,∞)^(m+1)} f = ∫_{raySet} y_m^m f`.
* `QED.DimReg.LPChange.integrableOn_posOrthant_iff`: integrability on the orthant is that of
  `(s, x) ↦ s^m f(s · simplexPoint x)` on `(0, ∞) ×ˢ Δₘ°`.
* `QED.DimReg.LPChange.integral_posOrthant_eq_cone`: for `f` integrable on the orthant,
  `∫_{(0,∞)^(m+1)} f = ∫_{Δₘ°} ∫_0^∞ s^m f(s · simplexPoint x) ds dx`.
-/

@[expose] public section

open MeasureTheory Set Matrix

namespace QED.DimReg.LPChange

open QED.Integration.Feynman (simplexPoint)
open QED.Integration.ChengWu (openSimplex mem_openSimplex)
open QED.Integration.TwoLoop (simplexPoint_castSucc simplexPoint_last sum_simplexPoint)

variable {m : ℕ}

/-- The source domain `{y : (y_0, …, y_{m-1}) ∈ Δₘ°, y_m > 0}`. -/
def raySet (m : ℕ) : Set (Fin (m + 1) → ℝ) :=
  {y | Fin.init y ∈ openSimplex m ∧ 0 < y (Fin.last m)}

/-- The cone map `y ↦ y_m · simplexPoint (y_0, …, y_{m-1})`. -/
noncomputable def rayMap (y : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  y (Fin.last m) • simplexPoint (Fin.init y)

theorem rayMap_castSucc (y : Fin (m + 1) → ℝ) (j : Fin m) :
    rayMap y j.castSucc = y (Fin.last m) * y j.castSucc := by
  simp [rayMap, simplexPoint_castSucc, Fin.init]

theorem rayMap_last (y : Fin (m + 1) → ℝ) :
    rayMap y (Fin.last m) = y (Fin.last m) * (1 - ∑ j : Fin m, y j.castSucc) := by
  simp [rayMap, simplexPoint_last, Fin.init]

theorem isOpen_openSimplex : IsOpen (openSimplex m) := by
  have h : openSimplex m = (⋂ i, {x : Fin m → ℝ | 0 < x i}) ∩ {x | ∑ i, x i < 1} := by
    ext x; simp [mem_openSimplex]
  rw [h]
  exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)

theorem measurableSet_openSimplex : MeasurableSet (openSimplex m) :=
  isOpen_openSimplex.measurableSet

theorem isOpen_raySet : IsOpen (raySet m) :=
  (isOpen_openSimplex.preimage (continuous_pi fun _ => continuous_apply _)).inter
    (isOpen_lt continuous_const (continuous_apply _))

theorem measurableSet_raySet : MeasurableSet (raySet m) :=
  isOpen_raySet.measurableSet

/-! ### The image and injectivity -/

theorem sum_rayMap (y : Fin (m + 1) → ℝ) : ∑ i, rayMap y i = y (Fin.last m) := by
  simp [rayMap, Pi.smul_apply, ← Finset.mul_sum, sum_simplexPoint]

theorem injOn_rayMap : InjOn (rayMap (m := m)) (raySet m) := by
  intro y hy y' hy' h
  have hs : y (Fin.last m) = y' (Fin.last m) := by rw [← sum_rayMap y, h, sum_rayMap y']
  funext i
  induction i using Fin.lastCases with
  | last => exact hs
  | cast j =>
    have := congrFun h j.castSucc
    rw [rayMap_castSucc, rayMap_castSucc, hs] at this
    exact mul_left_cancel₀ hy'.2.ne' this

theorem image_rayMap : rayMap '' raySet m = DimReg.posOrthant (m + 1) := by
  ext z
  rw [DimReg.mem_posOrthant]
  constructor
  · rintro ⟨y, ⟨hx, hs⟩, rfl⟩ i
    rw [mem_openSimplex] at hx
    induction i using Fin.lastCases with
    | last => rw [rayMap_last]; exact mul_pos hs (by simpa [Fin.init] using hx.2)
    | cast j => rw [rayMap_castSucc]; exact mul_pos hs (hx.1 j)
  · intro hz
    set S := ∑ i, z i
    have hS : 0 < S := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
    refine ⟨Fin.snoc (fun j => z j.castSucc / S) S, ⟨?_, by simpa using hS⟩, ?_⟩
    · rw [mem_openSimplex]
      refine ⟨fun j => by simpa [Fin.init] using div_pos (hz _) hS, ?_⟩
      have hsum : S = ∑ j : Fin m, z j.castSucc + z (Fin.last m) := Fin.sum_univ_castSucc z
      simp only [Fin.init, Fin.snoc_castSucc]
      rw [← Finset.sum_div, div_lt_one hS]
      linarith [hz (Fin.last m)]
    · have hsum : S = ∑ j : Fin m, z j.castSucc + z (Fin.last m) := Fin.sum_univ_castSucc z
      funext i
      induction i using Fin.lastCases with
      | last =>
        rw [rayMap_last]
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [← Finset.sum_div]
        field_simp
        linarith
      | cast j =>
        rw [rayMap_castSucc]
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        field_simp

/-! ### The derivative and its determinant -/

/-- The shear `z ↦ (z_0, …, z_{m-1}, z_m - ∑_{j<m} z_j)`. -/
noncomputable def shear (m : ℕ) : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
  ContinuousLinearMap.pi fun i => Fin.lastCases (motive := fun _ => (Fin (m + 1) → ℝ) →L[ℝ] ℝ)
    (ContinuousLinearMap.proj (Fin.last m) -
      ∑ j : Fin m, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) j.castSucc)
    (fun j => ContinuousLinearMap.proj j.castSucc) i

/-- The triangular part `v ↦ (y_m v_j + y_j v_m, …, v_m)`. -/
noncomputable def rayTri (y : Fin (m + 1) → ℝ) : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
  ContinuousLinearMap.pi fun i => Fin.lastCases (motive := fun _ => (Fin (m + 1) → ℝ) →L[ℝ] ℝ)
    (ContinuousLinearMap.proj (Fin.last m))
    (fun j => y (Fin.last m) • ContinuousLinearMap.proj j.castSucc +
      y j.castSucc • ContinuousLinearMap.proj (Fin.last m)) i

/-- The derivative of `rayMap`. -/
noncomputable def rayDeriv (y : Fin (m + 1) → ℝ) : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
  (shear m).comp (rayTri y)

theorem rayDeriv_castSucc (y v : Fin (m + 1) → ℝ) (j : Fin m) :
    rayDeriv y v j.castSucc = y (Fin.last m) * v j.castSucc + y j.castSucc * v (Fin.last m) := by
  simp [rayDeriv, shear, rayTri]

theorem rayDeriv_last (y v : Fin (m + 1) → ℝ) :
    rayDeriv y v (Fin.last m) = (1 - ∑ j : Fin m, y j.castSucc) * v (Fin.last m) -
      y (Fin.last m) * ∑ j : Fin m, v j.castSucc := by
  simp [rayDeriv, shear, rayTri, Finset.sum_add_distrib]
  simp only [Finset.mul_sum, Finset.sum_mul, sub_mul, one_mul]
  ring

theorem hasFDerivAt_rayMap (y : Fin (m + 1) → ℝ) : HasFDerivAt rayMap (rayDeriv y) y := by
  rw [hasFDerivAt_pi']
  intro i
  induction i using Fin.lastCases with
  | last =>
    simp only [rayMap_last]
    have h := (hasFDerivAt_apply (𝕜 := ℝ) (Fin.last m) y).mul
      ((hasFDerivAt_const (1 : ℝ) y).sub (HasFDerivAt.fun_sum (u := Finset.univ)
        fun j _ => hasFDerivAt_apply (𝕜 := ℝ) (j : Fin m).castSucc y))
    refine h.congr_fderiv ?_
    ext v
    simp [rayDeriv_last]
    ring
  | cast j =>
    simp only [rayMap_castSucc]
    refine ((hasFDerivAt_apply (𝕜 := ℝ) (Fin.last m) y).mul
      (hasFDerivAt_apply (𝕜 := ℝ) j.castSucc y)).congr_fderiv ?_
    ext v
    simp [rayDeriv_castSucc]

theorem det_shear : (shear m).det = 1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix',
    det_of_isLowerTriangular _ ?_]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [LinearMap.toMatrix'_apply]
    induction i using Fin.lastCases with
    | last => simp [shear, Fin.castSucc_ne_last]
    | cast j => simp [shear]
  · intro i k hik
    rw [LinearMap.toMatrix'_apply]
    induction i using Fin.lastCases with
    | last => exact absurd hik (not_lt.2 (Fin.le_last k))
    | cast j =>
      simp only [shear, ContinuousLinearMap.coe_coe, ContinuousLinearMap.pi_apply,
        Fin.lastCases_castSucc, ContinuousLinearMap.proj_apply]
      have : j.castSucc ≠ k := ne_of_lt (OrderDual.toDual_lt_toDual.1 hik)
      simp [this]

theorem det_rayTri (y : Fin (m + 1) → ℝ) : (rayTri y).det = y (Fin.last m) ^ m := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', det_of_isUpperTriangular ?_]
  · rw [Fin.prod_univ_castSucc]
    simp [LinearMap.toMatrix'_apply, rayTri, Fin.castSucc_ne_last]
  · intro i k hik
    rw [LinearMap.toMatrix'_apply]
    induction i using Fin.lastCases with
    | last =>
      have : Fin.last m ≠ k := (ne_of_lt (by simpa using hik)).symm
      simp [rayTri, this]
    | cast j =>
      have h1 : j.castSucc ≠ k := (ne_of_lt hik).symm
      have h2 : Fin.last m ≠ k := fun h => absurd hik (h ▸ not_lt.2 (Fin.le_last _))
      simp [rayTri, h1, h2]

theorem det_rayDeriv (y : Fin (m + 1) → ℝ) : (rayDeriv y).det = y (Fin.last m) ^ m := by
  rw [rayDeriv, ContinuousLinearMap.det]
  change LinearMap.det ((shear m : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ)) ∘ₗ
    (rayTri y : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ))) = _
  rw [LinearMap.det_comp]
  exact (congrArg₂ (· * ·) det_shear (det_rayTri y)).trans (one_mul _)

/-! ### The change of variables -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem abs_det_rayDeriv {y : Fin (m + 1) → ℝ} (hy : y ∈ raySet m) :
    |(rayDeriv y).det| = y (Fin.last m) ^ m := by
  rw [det_rayDeriv, abs_of_pos (pow_pos hy.2 _)]

/-- **The orthant in cone coordinates.** -/
theorem integral_posOrthant_eq_raySet (f : (Fin (m + 1) → ℝ) → E) :
    ∫ z in DimReg.posOrthant (m + 1), f z =
      ∫ y in raySet m, y (Fin.last m) ^ m • f (rayMap y) := by
  rw [← image_rayMap, integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_raySet
    (fun y _ => (hasFDerivAt_rayMap y).hasFDerivWithinAt) injOn_rayMap]
  exact setIntegral_congr_fun measurableSet_raySet fun y hy => by rw [abs_det_rayDeriv hy]

theorem integrableOn_posOrthant_iff_raySet (f : (Fin (m + 1) → ℝ) → E) :
    IntegrableOn f (DimReg.posOrthant (m + 1)) ↔
      IntegrableOn (fun y => y (Fin.last m) ^ m • f (rayMap y)) (raySet m) := by
  rw [← image_rayMap, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    measurableSet_raySet (fun y _ => (hasFDerivAt_rayMap y).hasFDerivWithinAt) injOn_rayMap]
  exact integrableOn_congr_fun (fun y hy => by rw [abs_det_rayDeriv hy]) measurableSet_raySet

/-! ### Splitting off the ray coordinate -/

/-- The splitting `y ↦ (y_m, (y_0, …, y_{m-1}))`. -/
noncomputable abbrev splitLast (m : ℕ) : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m)

theorem measurePreserving_splitLast :
    MeasurePreserving (splitLast m) volume (volume.prod volume) := by
  simpa [volume_pi] using
    measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => (volume : Measure ℝ)) (Fin.last m)

theorem splitLast_apply (y : Fin (m + 1) → ℝ) : splitLast m y = (y (Fin.last m), Fin.init y) := by
  simp [splitLast, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]

theorem raySet_eq_preimage : raySet m = splitLast m ⁻¹' (Ioi 0 ×ˢ openSimplex m) := by
  ext y
  simp [raySet, and_comm]

/-- The cone integrand `(s, x) ↦ s^m f(s · simplexPoint x)`. -/
noncomputable def coneIntegrand (f : (Fin (m + 1) → ℝ) → E) (p : ℝ × (Fin m → ℝ)) : E :=
  p.1 ^ m • f (p.1 • simplexPoint p.2)

theorem coneIntegrand_splitLast (f : (Fin (m + 1) → ℝ) → E) (y : Fin (m + 1) → ℝ) :
    coneIntegrand f (splitLast m y) = y (Fin.last m) ^ m • f (rayMap y) := by
  rw [splitLast_apply]; rfl

/-- **Integrability in cone coordinates.** -/
theorem integrableOn_posOrthant_iff (f : (Fin (m + 1) → ℝ) → E) :
    IntegrableOn f (DimReg.posOrthant (m + 1)) ↔
      IntegrableOn (coneIntegrand f) (Ioi 0 ×ˢ openSimplex m) (volume.prod volume) := by
  rw [integrableOn_posOrthant_iff_raySet, raySet_eq_preimage]
  simp_rw [← coneIntegrand_splitLast]
  exact measurePreserving_splitLast.integrableOn_comp_preimage (f := coneIntegrand f)
    (splitLast m).measurableEmbedding

theorem integral_posOrthant_eq_prod (f : (Fin (m + 1) → ℝ) → E) :
    ∫ z in DimReg.posOrthant (m + 1), f z =
      ∫ p in Ioi 0 ×ˢ openSimplex m, coneIntegrand f p ∂(volume.prod volume) := by
  rw [integral_posOrthant_eq_raySet, raySet_eq_preimage]
  simp_rw [← coneIntegrand_splitLast]
  exact measurePreserving_splitLast.setIntegral_preimage_emb (splitLast m).measurableEmbedding
    _ _

/-- **The cone formula**: for `f` integrable on the orthant,
`∫_{(0,∞)^(m+1)} f = ∫_{Δₘ°} ∫_0^∞ s^m f(s · simplexPoint x) ds dx`. -/
theorem integral_posOrthant_eq_cone (f : (Fin (m + 1) → ℝ) → E)
    (hf : IntegrableOn f (DimReg.posOrthant (m + 1))) :
    ∫ z in DimReg.posOrthant (m + 1), f z =
      ∫ x in openSimplex m, ∫ s in Ioi (0 : ℝ), s ^ m • f (s • simplexPoint x) := by
  rw [integral_posOrthant_eq_prod]
  have hi := (integrableOn_posOrthant_iff f).1 hf
  rw [IntegrableOn, ← Measure.prod_restrict] at hi
  rw [← Measure.prod_restrict, integral_prod _ hi,
    integral_integral_swap (f := fun s x => coneIntegrand f (s, x)) hi]
  rfl

end QED.DimReg.LPChange
