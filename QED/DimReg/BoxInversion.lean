/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.DimReg.Convergence
public import QED.DimReg.CubeSplit
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The orthant as a union of inverted unit cubes

The open orthant `(0, ∞)^N` is the disjoint union of the `2^N` boxes
`B_T = {x | xᵢ > 1 for i ∈ T, 0 < xᵢ ≤ 1 for i ∉ T}` of `QED.DimReg.Convergence`
(`QED.DimReg.posOrthant_eq_iUnion_box`, `QED.DimReg.pairwise_disjoint_box`). The inversion
`xᵢ ↦ 1 / xᵢ` of the coordinates in `T` (`QED.DimReg.boxInv`) maps the unit cube
`Q = (0, 1]^N` onto `B_T` up to the null set `{yᵢ = 1 for some i ∈ T}`, with Jacobian
`∏_{i ∈ T} yᵢ⁻²` (`QED.DimReg.boxJac`). Hence

  `∫_{(0,∞)^N} f = Σ_T ∫_Q (∏_{i ∈ T} yᵢ⁻²) f(boxInv T y) dy`

(`QED.DimReg.integral_posOrthant_eq_sum_box`), and `f` is integrable on the orthant iff every
pulled-back integrand is integrable on `Q` (`QED.DimReg.integrableOn_posOrthant_iff_box`). This
reduces the Lee–Pomeransky integral over the orthant to `2^N` integrals over the unit cube, the
domain of sector decomposition (`QED.DimReg.SplitTree.integral_eq_sum`).

## Main results

* `QED.DimReg.posOrthant_eq_iUnion_box`, `QED.DimReg.pairwise_disjoint_box`.
* `QED.DimReg.integral_box_eq`, `QED.DimReg.integrableOn_box_iff`: the change of variables on one
  box.
* `QED.DimReg.integral_posOrthant_eq_sum_box`, `QED.DimReg.integrableOn_posOrthant_iff_box`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.DimReg

variable {N : ℕ}

/-! ### The boxes partition the orthant -/

theorem posOrthant_eq_iUnion_box : posOrthant N = ⋃ T : Finset (Fin N), box T := by
  refine subset_antisymm posOrthant_subset_iUnion_box ?_
  intro x hx
  obtain ⟨T, hT⟩ := mem_iUnion.mp hx
  rw [mem_posOrthant]
  intro i
  have h := hT i (mem_univ i)
  unfold boxSide at h
  split_ifs at h with hi
  · exact zero_lt_one.trans h
  · exact h.1

theorem pairwise_disjoint_box :
    Pairwise (Function.onFun Disjoint (box : Finset (Fin N) → Set (Fin N → ℝ))) := by
  intro T T' hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  apply hne
  ext i
  have h := hx i (mem_univ i)
  have h' := hx' i (mem_univ i)
  unfold boxSide at h h'
  by_cases hi : i ∈ T <;> by_cases hi' : i ∈ T' <;> simp only [hi, hi', ite_true, ite_false] at h h'
  · simp [hi, hi']
  · exact absurd h'.2 (not_le.mpr h)
  · exact absurd h.2 (not_le.mpr h')
  · simp [hi, hi']

/-! ### The inversion -/

/-- The inversion `yᵢ ↦ 1 / yᵢ` of the coordinates in `T`. -/
noncomputable def boxInv (T : Finset (Fin N)) (y : Fin N → ℝ) : Fin N → ℝ :=
  fun i => if i ∈ T then (y i)⁻¹ else y i

/-- The Jacobian `∏_{i ∈ T} yᵢ⁻²` of the inversion on the unit cube. -/
noncomputable def boxJac (T : Finset (Fin N)) (y : Fin N → ℝ) : ℝ := ∏ i ∈ T, (y i ^ 2)⁻¹

theorem boxInv_boxInv (T : Finset (Fin N)) (y : Fin N → ℝ) : boxInv T (boxInv T y) = y := by
  funext i
  by_cases hi : i ∈ T <;> simp [boxInv, hi]

theorem boxInv_injective (T : Finset (Fin N)) : Function.Injective (boxInv T) :=
  Function.LeftInverse.injective (boxInv_boxInv T)

/-- The diagonal entries of the derivative of `boxInv T` at `y`. -/
noncomputable def boxInvDiag (T : Finset (Fin N)) (y : Fin N → ℝ) : Fin N → ℝ :=
  fun i => if i ∈ T then -(y i ^ 2)⁻¹ else 1

/-- The derivative of `boxInv T` at `y`: a diagonal map. -/
noncomputable def boxInvDeriv (T : Finset (Fin N)) (y : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.diagonal (boxInvDiag T y)))

theorem boxInvDeriv_apply (T : Finset (Fin N)) (y v : Fin N → ℝ) (i : Fin N) :
    boxInvDeriv T y v i = boxInvDiag T y i * v i := by
  simp [boxInvDeriv, Matrix.mulVec_diagonal]

theorem det_boxInvDeriv (T : Finset (Fin N)) (y : Fin N → ℝ) :
    (boxInvDeriv T y).det = ∏ i, boxInvDiag T y i := by
  rw [boxInvDeriv, ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap,
    LinearMap.det_toLin', Matrix.det_diagonal]

theorem abs_det_boxInvDeriv (T : Finset (Fin N)) (y : Fin N → ℝ) :
    |(boxInvDeriv T y).det| = boxJac T y := by
  rw [det_boxInvDeriv, Finset.abs_prod, boxJac, ← Finset.prod_filter_mul_prod_filter_not
    Finset.univ (· ∈ T)]
  have h1 : ∏ i ∈ Finset.univ.filter (· ∈ T), |boxInvDiag T y i| = ∏ i ∈ T, (y i ^ 2)⁻¹ := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp [boxInvDiag, hi, abs_inv, sq_abs]
  have h2 : ∏ i ∈ Finset.univ.filter (· ∉ T), |boxInvDiag T y i| = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    simp only [Finset.mem_filter] at hi
    simp [boxInvDiag, hi.2]
  rw [h1, h2, mul_one]

theorem hasFDerivAt_boxInv (T : Finset (Fin N)) {y : Fin N → ℝ} (hy : ∀ i, y i ≠ 0) :
    HasFDerivAt (boxInv T) (boxInvDeriv T y) y := by
  rw [hasFDerivAt_pi']
  intro i
  by_cases hi : i ∈ T
  · have h := (hasDerivAt_inv (hy i)).comp_hasFDerivAt y (hasFDerivAt_apply (𝕜 := ℝ) i y)
    convert h using 1
    · funext x; simp [boxInv, hi]
    · ext v; simp [boxInvDeriv_apply, boxInvDiag, hi]
  · have h := hasFDerivAt_apply (𝕜 := ℝ) i y
    convert h using 1
    · funext x; simp [boxInv, hi]
    · ext v; simp [boxInvDeriv_apply, boxInvDiag, hi]

/-! ### The change of variables on one box -/

/-- The part of the unit cube that the inversion maps onto `box T`: `yᵢ < 1` for `i ∈ T`. -/
def cubeOpen (T : Finset (Fin N)) : Set (Fin N → ℝ) := {y ∈ unitCube N | ∀ i ∈ T, y i < 1}

theorem measurableSet_cubeOpen (T : Finset (Fin N)) : MeasurableSet (cubeOpen T) := by
  have : cubeOpen T = unitCube N ∩ ⋂ i ∈ T, {y | y i < 1} := by ext; simp [cubeOpen]
  rw [this]
  exact (measurableSet_unitCube N).inter (Finset.measurableSet_biInter T fun i _ =>
    measurableSet_lt (measurable_pi_apply i) measurable_const)

theorem image_boxInv_cubeOpen (T : Finset (Fin N)) : boxInv T '' cubeOpen T = box T := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hT⟩, rfl⟩
    have hy' := mem_unitCube.mp hy
    intro i _
    unfold boxSide
    by_cases hi : i ∈ T
    · simp only [hi, ite_true, boxInv, mem_Ioi]
      exact one_lt_inv_iff₀.mpr ⟨(hy' i).1, hT i hi⟩
    · simp only [hi, ite_false, boxInv]
      exact hy' i
  · intro hx
    refine ⟨boxInv T x, ⟨mem_unitCube.mpr fun i => ?_, fun i hi => ?_⟩, boxInv_boxInv T x⟩
    · have h := hx i (mem_univ i)
      unfold boxSide at h
      by_cases hi : i ∈ T
      · simp only [hi, ite_true, mem_Ioi] at h
        simp only [boxInv, hi, ite_true]
        exact ⟨inv_pos.mpr (zero_lt_one.trans h), inv_le_one_of_one_le₀ h.le⟩
      · simp only [hi, ite_false] at h
        simpa [boxInv, hi] using h
    · have h := hx i (mem_univ i)
      simp only [boxSide, hi, ite_true, mem_Ioi] at h
      simp only [boxInv, hi, ite_true]
      exact inv_lt_one_of_one_lt₀ h

/-- A coordinate hyperplane `{yᵢ = c}` is Lebesgue-null. -/
theorem volume_coord_eq (i : Fin N) (c : ℝ) : volume {y : Fin N → ℝ | y i = c} = 0 := by
  have hsub : {y : Fin N → ℝ | y i = c} ⊆ univ.pi (Function.update (fun _ => univ) i {c}) := by
    intro y hy j _
    by_cases hj : j = i
    · subst hj; simpa using hy
    · simp [Function.update_of_ne hj]
  refine measure_mono_null hsub ?_
  rw [volume_pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem cubeOpen_ae_eq (T : Finset (Fin N)) : cubeOpen T =ᵐ[volume] unitCube N := by
  refine ae_eq_set.mpr ⟨by rw [sdiff_eq_empty.mpr (fun y hy => hy.1)]; simp, ?_⟩
  refine measure_mono_null (t := ⋃ i ∈ T, {y : Fin N → ℝ | y i = 1}) ?_
    ((measure_biUnion_null_iff T.countable_toSet).mpr fun i _ => volume_coord_eq i 1)
  intro y ⟨hy, hn⟩
  simp only [cubeOpen, mem_ofPred_eq, not_and, not_forall, not_lt] at hn
  obtain ⟨i, hi, h1⟩ := hn hy
  exact mem_iUnion₂.mpr ⟨i, hi, le_antisymm ((mem_unitCube.mp hy) i).2 h1⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cubeOpen_pos {T : Finset (Fin N)} {y : Fin N → ℝ} (hy : y ∈ cubeOpen T) (i : Fin N) :
    y i ≠ 0 :=
  ((mem_unitCube.mp hy.1) i).1.ne'

/-- **The change of variables on a box.** -/
theorem integral_box_eq (T : Finset (Fin N)) (f : (Fin N → ℝ) → E) :
    ∫ x in box T, f x = ∫ y in unitCube N, boxJac T y • f (boxInv T y) := by
  rw [← image_boxInv_cubeOpen T, integral_image_eq_integral_abs_det_fderiv_smul volume
    (measurableSet_cubeOpen T)
    (fun y hy => (hasFDerivAt_boxInv T (cubeOpen_pos hy)).hasFDerivWithinAt)
    (boxInv_injective T).injOn f, setIntegral_congr_set (cubeOpen_ae_eq T)]
  simp only [abs_det_boxInvDeriv]

theorem integrableOn_box_iff (T : Finset (Fin N)) (f : (Fin N → ℝ) → E) :
    IntegrableOn f (box T) ↔ IntegrableOn (fun y => boxJac T y • f (boxInv T y)) (unitCube N) := by
  rw [← image_boxInv_cubeOpen T, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (measurableSet_cubeOpen T)
    (fun y hy => (hasFDerivAt_boxInv T (cubeOpen_pos hy)).hasFDerivWithinAt)
    (boxInv_injective T).injOn f, integrableOn_congr_set_ae (cubeOpen_ae_eq T)]
  simp only [abs_det_boxInvDeriv]

/-! ### The orthant -/

theorem integrableOn_posOrthant_iff_box (f : (Fin N → ℝ) → E) :
    IntegrableOn f (posOrthant N) ↔
      ∀ T : Finset (Fin N), IntegrableOn (fun y => boxJac T y • f (boxInv T y)) (unitCube N) := by
  rw [posOrthant_eq_iUnion_box, integrableOn_finite_iUnion]
  exact forall_congr' fun T => integrableOn_box_iff T f

/-- **The orthant as `2^N` inverted unit cubes.** For `f` integrable on the orthant,
`∫_{(0,∞)^N} f = Σ_T ∫_Q (∏_{i ∈ T} yᵢ⁻²) f(boxInv T y) dy`. -/
theorem integral_posOrthant_eq_sum_box [CompleteSpace E] {f : (Fin N → ℝ) → E}
    (hf : IntegrableOn f (posOrthant N)) :
    ∫ x in posOrthant N, f x =
      ∑ T : Finset (Fin N), ∫ y in unitCube N, boxJac T y • f (boxInv T y) := by
  rw [posOrthant_eq_iUnion_box] at hf ⊢
  rw [integral_iUnion_fintype measurableSet_box pairwise_disjoint_box
    (fun T => hf.mono_set (subset_iUnion _ T))]
  exact Finset.sum_congr rfl fun T _ => integral_box_eq T f

end QED.DimReg
