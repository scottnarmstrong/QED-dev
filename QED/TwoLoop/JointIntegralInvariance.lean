/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Invariances of the joint energy-first integral

The joint energy-first integral (T₉) of packet T1 (decision D-38) is invariant under the changes
of loop momenta of obligation O2-6 (`docs/TWO-LOOP-DERIVATION.md`, section 4.3), for every
integrand: no integrability is assumed, because each change acts on both stages by a
measure-preserving equivalence, and on non-integrable data both sides are `0`.

* `QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_add`: real shifts
  `ℓ ↦ ℓ + a`.
* `QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix`: integer unimodular
  changes `ℓ ↦ M ℓ`, `(M ℓ) s = ∑ r, M s r • ℓ r`, acting equally on energies and on spatial
  components.
* `QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_neg`: the reflection
  `ℓ ↦ -ℓ`.
* `QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add`: the combined
  affine change `ℓ ↦ M ℓ + a`.

The mechanism (`jointEnergyFirstIntegral_comp_of_split`): if a change of loop momenta acts on the
energies `t` (at fixed spatial momenta `v`) and on the spatial momenta by maps that leave every
integral unchanged, it leaves the joint integral unchanged. A linear map with determinant `±1`
of a finite-dimensional real space leaves every integral against an additive Haar measure
unchanged (`integral_comp_linearMap_of_abs_det_eq_one`). The matrix acts on the energies
`Fin L → ℝ` with determinant `det M`, and on the spatial momenta `Fin L → Fin 3 → ℝ` with
determinant `(det M)³`, computed by transporting to `Fin 3 → Fin L → ℝ`, where it acts
componentwise.
-/

@[expose] public section

open MeasureTheory

namespace QED.TwoLoop.JointIntegralInvariance

/-! ### The splitting into energies and spatial components -/

/-- The loop momenta with energies `t` and spatial components `v`. -/
def joinMomenta {L : ℕ} (t : Fin L → ℝ) (v : Fin L → Fin 3 → ℝ) : Fin L → Fin 4 → ℝ :=
  fun s => Fin.cons (t s) (v s)

theorem jointEnergyFirstIntegral_eq_joinMomenta (L : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ) :
    jointEnergyFirstIntegral L F = ∫ v, ∫ t, F (joinMomenta t v) :=
  rfl

/-- A self-map of a measure space that leaves every complex integral unchanged. -/
def IntegralInvariant {X : Type*} [MeasureSpace X] (φ : X → X) : Prop :=
  ∀ G : X → ℂ, ∫ x, G (φ x) = ∫ x, G x

/-- A change of loop momenta that acts on the energies at fixed spatial components, and on the
spatial components, by maps that leave every integral unchanged, leaves the joint energy-first
integral unchanged. -/
theorem jointEnergyFirstIntegral_comp_of_split {L : ℕ} (φ : (Fin L → Fin 4 → ℝ) → Fin L → Fin 4 → ℝ)
    (α : (Fin L → Fin 3 → ℝ) → (Fin L → ℝ) → Fin L → ℝ)
    (β : (Fin L → Fin 3 → ℝ) → Fin L → Fin 3 → ℝ)
    (hφ : ∀ t v, φ (joinMomenta t v) = joinMomenta (α v t) (β v))
    (hα : ∀ v, IntegralInvariant (α v)) (hβ : IntegralInvariant β)
    (F : (Fin L → Fin 4 → ℝ) → ℂ) :
    jointEnergyFirstIntegral L (fun ℓ => F (φ ℓ)) = jointEnergyFirstIntegral L F := by
  rw [jointEnergyFirstIntegral_eq_joinMomenta, jointEnergyFirstIntegral_eq_joinMomenta]
  simp only [hφ]
  rw [show (fun v => ∫ t, F (joinMomenta (α v t) (β v))) =
      fun v => ∫ t, F (joinMomenta t (β v)) from
    funext fun v => hα v fun t => F (joinMomenta t (β v))]
  exact hβ fun v => ∫ t, F (joinMomenta t v)

/-! ### Shifts -/

theorem integralInvariant_add_right {X : Type*} [MeasureSpace X] [AddGroup X]
    [MeasurableAdd X] [(volume : Measure X).IsAddRightInvariant] (a : X) :
    IntegralInvariant (fun x : X => x + a) :=
  fun G => integral_add_right_eq_self G a

theorem joinMomenta_add {L : ℕ} (t : Fin L → ℝ) (v : Fin L → Fin 3 → ℝ)
    (a : Fin L → Fin 4 → ℝ) :
    joinMomenta t v + a =
      joinMomenta (t + fun s => a s 0) (v + fun s => Fin.tail (a s)) := by
  funext s i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [joinMomenta, Fin.tail]

/-- **Invariance under real shifts** (O2-6): for every integrand, the joint energy-first integral
is unchanged by `ℓ ↦ ℓ + a`. -/
theorem jointEnergyFirstIntegral_comp_add (L : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ)
    (a : Fin L → Fin 4 → ℝ) :
    jointEnergyFirstIntegral L (fun ℓ => F (ℓ + a)) = jointEnergyFirstIntegral L F :=
  jointEnergyFirstIntegral_comp_of_split (fun ℓ => ℓ + a) (fun _ t => t + fun s => a s 0)
    (fun v => v + fun s => Fin.tail (a s)) (fun t v => joinMomenta_add t v a)
    (fun _ => integralInvariant_add_right _) (integralInvariant_add_right _) F

/-! ### Linear changes of determinant `±1` -/

/-- A linear map of determinant `±1` of a finite-dimensional real space leaves every integral
against an additive Haar measure unchanged. -/
theorem integral_comp_linearMap_of_abs_det_eq_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (f : E →ₗ[ℝ] E) (hf : |LinearMap.det f| = 1)
    (G : E → ℂ) : ∫ x, G (f x) ∂μ = ∫ x, G x ∂μ := by
  have h0 : LinearMap.det f ≠ 0 := by
    intro h
    rw [h, abs_zero] at hf
    exact zero_ne_one hf
  let e : E ≃L[ℝ] E := (f.equivOfDetNeZero h0).toContinuousLinearEquiv
  have he : (e : E → E) = f := rfl
  have hmp : MeasurePreserving e μ μ := by
    refine ⟨e.continuous.measurable, ?_⟩
    rw [he, Measure.map_linearMap_addHaar_eq_smul_addHaar μ h0, abs_inv, hf, inv_one,
      ENNReal.ofReal_one, one_smul]
  exact hmp.integral_comp e.toHomeomorph.measurableEmbedding G

/-- The action `ℓ ↦ (s ↦ ∑ r, M s r • ℓ r)` of an integer matrix on families of vectors. -/
def matrixAct {L : ℕ} (V : Type*) [AddCommGroup V] [Module ℝ V]
    (M : Matrix (Fin L) (Fin L) ℤ) : (Fin L → V) →ₗ[ℝ] (Fin L → V) where
  toFun ℓ s := ∑ r, M s r • ℓ r
  map_add' ℓ ℓ' := by
    funext s
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' c ℓ := by
    funext s
    simp [Finset.smul_sum, smul_comm c]

theorem matrixAct_apply {L : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : Matrix (Fin L) (Fin L) ℤ) (ℓ : Fin L → V) (s : Fin L) :
    matrixAct V M ℓ s = ∑ r, M s r • ℓ r :=
  rfl

/-- On the energies the action is the real matrix of `M`, of determinant `det M`. -/
theorem det_matrixAct_real {L : ℕ} (M : Matrix (Fin L) (Fin L) ℤ) :
    LinearMap.det (matrixAct ℝ M) = (M.det : ℝ) := by
  have h : matrixAct ℝ M = Matrix.toLin' (M.map (Int.cast : ℤ → ℝ)) := by
    refine LinearMap.ext fun t => funext fun s => ?_
    simp [matrixAct_apply, Matrix.mulVec, dotProduct, zsmul_eq_mul]
  rw [h, LinearMap.det_toLin', ← Int.cast_det]

/-- Exchanging the two indices of a family of families, as a linear equivalence. -/
def piSwap (n L : ℕ) : (Fin n → Fin L → ℝ) ≃ₗ[ℝ] (Fin L → Fin n → ℝ) where
  toFun w s i := w i s
  invFun v i s := v s i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- On families of vectors of `ℝⁿ` the action has determinant `(det M)ⁿ`: after exchanging the
indices it acts componentwise. -/
theorem det_matrixAct_pi {L : ℕ} (n : ℕ) (M : Matrix (Fin L) (Fin L) ℤ) :
    LinearMap.det (matrixAct (Fin n → ℝ) M) = (M.det : ℝ) ^ n := by
  have h : matrixAct (Fin n → ℝ) M =
      (piSwap n L : (Fin n → Fin L → ℝ) →ₗ[ℝ] (Fin L → Fin n → ℝ)) ∘ₗ
        LinearMap.pi (fun i => (matrixAct ℝ M).comp (LinearMap.proj i)) ∘ₗ
        ((piSwap n L).symm : (Fin L → Fin n → ℝ) →ₗ[ℝ] (Fin n → Fin L → ℝ)) := by
    refine LinearMap.ext fun v => funext fun s => funext fun i => ?_
    simp [matrixAct_apply, piSwap, Finset.sum_apply]
  rw [h, LinearMap.det_conj, LinearMap.det_pi, det_matrixAct_real, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

theorem abs_intCast_det_eq_one {L : ℕ} {M : Matrix (Fin L) (Fin L) ℤ} (hM : IsUnit M.det) :
    |(M.det : ℝ)| = 1 := by
  rcases Int.isUnit_iff.mp hM with h | h <;> simp [h]

/-- **Invariance under integer unimodular changes** (O2-6): for every integrand, the joint
energy-first integral is unchanged by `ℓ ↦ M ℓ`, `(M ℓ) s = ∑ r, M s r • ℓ r`, for an integer
matrix `M` with `det M = ±1`, acting equally on energies and on spatial components. -/
theorem jointEnergyFirstIntegral_comp_matrix (L : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ)
    (M : Matrix (Fin L) (Fin L) ℤ) (hM : IsUnit M.det) :
    jointEnergyFirstIntegral L (fun ℓ => F (fun s => ∑ r, M s r • ℓ r)) =
      jointEnergyFirstIntegral L F := by
  have hdet := abs_intCast_det_eq_one hM
  refine jointEnergyFirstIntegral_comp_of_split (fun ℓ s => ∑ r, M s r • ℓ r)
    (fun _ t => matrixAct ℝ M t) (fun v => matrixAct (Fin 3 → ℝ) M v) (fun t v => ?_)
    (fun _ G => ?_) (fun G => ?_) F
  · funext s i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [joinMomenta, matrixAct_apply, Finset.sum_apply]
  · refine integral_comp_linearMap_of_abs_det_eq_one volume _ ?_ G
    rw [det_matrixAct_real, hdet]
  · refine integral_comp_linearMap_of_abs_det_eq_one volume _ ?_ G
    rw [det_matrixAct_pi, abs_pow, hdet, one_pow]

/-- **Invariance under the reflection** `ℓ ↦ -ℓ` (O2-6), for every integrand. -/
theorem jointEnergyFirstIntegral_comp_neg (L : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ) :
    jointEnergyFirstIntegral L (fun ℓ => F (-ℓ)) = jointEnergyFirstIntegral L F := by
  have hM : IsUnit (-1 : Matrix (Fin L) (Fin L) ℤ).det := by
    rw [Matrix.det_neg, Matrix.det_one, mul_one]
    exact (isUnit_one.neg).pow _
  have h := jointEnergyFirstIntegral_comp_matrix L F (-1) hM
  have hneg : ∀ ℓ : Fin L → Fin 4 → ℝ,
      (fun s => ∑ r, (-1 : Matrix (Fin L) (Fin L) ℤ) s r • ℓ r) = -ℓ := by
    intro ℓ
    funext s
    simp [Matrix.neg_apply, Matrix.one_apply, ite_smul, Finset.sum_neg_distrib]
  simpa only [hneg] using h

/-- **Invariance under integer unimodular affine changes** `ℓ ↦ M ℓ + a` (O2-6), for every
integrand. -/
theorem jointEnergyFirstIntegral_comp_matrix_add (L : ℕ) (F : (Fin L → Fin 4 → ℝ) → ℂ)
    (M : Matrix (Fin L) (Fin L) ℤ) (hM : IsUnit M.det) (a : Fin L → Fin 4 → ℝ) :
    jointEnergyFirstIntegral L (fun ℓ => F ((fun s => ∑ r, M s r • ℓ r) + a)) =
      jointEnergyFirstIntegral L F := by
  rw [jointEnergyFirstIntegral_comp_matrix L (fun ℓ => F (ℓ + a)) M hM,
    jointEnergyFirstIntegral_comp_add]

end QED.TwoLoop.JointIntegralInvariance

end
