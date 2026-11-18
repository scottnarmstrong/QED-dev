/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopMoments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Fourth moments of the two-loop energy and spatial integrals

Infrastructure for the parametric representation with numerators of degree at most four in the
loop momenta (obligations O2-10 and O2-11, `docs/TWO-LOOP-DERIVATION.md`, section 4.4), extending
`QED/Integration/TwoLoopMoments.lean`. With `U = det A` for a positive definite real `2 × 2`
matrix `A`, `Im w < 0`, and the pairing sums
`Πₛᵣₜq(B) = Bₛᵣ Bₜq + Bₛₜ Bᵣq + Bₛq Bᵣₜ`:

* energies, `u ∈ ℝ²`, `n ≥ 4`:
  `∫ uₛ uᵣ uₜ u_q (-uᵀAu + w)^{-n} du = -π/(4(n-1)(n-2)(n-3)) Πₛᵣₜq(A⁻¹) U^{-1/2} w^{3-n}`;
* spatial momenta, `y ∈ (ℝ³)²`, `k ≥ 6`:
  `∫ y_{sc} y_{rd} y_{te} y_{qf} (yᵀAy + w)^{-k} dy = π³/(4(k-1)⋯(k-5)) Π U^{-3/2} w^{5-k}`, with
  `Π = δ_{cd} δ_{ef} (A⁻¹)ₛᵣ (A⁻¹)ₜq + δ_{ce} δ_{df} (A⁻¹)ₛₜ (A⁻¹)ᵣq + δ_{cf} δ_{de} (A⁻¹)ₛq (A⁻¹)ᵣₜ`.

Both come from the isotropic fourth moment
`∫ xₐ x_b x_c x_d G(|x|²) dx = (δₐ_b δ_cd + δₐ_c δ_bd + δₐ_d δ_bc)/(n(n+2)) ∫ |x|⁴ G(|x|²) dx`
on `ℝⁿ` (`integral_mul_mul_mul_mul_sum_sq`): moments with an index occurring once vanish by the
reflection of that coordinate; `∫ xₐ⁴ G` does not depend on `a` (transpositions); and
`∫ xₐ⁴ G = 3 ∫ xₐ² x_b² G` for `a ≠ b`, by the isometric involution
`(xₐ, x_b) ↦ ((xₐ + x_b)/√2, (xₐ - x_b)/√2)` (`pairRotation`). The explicit kernels follow from
the scalar radial formulas and `q² = w² - 2w(w - q) + (w - q)²`.

Odd moments vanish (`integral_mul_inv_neg_quadratic_add_pow_eq_zero_of_odd`,
`integral_mul_inv_quadForm_add_pow_eq_zero_of_odd`), and a weight whose even part is a
polynomial of degree at most four integrates term by term
(`integral_mul_inv_neg_quadratic_add_pow_of_even_quartic`,
`integral_mul_inv_quadForm_add_pow_of_even_quartic`).

The formulas were checked numerically before formalization (2D tensor quadrature and a 6D
radial/1D×5D reduction; relative error below `1e-10`).

## Main statements

* `integral_mul_mul_mul_mul_sum_sq`: the isotropic fourth moment on `ι → ℝ`.
* `integral_mul_mul_mul_mul_comp_mulVec`: its pull-back by an invertible linear map.
* `integral_mul_mul_mul_mul_inv_neg_quadratic_add_pow`,
  `integral_mul_mul_mul_mul_inv_quadForm_add_pow`: the energy and spatial fourth moments.
* `integral_mul_inv_neg_quadratic_add_pow_of_even_quartic`,
  `integral_mul_inv_quadForm_add_pow_of_even_quartic`: weights with an even part of degree at most
  four.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix Filter
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Spatial (quadForm)

/-! ### Finite sums under the integral -/

/-- The integral of a fourfold finite sum of integrable functions. -/
theorem integral_sum_sum_sum_sum {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {κ₁ κ₂ κ₃ κ₄ : Type*} [Fintype κ₁] [Fintype κ₂] [Fintype κ₃] [Fintype κ₄]
    {F : κ₁ → κ₂ → κ₃ → κ₄ → X → ℂ} (h : ∀ i j k l, Integrable (F i j k l) μ) :
    ∫ x, ∑ i, ∑ j, ∑ k, ∑ l, F i j k l x ∂μ = ∑ i, ∑ j, ∑ k, ∑ l, ∫ x, F i j k l x ∂μ := by
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => h i j k l]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun l _ => h i j k l]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => h i j k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => h i j k l]

/-! ### Isometric changes of variables -/

section Isotropic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Invariance of `∫ F(x) G(|x|²)` under an isometric linear change of variables. -/
theorem integral_mul_comp_mulVec_of_isometry {N : Matrix ι ι ℝ} (hN : |N.det| = 1)
    (hS : ∀ x, ∑ i, (N *ᵥ x) i ^ 2 = ∑ i, x i ^ 2) (F : (ι → ℝ) → ℂ) (G : ℝ → ℂ) :
    ∫ x, F (N *ᵥ x) * G (∑ i, x i ^ 2) = ∫ x, F x * G (∑ i, x i ^ 2) := by
  have hN0 : N.det ≠ 0 := fun h => by rw [h, abs_zero] at hN; exact zero_ne_one hN
  have h := Spatial.integral_comp_mulVec hN0 (fun x => F x * G (∑ i, x i ^ 2))
  rw [hN, inv_one, one_smul] at h
  simpa only [hS] using h

/-- The reflection of the coordinate `a`. -/
def reflectMatrix (a : ι) : Matrix ι ι ℝ := diagonal (Function.update 1 a (-1))

theorem reflectMatrix_mulVec (a : ι) (x : ι → ℝ) (i : ι) :
    (reflectMatrix a *ᵥ x) i = if i = a then -x i else x i := by
  rw [reflectMatrix, mulVec_diagonal]
  by_cases hi : i = a
  · subst hi; simp
  · simp [hi]

theorem abs_det_reflectMatrix (a : ι) : |(reflectMatrix a).det| = 1 := by
  rw [reflectMatrix, det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ a)]
  simp

theorem sum_sq_reflectMatrix_mulVec (a : ι) (x : ι → ℝ) :
    ∑ i, (reflectMatrix a *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 :=
  Finset.sum_congr rfl fun i _ => by rw [reflectMatrix_mulVec]; split_ifs <;> ring

/-- A weight odd under the reflection of one coordinate has vanishing moment. -/
theorem integral_mul_sum_sq_eq_zero_of_reflect (a : ι) {F : (ι → ℝ) → ℂ}
    (hF : ∀ x, F (reflectMatrix a *ᵥ x) = -F x) (G : ℝ → ℂ) :
    ∫ x, F x * G (∑ i, x i ^ 2) = 0 := by
  have h := integral_mul_comp_mulVec_of_isometry (abs_det_reflectMatrix a)
    (sum_sq_reflectMatrix_mulVec a) F G
  simp only [hF, neg_mul, integral_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- `∫ xₐ⁴ G(|x|²)` does not depend on `a`. -/
theorem integral_pow_four_mul_sum_sq_eq (G : ℝ → ℂ) (a b : ι) :
    ∫ x : ι → ℝ, ((x a ^ 4 : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
      ∫ x : ι → ℝ, ((x b ^ 4 : ℝ) : ℂ) * G (∑ i, x i ^ 2) := by
  have hdet : |((Equiv.swap a b).permMatrix ℝ).det| = 1 := by
    rw [det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap a b)) with h | h <;> simp [h]
  have hS : ∀ x : ι → ℝ, ∑ i, ((Equiv.swap a b).permMatrix ℝ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
    intro x
    simp only [permMatrix_mulVec, Function.comp_apply]
    exact Equiv.sum_comp (Equiv.swap a b) (fun i => x i ^ 2)
  have h := integral_mul_comp_mulVec_of_isometry hdet hS (fun x => ((x b ^ 4 : ℝ) : ℂ)) G
  simp only [permMatrix_mulVec, Function.comp_apply, Equiv.swap_apply_right] at h
  exact h

/-- The isometric involution `(xₐ, x_b) ↦ ((xₐ + x_b)/√2, (xₐ - x_b)/√2)` (for `a ≠ b`). -/
noncomputable def pairRotation (a b : ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x := Function.update (Function.update x a ((Real.sqrt 2)⁻¹ * (x a + x b))) b
    ((Real.sqrt 2)⁻¹ * (x a - x b))
  map_add' x y := by
    funext i
    by_cases hb : i = b
    · subst hb; simp only [Function.update_self, Pi.add_apply]; ring
    · by_cases ha : i = a
      · subst ha; simp only [Function.update_of_ne hb, Function.update_self, Pi.add_apply]; ring
      · simp only [Function.update_of_ne hb, Function.update_of_ne ha, Pi.add_apply]
  map_smul' r x := by
    funext i
    by_cases hb : i = b
    · subst hb; simp only [Function.update_self, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · by_cases ha : i = a
      · subst ha
        simp only [Function.update_of_ne hb, Function.update_self, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring
      · simp only [Function.update_of_ne hb, Function.update_of_ne ha, Pi.smul_apply,
          RingHom.id_apply]

omit [Fintype ι] in
theorem pairRotation_apply_left {a b : ι} (hab : a ≠ b) (x : ι → ℝ) :
    pairRotation a b x a = (Real.sqrt 2)⁻¹ * (x a + x b) := by
  show Function.update (Function.update x a _) b _ a = _
  rw [Function.update_of_ne hab, Function.update_self]

omit [Fintype ι] in
theorem pairRotation_apply_right (a b : ι) (x : ι → ℝ) :
    pairRotation a b x b = (Real.sqrt 2)⁻¹ * (x a - x b) := by
  show Function.update (Function.update x a _) b _ b = _
  rw [Function.update_self]

omit [Fintype ι] in
theorem pairRotation_apply_of_ne {a b i : ι} (ha : i ≠ a) (hb : i ≠ b) (x : ι → ℝ) :
    pairRotation a b x i = x i := by
  show Function.update (Function.update x a _) b _ i = _
  rw [Function.update_of_ne hb, Function.update_of_ne ha]

theorem inv_sqrt_two_mul_self : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div]

omit [Fintype ι] in
theorem pairRotation_pairRotation {a b : ι} (hab : a ≠ b) (x : ι → ℝ) :
    pairRotation a b (pairRotation a b x) = x := by
  have h2 := inv_sqrt_two_mul_self
  funext i
  by_cases hb : i = b
  · subst hb
    rw [pairRotation_apply_right, pairRotation_apply_left hab, pairRotation_apply_right]
    linear_combination (2 * x i) * h2
  · by_cases ha : i = a
    · subst ha
      rw [pairRotation_apply_left hab, pairRotation_apply_left hab, pairRotation_apply_right]
      linear_combination (2 * x i) * h2
    · rw [pairRotation_apply_of_ne ha hb, pairRotation_apply_of_ne ha hb]

theorem sum_sq_pairRotation {a b : ι} (hab : a ≠ b) (x : ι → ℝ) :
    ∑ i, pairRotation a b x i ^ 2 = ∑ i, x i ^ 2 := by
  have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  have split : ∀ f : ι → ℝ, ∑ i, f i = f a + (f b + ∑ i ∈ (Finset.univ.erase a).erase b, f i) :=
    fun f => by rw [Finset.add_sum_erase _ _ hb, Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  rw [split (fun i => pairRotation a b x i ^ 2), split (fun i => x i ^ 2)]
  have hrest : ∑ i ∈ (Finset.univ.erase a).erase b, pairRotation a b x i ^ 2 =
      ∑ i ∈ (Finset.univ.erase a).erase b, x i ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨hib, hi'⟩ := Finset.mem_erase.mp hi
    rw [pairRotation_apply_of_ne (Finset.mem_erase.mp hi').1 hib]
  rw [hrest, pairRotation_apply_left hab, pairRotation_apply_right]
  have h2 := inv_sqrt_two_mul_self
  have : ((Real.sqrt 2)⁻¹ * (x a + x b)) ^ 2 + ((Real.sqrt 2)⁻¹ * (x a - x b)) ^ 2 =
      x a ^ 2 + x b ^ 2 := by
    linear_combination (2 * x a ^ 2 + 2 * x b ^ 2) * h2
  linarith

/-- The matrix of `pairRotation`. -/
noncomputable def pairRotationMatrix (a b : ι) : Matrix ι ι ℝ :=
  LinearMap.toMatrix' (pairRotation a b)

theorem pairRotationMatrix_mulVec (a b : ι) (x : ι → ℝ) :
    pairRotationMatrix a b *ᵥ x = pairRotation a b x :=
  LinearMap.toMatrix'_mulVec _ x

theorem abs_det_pairRotationMatrix {a b : ι} (hab : a ≠ b) :
    |(pairRotationMatrix a b).det| = 1 := by
  have hL : pairRotation a b * pairRotation a b = 1 :=
    LinearMap.ext fun x => pairRotation_pairRotation hab x
  have h : (pairRotationMatrix a b).det * (pairRotationMatrix a b).det = 1 := by
    rw [← Matrix.det_mul, pairRotationMatrix, ← LinearMap.toMatrix'_mul, hL,
      Module.End.one_eq_id, LinearMap.toMatrix'_id, Matrix.det_one]
  rcases mul_self_eq_one_iff.mp h with h1 | h1 <;> simp [h1]

/-! ### Integrability of the fourth-degree weights -/

omit [DecidableEq ι] in
theorem sq_le_sum_sq (x : ι → ℝ) (a : ι) : x a ^ 2 ≤ ∑ i, x i ^ 2 :=
  Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ a)

omit [DecidableEq ι] in
theorem abs_mul_le_sum_sq (x : ι → ℝ) (a b : ι) : |x a * x b| ≤ ∑ i, x i ^ 2 := by
  have ha := sq_le_sum_sq x a
  have hb := sq_le_sum_sq x b
  rw [abs_mul]
  nlinarith [abs_nonneg (x a), abs_nonneg (x b), sq_abs (x a), sq_abs (x b),
    sq_nonneg (|x a| - |x b|)]

omit [DecidableEq ι] in
theorem abs_mul_mul_mul_le_sum_sq_sq (x : ι → ℝ) (a b c d : ι) :
    |x a * x b * x c * x d| ≤ (∑ i, x i ^ 2) ^ 2 := by
  have h1 := abs_mul_le_sum_sq x a b
  have h2 := abs_mul_le_sum_sq x c d
  rw [mul_assoc, abs_mul, sq]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

omit [DecidableEq ι] in
/-- A continuous weight bounded by `|x|⁴` is integrable against `G(|x|²)` when `|x|⁴ G(|x|²)` is. -/
theorem integrable_mul_sum_sq_of_le {G : ℝ → ℂ} (hGc : Continuous G)
    (hG : Integrable fun x : ι → ℝ => (((∑ i, x i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2))
    {F : (ι → ℝ) → ℂ} (hFc : Continuous F) (hF : ∀ x, ‖F x‖ ≤ (∑ i, x i ^ 2) ^ 2) :
    Integrable fun x : ι → ℝ => F x * G (∑ i, x i ^ 2) := by
  refine hG.mono (hFc.mul (hGc.comp (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (hF x) (norm_nonneg _)

omit [DecidableEq ι] in
theorem integrable_mul_mul_mul_mul_sum_sq {G : ℝ → ℂ} (hGc : Continuous G)
    (hG : Integrable fun x : ι → ℝ => (((∑ i, x i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2))
    (a b c d : ι) :
    Integrable fun x : ι → ℝ => ((x a * x b * x c * x d : ℝ) : ℂ) * G (∑ i, x i ^ 2) :=
  integrable_mul_sum_sq_of_le hGc hG (continuous_ofReal.comp (by fun_prop)) fun x => by
    rw [norm_real, Real.norm_eq_abs]
    exact abs_mul_mul_mul_le_sum_sq_sq x a b c d

/-! ### The isotropic fourth moment -/

omit [DecidableEq ι] in
theorem integral_binomial_four {f₁ f₂ f₃ f₄ f₅ : (ι → ℝ) → ℂ} (h₁ : Integrable f₁)
    (h₂ : Integrable f₂) (h₃ : Integrable f₃) (h₄ : Integrable f₄) (h₅ : Integrable f₅) :
    ∫ x, (f₁ x + 4 * f₂ x + 6 * f₃ x + 4 * f₄ x + f₅ x) =
      (∫ x, f₁ x) + 4 * (∫ x, f₂ x) + 6 * (∫ x, f₃ x) + 4 * (∫ x, f₄ x) + ∫ x, f₅ x := by
  have e1 := integral_add (μ := volume) (f := fun x => f₁ x + 4 * f₂ x + 6 * f₃ x + 4 * f₄ x)
    (g := f₅) (((h₁.add (h₂.const_mul 4)).add (h₃.const_mul 6)).add (h₄.const_mul 4)) h₅
  have e2 := integral_add (μ := volume) (f := fun x => f₁ x + 4 * f₂ x + 6 * f₃ x)
    (g := fun x => 4 * f₄ x) ((h₁.add (h₂.const_mul 4)).add (h₃.const_mul 6)) (h₄.const_mul 4)
  have e3 := integral_add (μ := volume) (f := fun x => f₁ x + 4 * f₂ x)
    (g := fun x => 6 * f₃ x) (h₁.add (h₂.const_mul 4)) (h₃.const_mul 6)
  have e4 := integral_add (μ := volume) (f := f₁) (g := fun x => 4 * f₂ x) h₁ (h₂.const_mul 4)
  rw [e1, e2, e3, e4, integral_const_mul, integral_const_mul, integral_const_mul]

/-- `∫ xₐ⁴ G = 3 ∫ xₐ² x_b² G` for `a ≠ b`. -/
theorem integral_pow_four_mul_sum_sq_eq_three_mul {G : ℝ → ℂ} (hGc : Continuous G)
    (hG : Integrable fun x : ι → ℝ => (((∑ i, x i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2))
    {a b : ι} (hab : a ≠ b) :
    ∫ x : ι → ℝ, ((x a ^ 4 : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
      3 * ∫ x : ι → ℝ, ((x a ^ 2 * x b ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) := by
  have hint := integrable_mul_mul_mul_mul_sum_sq hGc hG
  have h := integral_mul_comp_mulVec_of_isometry (abs_det_pairRotationMatrix hab)
    (fun x => by rw [pairRotationMatrix_mulVec, sum_sq_pairRotation hab])
    (fun x => ((x a ^ 4 : ℝ) : ℂ)) G
  simp only [pairRotationMatrix_mulVec, pairRotation_apply_left hab] at h
  -- expand `((xₐ + x_b)/√2)⁴`
  have h4 : ∀ x : ι → ℝ, ((((Real.sqrt 2)⁻¹ * (x a + x b)) ^ 4 : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
      (1 / 4 : ℂ) * (((x a * x a * x a * x a : ℝ) : ℂ) * G (∑ i, x i ^ 2) +
        4 * (((x a * x a * x a * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2)) +
        6 * (((x a * x a * x b * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2)) +
        4 * (((x a * x b * x b * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2)) +
        ((x b * x b * x b * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2)) := fun x => by
    have h2 := inv_sqrt_two_mul_self
    have e : ((Real.sqrt 2)⁻¹ * (x a + x b)) ^ 4 = 1 / 4 * (x a ^ 4 + 4 * (x a ^ 3 * x b) +
        6 * (x a ^ 2 * x b ^ 2) + 4 * (x a * x b ^ 3) + x b ^ 4) := by
      have : ((Real.sqrt 2)⁻¹) ^ 4 = 1 / 4 := by
        rw [show ((Real.sqrt 2)⁻¹) ^ 4 = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) ^ 2 by ring, h2]
        norm_num
      rw [mul_pow, this]
      ring
    rw [e]
    push_cast
    ring
  simp only [h4] at h
  have hodd1 : ∫ x : ι → ℝ, ((x a * x a * x a * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2) = 0 :=
    integral_mul_sum_sq_eq_zero_of_reflect b (fun x => by
      simp only [reflectMatrix_mulVec, hab, ↓reduceIte]
      push_cast; ring) G
  have hodd2 : ∫ x : ι → ℝ, ((x a * x b * x b * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2) = 0 :=
    integral_mul_sum_sq_eq_zero_of_reflect a (fun x => by
      simp only [reflectMatrix_mulVec, hab.symm, ↓reduceIte]
      push_cast; ring) G
  have hswap := integral_pow_four_mul_sum_sq_eq G b a
  rw [integral_const_mul, integral_binomial_four (hint a a a a) (hint a a a b) (hint a a b b)
    (hint a b b b) (hint b b b b), hodd1, hodd2] at h
  have e4 : ∀ c : ι, ∫ x : ι → ℝ, ((x c * x c * x c * x c : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
      ∫ x : ι → ℝ, ((x c ^ 4 : ℝ) : ℂ) * G (∑ i, x i ^ 2) := fun c => by
    congr 1; funext x; congr 2; ring
  have e22 : ∫ x : ι → ℝ, ((x a * x a * x b * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
      ∫ x : ι → ℝ, ((x a ^ 2 * x b ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) := by
    congr 1; funext x; congr 2; ring
  rw [e4, e4, e22, hswap] at h
  linear_combination (-2 : ℂ) * h

/-- The pairing sum of Kronecker deltas `δₐ_b δ_cd + δₐ_c δ_bd + δₐ_d δ_bc`. -/
def deltaPair (a b c d : ι) : ℝ :=
  (if a = b then 1 else 0) * (if c = d then 1 else 0) +
    (if a = c then 1 else 0) * (if b = d then 1 else 0) +
    (if a = d then 1 else 0) * (if b = c then 1 else 0)

/-- **The isotropic fourth moment.** For continuous `G` with `|x|⁴ G(|x|²)` integrable,
`∫ xₐ x_b x_c x_d G(|x|²) dx = (δₐ_b δ_cd + δₐ_c δ_bd + δₐ_d δ_bc) (n(n+2))⁻¹ ∫ |x|⁴ G(|x|²) dx`,
`n = card ι`. -/
theorem integral_mul_mul_mul_mul_sum_sq {G : ℝ → ℂ} (hGc : Continuous G)
    (hG : Integrable fun x : ι → ℝ => (((∑ i, x i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2))
    (a b c d : ι) :
    ∫ x : ι → ℝ, ((x a * x b * x c * x d : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
      (deltaPair a b c d : ℂ) * (((Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ) + 2))⁻¹ *
        ∫ x : ι → ℝ, (((∑ i, x i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2)) := by
  have hint := integrable_mul_mul_mul_mul_sum_sq hGc hG
  have hne : Nonempty ι := ⟨a⟩
  set μ := ∫ x : ι → ℝ, ((x a ^ 4 : ℝ) : ℂ) * G (∑ i, x i ^ 2) with hμ
  have h4 : ∀ c, ∫ x : ι → ℝ, ((x c * x c * x c * x c : ℝ) : ℂ) * G (∑ i, x i ^ 2) = μ :=
    fun c => by
      rw [hμ, integral_pow_four_mul_sum_sq_eq G a c]
      congr 1; funext x; congr 2; ring
  have h22 : ∀ c d, c ≠ d →
      ∫ x : ι → ℝ, ((x c * x c * x d * x d : ℝ) : ℂ) * G (∑ i, x i ^ 2) = μ / 3 := fun c d hcd => by
    have h := integral_pow_four_mul_sum_sq_eq_three_mul hGc hG hcd
    rw [← integral_pow_four_mul_sum_sq_eq G a c, ← hμ] at h
    have e : ∫ x : ι → ℝ, ((x c * x c * x d * x d : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
        ∫ x : ι → ℝ, ((x c ^ 2 * x d ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) := by
      congr 1; funext x; congr 2; ring
    rw [e, h]
    ring
  -- the total
  have hcard : ((Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ) + 2)) ≠ 0 := by
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    exact_mod_cast (by positivity : ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) + 2)) ≠ 0)
  have htot : ∫ x : ι → ℝ, (((∑ i, x i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
      (Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ) + 2) * (μ / 3) := by
    have hpt : ∀ x : ι → ℝ, (((∑ i, x i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
        ∑ i, ∑ j, ((x i * x i * x j * x j : ℝ) : ℂ) * G (∑ i, x i ^ 2) := fun x => by
      rw [sq, Finset.sum_mul_sum]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [hpt]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i i j j]
    have hrow : ∀ i, ∫ x : ι → ℝ, ∑ j, ((x i * x i * x j * x j : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
        ∑ j, (μ / 3 + if i = j then 2 * μ / 3 else 0) := fun i => by
      rw [integral_finsetSum _ fun j _ => hint i i j j]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i = j
      · subst hij; simp only [h4, ↓reduceIte]; ring
      · simp only [h22 i j hij, hij, ↓reduceIte, add_zero]
    simp only [hrow, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, nsmul_eq_mul]
    ring
  -- the case analysis
  have hzero : ∀ c d e f : ι, c ≠ d → c ≠ e → c ≠ f →
      ∫ x : ι → ℝ, ((x c * x d * x e * x f : ℝ) : ℂ) * G (∑ i, x i ^ 2) = 0 :=
    fun c d e f hd he hf => integral_mul_sum_sq_eq_zero_of_reflect c (fun x => by
      simp only [reflectMatrix_mulVec, hd.symm, he.symm, hf.symm, ↓reduceIte]
      push_cast; ring) G
  have hp : ∀ (c d e f c' d' e' f' : ι),
      (∀ x : ι → ℝ, x c * x d * x e * x f = x c' * x d' * x e' * x f') →
      ∫ x : ι → ℝ, ((x c * x d * x e * x f : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
        ∫ x : ι → ℝ, ((x c' * x d' * x e' * x f' : ℝ) : ℂ) * G (∑ i, x i ^ 2) :=
    fun c d e f c' d' e' f' h => by
      congr 1; funext x; rw [h x]
  have key : ∫ x : ι → ℝ, ((x a * x b * x c * x d : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
      (deltaPair a b c d : ℂ) * (μ / 3) := by
    rcases eq_or_ne a b with rfl | hab
    · rcases eq_or_ne c d with rfl | hcd
      · rcases eq_or_ne a c with rfl | hac
        · rw [h4]; simp [deltaPair]; ring
        · rw [h22 a c hac]; simp [deltaPair, hac]
      · rcases eq_or_ne a c with rfl | hac
        · rw [hp a a a d d a a a (fun x => by ring), hzero d a a a hcd.symm hcd.symm hcd.symm]
          simp [deltaPair, hcd]
        · rcases eq_or_ne a d with rfl | had
          · rw [hp a a c a c a a a (fun x => by ring), hzero c a a a hac.symm hac.symm hac.symm]
            simp [deltaPair, hac, hac.symm]
          · rw [hp a a c d c a a d (fun x => by ring), hzero c a a d hac.symm hac.symm hcd]
            simp [deltaPair, hac, had, hcd]
    · rcases eq_or_ne a c with rfl | hac
      · rcases eq_or_ne b d with rfl | hbd
        · rw [hp a b a b a a b b (fun x => by ring), h22 a b hab]
          simp [deltaPair, hab, hab.symm]
        · rw [hp a b a d b a a d (fun x => by ring), hzero b a a d hab.symm hab.symm hbd]
          simp [deltaPair, hab, hab.symm, hbd]
      · rcases eq_or_ne a d with rfl | had
        · rcases eq_or_ne b c with rfl | hbc
          · rw [hp a b b a a a b b (fun x => by ring), h22 a b hab]
            simp [deltaPair, hab, hab.symm]
          · rw [hp a b c a b a c a (fun x => by ring), hzero b a c a hab.symm hbc hab.symm]
            simp [deltaPair, hab, hab.symm, hbc, hac, hac.symm]
        · rw [hzero a b c d hab hac had]
          simp [deltaPair, hab, hac, had]
  have hn2 : (Fintype.card ι : ℂ) + 2 ≠ 0 := by
    have : (0 : ℝ) < (Fintype.card ι : ℝ) + 2 := by positivity
    exact_mod_cast this.ne'
  rw [key, htot]
  field_simp

/-- The pairing sum `Bₐ_b B_cd + Bₐ_c B_bd + Bₐ_d B_bc` of a matrix. -/
def matPair (B : Matrix ι ι ℝ) (a b c d : ι) : ℝ :=
  B a b * B c d + B a c * B b d + B a d * B b c

theorem sum_mul_deltaPair (P : Matrix ι ι ℝ) (a b c d : ι) :
    ∑ i, ∑ j, ∑ k, ∑ l, P a i * P b j * P c k * P d l * deltaPair i j k l =
      matPair (P * Pᵀ) a b c d := by
  simp only [matPair, deltaPair, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.mem_univ, ite_true,
    Matrix.mul_apply, transpose_apply, Finset.sum_mul, Finset.mul_sum]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_ <;>
    (rw [Finset.sum_comm]
     exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

/-- **The pulled-back fourth moment.** For invertible `N` and `|N u|⁴ G(|N u|²)` integrable,
`∫ uₐ u_b u_c u_d G(|N u|²) du = Πₐ_bcd((Nᵀ N)⁻¹) (n(n+2))⁻¹ ∫ |N u|⁴ G(|N u|²) du`. -/
theorem integral_mul_mul_mul_mul_comp_mulVec {N : Matrix ι ι ℝ} (hN : N.det ≠ 0) {G : ℝ → ℂ}
    (hGc : Continuous G)
    (hG : Integrable fun u : ι → ℝ =>
      (((∑ i, (N *ᵥ u) i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, (N *ᵥ u) i ^ 2))
    (a b c d : ι) :
    ∫ u : ι → ℝ, ((u a * u b * u c * u d : ℝ) : ℂ) * G (∑ i, (N *ᵥ u) i ^ 2) =
      (matPair (Nᵀ * N)⁻¹ a b c d : ℂ) *
        (((Fintype.card ι : ℂ) * ((Fintype.card ι : ℂ) + 2))⁻¹ *
          ∫ u : ι → ℝ, (((∑ i, (N *ᵥ u) i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, (N *ᵥ u) i ^ 2)) := by
  have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  have hG' : Integrable fun x : ι → ℝ => (((∑ i, x i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) :=
    (Spatial.integrable_comp_mulVec_iff hN (g := fun x : ι → ℝ =>
      (((∑ i, x i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2))).mp hG
  have hX := Spatial.integral_comp_mulVec hN
    (fun x : ι → ℝ => (((∑ i, x i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2))
  have h := Spatial.integral_comp_mulVec hN
    (fun x : ι → ℝ => (((N⁻¹ *ᵥ x) a * (N⁻¹ *ᵥ x) b * (N⁻¹ *ᵥ x) c * (N⁻¹ *ᵥ x) d : ℝ) : ℂ) *
      G (∑ i, x i ^ 2))
  have hinv : ∀ u : ι → ℝ, N⁻¹ *ᵥ (N *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  simp only [hinv] at h
  rw [h, hX]
  have hint := integrable_mul_mul_mul_mul_sum_sq hGc hG'
  have hpt : ∀ x : ι → ℝ,
      (((N⁻¹ *ᵥ x) a * (N⁻¹ *ᵥ x) b * (N⁻¹ *ᵥ x) c * (N⁻¹ *ᵥ x) d : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
        ∑ i, ∑ j, ∑ k, ∑ l, ((N⁻¹ a i * N⁻¹ b j * N⁻¹ c k * N⁻¹ d l : ℝ) : ℂ) *
          (((x i * x j * x k * x l : ℝ) : ℂ) * G (∑ i, x i ^ 2)) := by
    intro x
    have e : ((N⁻¹ *ᵥ x) a * (N⁻¹ *ᵥ x) b * (N⁻¹ *ᵥ x) c * (N⁻¹ *ᵥ x) d : ℝ) =
        ∑ i, ∑ j, ∑ k, ∑ l, N⁻¹ a i * N⁻¹ b j * N⁻¹ c k * N⁻¹ d l * (x i * x j * x k * x l) := by
      have h2 : ∀ p q : ι, (N⁻¹ *ᵥ x) p * (N⁻¹ *ᵥ x) q =
          ∑ i, ∑ j, N⁻¹ p i * N⁻¹ q j * (x i * x j) := fun p q => by
        simp only [mulVec, dotProduct, Finset.sum_mul]
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [mul_assoc ((N⁻¹ *ᵥ x) a * (N⁻¹ *ᵥ x) b), h2 a b, h2 c d]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [e]
    push_cast
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp only [hpt]
  rw [integral_sum_sum_sum_sum fun i j k l => (hint i j k l).const_mul _]
  simp only [integral_const_mul, integral_mul_mul_mul_mul_sum_sq hGc hG']
  have hinvT : (Nᵀ * N)⁻¹ = N⁻¹ * (N⁻¹)ᵀ := by
    rw [Matrix.mul_inv_rev, ← transpose_nonsing_inv]
  rw [hinvT, ← sum_mul_deltaPair, real_smul, real_smul]
  push_cast
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

end Isotropic

/-! ### The energy and spatial fourth moments, general kernel -/

/-- **Energy fourth moment, general kernel.** For positive definite `A` and continuous `G` with
`q² G(q)` integrable, `q = uᵀAu`: `∫ uₛ uᵣ uₜ u_q G(q) du = Πₛᵣₜq(A⁻¹) · ⅛ ∫ q² G(q) du`. -/
theorem integral_mul_mul_mul_mul_quadratic {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    {G : ℝ → ℂ} (hGc : Continuous G)
    (hG : Integrable fun u : Fin 2 → ℝ => (((u ⬝ᵥ A *ᵥ u) ^ 2 : ℝ) : ℂ) * G (u ⬝ᵥ A *ᵥ u))
    (s r t q : Fin 2) :
    ∫ u : Fin 2 → ℝ, ((u s * u r * u t * u q : ℝ) : ℂ) * G (u ⬝ᵥ A *ᵥ u) =
      (matPair A⁻¹ s r t q : ℂ) *
        (8⁻¹ * ∫ u : Fin 2 → ℝ, (((u ⬝ᵥ A *ᵥ u) ^ 2 : ℝ) : ℂ) * G (u ⬝ᵥ A *ᵥ u)) := by
  have hq : ∀ u : Fin 2 → ℝ, u ⬝ᵥ A *ᵥ u = ∑ i, (cholesky A *ᵥ u) i ^ 2 := fun u => by
    rw [dotProduct_mulVec_eq_cholesky hA, Fin.sum_univ_two]
  simp only [hq] at hG ⊢
  rw [integral_mul_mul_mul_mul_comp_mulVec (det_cholesky_ne_zero hA) hGc hG s r t q,
    cholesky_transpose_mul_self hA, Fintype.card_fin]
  push_cast
  ring

/-- The spatial pairing sum
`δ_{cd} δ_{ef} (A⁻¹)ₛᵣ (A⁻¹)ₜq + δ_{ce} δ_{df} (A⁻¹)ₛₜ (A⁻¹)ᵣq + δ_{cf} δ_{de} (A⁻¹)ₛq (A⁻¹)ᵣₜ`. -/
noncomputable def spatialPair (A : Matrix (Fin 2) (Fin 2) ℝ) (s : Fin 2) (c : Fin 3) (r : Fin 2)
    (d : Fin 3) (t : Fin 2) (e : Fin 3) (q : Fin 2) (f : Fin 3) : ℝ :=
  (if c = d then A⁻¹ s r else 0) * (if e = f then A⁻¹ t q else 0) +
    (if c = e then A⁻¹ s t else 0) * (if d = f then A⁻¹ r q else 0) +
    (if c = f then A⁻¹ s q else 0) * (if d = e then A⁻¹ r t else 0)

theorem matPair_blockGram (A : Matrix (Fin 2) (Fin 2) ℝ) (s : Fin 2) (c : Fin 3) (r : Fin 2)
    (d : Fin 3) (t : Fin 2) (e : Fin 3) (q : Fin 2) (f : Fin 3) :
    matPair (blockGram A⁻¹) (sumIndex s c) (sumIndex r d) (sumIndex t e) (sumIndex q f) =
      spatialPair A s c r d t e q f := by
  simp only [matPair, spatialPair, blockGram, of_apply, sumComp_sumIndex, sumLoop_sumIndex]

/-- **Spatial fourth moment, general kernel.** For positive definite `A` and continuous `G` with
`q² G(q)` integrable, `q = quadForm A y`:
`∫ y_{sc} y_{rd} y_{te} y_{qf} G(q) dy = Π · (1/48) ∫ q² G(q) dy` (`Π = spatialPair`). -/
theorem integral_mul_mul_mul_mul_quadForm {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    {G : ℝ → ℂ} (hGc : Continuous G)
    (hG : Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      (((quadForm A y) ^ 2 : ℝ) : ℂ) * G (quadForm A y))
    (s : Fin 2) (c : Fin 3) (r : Fin 2) (d : Fin 3) (t : Fin 2) (e : Fin 3) (q : Fin 2)
    (f : Fin 3) :
    ∫ y : Fin 2 → Fin 3 → ℝ, ((y s c * y r d * y t e * y q f : ℝ) : ℂ) * G (quadForm A y) =
      (spatialPair A s c r d t e q f : ℂ) *
        (48⁻¹ * ∫ y : Fin 2 → Fin 3 → ℝ, (((quadForm A y) ^ 2 : ℝ) : ℂ) * G (quadForm A y)) := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  set N := blockGram (cholesky A) with hNdef
  have hdetM : IsUnit (cholesky A).det := isUnit_iff_ne_zero.mpr (det_cholesky_ne_zero hA)
  have hN : N.det ≠ 0 := det_blockGram_ne_zero hdetM
  have hNN : Nᵀ * N = blockGram A := by
    rw [hNdef, blockGram_transpose, blockGram_mul, cholesky_transpose_mul_self hA]
  have hq : ∀ u, quadForm A (sumPair u) = ∑ i, (N *ᵥ u) i ^ 2 := fun u => by
    rw [quadForm_sumPair, ← hNN, dotProduct_transpose_mul_mulVec]
  have hG' : Integrable fun u : Fin 3 ⊕ Fin 3 → ℝ =>
      (((∑ i, (N *ᵥ u) i ^ 2) ^ 2 : ℝ) : ℂ) * G (∑ i, (N *ᵥ u) i ^ 2) := by
    have := (measurePreserving_sumPair.integrable_comp_emb measurableEmbedding_sumPair).mpr hG
    simpa only [Function.comp_def, hq] using this
  rw [← measurePreserving_sumPair.integral_comp measurableEmbedding_sumPair,
    ← measurePreserving_sumPair.integral_comp measurableEmbedding_sumPair]
  simp only [hq]
  simp only [sumPair]
  rw [integral_mul_mul_mul_mul_comp_mulVec hN hGc hG', hNN, blockGram_inv hu, matPair_blockGram]
  have : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := rfl
  rw [this]
  push_cast
  ring

/-! ### Integrability of the fourth-degree monomials -/

theorem abs_mul_mul_mul_le_sq_trace_div_det {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (u : Fin 2 → ℝ) (s r t q : Fin 2) :
    |u s * u r * u t * u q| ≤ (A.trace / A.det) ^ 2 * (1 + u ⬝ᵥ A *ᵥ u) ^ 2 := by
  have hq := dotProduct_mulVec_self_nonneg hA u
  have htr := trace_div_det_nonneg hA
  have hu : ∑ i, u i ^ 2 ≤ A.trace / A.det * (u ⬝ᵥ A *ᵥ u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hA.det_pos]
    exact sum_sq_mul_det_le hA _
  have h4 := abs_mul_mul_mul_le_sum_sq_sq u s r t q
  have h0 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc |u s * u r * u t * u q| ≤ (∑ i, u i ^ 2) ^ 2 := h4
    _ ≤ (A.trace / A.det * (1 + u ⬝ᵥ A *ᵥ u)) ^ 2 := by
        gcongr
        nlinarith
    _ = _ := by ring

theorem integrable_mul_mul_mul_mul_inv_neg_quadratic_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {n : ℕ} (hn : 4 ≤ n) (s r t q : Fin 2) :
    Integrable fun u : Fin 2 → ℝ =>
      ((u s * u r * u t * u q : ℝ) : ℂ) * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹ := by
  have hb := (integrable_one_add_quadratic_pow_mul_norm hA hw (j := 2) (by omega)).const_mul
    ((A.trace / A.det) ^ 2)
  refine hb.mono' (((continuous_ofReal.comp (by fun_prop)).mul
    ((continuous_inv_neg_add_pow hw n).comp (continuous_quadratic A))).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (abs_mul_mul_mul_le_sq_trace_div_det hA u s r t q)
    (norm_nonneg _)

theorem abs_mul_mul_mul_le_sq_trace_div_det_quadForm {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) (y : Fin 2 → Fin 3 → ℝ) (s : Fin 2) (c : Fin 3) (r : Fin 2) (d : Fin 3)
    (t : Fin 2) (e : Fin 3) (q : Fin 2) (f : Fin 3) :
    |y s c * y r d * y t e * y q f| ≤ (A.trace / A.det) ^ 2 * (1 + quadForm A y) ^ 2 := by
  have hq := quadForm_nonneg hA y
  have htr := trace_div_det_nonneg hA
  have hu : ∑ s, ∑ c, y s c ^ 2 ≤ A.trace / A.det * quadForm A y := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hA.det_pos]
    exact sum_sum_sq_mul_det_le hA _
  have hle : ∀ s c, y s c ^ 2 ≤ ∑ s, ∑ c, y s c ^ 2 := fun s c =>
    (Finset.single_le_sum (fun c _ => sq_nonneg (y s c)) (Finset.mem_univ c)).trans
      (Finset.single_le_sum (f := fun s => ∑ c, y s c ^ 2)
        (fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg (y s c)) (Finset.mem_univ s))
  have hpair : ∀ s c r d, |y s c * y r d| ≤ ∑ s, ∑ c, y s c ^ 2 := fun s c r d => by
    have ha := hle s c
    have hb := hle r d
    rw [abs_mul]
    nlinarith [abs_nonneg (y s c), abs_nonneg (y r d), sq_abs (y s c), sq_abs (y r d),
      sq_nonneg (|y s c| - |y r d|)]
  have h0 : 0 ≤ ∑ s, ∑ c, y s c ^ 2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg _
  have h4 : |y s c * y r d * y t e * y q f| ≤ (∑ s, ∑ c, y s c ^ 2) ^ 2 := by
    rw [mul_assoc, abs_mul, sq]
    exact mul_le_mul (hpair s c r d) (hpair t e q f) (abs_nonneg _)
      ((abs_nonneg _).trans (hpair s c r d))
  calc |y s c * y r d * y t e * y q f| ≤ (∑ s, ∑ c, y s c ^ 2) ^ 2 := h4
    _ ≤ (A.trace / A.det * (1 + quadForm A y)) ^ 2 := by
        gcongr
        nlinarith
    _ = _ := by ring

theorem continuous_quadForm (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun v : Fin 2 → Fin 3 → ℝ => quadForm A v := by
  simp only [Spatial.quadForm_eq_sum]
  fun_prop

theorem integrable_mul_mul_mul_mul_inv_quadForm_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {k : ℕ} (hk : 6 ≤ k) (s : Fin 2) (c : Fin 3)
    (r : Fin 2) (d : Fin 3) (t : Fin 2) (e : Fin 3) (q : Fin 2) (f : Fin 3) :
    Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      ((y s c * y r d * y t e * y q f : ℝ) : ℂ) * ((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹ := by
  have hb := (integrable_one_add_quadForm_pow_mul_norm hA hw (j := 2) (by omega)).const_mul
    ((A.trace / A.det) ^ 2)
  refine hb.mono' (((continuous_ofReal.comp (by fun_prop)).mul
    ((continuous_inv_add_pow hw k).comp (continuous_quadForm A))).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (abs_mul_mul_mul_le_sq_trace_div_det_quadForm hA y s c r d t e q f) (norm_nonneg _)

/-! ### The explicit fourth moments -/

section Linear

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integral_add_add {f g h : X → ℂ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hh : Integrable h μ) : ∫ x, (f x + g x + h x) ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ + ∫ x, h x ∂μ := by
  rw [integral_add (f := fun x => f x + g x) (g := h) (hf.add hg) hh, integral_add hf hg]

theorem integral_const_mul_sub_const_mul_add {f g h : X → ℂ} (hf : Integrable f μ)
    (hg : Integrable g μ) (hh : Integrable h μ) (a b : ℂ) :
    ∫ x, (a * f x - b * g x + h x) ∂μ = a * ∫ x, f x ∂μ - b * ∫ x, g x ∂μ + ∫ x, h x ∂μ := by
  rw [integral_add (f := fun x => a * f x - b * g x) (g := h)
      ((hf.const_mul a).sub (hg.const_mul b)) hh,
    integral_sub (f := fun x => a * f x) (g := fun x => b * g x) (hf.const_mul a) (hg.const_mul b),
    integral_const_mul, integral_const_mul]

theorem integral_sub_const_mul_add_const_mul {f g h : X → ℂ} (hf : Integrable f μ)
    (hg : Integrable g μ) (hh : Integrable h μ) (a b : ℂ) :
    ∫ x, (f x - b * g x + a * h x) ∂μ = ∫ x, f x ∂μ - b * ∫ x, g x ∂μ + a * ∫ x, h x ∂μ := by
  rw [integral_add (f := fun x => f x - b * g x) (g := fun x => a * h x)
      (hf.sub (hg.const_mul b)) (hh.const_mul a),
    integral_sub (f := f) (g := fun x => b * g x) hf (hg.const_mul b),
    integral_const_mul, integral_const_mul]

end Linear

theorem ofReal_sq_mul_inv_neg_add_pow {w : ℂ} (hw : w.im < 0) (q : ℝ) (k : ℕ) :
    ((q ^ 2 : ℝ) : ℂ) * ((-(q : ℂ) + w) ^ (k + 4))⁻¹ =
      w ^ 2 * ((-(q : ℂ) + w) ^ (k + 4))⁻¹ - 2 * w * ((-(q : ℂ) + w) ^ (k + 3))⁻¹ +
        ((-(q : ℂ) + w) ^ (k + 2))⁻¹ := by
  have hD := neg_ofReal_add_ne_zero hw q
  rw [show k + 4 = (k + 2) + 2 by ring, show k + 3 = (k + 2) + 1 by ring, pow_add, pow_add]
  push_cast
  field_simp
  ring

theorem ofReal_sq_mul_inv_add_pow {w : ℂ} (hw : w.im < 0) (q : ℝ) (k : ℕ) :
    ((q ^ 2 : ℝ) : ℂ) * (((q : ℂ) + w) ^ (k + 6))⁻¹ =
      (((q : ℂ) + w) ^ (k + 4))⁻¹ - 2 * w * (((q : ℂ) + w) ^ (k + 5))⁻¹ +
        w ^ 2 * (((q : ℂ) + w) ^ (k + 6))⁻¹ := by
  have hD : (q : ℂ) + w ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [show k + 6 = (k + 4) + 2 by ring, show k + 5 = (k + 4) + 1 by ring, pow_add, pow_add]
  push_cast
  field_simp
  ring

/-- **The energy fourth moment.** For positive definite `A`, `Im w < 0` and `n ≥ 4`,
`∫ uₛ uᵣ uₜ u_q (-uᵀAu + w)^{-n} du = -π/(4(n-1)(n-2)(n-3)) Πₛᵣₜq(A⁻¹) (det A)^{-1/2} w^{3-n}`. -/
theorem integral_mul_mul_mul_mul_inv_neg_quadratic_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {n : ℕ} (hn : 4 ≤ n) (s r t q : Fin 2) :
    ∫ u : Fin 2 → ℝ, ((u s * u r * u t * u q : ℝ) : ℂ) *
        ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹ =
      -(π / (4 * (((n : ℂ) - 1) * ((n : ℂ) - 2) * ((n : ℂ) - 3)))) * (matPair A⁻¹ s r t q : ℂ) *
        ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * (w ^ (n - 3))⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_im] at hw; exact lt_irrefl 0 hw
  have hpt : ∀ u : Fin 2 → ℝ, (((u ⬝ᵥ A *ᵥ u) ^ 2 : ℝ) : ℂ) *
      ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (k + 4))⁻¹ =
      w ^ 2 * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (k + 4))⁻¹ -
        2 * w * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (k + 3))⁻¹ +
        ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (k + 2))⁻¹ := fun u =>
    ofReal_sq_mul_inv_neg_add_pow hw _ k
  have h4 := integrable_inv_neg_quadratic_add_pow hA hw (n := k + 4) (by omega)
  have h3 := integrable_inv_neg_quadratic_add_pow hA hw (n := k + 3) (by omega)
  have h2 := integrable_inv_neg_quadratic_add_pow hA hw (n := k + 2) (by omega)
  have hG : Integrable fun u : Fin 2 → ℝ => (((u ⬝ᵥ A *ᵥ u) ^ 2 : ℝ) : ℂ) *
      ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (k + 4))⁻¹ := by
    simp only [hpt]
    exact ((h4.const_mul _).sub (h3.const_mul _)).add h2
  rw [integral_mul_mul_mul_mul_quadratic hA (continuous_inv_neg_add_pow hw (k + 4)) hG s r t q]
  simp only [hpt]
  rw [integral_const_mul_sub_const_mul_add h4 h3 h2,
    integral_inv_neg_quadratic_add_pow hA hw (by omega),
    integral_inv_neg_quadratic_add_pow hA hw (by omega),
    integral_inv_neg_quadratic_add_pow hA hw (by omega)]
  have e1 : k + 4 - 1 = (k + 1) + 2 := by omega
  have e2 : k + 3 - 1 = (k + 1) + 1 := by omega
  have e3 : k + 2 - 1 = k + 1 := by omega
  have e4 : k + 4 - 3 = k + 1 := by omega
  rw [e1, e2, e3, e4, pow_add, pow_succ]
  push_cast
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hk2 : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
  have hk3 : (k : ℂ) + 3 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 2)
  have r1 : (k : ℂ) + 4 - 1 = (k : ℂ) + 3 := by ring
  have r2 : (k : ℂ) + 4 - 2 = (k : ℂ) + 2 := by ring
  have r3 : (k : ℂ) + 4 - 3 = (k : ℂ) + 1 := by ring
  have r4 : (k : ℂ) + 3 - 1 = (k : ℂ) + 2 := by ring
  have r5 : (k : ℂ) + 2 - 1 = (k : ℂ) + 1 := by ring
  rw [r1, r2, r3, r4, r5]
  have hs : ((Real.sqrt A.det : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA.det_pos).ne'
  field_simp
  ring

/-- **The spatial fourth moment.** For positive definite `A`, `Im w < 0` and `k ≥ 6`,
`∫ y_{sc} y_{rd} y_{te} y_{qf} (yᵀAy + w)^{-k} dy =
π³/(4(k-1)(k-2)(k-3)(k-4)(k-5)) Π (det A)^{-3/2} w^{5-k}` (`Π = spatialPair`). -/
theorem integral_mul_mul_mul_mul_inv_quadForm_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {k : ℕ} (hk : 6 ≤ k) (s : Fin 2) (c : Fin 3)
    (r : Fin 2) (d : Fin 3) (t : Fin 2) (e : Fin 3) (q : Fin 2) (f : Fin 3) :
    ∫ y : Fin 2 → Fin 3 → ℝ, ((y s c * y r d * y t e * y q f : ℝ) : ℂ) *
        ((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹ =
      (π : ℂ) ^ 3 * (4 * (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3) * ((k : ℂ) - 4) *
          ((k : ℂ) - 5)))⁻¹ * (spatialPair A s c r d t e q f : ℂ) *
        ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * (w ^ (k - 5))⁻¹ := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 6 := ⟨k - 6, by omega⟩
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_im] at hw; exact lt_irrefl 0 hw
  have hpt : ∀ y : Fin 2 → Fin 3 → ℝ, (((quadForm A y) ^ 2 : ℝ) : ℂ) *
      ((((quadForm A y : ℝ) : ℂ) + w) ^ (l + 6))⁻¹ =
      ((((quadForm A y : ℝ) : ℂ) + w) ^ (l + 4))⁻¹ -
        2 * w * ((((quadForm A y : ℝ) : ℂ) + w) ^ (l + 5))⁻¹ +
        w ^ 2 * ((((quadForm A y : ℝ) : ℂ) + w) ^ (l + 6))⁻¹ := fun y =>
    ofReal_sq_mul_inv_add_pow hw _ l
  have hs := mem_slitPlane_iff.mpr (Or.inr hw.ne)
  have h6 := Spatial.integrable_inv_quadForm_add_pow hA hs (k := l + 6) (by omega)
  have h5 := Spatial.integrable_inv_quadForm_add_pow hA hs (k := l + 5) (by omega)
  have h4 := Spatial.integrable_inv_quadForm_add_pow hA hs (k := l + 4) (by omega)
  have hG : Integrable fun y : Fin 2 → Fin 3 → ℝ => (((quadForm A y) ^ 2 : ℝ) : ℂ) *
      ((((quadForm A y : ℝ) : ℂ) + w) ^ (l + 6))⁻¹ := by
    simp only [hpt]
    exact (h4.sub (h5.const_mul _)).add (h6.const_mul _)
  rw [integral_mul_mul_mul_mul_quadForm hA (continuous_inv_add_pow hw (l + 6)) hG]
  simp only [hpt]
  rw [integral_sub_const_mul_add_const_mul h4 h5 h6,
    Spatial.integral_inv_quadForm_add_pow hA hs (by omega),
    Spatial.integral_inv_quadForm_add_pow hA hs (by omega),
    Spatial.integral_inv_quadForm_add_pow hA hs (by omega)]
  have e1 : l + 4 - 3 = l + 1 := by omega
  have e2 : l + 5 - 3 = (l + 1) + 1 := by omega
  have e3 : l + 6 - 3 = (l + 1) + 2 := by omega
  have e4 : l + 6 - 5 = l + 1 := by omega
  rw [e1, e2, e3, e4, pow_add, pow_succ]
  push_cast
  have hl1 : (l : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero l
  have hl2 : (l : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l + 1)
  have hl3 : (l : ℂ) + 3 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l + 2)
  have hl4 : (l : ℂ) + 4 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l + 3)
  have hl5 : (l : ℂ) + 5 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l + 4)
  have r1 : (l : ℂ) + 4 - 1 = (l : ℂ) + 3 := by ring
  have r2 : (l : ℂ) + 4 - 2 = (l : ℂ) + 2 := by ring
  have r3 : (l : ℂ) + 4 - 3 = (l : ℂ) + 1 := by ring
  have r4 : (l : ℂ) + 5 - 1 = (l : ℂ) + 4 := by ring
  have r5 : (l : ℂ) + 5 - 2 = (l : ℂ) + 3 := by ring
  have r6 : (l : ℂ) + 5 - 3 = (l : ℂ) + 2 := by ring
  have r7 : (l : ℂ) + 6 - 1 = (l : ℂ) + 5 := by ring
  have r8 : (l : ℂ) + 6 - 2 = (l : ℂ) + 4 := by ring
  have r9 : (l : ℂ) + 6 - 3 = (l : ℂ) + 3 := by ring
  have r10 : (l : ℂ) + 6 - 4 = (l : ℂ) + 2 := by ring
  have r11 : (l : ℂ) + 6 - 5 = (l : ℂ) + 1 := by ring
  rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11]
  have hsd : ((Real.sqrt A.det : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA.det_pos).ne'
  field_simp
  ring

/-! ### Odd and even parts of a weight -/

section Parity

variable {X : Type*} [AddCommGroup X] [MeasurableSpace X] [MeasurableNeg X] {μ : Measure X}
  [μ.IsNegInvariant]

/-- An odd weight against an even kernel integrates to zero. -/
theorem integral_mul_eq_zero_of_odd {g F : X → ℂ} (hF : ∀ u, F (-u) = F u)
    (hg : ∀ u, g (-u) = -g u) : ∫ u, g u * F u ∂μ = 0 := by
  have h := integral_neg_eq_self (fun u => g u * F u) μ
  simp only [hF, hg, neg_mul, integral_neg] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- Only the even part of a weight contributes against an even kernel: if
`g(u) + g(-u) = 2 h(u)`, then `∫ g F = ∫ h F`. -/
theorem integral_mul_eq_of_even {g h F : X → ℂ} (hF : ∀ u, F (-u) = F u)
    (hg : Integrable (fun u => g u * F u) μ) (heven : ∀ u, g u + g (-u) = 2 * h u) :
    ∫ u, g u * F u ∂μ = ∫ u, h u * F u ∂μ := by
  have hgneg : Integrable (fun u => g (-u) * F u) μ := by
    refine (hg.comp_neg).congr (Eventually.of_forall fun u => ?_)
    show g (-u) * F (-u) = g (-u) * F u
    rw [hF]
  have h1 : ∫ u, g (-u) * F u ∂μ = ∫ u, g u * F u ∂μ := by
    rw [← integral_neg_eq_self (fun u => g u * F u) μ]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      show g (-u) * F u = g (-u) * F (-u)
      rw [hF])
  have h2 : (∫ u, g u * F u ∂μ) + ∫ u, g (-u) * F u ∂μ = 2 * ∫ u, h u * F u ∂μ := by
    rw [← integral_add hg hgneg, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      show g u * F u + g (-u) * F u = 2 * (h u * F u)
      rw [← add_mul, heven u, mul_assoc])
  rw [h1] at h2
  linear_combination (1 / 2 : ℂ) * h2

end Parity

/-- Odd weights have vanishing energy integrals. -/
theorem integral_mul_inv_neg_quadratic_add_pow_eq_zero_of_odd (A : Matrix (Fin 2) (Fin 2) ℝ)
    (w : ℂ) (n : ℕ) {g : (Fin 2 → ℝ) → ℂ} (hg : ∀ u, g (-u) = -g u) :
    ∫ u : Fin 2 → ℝ, g u * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹ = 0 :=
  integral_mul_eq_zero_of_odd (fun u => by
    simp only [mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]) hg

/-- Odd weights have vanishing spatial integrals. -/
theorem integral_mul_inv_quadForm_add_pow_eq_zero_of_odd (A : Matrix (Fin 2) (Fin 2) ℝ)
    (w : ℂ) (k : ℕ) {h : (Fin 2 → Fin 3 → ℝ) → ℂ} (hh : ∀ y, h (-y) = -h y) :
    ∫ y : Fin 2 → Fin 3 → ℝ, h y * ((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹ = 0 :=
  integral_mul_eq_zero_of_odd (fun y => by
    simp only [Spatial.quadForm_eq_sum, Pi.neg_apply, neg_mul_neg]) hh

/-- **The energy integral of a weight with an even part of degree at most four.** If
`g(u) + g(-u) = 2 (a + ∑ₛᵣ Cₛᵣ uₛ uᵣ + ∑ₛᵣₜq Eₛᵣₜq uₛ uᵣ uₜ u_q)` and `g (-uᵀAu + w)^{-n}` is
integrable (`n ≥ 4`), then
`∫ g (-uᵀAu + w)^{-n} = a · (-(π/(n-1)) U^{-1/2} w^{1-n}) +
(∑ₛᵣ Cₛᵣ (A⁻¹)ₛᵣ) · π/(2(n-1)(n-2)) U^{-1/2} w^{2-n} +
(∑ Eₛᵣₜq Πₛᵣₜq(A⁻¹)) · (-π/(4(n-1)(n-2)(n-3))) U^{-1/2} w^{3-n}`. -/
theorem integral_mul_inv_neg_quadratic_add_pow_of_even_quartic {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {n : ℕ} (hn : 4 ≤ n) {g : (Fin 2 → ℝ) → ℂ}
    (hg : Integrable fun u : Fin 2 → ℝ => g u * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹)
    (a : ℂ) (C : Fin 2 → Fin 2 → ℂ) (E : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ)
    (heven : ∀ u, g u + g (-u) = 2 * (a + ∑ s, ∑ r, C s r * ((u s * u r : ℝ) : ℂ) +
      ∑ s, ∑ r, ∑ t, ∑ q, E s r t q * ((u s * u r * u t * u q : ℝ) : ℂ))) :
    ∫ u : Fin 2 → ℝ, g u * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹ =
      a * (-(π / ((n : ℂ) - 1)) * ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * (w ^ (n - 1))⁻¹) +
        (∑ s, ∑ r, C s r * (A⁻¹ s r : ℂ)) * (π / (2 * (((n : ℂ) - 1) * ((n : ℂ) - 2))) *
          ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * (w ^ (n - 2))⁻¹) +
        (∑ s, ∑ r, ∑ t, ∑ q, E s r t q * (matPair A⁻¹ s r t q : ℂ)) *
          (-(π / (4 * (((n : ℂ) - 1) * ((n : ℂ) - 2) * ((n : ℂ) - 3)))) *
            ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * (w ^ (n - 3))⁻¹) := by
  set F : (Fin 2 → ℝ) → ℂ := fun u => ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹ with hF
  have hFneg : ∀ u, F (-u) = F u := fun u => by
    simp only [hF, mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  rw [integral_mul_eq_of_even hFneg hg heven]
  have hFint : Integrable F := integrable_inv_neg_quadratic_add_pow hA hw (by omega)
  have hM2 : ∀ s r, Integrable fun u : Fin 2 → ℝ => C s r * (((u s * u r : ℝ) : ℂ) * F u) :=
    fun s r => (integrable_mul_mul_inv_neg_quadratic_add_pow hA hw (by omega) s r).const_mul _
  have hM4 : ∀ s r t q, Integrable fun u : Fin 2 → ℝ =>
      E s r t q * (((u s * u r * u t * u q : ℝ) : ℂ) * F u) :=
    fun s r t q =>
      (integrable_mul_mul_mul_mul_inv_neg_quadratic_add_pow hA hw hn s r t q).const_mul _
  have hpt : ∀ u, (a + ∑ s, ∑ r, C s r * ((u s * u r : ℝ) : ℂ) +
      ∑ s, ∑ r, ∑ t, ∑ q, E s r t q * ((u s * u r * u t * u q : ℝ) : ℂ)) * F u =
      a * F u + ∑ s, ∑ r, C s r * (((u s * u r : ℝ) : ℂ) * F u) +
        ∑ s, ∑ r, ∑ t, ∑ q, E s r t q * (((u s * u r * u t * u q : ℝ) : ℂ) * F u) := fun u => by
    simp only [add_mul, Finset.sum_mul, mul_assoc]
  simp only [hpt]
  have hS2 : Integrable fun u : Fin 2 → ℝ => ∑ s, ∑ r, C s r * (((u s * u r : ℝ) : ℂ) * F u) :=
    integrable_finsetSum _ fun s _ => integrable_finsetSum _ fun r _ => hM2 s r
  have hS4 : Integrable fun u : Fin 2 → ℝ =>
      ∑ s, ∑ r, ∑ t, ∑ q, E s r t q * (((u s * u r * u t * u q : ℝ) : ℂ) * F u) :=
    integrable_finsetSum _ fun s _ => integrable_finsetSum _ fun r _ =>
      integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun q _ => hM4 s r t q
  rw [integral_add_add (hFint.const_mul a) hS2 hS4,
    integral_const_mul, integral_sum_sum_sum_sum hM4,
    integral_finsetSum _ fun s _ => integrable_finsetSum _ fun r _ => hM2 s r]
  simp only [hF]
  rw [integral_inv_neg_quadratic_add_pow hA hw (by omega)]
  have e2 : ∀ s, ∫ u : Fin 2 → ℝ, ∑ r, C s r * (((u s * u r : ℝ) : ℂ) *
      ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹) = ∑ r, C s r * (π / (2 * (((n : ℂ) - 1) *
        ((n : ℂ) - 2))) * (A⁻¹ s r : ℂ) * ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * (w ^ (n - 2))⁻¹) :=
    fun s => by
      rw [integral_finsetSum _ fun r _ => hM2 s r]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [integral_const_mul, integral_mul_mul_inv_neg_quadratic_add_pow hA hw (by omega)]
  simp only [e2, integral_const_mul,
    integral_mul_mul_mul_mul_inv_neg_quadratic_add_pow hA hw hn]
  simp only [Finset.sum_mul]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  · refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ =>
      Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun q _ => ?_
    ring

/-- The integral of an eightfold finite sum of integrable functions on `(ℝ³)²`. -/
theorem integral_sum_eight {F : Fin 2 → Fin 3 → Fin 2 → Fin 3 → Fin 2 → Fin 3 → Fin 2 → Fin 3 →
    (Fin 2 → Fin 3 → ℝ) → ℂ} (h : ∀ s c r d t e q f, Integrable (F s c r d t e q f)) :
    ∫ y, ∑ s, ∑ c, ∑ r, ∑ d, ∑ t, ∑ e, ∑ q, ∑ f, F s c r d t e q f y =
      ∑ s, ∑ c, ∑ r, ∑ d, ∑ t, ∑ e, ∑ q, ∑ f, ∫ y, F s c r d t e q f y := by
  have h4 : ∀ s c r d, Integrable fun y => ∑ t, ∑ e, ∑ q, ∑ f, F s c r d t e q f y :=
    fun s c r d => integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun e _ =>
      integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun f _ => h s c r d t e q f
  rw [integral_finsetSum _ fun s _ => integrable_finsetSum _ fun c _ =>
    integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun d _ => h4 s c r d]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun r _ =>
    integrable_finsetSum _ fun d _ => h4 s c r d]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun r _ => integrable_finsetSum _ fun d _ => h4 s c r d]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_finsetSum _ fun d _ => h4 s c r d]
  refine Finset.sum_congr rfl fun d _ => ?_
  exact integral_sum_sum_sum_sum fun t e q f => h s c r d t e q f

/-- **The spatial integral of a weight with an even part of degree at most four.** If
`h(y) + h(-y) = 2 (a + ∑ D_{sc,rd} y_{sc} y_{rd} + ∑ E_{sc,rd,te,qf} y_{sc} y_{rd} y_{te} y_{qf})`
and `h (yᵀAy + w)^{-k}` is integrable (`k ≥ 6`), then
`∫ h (yᵀAy + w)^{-k} = a · π³/((k-1)(k-2)(k-3)) U^{-3/2} w^{3-k} +
(∑ D_{sc,rc} (A⁻¹)ₛᵣ) · π³/(2(k-1)⋯(k-4)) U^{-3/2} w^{4-k} +
(∑ E Π) · π³/(4(k-1)⋯(k-5)) U^{-3/2} w^{5-k}` (`Π = spatialPair`). -/
theorem integral_mul_inv_quadForm_add_pow_of_even_quartic {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {k : ℕ} (hk : 6 ≤ k)
    {h : (Fin 2 → Fin 3 → ℝ) → ℂ}
    (hh : Integrable fun y : Fin 2 → Fin 3 → ℝ => h y * ((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹)
    (a : ℂ) (D : Fin 2 → Fin 3 → Fin 2 → Fin 3 → ℂ)
    (E : Fin 2 → Fin 3 → Fin 2 → Fin 3 → Fin 2 → Fin 3 → Fin 2 → Fin 3 → ℂ)
    (heven : ∀ y, h y + h (-y) =
      2 * (a + ∑ s, ∑ c, ∑ r, ∑ d, D s c r d * ((y s c * y r d : ℝ) : ℂ) +
        ∑ s, ∑ c, ∑ r, ∑ d, ∑ t, ∑ e, ∑ q, ∑ f,
          E s c r d t e q f * ((y s c * y r d * y t e * y q f : ℝ) : ℂ))) :
    ∫ y : Fin 2 → Fin 3 → ℝ, h y * ((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹ =
      a * ((π : ℂ) ^ 3 * (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3))⁻¹ *
          ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * (w ^ (k - 3))⁻¹) +
        (∑ s, ∑ c, ∑ r, D s c r c * (A⁻¹ s r : ℂ)) * ((π : ℂ) ^ 3 *
          (2 * (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3) * ((k : ℂ) - 4)))⁻¹ *
          ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * (w ^ (k - 4))⁻¹) +
        (∑ s, ∑ c, ∑ r, ∑ d, ∑ t, ∑ e, ∑ q, ∑ f,
            E s c r d t e q f * (spatialPair A s c r d t e q f : ℂ)) *
          ((π : ℂ) ^ 3 * (4 * (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3) * ((k : ℂ) - 4) *
            ((k : ℂ) - 5)))⁻¹ * ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * (w ^ (k - 5))⁻¹) := by
  set F : (Fin 2 → Fin 3 → ℝ) → ℂ := fun y => ((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹ with hF
  have hqneg : ∀ y, quadForm A (-y) = quadForm A y := fun y => by
    simp only [Spatial.quadForm_eq_sum, Pi.neg_apply, neg_mul_neg]
  have hFneg : ∀ y, F (-y) = F y := fun y => by simp only [hF, hqneg]
  rw [integral_mul_eq_of_even hFneg hh heven]
  have hFint : Integrable F :=
    Spatial.integrable_inv_quadForm_add_pow hA (mem_slitPlane_iff.mpr (Or.inr hw.ne)) (by omega)
  have hM2 : ∀ s c r d, Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      D s c r d * (((y s c * y r d : ℝ) : ℂ) * F y) :=
    fun s c r d => (integrable_mul_mul_inv_quadForm_add_pow hA hw (by omega) s c r d).const_mul _
  have hM4 : ∀ s c r d t e q f, Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      E s c r d t e q f * (((y s c * y r d * y t e * y q f : ℝ) : ℂ) * F y) :=
    fun s c r d t e q f => (integrable_mul_mul_mul_mul_inv_quadForm_add_pow hA hw hk
      s c r d t e q f).const_mul _
  have hpt : ∀ y, (a + ∑ s, ∑ c, ∑ r, ∑ d, D s c r d * ((y s c * y r d : ℝ) : ℂ) +
      ∑ s, ∑ c, ∑ r, ∑ d, ∑ t, ∑ e, ∑ q, ∑ f,
        E s c r d t e q f * ((y s c * y r d * y t e * y q f : ℝ) : ℂ)) * F y =
      a * F y + ∑ s, ∑ c, ∑ r, ∑ d, D s c r d * (((y s c * y r d : ℝ) : ℂ) * F y) +
        ∑ s, ∑ c, ∑ r, ∑ d, ∑ t, ∑ e, ∑ q, ∑ f,
          E s c r d t e q f * (((y s c * y r d * y t e * y q f : ℝ) : ℂ) * F y) := fun y => by
    simp only [add_mul, Finset.sum_mul, mul_assoc]
  simp only [hpt]
  have hS2 : Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      ∑ s, ∑ c, ∑ r, ∑ d, D s c r d * (((y s c * y r d : ℝ) : ℂ) * F y) :=
    integrable_finsetSum _ fun s _ => integrable_finsetSum _ fun c _ =>
      integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun d _ => hM2 s c r d
  have hS4 : Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      ∑ s, ∑ c, ∑ r, ∑ d, ∑ t, ∑ e, ∑ q, ∑ f,
        E s c r d t e q f * (((y s c * y r d * y t e * y q f : ℝ) : ℂ) * F y) :=
    integrable_finsetSum _ fun s _ => integrable_finsetSum _ fun c _ =>
      integrable_finsetSum _ fun r _ => integrable_finsetSum _ fun d _ =>
      integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun e _ =>
      integrable_finsetSum _ fun q _ => integrable_finsetSum _ fun f _ => hM4 s c r d t e q f
  rw [integral_add_add (hFint.const_mul a) hS2 hS4,
    integral_const_mul, integral_sum_eight hM4, integral_sum_sum_sum_sum hM2]
  simp only [hF]
  rw [Spatial.integral_inv_quadForm_add_pow_of_im_neg hA hw (by omega)]
  simp only [integral_const_mul, integral_mul_mul_inv_quadForm_add_pow hA hw (by omega : 5 ≤ k),
    integral_mul_mul_mul_mul_inv_quadForm_add_pow hA hw hk, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl ?_) ?_
  · simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun r _ => ?_
    ring
  · simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun d _ =>
      Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun e _ =>
      Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun f _ => ?_
    ring

end QED.Integration.TwoLoop

end
