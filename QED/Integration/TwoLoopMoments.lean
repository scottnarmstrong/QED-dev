/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.TwoLoopParametric
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Second moments of the two-loop energy and spatial integrals

Infrastructure for the parametric representation with loop-momentum numerators (obligations
O2-10 and O2-11, `docs/TWO-LOOP-DERIVATION.md`, section 4.4). After Feynman parametrization and the
shift of the loop momenta, a numerator polynomial in the loop momenta leaves integrals of
monomials against the two kernels of the scalar case. With `U = det A` for a positive definite
real `2 × 2` matrix `A`, `Im w < 0`:

* energies, `u ∈ ℝ²`, `n ≥ 3`:
  `∫ uₛ uᵣ (-uᵀAu + w)^{-n} du = π/(2(n-1)(n-2)) (A⁻¹)ₛᵣ U^{-1/2} w^{2-n}`;
* spatial momenta, `y ∈ (ℝ³)²`, `k ≥ 5`:
  `∫ y_{sc} y_{rd} (yᵀAy + w)^{-k} dy = δ_{cd} π³/(2(k-1)(k-2)(k-3)(k-4)) (A⁻¹)ₛᵣ U^{-3/2} w^{4-k}`;

and the first moments vanish. Both are reduced to the radial formulas of the scalar case by the
identity `q (q + w)^{-k} = (q + w)^{1-k} - w (q + w)^{-k}`, after a linear change of variables
`u = N⁻¹ x` with `Nᵀ N` the Gram matrix of the quadratic form and the symmetry of
`∫ xₐ x_b g(|x|²) dx = δₐ_b (card)⁻¹ ∫ |x|² g(|x|²) dx` under reflections and transpositions of
coordinates.

## Main statements

* `integral_mul_mul_sum_sq`: the isotropic second moment on `ι → ℝ`.
* `integral_mul_mul_comp_mulVec`: its pull-back by an invertible linear map.
* `integral_mul_mul_inv_neg_quadratic_add_pow`, `integral_mul_mul_inv_quadForm_add_pow`: the
  energy and spatial second moments.
* `integrable_one_add_quadratic_pow_mul_norm`, `integrable_one_add_quadForm_pow_mul_norm`:
  integrability of the kernels against polynomial weights `(1 + q)^j`, for `n ≥ j + 2`
  (energies) and `k ≥ j + 4` (spatial momenta).
* `integral_one_add_quadratic_pow_mul_norm_le`, `integral_one_add_quadForm_pow_mul_norm_le`: the
  corresponding bounds, uniform in the real part of the constant, used for Fubini.
* `one_add_sum_sq_le`, `one_add_sum_sum_sq_le`: `1 + |t|² ≤ (1 + 2|τ|² + 2 tr A / U)(1 + q(t + τ))`.
* `integral_mul_inv_neg_quadratic_add_pow_of_even`, `integral_mul_inv_quadForm_add_pow_of_even`:
  the integral of a weight whose even part is a quadratic polynomial.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix Filter
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Spatial (quadForm)

/-! ### The isotropic second moment -/

section Isotropic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Off-diagonal moments vanish, by the reflection `xₐ ↦ -xₐ`. -/
theorem integral_mul_mul_sum_sq_of_ne (G : ℝ → ℂ) {a b : ι} (hab : a ≠ b) :
    ∫ x : ι → ℝ, ((x a * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2) = 0 := by
  set d : ι → ℝ := Function.update 1 a (-1) with hd
  have hdet : (diagonal d).det = -1 := by
    rw [det_diagonal, hd, Finset.prod_update_of_mem (Finset.mem_univ a)]
    simp
  have h := Spatial.integral_comp_mulVec (N := diagonal d) (by rw [hdet]; norm_num)
    (fun x : ι → ℝ => ((x a * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2))
  have hsq : ∀ x : ι → ℝ, ∑ i, (diagonal d *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
    intro x
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec_diagonal, hd]
    by_cases hi : i = a
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  have hpt : ∀ x : ι → ℝ, ((((diagonal d *ᵥ x) a * (diagonal d *ᵥ x) b : ℝ) : ℂ) *
      G (∑ i, (diagonal d *ᵥ x) i ^ 2)) = -(((x a * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2)) := by
    intro x
    rw [hsq, mulVec_diagonal, mulVec_diagonal, hd, Function.update_self,
      Function.update_of_ne hab.symm]
    simp only [Pi.one_apply]
    push_cast
    ring
  simp only [hpt, integral_neg, hdet, abs_neg, abs_one, inv_one, one_smul] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- Diagonal moments agree, by the transposition of two coordinates. -/
theorem integral_sq_mul_sum_sq_eq (G : ℝ → ℂ) (a b : ι) :
    ∫ x : ι → ℝ, ((x a ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
      ∫ x : ι → ℝ, ((x b ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) := by
  have hdet : |((Equiv.swap a b).permMatrix ℝ).det| = 1 := by
    rw [det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap a b)) with h | h <;> simp [h]
  have h := Spatial.integral_comp_mulVec (N := (Equiv.swap a b).permMatrix ℝ)
    (by intro h0; rw [h0, abs_zero] at hdet; exact zero_ne_one hdet)
    (fun x : ι → ℝ => ((x b ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2))
  rw [hdet, inv_one, one_smul] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hs := Equiv.sum_comp (Equiv.swap a b) (fun i => x i ^ 2)
  simp only [permMatrix_mulVec, Function.comp_apply, Equiv.swap_apply_right] at hs ⊢
  rw [hs]

omit [DecidableEq ι] in
theorem integrable_mul_mul_sum_sq {G : ℝ → ℂ} (hGc : Continuous G)
    (hG : Integrable fun x : ι → ℝ => ((∑ i, x i ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2)) (a b : ι) :
    Integrable fun x : ι → ℝ => ((x a * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2) := by
  refine hG.mono ((continuous_ofReal.comp (by fun_prop)).mul
    (hGc.comp (by fun_prop))).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have ha := Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ a)
  have hb := Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ b)
  have hle : |x a * x b| ≤ |∑ i, x i ^ 2| := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (x i)), abs_mul]
    nlinarith [abs_nonneg (x a), abs_nonneg (x b), sq_abs (x a), sq_abs (x b),
      sq_nonneg (|x a| - |x b|)]
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- **The isotropic second moment.** For continuous `G` with `|x|² G(|x|²)` integrable,
`∫ xₐ x_b G(|x|²) dx = δₐ_b (card ι)⁻¹ ∫ |x|² G(|x|²) dx`. -/
theorem integral_mul_mul_sum_sq {G : ℝ → ℂ} (hGc : Continuous G)
    (hG : Integrable fun x : ι → ℝ => ((∑ i, x i ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2)) (a b : ι) :
    ∫ x : ι → ℝ, ((x a * x b : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
      if a = b then ((Fintype.card ι : ℂ))⁻¹ *
        ∫ x : ι → ℝ, ((∑ i, x i ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) else 0 := by
  split_ifs with hab
  · subst hab
    have : Nonempty ι := ⟨a⟩
    have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hsum : ∫ x : ι → ℝ, ((∑ i, x i ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
        ∑ c : ι, ∫ x : ι → ℝ, ((x c ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) := by
      rw [← integral_finsetSum _ fun c _ => ?_]
      · congr 1
        funext x
        push_cast
        rw [Finset.sum_mul]
      · simpa [sq] using integrable_mul_mul_sum_sq hGc hG c c
    rw [hsum, Finset.sum_congr rfl fun c _ => integral_sq_mul_sum_sq_eq G c a, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    simp only [sq]
  · exact integral_mul_mul_sum_sq_of_ne G hab

omit [DecidableEq ι] in
/-- `uᵀ (Nᵀ N) u = |N u|²`. -/
theorem dotProduct_transpose_mul_mulVec (N : Matrix ι ι ℝ) (u : ι → ℝ) :
    u ⬝ᵥ (Nᵀ * N) *ᵥ u = ∑ i, (N *ᵥ u) i ^ 2 := by
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp [dotProduct, sq]

/-- **The pulled-back second moment.** For invertible `N` and `|N u|² G(|N u|²)` integrable,
`∫ uₐ u_b G(|N u|²) du = ((Nᵀ N)⁻¹)ₐ_b (card ι)⁻¹ ∫ |N u|² G(|N u|²) du`. -/
theorem integral_mul_mul_comp_mulVec {N : Matrix ι ι ℝ} (hN : N.det ≠ 0) {G : ℝ → ℂ}
    (hGc : Continuous G)
    (hG : Integrable fun u : ι → ℝ => ((∑ i, (N *ᵥ u) i ^ 2 : ℝ) : ℂ) * G (∑ i, (N *ᵥ u) i ^ 2))
    (a b : ι) :
    ∫ u : ι → ℝ, ((u a * u b : ℝ) : ℂ) * G (∑ i, (N *ᵥ u) i ^ 2) =
      ((Nᵀ * N)⁻¹ a b : ℂ) * (((Fintype.card ι : ℂ))⁻¹ *
        ∫ u : ι → ℝ, ((∑ i, (N *ᵥ u) i ^ 2 : ℝ) : ℂ) * G (∑ i, (N *ᵥ u) i ^ 2)) := by
  have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  have hG' : Integrable fun x : ι → ℝ => ((∑ i, x i ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) :=
    (Spatial.integrable_comp_mulVec_iff hN (g := fun x : ι → ℝ =>
      ((∑ i, x i ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2))).mp hG
  have hX := Spatial.integral_comp_mulVec hN
    (fun x : ι → ℝ => ((∑ i, x i ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2))
  have h := Spatial.integral_comp_mulVec hN
    (fun x : ι → ℝ => (((N⁻¹ *ᵥ x) a * (N⁻¹ *ᵥ x) b : ℝ) : ℂ) * G (∑ i, x i ^ 2))
  have hinv : ∀ u : ι → ℝ, N⁻¹ *ᵥ (N *ᵥ u) = u := fun u => by
    rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
  simp only [hinv] at h
  rw [h, hX]
  have hpt : ∀ x : ι → ℝ, (((N⁻¹ *ᵥ x) a * (N⁻¹ *ᵥ x) b : ℝ) : ℂ) * G (∑ i, x i ^ 2) =
      ∑ i, ∑ j, ((N⁻¹ a i * N⁻¹ b j : ℝ) : ℂ) * (((x i * x j : ℝ) : ℂ) * G (∑ k, x k ^ 2)) := by
    intro x
    have e : ((N⁻¹ *ᵥ x) a * (N⁻¹ *ᵥ x) b : ℝ) = ∑ i, ∑ j, N⁻¹ a i * N⁻¹ b j * (x i * x j) := by
      simp only [mulVec, dotProduct, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hpt]
  have hij : ∀ i j, ∫ x : ι → ℝ, ((N⁻¹ a i * N⁻¹ b j : ℝ) : ℂ) *
      (((x i * x j : ℝ) : ℂ) * G (∑ k, x k ^ 2)) =
      ((N⁻¹ a i * N⁻¹ b j : ℝ) : ℂ) * (if i = j then ((Fintype.card ι : ℂ))⁻¹ *
        ∫ x : ι → ℝ, ((∑ i, x i ^ 2 : ℝ) : ℂ) * G (∑ i, x i ^ 2) else 0) := fun i j => by
    rw [integral_const_mul, integral_mul_mul_sum_sq hGc hG']
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrable_mul_mul_sum_sq hGc hG' i j).const_mul _]
  rw [Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ =>
    (integrable_mul_mul_sum_sq hGc hG' i j).const_mul _]
  simp only [hij, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hinvT : (Nᵀ * N)⁻¹ a b = ∑ i, N⁻¹ a i * N⁻¹ b i := by
    rw [Matrix.mul_inv_rev, ← transpose_nonsing_inv, mul_apply]
    simp [transpose_apply]
  rw [hinvT, real_smul, real_smul]
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Polarization: two symmetric matrices with the same quadratic form are equal. -/
theorem eq_of_dotProduct_mulVec_eq {B C : Matrix ι ι ℝ} (hB : B.IsSymm) (hC : C.IsSymm)
    (h : ∀ u, u ⬝ᵥ B *ᵥ u = u ⬝ᵥ C *ᵥ u) : B = C := by
  have key : ∀ (D : Matrix ι ι ℝ) (i j : ι),
      (Pi.single i 1 + Pi.single j 1) ⬝ᵥ D *ᵥ (Pi.single i 1 + Pi.single j 1) =
        D i i + D i j + (D j i + D j j) := by
    intro D i j
    simp only [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single_one, single_dotProduct,
      one_mul, col_apply]
    ring
  have key1 : ∀ (D : Matrix ι ι ℝ) (i : ι), Pi.single i 1 ⬝ᵥ D *ᵥ Pi.single i 1 = D i i := by
    intro D i
    simp only [mulVec_single_one, single_dotProduct, one_mul, col_apply]
  ext i j
  have h1 := h (Pi.single i 1)
  have h2 := h (Pi.single j 1)
  have h3 := h (Pi.single i 1 + Pi.single j 1)
  rw [key1, key1] at h1 h2
  rw [key, key] at h3
  have hb := hB.apply i j
  have hc := hC.apply i j
  linarith

end Isotropic

/-! ### The energy second moment -/

/-- `Nᵀ N = A` for the Cholesky factor `N` of a positive definite `A`. -/
theorem cholesky_transpose_mul_self {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) :
    (cholesky A)ᵀ * cholesky A = A := by
  refine eq_of_dotProduct_mulVec_eq ?_ ?_ fun u => ?_
  · exact (isSymm_transpose_mul_self _)
  · have hsym : A 1 0 = A 0 1 := by simpa using hA.isHermitian.apply 0 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hsym]
  · rw [dotProduct_transpose_mul_mulVec, dotProduct_mulVec_eq_cholesky hA, Fin.sum_univ_two]

theorem det_cholesky_ne_zero {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) :
    (cholesky A).det ≠ 0 := by
  rw [det_cholesky hA]
  exact (Real.sqrt_pos.mpr hA.det_pos).ne'

/-- **Energy second moment, general kernel.** For positive definite `A` and continuous `G` with
`q G(q)` integrable, `q = uᵀAu`: `∫ uₛ uᵣ G(q) du = (A⁻¹)ₛᵣ · ½ ∫ q G(q) du`. -/
theorem integral_mul_mul_quadratic {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) {G : ℝ → ℂ}
    (hGc : Continuous G)
    (hG : Integrable fun u : Fin 2 → ℝ => ((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) * G (u ⬝ᵥ A *ᵥ u))
    (s r : Fin 2) :
    ∫ u : Fin 2 → ℝ, ((u s * u r : ℝ) : ℂ) * G (u ⬝ᵥ A *ᵥ u) =
      (A⁻¹ s r : ℂ) * (2⁻¹ * ∫ u : Fin 2 → ℝ, ((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) * G (u ⬝ᵥ A *ᵥ u)) := by
  have hq : ∀ u : Fin 2 → ℝ, u ⬝ᵥ A *ᵥ u = ∑ i, (cholesky A *ᵥ u) i ^ 2 := fun u => by
    rw [dotProduct_mulVec_eq_cholesky hA, Fin.sum_univ_two]
  simp only [hq] at hG ⊢
  rw [integral_mul_mul_comp_mulVec (det_cholesky_ne_zero hA) hGc hG s r,
    cholesky_transpose_mul_self hA, Fintype.card_fin]
  push_cast
  ring

/-! ### The spatial second moment -/

/-- The loop index `0` or `1` of a coordinate of `ℝ^{Fin 3 ⊕ Fin 3}`. -/
def sumLoop : Fin 3 ⊕ Fin 3 → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The spatial component of a coordinate of `ℝ^{Fin 3 ⊕ Fin 3}`. -/
def sumComp : Fin 3 ⊕ Fin 3 → Fin 3 := Sum.elim id id

/-- The coordinate of `ℝ^{Fin 3 ⊕ Fin 3}` of loop `s` and spatial component `c`. -/
def sumIndex (s : Fin 2) (c : Fin 3) : Fin 3 ⊕ Fin 3 := if s = 0 then Sum.inl c else Sum.inr c

/-- The pair `(v₁, v₂) ∈ (ℝ³)²` with coordinates `u : Fin 3 ⊕ Fin 3 → ℝ`. -/
def sumPair (u : Fin 3 ⊕ Fin 3 → ℝ) : Fin 2 → Fin 3 → ℝ := fun s c => u (sumIndex s c)

theorem sumPair_eq (u : Fin 3 ⊕ Fin 3 → ℝ) :
    sumPair u = MeasurableEquiv.finTwoArrow.symm
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => ℝ) u) := by
  funext s c
  fin_cases s <;> rfl

theorem measurePreserving_sumPair : MeasurePreserving sumPair := by
  have h := (MeasurePreserving.symm _ (volume_preserving_finTwoArrow (Fin 3 → ℝ))).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => ℝ))
  convert h using 1
  funext u
  exact sumPair_eq u

theorem measurableEmbedding_sumPair : MeasurableEmbedding sumPair := by
  have h := (MeasurableEquiv.finTwoArrow.symm.measurableEmbedding).comp
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 3 ⊕ Fin 3 => ℝ)).measurableEmbedding
  convert h using 1
  funext u
  exact sumPair_eq u

theorem sumIndex_eq_sumIndex_iff (s r : Fin 2) (c d : Fin 3) :
    sumIndex s c = sumIndex r d ↔ s = r ∧ c = d := by
  fin_cases s <;> fin_cases r <;> simp [sumIndex]

theorem sumLoop_sumIndex (s : Fin 2) (c : Fin 3) : sumLoop (sumIndex s c) = s := by
  fin_cases s <;> rfl

theorem sumComp_sumIndex (s : Fin 2) (c : Fin 3) : sumComp (sumIndex s c) = c := by
  fin_cases s <;> rfl

/-- The matrix `A ⊗ 1₃` on `ℝ^{Fin 3 ⊕ Fin 3}`: the Gram matrix of `quadForm A`. -/
def blockGram (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.of fun i j => if sumComp i = sumComp j then A (sumLoop i) (sumLoop j) else 0

theorem sum_sum_type_eq (f : Fin 3 ⊕ Fin 3 → ℝ) :
    ∑ i, f i = ∑ s : Fin 2, ∑ c : Fin 3, f (sumIndex s c) := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  rfl

theorem blockGram_mul (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    blockGram A * blockGram B = blockGram (A * B) := by
  ext i j
  rw [mul_apply, sum_sum_type_eq]
  simp only [blockGram, of_apply, sumLoop_sumIndex, sumComp_sumIndex, ite_mul, zero_mul,
    mul_ite, mul_zero]
  rw [mul_apply]
  by_cases h : sumComp i = sumComp j
  · simp only [h, ite_true]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single (sumComp j)]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  · simp only [h, ite_false]
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun c _ => ?_
    by_cases h1 : sumComp i = c
    · subst h1; simp [h]
    · simp [h1]

theorem blockGram_one : blockGram (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext i j
  simp only [blockGram, of_apply, one_apply]
  rcases i with c | c <;> rcases j with d | d <;> simp [sumComp, sumLoop]

theorem blockGram_transpose (A : Matrix (Fin 2) (Fin 2) ℝ) : (blockGram A)ᵀ = blockGram Aᵀ := by
  ext i j
  simp only [transpose_apply, blockGram, of_apply, eq_comm (a := sumComp j)]

theorem blockGram_inv {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : IsUnit A.det) :
    (blockGram A)⁻¹ = blockGram A⁻¹ := by
  refine inv_eq_right_inv ?_
  rw [blockGram_mul, mul_nonsing_inv _ hA, blockGram_one]

theorem det_blockGram_ne_zero {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : IsUnit A.det) :
    (blockGram A).det ≠ 0 := by
  intro h
  have := congrArg det ((blockGram_mul A A⁻¹).trans (by rw [mul_nonsing_inv _ hA, blockGram_one]))
  rw [det_mul, h, zero_mul, det_one] at this
  exact zero_ne_one this

theorem quadForm_sumPair (A : Matrix (Fin 2) (Fin 2) ℝ) (u : Fin 3 ⊕ Fin 3 → ℝ) :
    quadForm A (sumPair u) = u ⬝ᵥ blockGram A *ᵥ u := by
  rw [Spatial.quadForm_eq_sum]
  simp only [dotProduct, mulVec, sum_sum_type_eq, sumPair, blockGram, of_apply,
    sumLoop_sumIndex, sumComp_sumIndex, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun c _ => by ring

/-- **Spatial second moment, general kernel.** For positive definite `A` and continuous `G` with
`q G(q)` integrable, `q = quadForm A y`:
`∫ y_{sc} y_{rd} G(q) dy = δ_{cd} (A⁻¹)ₛᵣ · ⅙ ∫ q G(q) dy`. -/
theorem integral_mul_mul_quadForm {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) {G : ℝ → ℂ}
    (hGc : Continuous G)
    (hG : Integrable fun y : Fin 2 → Fin 3 → ℝ => ((quadForm A y : ℝ) : ℂ) * G (quadForm A y))
    (s r : Fin 2) (c d : Fin 3) :
    ∫ y : Fin 2 → Fin 3 → ℝ, ((y s c * y r d : ℝ) : ℂ) * G (quadForm A y) =
      if c = d then (A⁻¹ s r : ℂ) *
        (6⁻¹ * ∫ y : Fin 2 → Fin 3 → ℝ, ((quadForm A y : ℝ) : ℂ) * G (quadForm A y))
      else 0 := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  set N := blockGram (cholesky A) with hNdef
  have hdetM : IsUnit (cholesky A).det := isUnit_iff_ne_zero.mpr (det_cholesky_ne_zero hA)
  have hN : N.det ≠ 0 := det_blockGram_ne_zero hdetM
  have hNN : Nᵀ * N = blockGram A := by
    rw [hNdef, blockGram_transpose, blockGram_mul, cholesky_transpose_mul_self hA]
  have hq : ∀ u, quadForm A (sumPair u) = ∑ i, (N *ᵥ u) i ^ 2 := fun u => by
    rw [quadForm_sumPair, ← hNN, dotProduct_transpose_mul_mulVec]
  have hG' : Integrable fun u : Fin 3 ⊕ Fin 3 → ℝ =>
      ((∑ i, (N *ᵥ u) i ^ 2 : ℝ) : ℂ) * G (∑ i, (N *ᵥ u) i ^ 2) := by
    have := (measurePreserving_sumPair.integrable_comp_emb measurableEmbedding_sumPair).mpr hG
    simpa only [Function.comp_def, hq] using this
  rw [← measurePreserving_sumPair.integral_comp measurableEmbedding_sumPair,
    ← measurePreserving_sumPair.integral_comp measurableEmbedding_sumPair]
  simp only [hq]
  simp only [sumPair]
  rw [integral_mul_mul_comp_mulVec hN hGc hG', hNN, blockGram_inv hu]
  simp only [blockGram, of_apply, sumComp_sumIndex, sumLoop_sumIndex]
  split_ifs with h
  · have : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := rfl
    rw [this]
    push_cast
    ring
  · simp

/-! ### Polynomial weights: comparison with the quadratic form -/

/-- `|u|² det A ≤ tr A · uᵀAu` for positive definite `2 × 2` matrices `A`. -/
theorem sum_sq_mul_det_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (u : Fin 2 → ℝ) :
    (∑ i, u i ^ 2) * A.det ≤ A.trace * (u ⬝ᵥ A *ᵥ u) := by
  have hsym : A 1 0 = A 0 1 := by simpa using hA.isHermitian.apply 0 1
  simp only [Fin.sum_univ_two, det_fin_two, trace_fin_two, dotProduct, mulVec, hsym]
  nlinarith [sq_nonneg (A 0 0 * u 0 + A 0 1 * u 1), sq_nonneg (A 0 1 * u 0 + A 1 1 * u 1)]

theorem trace_div_det_nonneg {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) :
    0 ≤ A.trace / A.det := by
  have h0 : 0 < A 0 0 := hA.diag_pos
  have h1 : 0 < A 1 1 := hA.diag_pos
  exact div_nonneg (by rw [trace_fin_two]; linarith) hA.det_pos.le

/-- The energy weight comparison: `1 + |t|² ≤ (1 + 2|τ|² + 2 tr A / det A)(1 + uᵀAu)`, `u = t + τ`. -/
theorem one_add_sum_sq_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef) (t τ : Fin 2 → ℝ) :
    1 + ∑ i, t i ^ 2 ≤ (1 + 2 * ∑ i, τ i ^ 2 + 2 * (A.trace / A.det)) *
      (1 + (t + τ) ⬝ᵥ A *ᵥ (t + τ)) := by
  have hdet := hA.det_pos
  have htr := trace_div_det_nonneg hA
  have hq := dotProduct_mulVec_self_nonneg hA (t + τ)
  have hu : ∑ i, (t + τ) i ^ 2 ≤ A.trace / A.det * ((t + τ) ⬝ᵥ A *ᵥ (t + τ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hdet]
    exact sum_sq_mul_det_le hA _
  have ht : ∑ i, t i ^ 2 ≤ 2 * ∑ i, (t + τ) i ^ 2 + 2 * ∑ i, τ i ^ 2 := by
    simp only [Fin.sum_univ_two, Pi.add_apply]
    nlinarith [sq_nonneg (t 0 + 2 * τ 0), sq_nonneg (t 1 + 2 * τ 1)]
  have hτ : 0 ≤ ∑ i, τ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [mul_nonneg hτ hq, mul_nonneg htr hq]

/-- `|y|² det A ≤ tr A · yᵀAy` on `(ℝ³)²`. -/
theorem sum_sum_sq_mul_det_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (y : Fin 2 → Fin 3 → ℝ) :
    (∑ s, ∑ c, y s c ^ 2) * A.det ≤ A.trace * quadForm A y := by
  rw [quadForm_eq_sum_dotProduct, Finset.sum_comm, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => sum_sq_mul_det_le hA (fun s => y s c)

theorem sum_sq_le_two_mul {ι : Type*} (S : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ S, f i ^ 2 ≤ 2 * ∑ i ∈ S, (f i + g i) ^ 2 + 2 * ∑ i ∈ S, g i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (f i + 2 * g i)]

/-- The spatial weight comparison:
`1 + |v|² ≤ (1 + 2|σ|² + 2 tr A / det A)(1 + yᵀAy)`, `y = v + σ`. -/
theorem one_add_sum_sum_sq_le {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.PosDef)
    (v σ : Fin 2 → Fin 3 → ℝ) :
    1 + ∑ s, ∑ c, v s c ^ 2 ≤ (1 + 2 * ∑ s, ∑ c, σ s c ^ 2 + 2 * (A.trace / A.det)) *
      (1 + quadForm A (v + σ)) := by
  have hdet := hA.det_pos
  have htr := trace_div_det_nonneg hA
  have hq := quadForm_nonneg hA (v + σ)
  have hu : ∑ s, ∑ c, (v + σ) s c ^ 2 ≤ A.trace / A.det * quadForm A (v + σ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hdet]
    exact sum_sum_sq_mul_det_le hA _
  have ht : ∑ s, ∑ c, v s c ^ 2 ≤ 2 * ∑ s, ∑ c, (v + σ) s c ^ 2 + 2 * ∑ s, ∑ c, σ s c ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    simpa only [Pi.add_apply] using sum_sq_le_two_mul Finset.univ (v s) (σ s)
  have hσ : 0 ≤ ∑ s, ∑ c, σ s c ^ 2 :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg _
  nlinarith [mul_nonneg hσ hq, mul_nonneg htr hq]

/-! ### Polynomial weights: integrability and uniform bounds -/

theorem one_add_pow_mul_norm_inv_neg_I_le {q : ℝ} (hq : 0 ≤ q) {j n : ℕ} (hjn : j ≤ n) :
    (1 + q) ^ j * ‖((-(q : ℂ) + -I) ^ n)⁻¹‖ ≤ 2 ^ j * ‖((-(q : ℂ) + -I) ^ (n - j))⁻¹‖ := by
  set z : ℂ := -(q : ℂ) + -I with hzdef
  have hz2 : ‖z‖ ^ 2 = q ^ 2 + 1 := by
    rw [Complex.sq_norm, normSq_apply]
    simp [hzdef]
    ring
  have hz0 : 0 < ‖z‖ := by
    have : (0 : ℝ) < ‖z‖ ^ 2 := by rw [hz2]; positivity
    rcases (norm_nonneg z).lt_or_eq with h | h
    · exact h
    · rw [← h] at this; norm_num at this
  have hz : 1 + q ≤ 2 * ‖z‖ := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp ?_
    rw [mul_pow, hz2]
    nlinarith [sq_nonneg (3 * q - 1)]
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
  have h1 : (1 + q) ^ j ≤ 2 ^ j * ‖z‖ ^ j := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hz j
  have hzj : 0 < ‖z‖ ^ j := pow_pos hz0 j
  rw [Nat.add_sub_cancel_left, norm_inv, norm_inv, norm_pow, norm_pow, pow_add,
    show (1 + q) ^ j * (‖z‖ ^ j * ‖z‖ ^ k)⁻¹ = ((1 + q) ^ j / ‖z‖ ^ j) * (‖z‖ ^ k)⁻¹ by
      field_simp]
  gcongr
  rw [div_le_iff₀ hzj]
  exact h1

/-- The pointwise energy comparison with a polynomial weight. -/
theorem one_add_pow_mul_norm_inv_neg_add_le {q K ε δ : ℝ} {w : ℂ} (hq : 0 ≤ q) (hw : |w.re| ≤ K)
    (hwi : w.im = -ε) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8) (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2)
    {j n : ℕ} (hjn : j ≤ n) :
    (1 + q) ^ j * ‖((-(q : ℂ) + w) ^ n)⁻¹‖ ≤
      (Real.sqrt δ ^ n)⁻¹ * 2 ^ j * ‖((-(q : ℂ) + -I) ^ (n - j))⁻¹‖ := by
  have h1 := norm_inv_neg_add_pow_le_uniform hq hw hwi hδ0 hδ hδε n
  have h2 := one_add_pow_mul_norm_inv_neg_I_le hq hjn
  calc (1 + q) ^ j * ‖((-(q : ℂ) + w) ^ n)⁻¹‖
      ≤ (1 + q) ^ j * ((Real.sqrt δ ^ n)⁻¹ * ‖((-(q : ℂ) + -I) ^ n)⁻¹‖) := by gcongr
    _ = (Real.sqrt δ ^ n)⁻¹ * ((1 + q) ^ j * ‖((-(q : ℂ) + -I) ^ n)⁻¹‖) := by ring
    _ ≤ (Real.sqrt δ ^ n)⁻¹ * (2 ^ j * ‖((-(q : ℂ) + -I) ^ (n - j))⁻¹‖) := by gcongr
    _ = _ := by ring

theorem continuous_quadratic (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun u : Fin 2 → ℝ => u ⬝ᵥ A *ᵥ u := by
  simp only [dotProduct, mulVec]
  fun_prop

theorem continuous_inv_neg_add_pow {w : ℂ} (hw : w.im < 0) (n : ℕ) :
    Continuous fun q : ℝ => ((-(q : ℂ) + w) ^ n)⁻¹ :=
  Continuous.inv₀ (by fun_prop) fun q => pow_ne_zero _ (neg_ofReal_add_ne_zero hw q)

theorem continuous_inv_add_pow {w : ℂ} (hw : w.im < 0) (n : ℕ) :
    Continuous fun q : ℝ => (((q : ℂ) + w) ^ n)⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) fun q => pow_ne_zero _ fun h => ?_
  have := congrArg Complex.im h
  simp at this
  linarith

/-- **Energy integrability against `(1 + uᵀAu)^j`**, for `n ≥ j + 2`. -/
theorem integrable_one_add_quadratic_pow_mul_norm {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {j n : ℕ} (hjn : j + 2 ≤ n) :
    Integrable fun u : Fin 2 → ℝ =>
      (1 + u ⬝ᵥ A *ᵥ u) ^ j * ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹‖ := by
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta (abs_nonneg w.re) (by linarith : 0 < -w.im)
  have hb := (integrable_inv_neg_quadratic_add_pow hA (w := -I) (by simp)
    (by omega : 2 ≤ n - j)).norm.const_mul ((Real.sqrt δ ^ n)⁻¹ * 2 ^ j)
  refine hb.mono' ?_ (Eventually.of_forall fun u => ?_)
  · exact (((continuous_const.add (continuous_quadratic A)).pow j).mul
      ((continuous_inv_neg_add_pow hw n).comp (continuous_quadratic A)).norm).aestronglyMeasurable
  · have hq := dotProduct_mulVec_self_nonneg hA u
    rw [Real.norm_of_nonneg (by positivity)]
    exact one_add_pow_mul_norm_inv_neg_add_le hq le_rfl (by ring) hδ0 hδ hδε (by omega)

/-- **The uniform energy bound against `(1 + uᵀAu)^j`**:
`∫ (1 + q)^j ‖(-q + w)^{-n}‖ ≤ (√δ)^{-n} 2^j (det A)^{-1/2} K_{n-j}`. -/
theorem integral_one_add_quadratic_pow_mul_norm_le {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} {K ε δ : ℝ} (hw : |w.re| ≤ K) (hwi : w.im = -ε) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 8) (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) {j n : ℕ} (hjn : j + 2 ≤ n) :
    ∫ u : Fin 2 → ℝ, (1 + u ⬝ᵥ A *ᵥ u) ^ j * ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹‖ ≤
      (Real.sqrt δ ^ n)⁻¹ * 2 ^ j * ((Real.sqrt A.det)⁻¹ * energyNormConst (n - j)) := by
  rw [← integral_norm_inv_neg_quadratic hA (n - j), ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => ?_) ?_
    (Eventually.of_forall fun u => ?_)
  · have hq := dotProduct_mulVec_self_nonneg hA u
    positivity
  · exact (integrable_inv_neg_quadratic_add_pow hA (w := -I) (by simp)
      (by omega : 2 ≤ n - j)).norm.const_mul _
  · exact one_add_pow_mul_norm_inv_neg_add_le (dotProduct_mulVec_self_nonneg hA u) hw hwi hδ0
      hδ hδε (by omega)

/-- The constant `π³ / ((k-1)(k-2)(k-3))` of the six-dimensional formula. -/
noncomputable def spatialNormConst (k : ℕ) : ℝ :=
  π ^ 3 * (((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3))⁻¹

/-- The pointwise spatial comparison with a polynomial weight. -/
theorem one_add_pow_mul_norm_inv_add_le {q K ε δ V : ℝ} (hq : 0 ≤ q) (hV : |V| ≤ K)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8) (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) {j k : ℕ}
    (hjk : j ≤ k) :
    (1 + q) ^ j * ‖(((q : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ k)⁻¹‖ ≤
      (Real.sqrt δ ^ k)⁻¹ * ‖(((q : ℂ) + 1) ^ (k - j))⁻¹‖ := by
  have h1 := norm_inv_add_pow_le_uniform hq hV hδ0 hδ hδε k
  have hq1 : ((q : ℂ) + 1) = ((q + 1 : ℝ) : ℂ) := by push_cast; ring
  have hpos : 0 < q + 1 := by linarith
  have hn : ∀ m : ℕ, ‖(((q : ℂ) + 1) ^ m)⁻¹‖ = ((q + 1) ^ m)⁻¹ := fun m => by
    rw [hq1, norm_inv, norm_pow, norm_real, Real.norm_of_nonneg hpos.le]
  obtain ⟨l, rfl⟩ : ∃ l, k = j + l := ⟨k - j, by omega⟩
  rw [Nat.add_sub_cancel_left, hn]
  rw [hn] at h1
  calc (1 + q) ^ j * ‖(((q : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ (j + l))⁻¹‖
      ≤ (1 + q) ^ j * ((Real.sqrt δ ^ (j + l))⁻¹ * ((q + 1) ^ (j + l))⁻¹) := by gcongr
    _ = (Real.sqrt δ ^ (j + l))⁻¹ * ((q + 1) ^ l)⁻¹ := by
        rw [pow_add]
        field_simp
        ring

/-- **Spatial integrability against `(1 + yᵀAy)^j`**, for `k ≥ j + 4`. -/
theorem integrable_one_add_quadForm_pow_mul_norm {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {j k : ℕ} (hjk : j + 4 ≤ k) :
    Integrable fun v : Fin 2 → Fin 3 → ℝ =>
      (1 + quadForm A v) ^ j * ‖((((quadForm A v : ℝ) : ℂ) + w) ^ k)⁻¹‖ := by
  have hw' : w = ((w.re : ℝ) : ℂ) - ((-w.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  obtain ⟨δ, hδ0, hδ, hδε⟩ := exists_delta (abs_nonneg w.re) (by linarith : 0 < -w.im)
  have hb := (Spatial.integrable_inv_quadForm_add_pow hA (w := 1) one_mem_slitPlane
    (by omega : 4 ≤ k - j)).norm.const_mul (Real.sqrt δ ^ k)⁻¹
  have hcq : Continuous fun v : Fin 2 → Fin 3 → ℝ => quadForm A v := by
    simp only [Spatial.quadForm_eq_sum]
    fun_prop
  refine hb.mono' ?_ (Eventually.of_forall fun v => ?_)
  · exact (((continuous_const.add hcq).pow j).mul
      ((continuous_inv_add_pow hw k).comp hcq).norm).aestronglyMeasurable
  · have hq := quadForm_nonneg hA v
    rw [Real.norm_of_nonneg (by positivity)]
    conv_lhs => rw [hw']
    exact one_add_pow_mul_norm_inv_add_le hq le_rfl hδ0 hδ hδε (by omega)

/-- **The uniform spatial bound against `(1 + yᵀAy)^j`**:
`∫ (1 + q)^j ‖(q + V - iε)^{-k}‖ ≤ (√δ)^{-k} π³/((k'-1)(k'-2)(k'-3)) (det A)^{-3/2}`,
`k' = k - j`. -/
theorem integral_one_add_quadForm_pow_mul_norm_le {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {V K ε δ : ℝ} (hV : |V| ≤ K) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) {j k : ℕ} (hjk : j + 4 ≤ k) :
    ∫ v : Fin 2 → Fin 3 → ℝ,
        (1 + quadForm A v) ^ j * ‖((((quadForm A v : ℝ) : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ k)⁻¹‖ ≤
      (Real.sqrt δ ^ k)⁻¹ * (spatialNormConst (k - j) * (Real.sqrt A.det ^ 3)⁻¹) := by
  have hc := integral_norm_inv_quadForm_add_one hA (by omega : 4 ≤ k - j)
  have hc' : spatialNormConst (k - j) * (Real.sqrt A.det ^ 3)⁻¹ =
      ∫ v : Fin 2 → Fin 3 → ℝ, ‖((((quadForm A v : ℝ) : ℂ) + 1) ^ (k - j))⁻¹‖ := by
    rw [hc, spatialNormConst]
  rw [hc', ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun v => ?_) ?_
    (Eventually.of_forall fun v => ?_)
  · have hq := quadForm_nonneg hA v
    positivity
  · exact (Spatial.integrable_inv_quadForm_add_pow hA (w := 1) one_mem_slitPlane
      (by omega : 4 ≤ k - j)).norm.const_mul _
  · exact one_add_pow_mul_norm_inv_add_le (quadForm_nonneg hA v) hV hδ0 hδ hδε (by omega)

/-! ### The explicit second moments -/

theorem ofReal_mul_inv_neg_add_pow {w : ℂ} (hw : w.im < 0) (q : ℝ) (k : ℕ) :
    (q : ℂ) * ((-(q : ℂ) + w) ^ (k + 1))⁻¹ =
      w * ((-(q : ℂ) + w) ^ (k + 1))⁻¹ - ((-(q : ℂ) + w) ^ k)⁻¹ := by
  have hD := neg_ofReal_add_ne_zero hw q
  rw [pow_succ]
  field_simp
  ring

theorem ofReal_mul_inv_add_pow {w : ℂ} (hw : w.im < 0) (q : ℝ) (k : ℕ) :
    (q : ℂ) * (((q : ℂ) + w) ^ (k + 1))⁻¹ =
      (((q : ℂ) + w) ^ k)⁻¹ - w * (((q : ℂ) + w) ^ (k + 1))⁻¹ := by
  have hD : (q : ℂ) + w ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [pow_succ]
  field_simp
  ring

theorem integrable_mul_mul_inv_neg_quadratic_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {n : ℕ} (hn : 3 ≤ n) (s r : Fin 2) :
    Integrable fun u : Fin 2 → ℝ =>
      ((u s * u r : ℝ) : ℂ) * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹ := by
  have hb := (integrable_one_add_quadratic_pow_mul_norm hA hw (j := 1) (by omega)).const_mul
    (A.trace / A.det)
  refine hb.mono' (((continuous_ofReal.comp (by fun_prop)).mul
    ((continuous_inv_neg_add_pow hw n).comp (continuous_quadratic A))).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  have hq := dotProduct_mulVec_self_nonneg hA u
  have htr := trace_div_det_nonneg hA
  have hu : ∑ i, u i ^ 2 ≤ A.trace / A.det * (u ⬝ᵥ A *ᵥ u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hA.det_pos]
    exact sum_sq_mul_det_le hA _
  have hsr : |u s * u r| ≤ ∑ i, u i ^ 2 := by
    have ha := Finset.single_le_sum (fun i _ => sq_nonneg (u i)) (Finset.mem_univ s)
    have hb := Finset.single_le_sum (fun i _ => sq_nonneg (u i)) (Finset.mem_univ r)
    rw [abs_mul]
    nlinarith [abs_nonneg (u s), abs_nonneg (u r), sq_abs (u s), sq_abs (u r),
      sq_nonneg (|u s| - |u r|)]
  rw [norm_mul, norm_real, Real.norm_eq_abs, pow_one]
  calc |u s * u r| * ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹‖
      ≤ (A.trace / A.det * (1 + u ⬝ᵥ A *ᵥ u)) * ‖((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹‖ := by
        gcongr
        nlinarith
    _ = _ := by ring

/-- **The energy second moment.** For positive definite `A`, `Im w < 0` and `n ≥ 3`,
`∫ uₛ uᵣ (-uᵀAu + w)^{-n} du = π/(2(n-1)(n-2)) (A⁻¹)ₛᵣ (det A)^{-1/2} w^{2-n}`. -/
theorem integral_mul_mul_inv_neg_quadratic_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {n : ℕ} (hn : 3 ≤ n) (s r : Fin 2) :
    ∫ u : Fin 2 → ℝ, ((u s * u r : ℝ) : ℂ) * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹ =
      π / (2 * (((n : ℂ) - 1) * ((n : ℂ) - 2))) * (A⁻¹ s r : ℂ) *
        ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * (w ^ (n - 2))⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_im] at hw; exact lt_irrefl 0 hw
  have hpt : ∀ u : Fin 2 → ℝ, ((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) *
      ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (k + 3))⁻¹ =
      w * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (k + 3))⁻¹ -
        ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (k + 2))⁻¹ := fun u =>
    ofReal_mul_inv_neg_add_pow hw _ (k + 2)
  have h3 := integrable_inv_neg_quadratic_add_pow hA hw (n := k + 3) (by omega)
  have h2 := integrable_inv_neg_quadratic_add_pow hA hw (n := k + 2) (by omega)
  have hG : Integrable fun u : Fin 2 → ℝ => ((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) *
      ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ (k + 3))⁻¹ := by
    simp only [hpt]
    exact (h3.const_mul w).sub h2
  rw [integral_mul_mul_quadratic hA (continuous_inv_neg_add_pow hw (k + 3)) hG s r]
  simp only [hpt]
  rw [integral_sub (h3.const_mul w) h2, integral_const_mul,
    integral_inv_neg_quadratic_add_pow hA hw (by omega),
    integral_inv_neg_quadratic_add_pow hA hw (by omega)]
  have e1 : k + 3 - 1 = (k + 1) + 1 := by omega
  have e2 : k + 2 - 1 = k + 1 := by omega
  have e3 : k + 3 - 2 = k + 1 := by omega
  rw [e1, e2, e3, pow_succ]
  push_cast
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hk2 : (k : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k + 1)
  have hk3 : (k : ℂ) + 3 - 1 = (k : ℂ) + 2 := by ring
  have hk4 : (k : ℂ) + 3 - 2 = (k : ℂ) + 1 := by ring
  have hk5 : (k : ℂ) + 2 - 1 = (k : ℂ) + 1 := by ring
  rw [hk3, hk4, hk5]
  have hs : ((Real.sqrt A.det : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA.det_pos).ne'
  field_simp
  ring

theorem integrable_mul_mul_inv_quadForm_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {k : ℕ} (hk : 5 ≤ k) (s : Fin 2) (c : Fin 3)
    (r : Fin 2) (d : Fin 3) :
    Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      ((y s c * y r d : ℝ) : ℂ) * ((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹ := by
  have hb := (integrable_one_add_quadForm_pow_mul_norm hA hw (j := 1) (by omega)).const_mul
    (A.trace / A.det)
  have hcq : Continuous fun v : Fin 2 → Fin 3 → ℝ => quadForm A v := by
    simp only [Spatial.quadForm_eq_sum]
    fun_prop
  refine hb.mono' (((continuous_ofReal.comp (by fun_prop)).mul
    ((continuous_inv_add_pow hw k).comp hcq)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  have hq := quadForm_nonneg hA y
  have htr := trace_div_det_nonneg hA
  have hu : ∑ s, ∑ c, y s c ^ 2 ≤ A.trace / A.det * quadForm A y := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hA.det_pos]
    exact sum_sum_sq_mul_det_le hA _
  have hsr : |y s c * y r d| ≤ ∑ s, ∑ c, y s c ^ 2 := by
    have hle : ∀ s c, y s c ^ 2 ≤ ∑ s, ∑ c, y s c ^ 2 := fun s c =>
      (Finset.single_le_sum (fun c _ => sq_nonneg (y s c)) (Finset.mem_univ c)).trans
        (Finset.single_le_sum (f := fun s => ∑ c, y s c ^ 2)
          (fun s _ => Finset.sum_nonneg fun c _ => sq_nonneg (y s c)) (Finset.mem_univ s))
    have ha := hle s c
    have hb := hle r d
    rw [abs_mul]
    nlinarith [abs_nonneg (y s c), abs_nonneg (y r d), sq_abs (y s c), sq_abs (y r d),
      sq_nonneg (|y s c| - |y r d|)]
  rw [norm_mul, norm_real, Real.norm_eq_abs, pow_one]
  calc |y s c * y r d| * ‖((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹‖
      ≤ (A.trace / A.det * (1 + quadForm A y)) * ‖((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹‖ := by
        gcongr
        nlinarith
    _ = _ := by ring

/-- **The spatial second moment.** For positive definite `A`, `Im w < 0` and `k ≥ 5`,
`∫ y_{sc} y_{rd} (yᵀAy + w)^{-k} dy = δ_{cd} π³/(2(k-1)(k-2)(k-3)(k-4)) (A⁻¹)ₛᵣ
(det A)^{-3/2} w^{4-k}`. -/
theorem integral_mul_mul_inv_quadForm_add_pow {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {k : ℕ} (hk : 5 ≤ k) (s r : Fin 2) (c d : Fin 3) :
    ∫ y : Fin 2 → Fin 3 → ℝ, ((y s c * y r d : ℝ) : ℂ) * ((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹ =
      if c = d then (π : ℂ) ^ 3 *
          (2 * (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3) * ((k : ℂ) - 4)))⁻¹ *
          (A⁻¹ s r : ℂ) * ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * (w ^ (k - 4))⁻¹
      else 0 := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 5 := ⟨k - 5, by omega⟩
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_im] at hw; exact lt_irrefl 0 hw
  have hpt : ∀ y : Fin 2 → Fin 3 → ℝ, ((quadForm A y : ℝ) : ℂ) *
      ((((quadForm A y : ℝ) : ℂ) + w) ^ (l + 5))⁻¹ =
      ((((quadForm A y : ℝ) : ℂ) + w) ^ (l + 4))⁻¹ -
        w * ((((quadForm A y : ℝ) : ℂ) + w) ^ (l + 5))⁻¹ := fun y =>
    ofReal_mul_inv_add_pow hw _ (l + 4)
  have hs := mem_slitPlane_iff.mpr (Or.inr hw.ne)
  have h5 := Spatial.integrable_inv_quadForm_add_pow hA hs (k := l + 5) (by omega)
  have h4 := Spatial.integrable_inv_quadForm_add_pow hA hs (k := l + 4) (by omega)
  have hG : Integrable fun y : Fin 2 → Fin 3 → ℝ => ((quadForm A y : ℝ) : ℂ) *
      ((((quadForm A y : ℝ) : ℂ) + w) ^ (l + 5))⁻¹ := by
    simp only [hpt]
    exact h4.sub (h5.const_mul w)
  rw [integral_mul_mul_quadForm hA (continuous_inv_add_pow hw (l + 5)) hG s r c d]
  split_ifs with h
  · simp only [hpt]
    rw [integral_sub h4 (h5.const_mul w), integral_const_mul,
      Spatial.integral_inv_quadForm_add_pow hA hs (by omega),
      Spatial.integral_inv_quadForm_add_pow hA hs (by omega)]
    have e1 : l + 4 - 3 = l + 1 := by omega
    have e2 : l + 5 - 3 = (l + 1) + 1 := by omega
    have e3 : l + 5 - 4 = l + 1 := by omega
    rw [e1, e2, e3, pow_succ]
    push_cast
    have hl1 : (l : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero l
    have hl2 : (l : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l + 1)
    have hl3 : (l : ℂ) + 3 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l + 2)
    have hl4 : (l : ℂ) + 4 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (l + 3)
    have r1 : (l : ℂ) + 4 - 1 = (l : ℂ) + 3 := by ring
    have r2 : (l : ℂ) + 4 - 2 = (l : ℂ) + 2 := by ring
    have r3 : (l : ℂ) + 4 - 3 = (l : ℂ) + 1 := by ring
    have r4 : (l : ℂ) + 5 - 1 = (l : ℂ) + 4 := by ring
    have r5 : (l : ℂ) + 5 - 2 = (l : ℂ) + 3 := by ring
    have r6 : (l : ℂ) + 5 - 3 = (l : ℂ) + 2 := by ring
    have r7 : (l : ℂ) + 5 - 4 = (l : ℂ) + 1 := by ring
    rw [r1, r2, r3, r4, r5, r6, r7]
    have hsd : ((Real.sqrt A.det : ℝ) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA.det_pos).ne'
    field_simp
    ring
  · rfl

/-! ### Weights with a quadratic even part -/

/-- **The energy integral of a weight with quadratic even part.** If `g(u) + g(-u) =
2 (a + ∑ₛᵣ Cₛᵣ uₛ uᵣ)` and `g (-uᵀAu + w)^{-n}` is integrable (`n ≥ 3`), then
`∫ g (-uᵀAu + w)^{-n} = a · (-(π/(n-1)) U^{-1/2} w^{1-n}) +
(∑ₛᵣ Cₛᵣ (A⁻¹)ₛᵣ) · π/(2(n-1)(n-2)) U^{-1/2} w^{2-n}`, `U = det A`. -/
theorem integral_mul_inv_neg_quadratic_add_pow_of_even {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {n : ℕ} (hn : 3 ≤ n) {g : (Fin 2 → ℝ) → ℂ}
    (hg : Integrable fun u : Fin 2 → ℝ => g u * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹)
    (a : ℂ) (C : Fin 2 → Fin 2 → ℂ)
    (heven : ∀ u, g u + g (-u) = 2 * (a + ∑ s, ∑ r, C s r * ((u s * u r : ℝ) : ℂ))) :
    ∫ u : Fin 2 → ℝ, g u * ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹ =
      a * (-(π / ((n : ℂ) - 1)) * ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * (w ^ (n - 1))⁻¹) +
        (∑ s, ∑ r, C s r * (A⁻¹ s r : ℂ)) * (π / (2 * (((n : ℂ) - 1) * ((n : ℂ) - 2))) *
          ((Real.sqrt A.det : ℝ) : ℂ)⁻¹ * (w ^ (n - 2))⁻¹) := by
  set F : (Fin 2 → ℝ) → ℂ := fun u => ((-((u ⬝ᵥ A *ᵥ u : ℝ) : ℂ) + w) ^ n)⁻¹ with hF
  have hFneg : ∀ u, F (-u) = F u := fun u => by
    simp only [hF, mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  have hg' : Integrable fun u => g u * F u := hg
  have hgneg : Integrable fun u => g (-u) * F u := by
    refine (hg'.comp_neg).congr (Eventually.of_forall fun u => ?_)
    show g (-u) * F (-u) = g (-u) * F u
    rw [hFneg]
  have h1 : ∫ u, g (-u) * F u = ∫ u, g u * F u := by
    rw [← integral_neg_eq_self (fun u => g u * F u) volume]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      show g (-u) * F u = g (-u) * F (-u)
      rw [hFneg])
  have hFint : Integrable F := integrable_inv_neg_quadratic_add_pow hA hw (by omega)
  have hM : ∀ s r, Integrable fun u : Fin 2 → ℝ => C s r * (((u s * u r : ℝ) : ℂ) * F u) :=
    fun s r => (integrable_mul_mul_inv_neg_quadratic_add_pow hA hw hn s r).const_mul _
  have h2 : (∫ u, g u * F u) + ∫ u, g (-u) * F u =
      2 * (a * (∫ u, F u) + ∑ s, ∑ r, C s r * ∫ u, ((u s * u r : ℝ) : ℂ) * F u) := by
    rw [← integral_add hg' hgneg]
    have hpt : ∀ u, g u * F u + g (-u) * F u =
        2 * (a * F u + ∑ s, ∑ r, C s r * (((u s * u r : ℝ) : ℂ) * F u)) := fun u => by
      rw [← add_mul, heven u, mul_assoc, add_mul, Finset.sum_mul]
      congr 2
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by ring
    simp only [hpt]
    rw [integral_const_mul, integral_add (hFint.const_mul a)
      (integrable_finsetSum _ fun s _ => integrable_finsetSum _ fun r _ => hM s r),
      integral_const_mul, integral_finsetSum _ fun s _ => integrable_finsetSum _ fun r _ => hM s r]
    congr 2
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_finsetSum _ fun r _ => hM s r]
    exact Finset.sum_congr rfl fun r _ => integral_const_mul _ _
  rw [h1] at h2
  have h3 : ∫ u, g u * F u =
      a * (∫ u, F u) + ∑ s, ∑ r, C s r * ∫ u, ((u s * u r : ℝ) : ℂ) * F u := by
    linear_combination (1 / 2 : ℂ) * h2
  rw [h3]
  simp only [hF]
  rw [integral_inv_neg_quadratic_add_pow hA hw (by omega)]
  simp only [integral_mul_mul_inv_neg_quadratic_add_pow hA hw hn]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **The spatial integral of a weight with quadratic even part.** If `h(y) + h(-y) =
2 (a + ∑ D_{sc,rd} y_{sc} y_{rd})` and `h (yᵀAy + w)^{-k}` is integrable (`k ≥ 5`), then
`∫ h (yᵀAy + w)^{-k} = a · π³/((k-1)(k-2)(k-3)) U^{-3/2} w^{3-k} +
(∑ D_{sc,rc} (A⁻¹)ₛᵣ) · π³/(2(k-1)(k-2)(k-3)(k-4)) U^{-3/2} w^{4-k}`. -/
theorem integral_mul_inv_quadForm_add_pow_of_even {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A.PosDef) {w : ℂ} (hw : w.im < 0) {k : ℕ} (hk : 5 ≤ k)
    {h : (Fin 2 → Fin 3 → ℝ) → ℂ}
    (hh : Integrable fun y : Fin 2 → Fin 3 → ℝ => h y * ((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹)
    (a : ℂ) (D : Fin 2 → Fin 3 → Fin 2 → Fin 3 → ℂ)
    (heven : ∀ y, h y + h (-y) =
      2 * (a + ∑ s, ∑ c, ∑ r, ∑ d, D s c r d * ((y s c * y r d : ℝ) : ℂ))) :
    ∫ y : Fin 2 → Fin 3 → ℝ, h y * ((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹ =
      a * ((π : ℂ) ^ 3 * (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3))⁻¹ *
          ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * (w ^ (k - 3))⁻¹) +
        (∑ s, ∑ c, ∑ r, D s c r c * (A⁻¹ s r : ℂ)) * ((π : ℂ) ^ 3 *
          (2 * (((k : ℂ) - 1) * ((k : ℂ) - 2) * ((k : ℂ) - 3) * ((k : ℂ) - 4)))⁻¹ *
          ((Real.sqrt A.det ^ 3 : ℝ) : ℂ)⁻¹ * (w ^ (k - 4))⁻¹) := by
  set F : (Fin 2 → Fin 3 → ℝ) → ℂ := fun y => ((((quadForm A y : ℝ) : ℂ) + w) ^ k)⁻¹ with hF
  have hqneg : ∀ y, quadForm A (-y) = quadForm A y := fun y => by
    simp only [Spatial.quadForm_eq_sum, Pi.neg_apply, neg_mul_neg]
  have hFneg : ∀ y, F (-y) = F y := fun y => by simp only [hF, hqneg]
  have hh' : Integrable fun y => h y * F y := hh
  have hhneg : Integrable fun y => h (-y) * F y := by
    refine (hh'.comp_neg).congr (Eventually.of_forall fun y => ?_)
    show h (-y) * F (-y) = h (-y) * F y
    rw [hFneg]
  have h1 : ∫ y, h (-y) * F y = ∫ y, h y * F y := by
    rw [← integral_neg_eq_self (fun y => h y * F y) volume]
    exact integral_congr_ae (Eventually.of_forall fun y => by
      show h (-y) * F y = h (-y) * F (-y)
      rw [hFneg])
  have hFint : Integrable F :=
    Spatial.integrable_inv_quadForm_add_pow hA (mem_slitPlane_iff.mpr (Or.inr hw.ne)) (by omega)
  have hM : ∀ s c r d, Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      D s c r d * (((y s c * y r d : ℝ) : ℂ) * F y) :=
    fun s c r d => (integrable_mul_mul_inv_quadForm_add_pow hA hw hk s c r d).const_mul _
  have hM1 : ∀ s c r, Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      ∑ d, D s c r d * (((y s c * y r d : ℝ) : ℂ) * F y) :=
    fun s c r => integrable_finsetSum _ fun d _ => hM s c r d
  have hM2 : ∀ s c, Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      ∑ r, ∑ d, D s c r d * (((y s c * y r d : ℝ) : ℂ) * F y) :=
    fun s c => integrable_finsetSum _ fun r _ => hM1 s c r
  have hM3 : ∀ s, Integrable fun y : Fin 2 → Fin 3 → ℝ =>
      ∑ c, ∑ r, ∑ d, D s c r d * (((y s c * y r d : ℝ) : ℂ) * F y) :=
    fun s => integrable_finsetSum _ fun c _ => hM2 s c
  have h2 : (∫ y, h y * F y) + ∫ y, h (-y) * F y =
      2 * (a * (∫ y, F y) + ∑ s, ∑ c, ∑ r, ∑ d,
        D s c r d * ∫ y, ((y s c * y r d : ℝ) : ℂ) * F y) := by
    rw [← integral_add hh' hhneg]
    have hpt : ∀ y, h y * F y + h (-y) * F y =
        2 * (a * F y + ∑ s, ∑ c, ∑ r, ∑ d, D s c r d * (((y s c * y r d : ℝ) : ℂ) * F y)) :=
      fun y => by
      rw [← add_mul, heven y, mul_assoc, add_mul, Finset.sum_mul]
      congr 2
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp only [hpt]
    rw [integral_const_mul, integral_add (hFint.const_mul a)
      (integrable_finsetSum _ fun s _ => hM3 s), integral_const_mul,
      integral_finsetSum _ fun s _ => hM3 s]
    congr 2
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [integral_finsetSum _ fun c _ => hM2 s c]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ fun r _ => hM1 s c r]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_finsetSum _ fun d _ => hM s c r d]
    exact Finset.sum_congr rfl fun d _ => integral_const_mul _ _
  rw [h1] at h2
  have h3 : ∫ y, h y * F y = a * (∫ y, F y) + ∑ s, ∑ c, ∑ r, ∑ d,
      D s c r d * ∫ y, ((y s c * y r d : ℝ) : ℂ) * F y := by
    linear_combination (1 / 2 : ℂ) * h2
  rw [h3]
  simp only [hF]
  rw [Spatial.integral_inv_quadForm_add_pow_of_im_neg hA hw (by omega)]
  simp only [integral_mul_mul_inv_quadForm_add_pow hA hw hk, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

end QED.Integration.TwoLoop

end
