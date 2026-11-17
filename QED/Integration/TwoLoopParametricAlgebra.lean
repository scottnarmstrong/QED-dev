/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Algebra.Dot
public import QED.Integration.FeynmanParameterGeneral
public import QED.Integration.SpatialIntegralSix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The two-loop parametric representation: data and algebra

Algebraic part of the scalar two-loop parametric representation (assembly of obligation O2-10,
`docs/TWO-LOOP-DERIVATION.md`, section 4.4). For `N = m + 1` propagators with line momenta
`kᵢ(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ` affine in the two loop momenta `ℓ₁, ℓ₂ ∈ ℝ⁴`, masses `Mᵢ` and `ε > 0`,
the Minkowski denominators are `Dᵢ(ℓ) = kᵢ·kᵢ + Mᵢ² - iε` in the mostly-plus metric
(`kᵢ·kᵢ = -(kᵢ⁰)² + |k⃗ᵢ|²`), the convention of the frozen one-loop propagators
`QED.OneLoop.electronPropagator` and `QED.OneLoop.photonPropagator`.

For Feynman parameters `z` (barycentric, `∑ᵢ zᵢ = 1`) the combined denominator is
`∑ᵢ zᵢ Dᵢ = -(t + τ)ᵀ A (t + τ) + (v + σ)ᵀ A (v + σ) + V - iε` (`sum_mul_lineDenom_eq`), with
`t = (ℓ₁⁰, ℓ₂⁰)`, `v = (ℓ⃗₁, ℓ⃗₂)`, the Symanzik matrix `A(z)ₛₜ = ∑ᵢ zᵢ αᵢₛ αᵢₜ` (its determinant
is the first Symanzik polynomial `U`), the shifts `τ = A⁻¹ b⁰`, `σ = A⁻¹ b⃗` and the remainder
`V(z) = ∑ᵢ zᵢ (Mᵢ² + pᵢ·pᵢ) - ∑ₛₜ (A⁻¹)ₛₜ Bₛ·Bₜ`, `Bₛ = ∑ᵢ zᵢ αᵢₛ pᵢ` (Minkowski products).

## Main statements

* `lineDenom`, `symanzikMatrix`, `symanzikU`, `symanzikVector`, `symanzikV`: the data.
* `sum_mul_lineDenom_eq`: completing the square in the energies and in the spatial momenta.
* `abs_symanzikV_le`, `abs_re_shifted_le`: the remainders are bounded on the simplex, uniformly
  in the Feynman parameters (even where `U → 0`).
* `posDef_symanzikMatrix`: `A(z)` is positive definite when every `zᵢ > 0` and two of the
  `αᵢ` are linearly independent.
* `ae_simplexPoint_ne_zero`: almost every point of `ℝᵐ` has all barycentric coordinates nonzero,
  so the boundary of the simplex is null.
* `sq_mul_add_one_sq_le`: the uniform lower bound `δ (u + 1)² ≤ (u - R)² + ε²`.
-/

@[expose] public section

open Complex MeasureTheory Set Matrix
open scoped Real

namespace QED.Integration.TwoLoop

open QED.Integration.Feynman (simplexSet simplexPoint simplexComb)
open QED.Integration.Spatial (quadForm)

variable {m : ℕ}

/-! ### The data -/

/-- The momentum `kᵢ(ℓ) = ∑ₛ αᵢₛ ℓₛ + pᵢ` of line `i`. -/
def lineMomentum (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ) (i : Fin (m + 1))
    (ℓ : Fin 2 → Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => ∑ s, α i s * ℓ s μ + p i μ

/-- The Minkowski denominator `Dᵢ(ℓ) = kᵢ·kᵢ + Mᵢ² - iε` of line `i` (mostly-plus metric). -/
noncomputable def lineDenom (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (ε : ℝ) (i : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ((Minkowski.dot (lineMomentum α p i ℓ) (lineMomentum α p i ℓ) + M i ^ 2 : ℝ) : ℂ) -
    (ε : ℂ) * I

/-- The Symanzik matrix `A(z)ₛₜ = ∑ᵢ zᵢ αᵢₛ αᵢₜ`. -/
def symanzikMatrix (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun s t => ∑ i, z i * α i s * α i t

/-- The first Symanzik polynomial `U(z) = det A(z)`. -/
def symanzikU (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) : ℝ :=
  (symanzikMatrix α z).det

/-- The four-vectors `Bₛ(z) = ∑ᵢ zᵢ αᵢₛ pᵢ`. -/
def symanzikVector (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) : Fin 2 → Fin 4 → ℝ :=
  fun s μ => ∑ i, z i * α i s * p i μ

/-- The remainder `V(z) = ∑ᵢ zᵢ (Mᵢ² + pᵢ·pᵢ) - ∑ₛₜ (A(z)⁻¹)ₛₜ Bₛ(z)·Bₜ(z)` (Minkowski
products); it is `F/U` for the second Symanzik polynomial `F`. -/
noncomputable def symanzikV (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i, z i * (M i ^ 2 + Minkowski.dot (p i) (p i)) -
    ∑ s, ∑ t, (symanzikMatrix α z)⁻¹ s t *
      Minkowski.dot (symanzikVector α p z s) (symanzikVector α p z t)

/-- The loop momenta with energies `t` and spatial components `v`, as in the joint energy-first
integral. -/
def loopMomenta (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  fun s => (Fin.cons (t s) (v s) : Fin 4 → ℝ)

/-- The coefficient vector `βₛ = ∑ᵢ zᵢ αᵢₛ qᵢ` of a column `q`. -/
def coefVec (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) (q : Fin (m + 1) → ℝ) :
    Fin 2 → ℝ :=
  fun s => ∑ i, z i * α i s * q i

/-- The remainder `∑ᵢ zᵢ qᵢ² - βᵀ A⁻¹ β` of completing the square for one column `q`. -/
noncomputable def remainder (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ)
    (q : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i, z i * q i ^ 2 - coefVec α z q ⬝ᵥ (symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q

/-- The energy shift `τ = A⁻¹ b⁰`. -/
noncomputable def energyShift (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) : Fin 2 → ℝ :=
  (symanzikMatrix α z)⁻¹ *ᵥ coefVec α z (fun i => p i 0)

/-- The spatial shift `σ = A⁻¹ b⃗`, componentwise. -/
noncomputable def spatialShift (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (z : Fin (m + 1) → ℝ) : Fin 2 → Fin 3 → ℝ :=
  fun s c => ((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z (fun i => p i c.succ)) s

/-! ### The barycentric point and the quadratic form -/

/-- `simplexPoint x = (x, 1 - ∑ᵢ xᵢ)`, recovered from the public API of the Feynman file. -/
theorem simplexPoint_eq_snoc (x : Fin m → ℝ) :
    simplexPoint x = Fin.snoc x (1 - ∑ i, x i) := by
  funext i
  have h := Feynman.simplexComb_im (Pi.single i I) x
  rw [Feynman.simplexComb_eq_sum_simplexPoint] at h
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, mul_I_im, ofReal_re] at h
  rw [h]
  induction i using Fin.lastCases with
  | last => simp [Fin.castSucc_ne_last]
  | cast j =>
    simp only [Fin.snoc_castSucc]
    simp [apply_ite Complex.im, (Fin.castSucc_ne_last j).symm]

theorem simplexPoint_castSucc (x : Fin m → ℝ) (j : Fin m) : simplexPoint x j.castSucc = x j := by
  simp [simplexPoint_eq_snoc]

theorem simplexPoint_last (x : Fin m → ℝ) : simplexPoint x (Fin.last m) = 1 - ∑ i, x i := by
  simp [simplexPoint_eq_snoc]

theorem sum_simplexPoint (x : Fin m → ℝ) : ∑ i, simplexPoint x i = 1 := by
  simp [simplexPoint_eq_snoc, Fin.sum_univ_castSucc]

theorem continuous_simplexPoint (i : Fin (m + 1)) : Continuous fun x : Fin m → ℝ => simplexPoint x i := by
  induction i using Fin.lastCases with
  | last => simp only [simplexPoint_last]; fun_prop
  | cast j => simp only [simplexPoint_castSucc]; fun_prop

/-- `quadForm A v = ∑_c (v_{·c})ᵀ A v_{·c}`, recovered from `quadForm_eq_sum`. -/
theorem quadForm_eq_sum_dotProduct (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    quadForm A v = ∑ c : Fin 3, (fun s => v s c) ⬝ᵥ A *ᵥ (fun s => v s c) := by
  rw [Spatial.quadForm_eq_sum]
  simp only [dotProduct, mulVec, Fin.sum_univ_two, Fin.sum_univ_three]
  ring

/-! ### Completing the square -/

theorem minkowski_dot_self (k : Fin 4 → ℝ) :
    Minkowski.dot k k = -k 0 ^ 2 + ∑ c : Fin 3, k c.succ ^ 2 := by
  simp only [Minkowski.dot, Minkowski.metric, Fin.sum_univ_four, Fin.sum_univ_three]
  simp
  ring

theorem minkowski_dot_eq (k l : Fin 4 → ℝ) :
    Minkowski.dot k l = -(k 0 * l 0) + ∑ c : Fin 3, k c.succ * l c.succ := by
  simp only [Minkowski.dot, Minkowski.metric, Fin.sum_univ_four, Fin.sum_univ_three]
  simp
  ring

theorem symanzikMatrix_isSymm (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ) :
    (symanzikMatrix α z).IsSymm := by
  ext s t
  simp only [transpose_apply, symanzikMatrix, of_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `∑ᵢ zᵢ (αᵢ·y + qᵢ)² = yᵀ A y + 2 β·y + ∑ᵢ zᵢ qᵢ²`. -/
theorem sum_mul_sq_eq (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ)
    (q : Fin (m + 1) → ℝ) (y : Fin 2 → ℝ) :
    ∑ i, z i * (∑ s, α i s * y s + q i) ^ 2 =
      y ⬝ᵥ symanzikMatrix α z *ᵥ y + 2 * (coefVec α z q ⬝ᵥ y) + ∑ i, z i * q i ^ 2 := by
  simp only [dotProduct, mulVec, symanzikMatrix, coefVec, of_apply, Fin.sum_univ_two,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The quadratic form of `A(z)` is `∑ᵢ zᵢ (αᵢ·y)²`. -/
theorem dotProduct_symanzikMatrix_mulVec (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ)
    (y : Fin 2 → ℝ) :
    y ⬝ᵥ symanzikMatrix α z *ᵥ y = ∑ i, z i * (∑ s, α i s * y s) ^ 2 := by
  have := sum_mul_sq_eq α z 0 y
  simp only [Pi.zero_apply, add_zero] at this
  rw [this]
  simp [coefVec]

/-- Completing the square: `(y + A⁻¹β)ᵀ A (y + A⁻¹β) = yᵀAy + 2 β·y + βᵀA⁻¹β`. -/
theorem dotProduct_mulVec_add_inv {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.IsSymm)
    (hdet : IsUnit A.det) (y β : Fin 2 → ℝ) :
    (y + A⁻¹ *ᵥ β) ⬝ᵥ A *ᵥ (y + A⁻¹ *ᵥ β) = y ⬝ᵥ A *ᵥ y + 2 * (β ⬝ᵥ y) + β ⬝ᵥ A⁻¹ *ᵥ β := by
  have h1 : A *ᵥ (A⁻¹ *ᵥ β) = β := by rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have h2 : (A⁻¹ *ᵥ β) ⬝ᵥ A *ᵥ y = β ⬝ᵥ y := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq, h1]
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, h1, h2,
    dotProduct_comm (A⁻¹ *ᵥ β) β, dotProduct_comm y β]
  ring

/-- `∑ᵢ zᵢ (αᵢ·y + qᵢ)² = (y + A⁻¹β)ᵀ A (y + A⁻¹β) + (∑ᵢ zᵢ qᵢ² - βᵀA⁻¹β)`. -/
theorem sum_mul_sq_eq_shift (α : Fin (m + 1) → Fin 2 → ℝ) (z : Fin (m + 1) → ℝ)
    (hdet : symanzikU α z ≠ 0) (q : Fin (m + 1) → ℝ) (y : Fin 2 → ℝ) :
    ∑ i, z i * (∑ s, α i s * y s + q i) ^ 2 =
      (y + (symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q) ⬝ᵥ symanzikMatrix α z *ᵥ
          (y + (symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q) + remainder α z q := by
  rw [dotProduct_mulVec_add_inv (symanzikMatrix_isSymm α z) (isUnit_iff_ne_zero.mpr hdet),
    sum_mul_sq_eq, remainder]
  ring

theorem remainder_nonneg (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hdet : symanzikU α z ≠ 0) (q : Fin (m + 1) → ℝ) :
    0 ≤ remainder α z q := by
  have h := sum_mul_sq_eq_shift α z hdet q (-((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q))
  rw [neg_add_cancel, zero_dotProduct, zero_add] at h
  rw [← h]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (sq_nonneg _)

theorem remainder_le (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 ≤ z i) (hdet : symanzikU α z ≠ 0) (q : Fin (m + 1) → ℝ) :
    remainder α z q ≤ ∑ i, z i * q i ^ 2 := by
  have h := sum_mul_sq_eq_shift α z hdet q 0
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at h
  have hq : 0 ≤ ((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q) ⬝ᵥ
      symanzikMatrix α z *ᵥ ((symanzikMatrix α z)⁻¹ *ᵥ coefVec α z q) := by
    rw [dotProduct_symanzikMatrix_mulVec]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (sq_nonneg _)
  linarith

/-- The remainder in components: `V = ∑ᵢ zᵢ Mᵢ² - R(p⁰) + ∑_c R(p^c)`. -/
theorem symanzikV_eq (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (z : Fin (m + 1) → ℝ) :
    symanzikV α p M z = ∑ i, z i * M i ^ 2 - remainder α z (fun i => p i 0) +
      ∑ c : Fin 3, remainder α z (fun i => p i c.succ) := by
  have h1 : ∑ i, z i * (M i ^ 2 + Minkowski.dot (p i) (p i)) =
      ∑ i, z i * M i ^ 2 - ∑ i, z i * p i 0 ^ 2 + ∑ c : Fin 3, ∑ i, z i * p i c.succ ^ 2 := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))), ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [minkowski_dot_self]
    simp only [Fin.sum_univ_three]
    ring
  rw [symanzikV, h1]
  simp only [remainder, minkowski_dot_eq, dotProduct, mulVec, Fin.sum_univ_two,
    Fin.sum_univ_three, symanzikVector, coefVec]
  ring

/-- **Completing the square.** For barycentric `z` with `U(z) ≠ 0`, the combined denominator is
`∑ᵢ zᵢ Dᵢ = -(t + τ)ᵀ A (t + τ) + ((v + σ)ᵀ A (v + σ) + V - iε)`. -/
theorem sum_mul_lineDenom_eq (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (ε : ℝ) {z : Fin (m + 1) → ℝ} (hz1 : ∑ i, z i = 1)
    (hdet : symanzikU α z ≠ 0) (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    ∑ i, (z i : ℂ) * lineDenom α p M ε i (loopMomenta t v) =
      -(((t + energyShift α p z) ⬝ᵥ symanzikMatrix α z *ᵥ (t + energyShift α p z) : ℝ) : ℂ) +
        (((quadForm (symanzikMatrix α z) (v + spatialShift α p z) : ℝ) : ℂ) +
          (((symanzikV α p M z : ℝ) : ℂ) - (ε : ℂ) * I)) := by
  -- the real part
  have hk0 : ∀ i, lineMomentum α p i (loopMomenta t v) 0 = ∑ s, α i s * t s + p i 0 := by
    intro i; simp [lineMomentum, loopMomenta]
  have hkc : ∀ i (c : Fin 3), lineMomentum α p i (loopMomenta t v) c.succ =
      ∑ s, α i s * v s c + p i c.succ := by
    intro i c; simp [lineMomentum, loopMomenta]
  have hreal : ∑ i, z i * (Minkowski.dot (lineMomentum α p i (loopMomenta t v))
      (lineMomentum α p i (loopMomenta t v)) + M i ^ 2) =
      -((t + energyShift α p z) ⬝ᵥ symanzikMatrix α z *ᵥ (t + energyShift α p z)) +
        (quadForm (symanzikMatrix α z) (v + spatialShift α p z) + symanzikV α p M z) := by
    have he := sum_mul_sq_eq_shift α z hdet (fun i => p i 0) t
    have hs : ∀ c : Fin 3, ∑ i, z i * (∑ s, α i s * v s c + p i c.succ) ^ 2 =
        (fun s => (v + spatialShift α p z) s c) ⬝ᵥ symanzikMatrix α z *ᵥ
          (fun s => (v + spatialShift α p z) s c) + remainder α z (fun i => p i c.succ) := by
      intro c
      exact sum_mul_sq_eq_shift α z hdet (fun i => p i c.succ) (fun s => v s c)
    have hsum : ∑ i, z i * (Minkowski.dot (lineMomentum α p i (loopMomenta t v))
        (lineMomentum α p i (loopMomenta t v)) + M i ^ 2) =
        -∑ i, z i * (∑ s, α i s * t s + p i 0) ^ 2 +
          ∑ c : Fin 3, ∑ i, z i * (∑ s, α i s * v s c + p i c.succ) ^ 2 +
            ∑ i, z i * M i ^ 2 := by
      rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))), ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [minkowski_dot_self, hk0]
      simp only [hkc, Fin.sum_univ_three]
      ring
    rw [hsum, he, symanzikV_eq]
    simp only [hs, quadForm_eq_sum_dotProduct, energyShift, Finset.sum_add_distrib]
    ring
  have hz1' : ∑ i, (z i : ℂ) = 1 := by exact_mod_cast hz1
  have hc : ∑ i, (z i : ℂ) * lineDenom α p M ε i (loopMomenta t v) =
      ((∑ i, z i * (Minkowski.dot (lineMomentum α p i (loopMomenta t v))
        (lineMomentum α p i (loopMomenta t v)) + M i ^ 2) : ℝ) : ℂ) -
          (∑ i, (z i : ℂ)) * ((ε : ℂ) * I) := by
    simp only [lineDenom, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    push_cast
    rfl
  rw [hc, hreal, hz1']
  push_cast
  ring

/-- The denominators at the loop momenta `(t, v)`, explicitly. -/
theorem lineDenom_loopMomenta (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) (ε : ℝ) (i : Fin (m + 1)) (t : Fin 2 → ℝ) (v : Fin 2 → Fin 3 → ℝ) :
    lineDenom α p M ε i (loopMomenta t v) =
      ((-(∑ s, α i s * t s + p i 0) ^ 2 + ∑ c : Fin 3, (∑ s, α i s * v s c + p i c.succ) ^ 2 +
        M i ^ 2 : ℝ) : ℂ) - (ε : ℂ) * I := by
  have hk0 : lineMomentum α p i (loopMomenta t v) 0 = ∑ s, α i s * t s + p i 0 := by
    simp [lineMomentum, loopMomenta]
  have hkc : ∀ c : Fin 3, lineMomentum α p i (loopMomenta t v) c.succ =
      ∑ s, α i s * v s c + p i c.succ := by
    intro c; simp [lineMomentum, loopMomenta]
  rw [lineDenom, minkowski_dot_self, hk0]
  simp only [hkc]

/-! ### Bounds on the remainders -/

/-- On the simplex, `|V(z)| ≤ ∑ᵢ (Mᵢ² + ∑_μ (pᵢ^μ)²)`. -/
theorem abs_symanzikV_le (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) {z : Fin (m + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hdet : symanzikU α z ≠ 0) :
    |symanzikV α p M z| ≤ ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2) := by
  have hzle : ∀ i, z i ≤ 1 := fun i => by
    rw [← hz1]
    exact Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i)
  have hle : ∀ q : Fin (m + 1) → ℝ, ∑ i, z i * q i ^ 2 ≤ ∑ i, q i ^ 2 := fun q =>
    Finset.sum_le_sum fun i _ => by nlinarith [hz i, hzle i, sq_nonneg (q i)]
  have hnn : ∀ q : Fin (m + 1) → ℝ, 0 ≤ ∑ i, z i * q i ^ 2 := fun q =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (sq_nonneg _)
  have r0 := remainder_nonneg α hz hdet (fun i => p i 0)
  have r0' := remainder_le α hz hdet (fun i => p i 0)
  have rc := fun c : Fin 3 => remainder_nonneg α hz hdet (fun i => p i c.succ)
  have rc' := fun c : Fin 3 => remainder_le α hz hdet (fun i => p i c.succ)
  have hM := hle M
  have hM0 := hnn M
  have h0 := hle (fun i => p i 0)
  have hc := fun c : Fin 3 => hle (fun i => p i c.succ)
  have htot : ∑ i, (M i ^ 2 + ∑ μ, p i μ ^ 2) = ∑ i, M i ^ 2 + ∑ i, p i 0 ^ 2 +
      ∑ c : Fin 3, ∑ i, p i c.succ ^ 2 := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))), ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_succ]
    ring
  rw [symanzikV_eq, htot, abs_le]
  simp only [Fin.sum_univ_three] at *
  have := rc 0; have := rc 1; have := rc 2
  have := rc' 0; have := rc' 1; have := rc' 2
  have := hc 0; have := hc 1; have := hc 2
  constructor <;> nlinarith

/-- At fixed spatial momenta, the real part of the shifted constant is bounded on the simplex:
`|(v + σ)ᵀ A (v + σ) + V| ≤ ∑ᵢ ((pᵢ⁰)² + Mᵢ² + ∑_c (αᵢ·v_c + pᵢ^c)²)`. -/
theorem abs_re_shifted_le (α : Fin (m + 1) → Fin 2 → ℝ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (M : Fin (m + 1) → ℝ) {z : Fin (m + 1) → ℝ} (hz : ∀ i, 0 ≤ z i) (hz1 : ∑ i, z i = 1)
    (hdet : symanzikU α z ≠ 0) (v : Fin 2 → Fin 3 → ℝ) :
    |quadForm (symanzikMatrix α z) (v + spatialShift α p z) + symanzikV α p M z| ≤
      ∑ i, (p i 0 ^ 2 + M i ^ 2 + ∑ c : Fin 3, (∑ s, α i s * v s c + p i c.succ) ^ 2) := by
  have hzle : ∀ i, z i ≤ 1 := fun i => by
    rw [← hz1]
    exact Finset.single_le_sum (fun j _ => hz j) (Finset.mem_univ i)
  have hle : ∀ q : Fin (m + 1) → ℝ, ∑ i, z i * q i ^ 2 ≤ ∑ i, q i ^ 2 := fun q =>
    Finset.sum_le_sum fun i _ => by nlinarith [hz i, hzle i, sq_nonneg (q i)]
  have hnn : ∀ q : Fin (m + 1) → ℝ, 0 ≤ ∑ i, z i * q i ^ 2 := fun q =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hz i) (sq_nonneg _)
  -- `(v + σ)ᵀ A (v + σ) + ∑_c R_c = ∑_c ∑ᵢ zᵢ (αᵢ·v_c + pᵢ^c)²`
  have hs : quadForm (symanzikMatrix α z) (v + spatialShift α p z) +
      ∑ c : Fin 3, remainder α z (fun i => p i c.succ) =
      ∑ c : Fin 3, ∑ i, z i * (∑ s, α i s * v s c + p i c.succ) ^ 2 := by
    rw [quadForm_eq_sum_dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sum_mul_sq_eq_shift α z hdet (fun i => p i c.succ) (fun s => v s c)]
    rfl
  have r0 := remainder_nonneg α hz hdet (fun i => p i 0)
  have r0' := remainder_le α hz hdet (fun i => p i 0)
  have hM := hle M
  have hM0 := hnn M
  have h0 := hle (fun i => p i 0)
  have hc : ∀ c : Fin 3, ∑ i, z i * (∑ s, α i s * v s c + p i c.succ) ^ 2 ≤
      ∑ i, (∑ s, α i s * v s c + p i c.succ) ^ 2 := fun c => hle _
  have hc0 : ∀ c : Fin 3, 0 ≤ ∑ i, z i * (∑ s, α i s * v s c + p i c.succ) ^ 2 :=
    fun c => hnn _
  have htot : ∑ i, (p i 0 ^ 2 + M i ^ 2 + ∑ c : Fin 3, (∑ s, α i s * v s c + p i c.succ) ^ 2) =
      ∑ i, p i 0 ^ 2 + ∑ i, M i ^ 2 +
        ∑ c : Fin 3, ∑ i, (∑ s, α i s * v s c + p i c.succ) ^ 2 := by
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))), ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
  have hV := symanzikV_eq α p M z
  rw [htot, abs_le]
  simp only [Fin.sum_univ_three] at *
  have := hc 0; have := hc 1; have := hc 2
  have := hc0 0; have := hc0 1; have := hc0 2
  constructor <;> nlinarith

/-! ### Positive definiteness on the interior -/

theorem posDef_symanzikMatrix (α : Fin (m + 1) → Fin 2 → ℝ) {z : Fin (m + 1) → ℝ}
    (hz : ∀ i, 0 < z i) (hspan : ∃ i j, α i 0 * α j 1 - α i 1 * α j 0 ≠ 0) :
    (symanzikMatrix α z).PosDef := by
  obtain ⟨i₀, j₀, hij⟩ := hspan
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun y hy => ?_⟩
  · ext s t
    simp only [conjTranspose_apply, star_trivial, symanzikMatrix, of_apply]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [star_trivial, dotProduct_symanzikMatrix_mulVec]
    refine Finset.sum_pos' (fun i _ => mul_nonneg (hz i).le (sq_nonneg _)) ?_
    by_contra hcon
    push Not at hcon
    have hzero : ∀ i, ∑ s, α i s * y s = 0 := fun i => by
      have h1 := hcon i (Finset.mem_univ i)
      have h2 : 0 ≤ z i * (∑ s, α i s * y s) ^ 2 := mul_nonneg (hz i).le (sq_nonneg _)
      have h3 : z i * (∑ s, α i s * y s) ^ 2 = 0 := le_antisymm h1 h2
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h (hz i).ne'
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    have ha := hzero i₀
    have hb := hzero j₀
    simp only [Fin.sum_univ_two] at ha hb
    have hy0 : y 0 = 0 := by
      have : y 0 * (α i₀ 0 * α j₀ 1 - α i₀ 1 * α j₀ 0) = 0 := by linear_combination α j₀ 1 * ha - α i₀ 1 * hb
      exact (mul_eq_zero.mp this).resolve_right hij
    have hy1 : y 1 = 0 := by
      have : y 1 * (α i₀ 0 * α j₀ 1 - α i₀ 1 * α j₀ 0) = 0 := by linear_combination α i₀ 0 * hb - α j₀ 0 * ha
      exact (mul_eq_zero.mp this).resolve_right hij
    exact hy (funext fun s => by fin_cases s <;> simp [hy0, hy1])

/-! ### The boundary of the simplex is null -/

theorem volume_linearMap_eq_const {n : ℕ} {f : (Fin n → ℝ) →ₗ[ℝ] ℝ} (hf : f ≠ 0) (c : ℝ) :
    volume {x : Fin n → ℝ | f x = c} = 0 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  set q : Fin n → ℝ := (c / f x₀) • x₀
  have hq : f q = c := by simp [q, div_mul_cancel₀ _ hx₀]
  have hset : {x : Fin n → ℝ | f x = c} = (fun x => x + -q) ⁻¹' (LinearMap.ker f : Set _) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, map_add,
      map_neg, hq]
    constructor <;> intro h <;> linarith
  have hker : LinearMap.ker f ≠ ⊤ := by
    intro h
    apply hx₀
    have : x₀ ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    simpa using this
  rw [hset, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume _ hker

/-- Almost every `x ∈ ℝᵐ` (`m ≥ 1`) has all barycentric coordinates `simplexPoint x i` nonzero. -/
theorem ae_simplexPoint_ne_zero (hm : 0 < m) :
    ∀ᵐ x : Fin m → ℝ, ∀ i, simplexPoint x i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  induction i using Fin.lastCases with
  | last =>
    have hf : (∑ j : Fin m, LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) ≠ 0 := by
      intro h
      have := LinearMap.congr_fun h (fun _ => 1)
      simp at this
      omega
    convert volume_linearMap_eq_const hf 1 using 2
    ext x
    have hsum : (∑ j : Fin m, LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) x =
        ∑ i, x i := by
      rw [LinearMap.sum_apply]
      rfl
    simp only [simplexPoint_last, Set.mem_ofPred_eq, ne_eq, not_not, hsum]
    constructor <;> intro h <;> linarith
  | cast j =>
    have hf : (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) ≠ 0 := by
      intro h
      have := LinearMap.congr_fun h (Pi.single j 1)
      simp at this
    convert volume_linearMap_eq_const hf 0 using 2
    ext x
    simp [simplexPoint_castSucc]

/-! ### The uniform lower bound -/

/-- If `|R| ≤ K`, `u ≥ 0`, `δ ≤ 1/8` and `4 δ (K + 1)² ≤ ε²`, then
`δ (u + 1)² ≤ (u - R)² + ε²`. -/
theorem sq_mul_add_one_sq_le {R K u ε δ : ℝ} (hR : |R| ≤ K) (hu : 0 ≤ u) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 8) (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) :
    δ * (u + 1) ^ 2 ≤ (u - R) ^ 2 + ε ^ 2 := by
  have hK : 0 ≤ K := (abs_nonneg R).trans hR
  obtain ⟨hR1, hR2⟩ := abs_le.mp hR
  rcases le_or_gt (2 * K) u with h | h
  · have h1 : u / 2 ≤ u - R := by linarith
    have h2 : (u / 2) ^ 2 ≤ (u - R) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    have h4 : 4 ≤ 4 * (K + 1) ^ 2 := by nlinarith
    have h3 : 2 * δ ≤ ε ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left h4 hδ0]
    nlinarith [sq_nonneg (u - 1)]
  · have h1 : δ * (u + 1) ^ 2 ≤ δ * (4 * (K + 1) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hδ0
      nlinarith
    nlinarith [sq_nonneg (u - R)]

/-- A positive admissible `δ`: `δ = min (1/8) (ε² / (4 (K + 1)²))`. -/
theorem exists_delta {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2 := by
  refine ⟨min (1 / 8) (ε ^ 2 / (4 * (K + 1) ^ 2)), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  have h4 : 0 < 4 * (K + 1) ^ 2 := by positivity
  calc min (1 / 8) (ε ^ 2 / (4 * (K + 1) ^ 2)) * (4 * (K + 1) ^ 2)
      ≤ ε ^ 2 / (4 * (K + 1) ^ 2) * (4 * (K + 1) ^ 2) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) h4.le
    _ = ε ^ 2 := div_mul_cancel₀ _ h4.ne'

/-- From `c ‖b‖ ≤ ‖a‖` to `‖a^{-n}‖ ≤ c^{-n} ‖b^{-n}‖`. -/
theorem norm_inv_pow_le_of_le {a b : ℂ} {c : ℝ} (hc : 0 < c) (hb : b ≠ 0) (h : c * ‖b‖ ≤ ‖a‖)
    (n : ℕ) : ‖(a ^ n)⁻¹‖ ≤ (c ^ n)⁻¹ * ‖(b ^ n)⁻¹‖ := by
  have hb' : 0 < ‖b‖ := norm_pos_iff.mpr hb
  rw [norm_inv, norm_inv, norm_pow, norm_pow, ← mul_inv, ← mul_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h n)

/-- The energy comparison: for `u ≥ 0`, `|Re w| ≤ K`, `Im w = -ε`, admissible `δ`,
`‖(-u + w)^{-n}‖ ≤ (√δ)^{-n} ‖(-u - i)^{-n}‖`. -/
theorem norm_inv_neg_add_pow_le_uniform {u K ε δ : ℝ} {w : ℂ} (hu : 0 ≤ u) (hw : |w.re| ≤ K)
    (hwi : w.im = -ε) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8) (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2)
    (n : ℕ) :
    ‖((-(u : ℂ) + w) ^ n)⁻¹‖ ≤ (Real.sqrt δ ^ n)⁻¹ * ‖((-(u : ℂ) + -I) ^ n)⁻¹‖ := by
  refine norm_inv_pow_le_of_le (Real.sqrt_pos.mpr hδ0) ?_ ?_ n
  · intro h
    have := congrArg Complex.im h
    simp at this
  · have key := sq_mul_add_one_sq_le hw hu hδ0.le hδ hδε
    have hsq : (Real.sqrt δ * ‖-(u : ℂ) + -I‖) ^ 2 ≤ ‖-(u : ℂ) + w‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hδ0.le, Complex.sq_norm, Complex.sq_norm, normSq_apply,
        normSq_apply]
      simp only [add_re, neg_re, ofReal_re, I_re, add_im, neg_im, ofReal_im, I_im, hwi]
      nlinarith [sq_nonneg u]
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

/-- The spatial comparison: for `u ≥ 0`, `|V| ≤ K`, admissible `δ`,
`‖(u + V - iε)^{-n}‖ ≤ (√δ)^{-n} ‖(u + 1)^{-n}‖`. -/
theorem norm_inv_add_pow_le_uniform {u K ε δ V : ℝ} (hu : 0 ≤ u) (hV : |V| ≤ K)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8) (hδε : δ * (4 * (K + 1) ^ 2) ≤ ε ^ 2) (n : ℕ) :
    ‖(((u : ℂ) + ((V : ℂ) - (ε : ℂ) * I)) ^ n)⁻¹‖ ≤
      (Real.sqrt δ ^ n)⁻¹ * ‖(((u : ℂ) + 1) ^ n)⁻¹‖ := by
  refine norm_inv_pow_le_of_le (Real.sqrt_pos.mpr hδ0) ?_ ?_ n
  · exact_mod_cast (by positivity : (u + 1 : ℝ) ≠ 0)
  · have hV' : |-V| ≤ K := by rwa [abs_neg]
    have key := sq_mul_add_one_sq_le hV' hu hδ0.le hδ hδε
    have hsq : (Real.sqrt δ * ‖(u : ℂ) + 1‖) ^ 2 ≤ ‖(u : ℂ) + ((V : ℂ) - (ε : ℂ) * I)‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hδ0.le, Complex.sq_norm, Complex.sq_norm, normSq_apply,
        normSq_apply]
      simp only [add_re, sub_re, ofReal_re, one_re, add_im, sub_im, ofReal_im, one_im,
        mul_re, mul_im, I_re, I_im]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp hsq

end QED.Integration.TwoLoop

end
