/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2ParamPiece
public import QED.TwoLoop.JointIntegralInvariance

/-!
# Symanzik data under a change of routing

Helper level for the Phase 5 Stage 2 goal (WI₂) `QED.Graded.d₁_eq_d₂_one` (decision D-57),
step A6. An integer unimodular affine change of loop momenta `ℓ ↦ M ℓ + a` (`loopAff`) turns
parametric data `(α, q)` into the rerouted data `(α M, q + α a)` (`rrAlpha`, `rrMom`) with the
same line momenta (`lineMomentum_rr`, `lineDenom_rr`). The Symanzik matrix becomes `Mᵀ A M`
(`symanzikMatrix_rr`), so `U` is multiplied by `(det M)² = 1` (`symanzikU_rr`), and the remainder
`V` is unchanged where `U ≠ 0` (`symanzikV_rr`): it is the value of `∑ᵢ zᵢ Dᵢ` at its critical
point, which the affine change moves but does not change. Hence a lower bound for `V` transfers to
the rerouted data (`symanzikV_rr_ge`).

The proof for one column (`remainder_rr`) is the identity
`(Mᵀ x)ᵀ (Mᵀ A M)⁻¹ (Mᵀ x) = xᵀ A⁻¹ x` with `x = β + A b`, expanded by the symmetry of `A`
(`dotProduct_inv_reroute`).
-/

@[expose] public section

open Matrix

namespace QED.GradedProof.WI2

open QED.Integration.TwoLoop

variable {m : ℕ}

/-- The affine change of loop momenta `ℓ ↦ M ℓ + a`. -/
def loopAff (M : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → Fin 4 → ℝ) (ℓ : Fin 2 → Fin 4 → ℝ) :
    Fin 2 → Fin 4 → ℝ :=
  (fun s => ∑ r, M s r • ℓ r) + a

/-- The rerouted loop matrix `(α M)ᵢᵣ = ∑ₛ αᵢₛ Mₛᵣ`. -/
def rrAlpha (α : Fin (m + 1) → Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    Fin (m + 1) → Fin 2 → ℝ :=
  fun i r => ∑ s, α i s * (M s r : ℝ)

/-- The rerouted external line momenta `qᵢ + ∑ₛ αᵢₛ aₛ`. -/
def rrMom (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → Fin 4 → ℝ)
    (a : Fin 2 → Fin 4 → ℝ) : Fin (m + 1) → Fin 4 → ℝ :=
  fun i => q i + ∑ s, α i s • a s

theorem lineMomentum_rr (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → Fin 4 → ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → Fin 4 → ℝ) (i : Fin (m + 1))
    (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineMomentum (rrAlpha α M) (rrMom α q a) i ℓ = lineMomentum α q i (loopAff M a ℓ) := by
  funext μ
  simp only [lineMomentum, rrAlpha, rrMom, loopAff, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul,
    smul_eq_mul, Fin.sum_univ_two, Pi.mul_apply, Pi.intCast_apply]
  ring

theorem lineDenom_rr (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → Fin 4 → ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (a : Fin 2 → Fin 4 → ℝ) (Ms : Fin (m + 1) → ℝ) (ε : ℝ)
    (i : Fin (m + 1)) (ℓ : Fin 2 → Fin 4 → ℝ) :
    lineDenom (rrAlpha α M) (rrMom α q a) Ms ε i ℓ = lineDenom α q Ms ε i (loopAff M a ℓ) := by
  simp only [lineDenom, lineMomentum_rr]

/-- The joint energy-first integral is invariant under `loopAff` for unimodular `M`. -/
theorem jointEnergyFirstIntegral_loopAff (F : (Fin 2 → Fin 4 → ℝ) → ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : IsUnit M.det) (a : Fin 2 → Fin 4 → ℝ) :
    QED.TwoLoop.jointEnergyFirstIntegral 2 (fun ℓ => F (loopAff M a ℓ)) =
      QED.TwoLoop.jointEnergyFirstIntegral 2 F :=
  QED.TwoLoop.JointIntegralInvariance.jointEnergyFirstIntegral_comp_matrix_add 2 F M hM a

/-- The real matrix of an integer matrix. -/
abbrev realMat (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  M.map (Int.cast : ℤ → ℝ)

theorem isUnit_det_realMat {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : IsUnit M.det) :
    IsUnit (realMat M).det := by
  have h := (Int.castRingHom ℝ).map_det M
  have h' : (Int.castRingHom ℝ).mapMatrix M = realMat M := rfl
  rw [h'] at h
  rw [← h]
  exact hM.map _

theorem symanzikMatrix_rr (α : Fin (m + 1) → Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (z : Fin (m + 1) → ℝ) :
    symanzikMatrix (rrAlpha α M) z = (realMat M)ᵀ * symanzikMatrix α z * realMat M := by
  ext s t
  simp only [symanzikMatrix, rrAlpha, mul_apply, transpose_apply, map_apply, of_apply,
    Fin.sum_univ_two, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem symanzikU_rr (α : Fin (m + 1) → Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (z : Fin (m + 1) → ℝ) :
    symanzikU (rrAlpha α M) z = (realMat M).det ^ 2 * symanzikU α z := by
  rw [symanzikU, symanzikMatrix_rr, det_mul, det_mul, det_transpose, symanzikU]
  ring

/-- **The quadratic form of the inverse under a change of basis.** -/
theorem dotProduct_inv_reroute (A R : Matrix (Fin 2) (Fin 2) ℝ) (hA : Aᵀ = A)
    (hdet : IsUnit A.det) (hR : IsUnit R.det) (β b : Fin 2 → ℝ) :
    (Rᵀ *ᵥ (β + A *ᵥ b)) ⬝ᵥ (Rᵀ * A * R)⁻¹ *ᵥ (Rᵀ *ᵥ (β + A *ᵥ b)) =
      β ⬝ᵥ A⁻¹ *ᵥ β + 2 * (β ⬝ᵥ b) + b ⬝ᵥ A *ᵥ b := by
  have hRt : IsUnit Rᵀ.det := by rwa [det_transpose]
  set x := β + A *ᵥ b
  have hx : (Rᵀ *ᵥ x) ⬝ᵥ (Rᵀ * A * R)⁻¹ *ᵥ (Rᵀ *ᵥ x) = x ⬝ᵥ A⁻¹ *ᵥ x := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc R⁻¹,
      Matrix.mul_assoc A⁻¹, nonsing_inv_mul _ hRt, Matrix.mul_one, dotProduct_mulVec,
      mulVec_transpose, vecMul_vecMul, ← Matrix.mul_assoc, mul_nonsing_inv _ hR, Matrix.one_mul,
      ← dotProduct_mulVec]
  rw [hx]
  have hAA : A⁻¹ *ᵥ (A *ᵥ b) = b := by rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  have hsym : (A *ᵥ b) ⬝ᵥ A⁻¹ *ᵥ β = b ⬝ᵥ β := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hA, mulVec_mulVec,
      mul_nonsing_inv _ hdet, one_mulVec, dotProduct_comm]
  simp only [x, mulVec_add, add_dotProduct, dotProduct_add, hAA, hsym]
  rw [dotProduct_comm b β, dotProduct_comm (A *ᵥ b) b]
  ring

theorem coefVec_rr (α : Fin (m + 1) → Fin 2 → ℝ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (z q : Fin (m + 1) → ℝ) (b : Fin 2 → ℝ) :
    coefVec (rrAlpha α M) z (fun i => q i + ∑ s, α i s * b s) =
      (realMat M)ᵀ *ᵥ (coefVec α z q + symanzikMatrix α z *ᵥ b) := by
  funext r
  simp only [coefVec, rrAlpha, mulVec, dotProduct, transpose_apply, map_apply, Pi.add_apply,
    symanzikMatrix, of_apply, Fin.sum_univ_two, Finset.mul_sum, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The remainder of one column is invariant under rerouting** where `U ≠ 0`. -/
theorem remainder_rr (α : Fin (m + 1) → Fin 2 → ℝ) {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hM : IsUnit M.det) {z : Fin (m + 1) → ℝ} (hU : symanzikU α z ≠ 0)
    (q : Fin (m + 1) → ℝ) (b : Fin 2 → ℝ) :
    remainder (rrAlpha α M) z (fun i => q i + ∑ s, α i s * b s) = remainder α z q := by
  have hsq := sum_mul_sq_eq α z q b
  have hA : (symanzikMatrix α z)ᵀ = symanzikMatrix α z := symanzikMatrix_isSymm α z
  have hdet : IsUnit (symanzikMatrix α z).det := isUnit_iff_ne_zero.mpr hU
  rw [remainder, remainder, coefVec_rr, symanzikMatrix_rr,
    dotProduct_inv_reroute _ _ hA hdet (isUnit_det_realMat hM)]
  have e : ∑ i, z i * (q i + ∑ s, α i s * b s) ^ 2 =
      ∑ i, z i * (∑ s, α i s * b s + q i) ^ 2 :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [e, hsq]
  ring

/-- **`V` is invariant under rerouting** where `U ≠ 0`. -/
theorem symanzikV_rr (α : Fin (m + 1) → Fin 2 → ℝ) (q : Fin (m + 1) → Fin 4 → ℝ)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : IsUnit M.det) (a : Fin 2 → Fin 4 → ℝ)
    (Ms : Fin (m + 1) → ℝ) {z : Fin (m + 1) → ℝ} (hU : symanzikU α z ≠ 0) :
    symanzikV (rrAlpha α M) (rrMom α q a) Ms z = symanzikV α q Ms z := by
  have hc : ∀ μ : Fin 4, (fun i => rrMom α q a i μ) =
      fun i => q i μ + ∑ s, α i s * (fun s => a s μ) s := fun μ => by
    funext i
    simp only [rrMom, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [symanzikV_eq, symanzikV_eq, hc 0, remainder_rr α hM hU]
  simp only [hc, remainder_rr α hM hU]

/-- **A lower bound for `V` transfers to the rerouted data.** -/
theorem symanzikV_rr_ge {α : Fin (m + 1) → Fin 2 → ℝ} {q : Fin (m + 1) → Fin 4 → ℝ}
    {Ms : Fin (m + 1) → ℝ} {c : ℝ}
    (h : ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU α z ≠ 0 →
      c ≤ symanzikV α q Ms z)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : IsUnit M.det) (a : Fin 2 → Fin 4 → ℝ) :
    ∀ z : Fin (m + 1) → ℝ, (∀ i, 0 ≤ z i) → ∑ i, z i = 1 → symanzikU (rrAlpha α M) z ≠ 0 →
      c ≤ symanzikV (rrAlpha α M) (rrMom α q a) Ms z := by
  intro z hz hz1 hU
  rw [symanzikU_rr] at hU
  have hU' : symanzikU α z ≠ 0 := right_ne_zero_of_mul hU
  rw [symanzikV_rr α q hM a Ms hU']
  exact h z hz hz1 hU'

end QED.GradedProof.WI2

end
