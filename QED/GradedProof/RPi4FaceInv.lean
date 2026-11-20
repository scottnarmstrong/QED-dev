/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceScale
public import QED.GradedProof.RPi4CollapseSwap

/-!
# (R-Π₄) step L6d2: the parametric integrand on a face, rescaled

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d2. On the face of
loop `1` (the subgraph loop of the self-energy and of the first vertex face) the Symanzik matrix
has the form `A = [[a, ρb], [ρb, ρc]]` with `a, b, c` bounded and `Û = ac - ρb² ≥ c₀ > 0`, and the
loop-`1` component of the vector `β` is `ρ b₁`. Then `U = ρ Û`,
`A⁻¹ = Ĝ + (a/(ρÛ)) E₁` with `Ĝ = [[c, -b], [-b, 0]]/Û`, and the shift is a polynomial in
`ρ` divided by `Û`. The factor `ρ^{p+1}` of the join coordinates (`p` lines of the subgraph and
the photon) cancels the singular powers:

* `IsFaceMat`, `uHat`, `faceG`, `det_face`, **`inv_face`**;
* `shat`, `loopShift_face` (the shift in the rescaled data), `faceX`;
* **`paramAtV_face_se`** (degree `≤ 1` along loop `1`, `1 ≤ p`) and **`paramAtV_face_vtx`**
  (degree `≤ 2`, `2 ≤ p`): `ρ^{p+1} paramAtV = Û⁻² ρ^{p-d} [bracket]`, with a bracket built
  from `evalC`, `cTwoG`, `cFourG`, `cFourX` at the rescaled data, regular at `ρ = 0`.
-/

@[expose] public section

open Complex

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop QED.TwoLoop.ClassLimit
open QED.GradedProof.WI2 (ehat)

/-! ### The inverse of a face matrix -/

/-- A `2 × 2` matrix of the face form `[[a, ρb], [ρb, ρc]]`. -/
structure IsFaceMat (A : Matrix (Fin 2) (Fin 2) ℝ) (ρ a b c : ℝ) : Prop where
  h00 : A 0 0 = a
  h01 : A 0 1 = ρ * b
  h10 : A 1 0 = ρ * b
  h11 : A 1 1 = ρ * c

/-- The rescaled determinant `Û = ac - ρb²`. -/
def uHat (ρ a b c : ℝ) : ℝ := a * c - ρ * b ^ 2

/-- The bounded part `[[c, -b], [-b, 0]]/Û` of the inverse of a face matrix. -/
noncomputable def faceG (ρ a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c / uHat ρ a b c, -b / uHat ρ a b c; -b / uHat ρ a b c, 0]

variable {A : Matrix (Fin 2) (Fin 2) ℝ} {ρ a b c : ℝ}

theorem det_face (h : IsFaceMat A ρ a b c) : A.det = ρ * uHat ρ a b c := by
  rw [Matrix.det_fin_two, h.h00, h.h01, h.h10, h.h11, uHat]
  ring

/-- **The inverse of a face matrix**: `A⁻¹ = Ĝ + (a/(ρÛ)) E₁`. -/
theorem inv_face (h : IsFaceMat A ρ a b c) (hρ : ρ ≠ 0) (hu : uHat ρ a b c ≠ 0) :
    A⁻¹ = faceG ρ a b c + (a / (ρ * uHat ρ a b c)) • eS 1 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.eta_fin_two A, h.h00, h.h01, h.h10, h.h11]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [faceG, eS, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    (try simp only [uHat]) <;> ring

/-! ### The shift -/

/-- The rescaled shift: `Ŝ₀ = (c β₀ - ρ b b₁)/Û`, `Ŝ₁ = (a b₁ - b β₀)/Û`. -/
noncomputable def shat (ρ a b c : ℝ) (β₀ b₁ : Fin 4 → ℝ) : Fin 2 → Fin 4 → ℝ :=
  ![fun μ => (c * β₀ μ - ρ * b * b₁ μ) / uHat ρ a b c,
    fun μ => (a * b₁ μ - b * β₀ μ) / uHat ρ a b c]

/-- The argument `-Ŝ` of the moment functional. -/
noncomputable def faceX (ρ a b c : ℝ) (β₀ b₁ : Fin 4 → ℝ) : LoopIndex → ℂ :=
  loopComp (-shat ρ a b c β₀ b₁)

variable {m : ℕ} {α : Fin (m + 1) → Fin 2 → ℝ} {pp : Fin (m + 1) → Fin 4 → ℝ}
  {z : Fin (m + 1) → ℝ} {b₁ : Fin 4 → ℝ}

theorem loopShift_face (h : IsFaceMat (symanzikMatrix α z) ρ a b c) (hρ : ρ ≠ 0)
    (hu : uHat ρ a b c ≠ 0) (hβ : ∀ μ, symanzikVector α pp z 1 μ = ρ * b₁ μ) :
    loopShift α pp z = shat ρ a b c (symanzikVector α pp z 0) b₁ := by
  funext s μ
  rw [QED.TwoLoop.LimitCovariance.loopShift_apply, inv_face h hρ hu]
  have e : ∀ t, ∑ i, z i * α i t * pp i μ = symanzikVector α pp z t μ := fun _ => rfl
  simp only [e, Fin.sum_univ_two, hβ]
  fin_cases s <;> simp [faceG, eS, shat] <;> field_simp <;> ring

/-! ### The rescaled integrand -/

section Rescaled

variable (n : ℕ) (Q : LoopQuartic) (ρ a b c : ℝ) (β₀ b₁ : Fin 4 → ℝ) (v : ℝ)

/-- The bracket of the rescaled integrand on a self-energy face (degree `≤ 1`). -/
noncomputable def faceBrSE : ℂ :=
  ((n - 4).factorial : ℂ) * Q.evalC (faceX ρ a b c β₀ b₁) * ((v : ℂ) ^ (n - 3))⁻¹ +
    ((n - 5).factorial : ℂ) / 2 * cTwoG Q (faceG ρ a b c) (faceX ρ a b c β₀ b₁) *
      ((v : ℂ) ^ (n - 4))⁻¹ +
    ((n - 6).factorial : ℂ) / 4 * cFourG Q (faceG ρ a b c) * ((v : ℂ) ^ (n - 5))⁻¹

/-- The bracket of the rescaled integrand on a vertex face (degree `≤ 2`). -/
noncomputable def faceBrVtx : ℂ :=
  ((n - 4).factorial : ℂ) * ((ρ : ℂ) * Q.evalC (faceX ρ a b c β₀ b₁)) *
      ((v : ℂ) ^ (n - 3))⁻¹ +
    ((n - 5).factorial : ℂ) / 2 * ((ρ : ℂ) * cTwoG Q (faceG ρ a b c) (faceX ρ a b c β₀ b₁) +
      ((a / uHat ρ a b c : ℝ) : ℂ) * cTwoG Q (eS 1) (faceX ρ a b c β₀ b₁)) *
      ((v : ℂ) ^ (n - 4))⁻¹ +
    ((n - 6).factorial : ℂ) / 4 * ((ρ : ℂ) * cFourG Q (faceG ρ a b c) +
      ((a / uHat ρ a b c : ℝ) : ℂ) * cFourX Q (faceG ρ a b c) (eS 1)) * ((v : ℂ) ^ (n - 5))⁻¹

end Rescaled

variable {n p : ℕ} {Q : LoopQuartic}

theorem paramAtV_face_aux (h : IsFaceMat (symanzikMatrix α z) ρ a b c) (hρ : ρ ≠ 0)
    (hu : uHat ρ a b c ≠ 0) (hβ : ∀ μ, symanzikVector α pp z 1 μ = ρ * b₁ μ) (v : ℝ) :
    paramAtV n Q α pp z v = (((ρ * uHat ρ a b c) ^ 2 : ℝ) : ℂ)⁻¹ *
      (((n - 4).factorial : ℂ) * Q.evalC (faceX ρ a b c (symanzikVector α pp z 0) b₁) *
          ((v : ℂ) ^ (n - 3))⁻¹ +
        ((n - 5).factorial : ℂ) / 2 *
          (cTwoG Q (faceG ρ a b c) (faceX ρ a b c (symanzikVector α pp z 0) b₁) +
            ((a / (ρ * uHat ρ a b c) : ℝ) : ℂ) *
              cTwoG Q (eS 1) (faceX ρ a b c (symanzikVector α pp z 0) b₁)) *
          ((v : ℂ) ^ (n - 4))⁻¹ +
        ((n - 6).factorial : ℂ) / 4 * (cFourG Q (faceG ρ a b c) +
          ((a / (ρ * uHat ρ a b c) : ℝ) : ℂ) * cFourX Q (faceG ρ a b c) (eS 1) +
          ((a / (ρ * uHat ρ a b c) : ℝ) : ℂ) ^ 2 * cFourG Q (eS 1)) *
          ((v : ℂ) ^ (n - 5))⁻¹) := by
  have hS := loopShift_face h hρ hu hβ
  have hU : symanzikU α z = ρ * uHat ρ a b c := det_face h
  have hI := inv_face h hρ hu
  simp only [paramAtV, ehat, contractTwo_eq_cTwoG, contractFour_eq_cFourG, hI, hS, hU,
    cTwoG_add_smul, cFourG_add_smul, faceX]
  ring

/-- **The rescaled integrand on a self-energy face**: for a numerator of degree `≤ 1` along
loop `1` and `1 ≤ p`, `ρ^{p+1} paramAtV = Û⁻² ρ^{p-1} faceBrSE`. -/
theorem paramAtV_face_se (hQ : LoopDegLe 1 1 Q) (hp : 1 ≤ p)
    (h : IsFaceMat (symanzikMatrix α z) ρ a b c) (hρ : ρ ≠ 0) (hu : uHat ρ a b c ≠ 0)
    (hβ : ∀ μ, symanzikVector α pp z 1 μ = ρ * b₁ μ) (v : ℝ) :
    (ρ : ℂ) ^ (p + 1) * paramAtV n Q α pp z v = ((uHat ρ a b c ^ 2 : ℝ) : ℂ)⁻¹ *
      ((ρ : ℂ) ^ (p - 1) * faceBrSE n Q ρ a b c (symanzikVector α pp z 0) b₁ v) := by
  rw [paramAtV_face_aux h hρ hu hβ, cTwoG_eS hQ, cFourX_eS hQ,
    cFourG_eS (hQ.mono (by norm_num))]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hρc : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ
  have huc : (uHat ρ a b c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu
  simp only [faceBrSE, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- **The rescaled integrand on a vertex face**: for a numerator of degree `≤ 2` along loop `1`
and `2 ≤ p`, `ρ^{p+1} paramAtV = Û⁻² ρ^{p-2} faceBrVtx`. -/
theorem paramAtV_face_vtx (hQ : LoopDegLe 1 2 Q) (hp : 2 ≤ p)
    (h : IsFaceMat (symanzikMatrix α z) ρ a b c) (hρ : ρ ≠ 0) (hu : uHat ρ a b c ≠ 0)
    (hβ : ∀ μ, symanzikVector α pp z 1 μ = ρ * b₁ μ) (v : ℝ) :
    (ρ : ℂ) ^ (p + 1) * paramAtV n Q α pp z v = ((uHat ρ a b c ^ 2 : ℝ) : ℂ)⁻¹ *
      ((ρ : ℂ) ^ (p - 2) * faceBrVtx n Q ρ a b c (symanzikVector α pp z 0) b₁ v) := by
  rw [paramAtV_face_aux h hρ hu hβ, cFourG_eS hQ]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have hρc : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ
  have huc : (uHat ρ a b c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu
  simp only [faceBrVtx, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

end QED.GradedProof.RPi4

end
