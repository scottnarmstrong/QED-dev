/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4FaceInv
public import QED.GradedProof.RPi4Join

/-!
# (R-Π₄) step L6d1: the face data in join coordinates

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L6d1. After sorting
the lines so that the face block (the subgraph lines and the photon) comes first,
`integral_simplex_join` writes the Feynman point as `z = (ρ W, (1 - ρ) V)` with barycentric
points `W` (face block) and `V` (rest). If every line of the rest has loop row `(1, 0)`, the
Symanzik matrix is a face matrix with data affine in `ρ`:

* `joinA` (concatenation indexed by `Fin (p + 1 + q + 1)`), `sum_join`, `joinZ`,
  `symanzikMatrix_join`, `symanzikVector_join`;
* **`isFaceMat_join`**: `A = [[a₀ + ρ a₁, ρ b], [ρ b, ρ c]]`, with `a₀ = ∑ V`,
  `a₁ = ∑ W α₀² - ∑ V`, `b = ∑ W α₀ α₁`, `c = ∑ W α₁²`;
* **`symanzikVector_join_one`**, `symanzikVector_join_zero`: `β₁ = ρ b₁`, `β₀ = P₀ + ρ P₁`;
* **`uHat_join_ge`**: on the self-energy/vertex face of loop `1` (face rows `(0, 1)` and
  `(1, -1)`, `W`, `V` barycentric), `Û = 1 - ρ + ρθ(1 - θ) ≥ 1 - ρ`.
-/

@[expose] public section

namespace QED.GradedProof.RPi4

open QED.Integration.TwoLoop

variable {p q : ℕ}

/-- The Feynman point `(ρ W, (1 - ρ) V)` of the join coordinates. -/
noncomputable def joinZ (ρ : ℝ) (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ) :
    Fin (p + 1 + q + 1) → ℝ :=
  Fin.append (m := p + 1) (n := q + 1) (ρ • W) ((1 - ρ) • V)

/-- Concatenation of the face-block and rest data, indexed by `Fin (p + 1 + q + 1)`. -/
def joinA {β : Type*} (f : Fin (p + 1) → β) (g : Fin (q + 1) → β) : Fin (p + 1 + q + 1) → β :=
  Fin.append (m := p + 1) (n := q + 1) f g

theorem sum_join (f : Fin (p + 1 + q + 1) → ℝ) :
    ∑ i, f i = ∑ i : Fin (p + 1), f (Fin.castAdd (q + 1) i) +
      ∑ j : Fin (q + 1), f (Fin.natAdd (p + 1) j) :=
  Fin.sum_univ_add (a := p + 1) (b := q + 1) f

variable (αF : Fin (p + 1) → Fin 2 → ℝ) (αR : Fin (q + 1) → Fin 2 → ℝ)
  (pF : Fin (p + 1) → Fin 4 → ℝ) (pR : Fin (q + 1) → Fin 4 → ℝ) (ρ : ℝ)
  (W : Fin (p + 1) → ℝ) (V : Fin (q + 1) → ℝ)

theorem symanzikMatrix_join (s t : Fin 2) :
    symanzikMatrix (joinA αF αR) (joinZ ρ W V) s t =
      ρ * ∑ i, W i * αF i s * αF i t + (1 - ρ) * ∑ j, V j * αR j s * αR j t := by
  simp only [symanzikMatrix, Matrix.of_apply]
  rw [sum_join]
  simp only [joinZ, joinA, Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

theorem symanzikVector_join (s : Fin 2) (μ : Fin 4) :
    symanzikVector (joinA αF αR) (joinA pF pR) (joinZ ρ W V) s μ =
      ρ * ∑ i, W i * αF i s * pF i μ + (1 - ρ) * ∑ j, V j * αR j s * pR j μ := by
  simp only [symanzikVector]
  rw [sum_join]
  simp only [joinZ, joinA, Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

variable {αR}

/-- **The Symanzik matrix in join coordinates is a face matrix.** -/
theorem isFaceMat_join (hR : ∀ j, αR j = ![1, 0]) :
    IsFaceMat (symanzikMatrix (joinA αF αR) (joinZ ρ W V)) ρ
      (∑ j, V j + ρ * (∑ i, W i * αF i 0 * αF i 0 - ∑ j, V j))
      (∑ i, W i * αF i 0 * αF i 1) (∑ i, W i * αF i 1 * αF i 1) := by
  have h0 : ∀ j, αR j 0 = 1 := fun j => by simp [hR j]
  have h1 : ∀ j, αR j 1 = 0 := fun j => by simp [hR j]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [symanzikMatrix_join] <;> simp only [h0, h1, mul_one, mul_zero,
    Finset.sum_const_zero, add_zero]
  · ring
  · congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem symanzikVector_join_one (hR : ∀ j, αR j = ![1, 0]) (μ : Fin 4) :
    symanzikVector (joinA αF αR) (joinA pF pR) (joinZ ρ W V) 1 μ =
      ρ * ∑ i, W i * αF i 1 * pF i μ := by
  rw [symanzikVector_join]
  simp [hR]

theorem symanzikVector_join_zero (hR : ∀ j, αR j = ![1, 0]) (μ : Fin 4) :
    symanzikVector (joinA αF αR) (joinA pF pR) (joinZ ρ W V) 0 μ =
      ∑ j, V j * pR j μ + ρ * (∑ i, W i * αF i 0 * pF i μ - ∑ j, V j * pR j μ) := by
  rw [symanzikVector_join]
  simp only [hR, Matrix.cons_val_zero, mul_one]
  ring

/-- **The rescaled determinant on the face of loop `1`** is at least `1 - ρ`. -/
theorem uHat_join_ge (hF : ∀ i, αF i = ![0, 1] ∨ αF i = ![1, -1]) (hW : ∀ i, 0 ≤ W i)
    (hW1 : ∑ i, W i = 1) (hV1 : ∑ j, V j = 1) (hρ : 0 ≤ ρ) :
    1 - ρ ≤ uHat ρ (∑ j, V j + ρ * (∑ i, W i * αF i 0 * αF i 0 - ∑ j, V j))
      (∑ i, W i * αF i 0 * αF i 1) (∑ i, W i * αF i 1 * αF i 1) := by
  set θ := ∑ i, W i * αF i 0 * αF i 0 with hθ
  have e1 : ∀ i, αF i 1 * αF i 1 = 1 := fun i => by rcases hF i with h | h <;> simp [h]
  have e2 : ∀ i, αF i 0 * αF i 1 = -(αF i 0 * αF i 0) := fun i => by
    rcases hF i with h | h <;> simp [h]
  have e3 : ∀ i, αF i 0 * αF i 0 ≤ 1 := fun i => by rcases hF i with h | h <;> simp [h]
  have hc : ∑ i, W i * αF i 1 * αF i 1 = 1 := by
    simp only [mul_assoc, e1, mul_one, hW1]
  have hb : ∑ i, W i * αF i 0 * αF i 1 = -θ := by
    simp only [hθ, mul_assoc, e2, mul_neg, Finset.sum_neg_distrib]
  have hθ0 : 0 ≤ θ := Finset.sum_nonneg fun i _ => by
    rw [mul_assoc]; exact mul_nonneg (hW i) (mul_self_nonneg _)
  have hθ1 : θ ≤ 1 := by
    rw [← hW1]
    exact Finset.sum_le_sum fun i _ => by
      rw [mul_assoc]; exact mul_le_of_le_one_right (hW i) (e3 i)
  rw [hc, hb, hV1, uHat]
  nlinarith [mul_nonneg hρ (mul_nonneg hθ0 (sub_nonneg.mpr hθ1))]

end QED.GradedProof.RPi4

end
