/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SimplexMerge

/-!
# Merging the line pairs of the crossed ladder

The eight Feynman parameters of the Pauli–Villars form of the crossed ladder contain three pairs:
the electron pair `(z₁, z₂)` (the two lines next to the external vertex), the outer photon
`(z₄, z₆)` and the inner photon `(z₅, z₇)` (lines `4, 5` at mass `m_γ`, lines `6, 7` at mass `Λ`);
`z₀` and `z₃` are single lines. For every `f` integrable on `Δ₇`
(`integral_simplex_crossedSplit`):
`∫_{Δ₇} f(z) = ∫_{w ∈ Δ₄} ∫₀^{w₁} ∫₀^{w₃} ∫₀^{w₄} f(w₀, t₃, w₁ - t₃, w₂, t₂, t₁, w₃ - t₂, w₄ - t₁)`,
`w = (z_A, z_M, z_c, z_a, z_b)` the barycentric point of the merged groups, and the merged
integrand is integrable on `Δ₄`. A permutation of the coordinates followed by three applications
of `QED.Integration.SimplexMerge.integral_simplex_splitAt` (the analogue of
`QED/TwoLoop/UnitLGraphReduceMerge.lean`).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.TwoLoop.UnitXGraph

open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.SimplexMerge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The point of `ℝ⁸` with group sums `w = (z_A, z_M, z_c, z_a, z_b)` and splits `z₁ = t₃`,
`z₄ = t₂`, `z₅ = t₁`. -/
def crossedSplit (w : Fin 5 → ℝ) (t₃ t₂ t₁ : ℝ) : Fin 8 → ℝ :=
  ![w 0, t₃, w 1 - t₃, w 2, t₂, t₁, w 3 - t₂, w 4 - t₁]

/-- The merged integrand `∫₀^{w₁} ∫₀^{w₃} ∫₀^{w₄} f(crossedSplit w t₃ t₂ t₁) dt₁ dt₂ dt₃`. -/
noncomputable def crossedMerged (f : (Fin 8 → ℝ) → E) (w : Fin 5 → ℝ) : E :=
  ∫ t₃ in (0 : ℝ)..w 1, ∫ t₂ in (0 : ℝ)..w 3, ∫ t₁ in (0 : ℝ)..w 4, f (crossedSplit w t₃ t₂ t₁)

/-- The reordering of the coordinates: `z = u ∘ crossedPerm` for
`u = (w₀, t₃, w₂, t₂, t₁, w₁ - t₃, w₃ - t₂, w₄ - t₁)`. -/
def crossedPerm : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 5, 2, 3, 4, 6, 7]
  invFun := ![0, 1, 3, 4, 5, 2, 6, 7]
  left_inv := by decide
  right_inv := by decide

theorem splitAt_chain_crossed (w : Fin 5 → ℝ) (t₃ t₂ t₁ : ℝ) :
    splitAt 4 (splitAt 3 (splitAt 1 w t₃) t₂) t₁ ∘ crossedPerm = crossedSplit w t₃ t₂ t₁ := by
  funext k
  fin_cases k <;> simp [splitAt, crossedPerm, crossedSplit, Fin.snoc, Function.update] <;> rfl

theorem splitAt_bound_crossed₁ (w : Fin 5 → ℝ) (t₃ : ℝ) : splitAt 1 w t₃ 3 = w 3 := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]
  rfl

theorem splitAt_bound_crossed₂ (w : Fin 5 → ℝ) (t₃ t₂ : ℝ) :
    splitAt 3 (splitAt 1 w t₃) t₂ 4 = w 4 := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]
  rfl

/-- **Merging the three line pairs of the crossed ladder.** -/
theorem integral_simplex_crossedSplit {f : (Fin 8 → ℝ) → E}
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet 7)) :
    IntegrableOn (fun y => crossedMerged f (simplexPoint y)) (simplexSet 4) ∧
    ∫ x in simplexSet 7, f (simplexPoint x) =
      ∫ y in simplexSet 4, crossedMerged f (simplexPoint y) := by
  set h₀ : (Fin 8 → ℝ) → E := fun u => f (u ∘ crossedPerm)
  have hinv : ∀ u : Fin 8 → ℝ, (u ∘ ⇑crossedPerm⁻¹) ∘ ⇑crossedPerm = u := fun u => by
    funext k; simp
  have hcomp : (fun x => h₀ (simplexPoint x ∘ ⇑crossedPerm⁻¹)) = fun x => f (simplexPoint x) := by
    funext x; simp only [h₀, hinv]
  have hf₀ : IntegrableOn (fun x => h₀ (simplexPoint x)) (simplexSet 7) := by
    rw [← integrableOn_simplex_comp_perm_iff crossedPerm⁻¹ h₀, hcomp]
    exact hf
  have e₀ : ∫ x in simplexSet 7, f (simplexPoint x) = ∫ x in simplexSet 7, h₀ (simplexPoint x) := by
    rw [← integral_simplex_comp_perm crossedPerm⁻¹ h₀, hcomp]
  set h₁ : (Fin 7 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 4, h₀ (splitAt 4 v t)
  obtain ⟨I₁, e₁⟩ := integral_simplex_splitAt (m := 6) (by norm_num) 4 (f := h₀) hf₀
  set h₂ : (Fin 6 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 3, h₁ (splitAt 3 v t)
  obtain ⟨I₂, e₂⟩ := integral_simplex_splitAt (m := 5) (by norm_num) 3 (f := h₁) I₁
  obtain ⟨I₃, e₃⟩ := integral_simplex_splitAt (m := 4) (by norm_num) 1 (f := h₂) I₂
  have hpt : ∀ w : Fin 5 → ℝ, ∫ t in (0 : ℝ)..w 1, h₂ (splitAt 1 w t) = crossedMerged f w := by
    intro w
    simp only [h₂, h₁, h₀, splitAt_bound_crossed₁, splitAt_bound_crossed₂, splitAt_chain_crossed,
      crossedMerged]
  simp only [hpt] at I₃ e₃
  exact ⟨I₃, by rw [e₀, e₁, e₂, e₃]⟩

end QED.TwoLoop.UnitXGraph

end
