/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SimplexMerge

/-!
# Merging the line pairs of the corner class `C₊`

The eight Feynman parameters of the Pauli–Villars form of `C₊` contain three pairs: the outer
electron pair `(z₀, z₁)`, the outer photon `(z₄, z₆)` and the inner photon `(z₅, z₇)` (lines
`4, 5` at mass `m_γ`, lines `6, 7` at mass `Λ`); `z₂ = y₃` and `z₃ = y₄` are single lines. For
every `f` integrable on `Δ₇` (`integral_simplex_cornerSplit`):
`∫_{Δ₇} f(z) = ∫_{w ∈ Δ₄} ∫₀^{w₀} ∫₀^{w₃} ∫₀^{w₄} f(t₃, w₀ - t₃, w₁, w₂, t₂, t₁, w₃ - t₂, w₄ - t₁)`,
`w = (z_o, y₃, y₄, z_a, z_b)` the barycentric point of the merged groups, and the merged
integrand is integrable on `Δ₄` (the analogue of `QED/TwoLoop/UnitXGraphReduceMerge.lean`).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.TwoLoop.UnitSCReduce

open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.SimplexMerge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The point of `ℝ⁸` with group sums `w = (z_o, y₃, y₄, z_a, z_b)` and splits `z₀ = t₃`,
`z₄ = t₂`, `z₅ = t₁`. -/
def cornerSplit (w : Fin 5 → ℝ) (t₃ t₂ t₁ : ℝ) : Fin 8 → ℝ :=
  ![t₃, w 0 - t₃, w 1, w 2, t₂, t₁, w 3 - t₂, w 4 - t₁]

/-- The merged integrand `∫₀^{w₀} ∫₀^{w₃} ∫₀^{w₄} f(cornerSplit w t₃ t₂ t₁) dt₁ dt₂ dt₃`. -/
noncomputable def cornerMerged (f : (Fin 8 → ℝ) → E) (w : Fin 5 → ℝ) : E :=
  ∫ t₃ in (0 : ℝ)..w 0, ∫ t₂ in (0 : ℝ)..w 3, ∫ t₁ in (0 : ℝ)..w 4, f (cornerSplit w t₃ t₂ t₁)

/-- The reordering of the coordinates: `z = u ∘ cornerPerm` for
`u = (t₃, w₁, w₂, t₂, t₁, w₀ - t₃, w₃ - t₂, w₄ - t₁)`. -/
def cornerPerm : Equiv.Perm (Fin 8) where
  toFun := ![0, 5, 1, 2, 3, 4, 6, 7]
  invFun := ![0, 2, 3, 4, 5, 1, 6, 7]
  left_inv := by decide
  right_inv := by decide

theorem splitAt_chain_corner (w : Fin 5 → ℝ) (t₃ t₂ t₁ : ℝ) :
    splitAt 4 (splitAt 3 (splitAt 0 w t₃) t₂) t₁ ∘ cornerPerm = cornerSplit w t₃ t₂ t₁ := by
  funext k
  fin_cases k <;> simp [splitAt, cornerPerm, cornerSplit, Fin.snoc, Function.update] <;> rfl

theorem splitAt_bound_corner₁ (w : Fin 5 → ℝ) (t₃ : ℝ) : splitAt 0 w t₃ 3 = w 3 := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]
  rfl

theorem splitAt_bound_corner₂ (w : Fin 5 → ℝ) (t₃ t₂ : ℝ) :
    splitAt 3 (splitAt 0 w t₃) t₂ 4 = w 4 := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]
  rfl

/-- **Merging the three line pairs of `C₊`.** -/
theorem integral_simplex_cornerSplit {f : (Fin 8 → ℝ) → E}
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet 7)) :
    IntegrableOn (fun y => cornerMerged f (simplexPoint y)) (simplexSet 4) ∧
    ∫ x in simplexSet 7, f (simplexPoint x) =
      ∫ y in simplexSet 4, cornerMerged f (simplexPoint y) := by
  set h₀ : (Fin 8 → ℝ) → E := fun u => f (u ∘ cornerPerm)
  have hinv : ∀ u : Fin 8 → ℝ, (u ∘ ⇑cornerPerm⁻¹) ∘ ⇑cornerPerm = u := fun u => by
    funext k; simp
  have hcomp : (fun x => h₀ (simplexPoint x ∘ ⇑cornerPerm⁻¹)) = fun x => f (simplexPoint x) := by
    funext x; simp only [h₀, hinv]
  have hf₀ : IntegrableOn (fun x => h₀ (simplexPoint x)) (simplexSet 7) := by
    rw [← integrableOn_simplex_comp_perm_iff cornerPerm⁻¹ h₀, hcomp]
    exact hf
  have e₀ : ∫ x in simplexSet 7, f (simplexPoint x) = ∫ x in simplexSet 7, h₀ (simplexPoint x) := by
    rw [← integral_simplex_comp_perm cornerPerm⁻¹ h₀, hcomp]
  set h₁ : (Fin 7 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 4, h₀ (splitAt 4 v t)
  obtain ⟨I₁, e₁⟩ := integral_simplex_splitAt (m := 6) (by norm_num) 4 (f := h₀) hf₀
  set h₂ : (Fin 6 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 3, h₁ (splitAt 3 v t)
  obtain ⟨I₂, e₂⟩ := integral_simplex_splitAt (m := 5) (by norm_num) 3 (f := h₁) I₁
  obtain ⟨I₃, e₃⟩ := integral_simplex_splitAt (m := 4) (by norm_num) 0 (f := h₂) I₂
  have hpt : ∀ w : Fin 5 → ℝ, ∫ t in (0 : ℝ)..w 0, h₂ (splitAt 0 w t) = cornerMerged f w := by
    intro w
    simp only [h₂, h₁, h₀, splitAt_bound_corner₁, splitAt_bound_corner₂, splitAt_chain_corner,
      cornerMerged]
  simp only [hpt] at I₃ e₃
  exact ⟨I₃, by rw [e₀, e₁, e₂, e₃]⟩

end QED.TwoLoop.UnitSCReduce

end
