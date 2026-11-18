/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SimplexMerge

/-!
# Merging the line groups of the self-energy class `S₊`

The eight Feynman parameters of the Pauli–Villars form of `S₊` come in four groups: the three
outer electron lines `(z₀, z₁, z₃)`, the inner electron `z₂`, the outer photon `(z₄, z₆)` and the
inner photon `(z₅, z₇)` (lines `4, 5` at mass `m_γ`, lines `6, 7` at mass `Λ`). For every `f`
integrable on `Δ₇` (`integral_simplex_selfSplit`):
`∫_{Δ₇} f(z) = ∫_{w ∈ Δ₃} ∫₀^{w₀} ∫₀^{t₄} ∫₀^{w₂} ∫₀^{w₃} f(t₃, t₄ - t₃, w₁, w₀ - t₄, t₂, t₁, w₂ - t₂, w₃ - t₁)`,
`w = (z_o, Y, z_a, z_b)` the barycentric point of the merged groups, and the merged integrand is
integrable on `Δ₃`. A permutation of the coordinates followed by four applications of
`QED.Integration.SimplexMerge.integral_simplex_splitAt` (the three-line group is split twice; the
analogue of `QED/TwoLoop/UnitLGraphReduceMerge.lean`).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.TwoLoop.UnitSCReduce

open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.SimplexMerge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The point of `ℝ⁸` with group sums `w = (z_o, Y, z_a, z_b)` and splits
`z₀ = t₃`, `z₁ = t₄ - t₃`, `z₃ = w₀ - t₄`, `z₄ = t₂`, `z₅ = t₁`. -/
def selfSplit (w : Fin 4 → ℝ) (t₄ t₃ t₂ t₁ : ℝ) : Fin 8 → ℝ :=
  ![t₃, t₄ - t₃, w 1, w 0 - t₄, t₂, t₁, w 2 - t₂, w 3 - t₁]

/-- The merged integrand
`∫₀^{w₀} ∫₀^{t₄} ∫₀^{w₂} ∫₀^{w₃} f(selfSplit w t₄ t₃ t₂ t₁) dt₁ dt₂ dt₃ dt₄`. -/
noncomputable def selfMerged (f : (Fin 8 → ℝ) → E) (w : Fin 4 → ℝ) : E :=
  ∫ t₄ in (0 : ℝ)..w 0, ∫ t₃ in (0 : ℝ)..t₄, ∫ t₂ in (0 : ℝ)..w 2, ∫ t₁ in (0 : ℝ)..w 3,
    f (selfSplit w t₄ t₃ t₂ t₁)

/-- The reordering of the coordinates: `z = u ∘ selfPerm` for
`u = (t₃, w₁, t₂, t₁, w₀ - t₄, t₄ - t₃, w₂ - t₂, w₃ - t₁)`. -/
def selfPerm : Equiv.Perm (Fin 8) where
  toFun := ![0, 5, 1, 4, 2, 3, 6, 7]
  invFun := ![0, 2, 4, 5, 3, 1, 6, 7]
  left_inv := by decide
  right_inv := by decide

theorem selfSplitAt_chain (w : Fin 4 → ℝ) (t₄ t₃ t₂ t₁ : ℝ) :
    splitAt 3 (splitAt 2 (splitAt 0 (splitAt 0 w t₄) t₃) t₂) t₁ ∘ selfPerm =
      selfSplit w t₄ t₃ t₂ t₁ := by
  funext k
  fin_cases k <;> simp [splitAt, selfPerm, selfSplit, Fin.snoc, Function.update] <;> rfl

theorem selfSplitAt_bound₁ (w : Fin 4 → ℝ) (t₄ : ℝ) : splitAt 0 w t₄ 0 = t₄ := by
  simp [splitAt, Fin.snoc, Function.update]

theorem selfSplitAt_bound₂ (w : Fin 4 → ℝ) (t₄ t₃ : ℝ) :
    splitAt 0 (splitAt 0 w t₄) t₃ 2 = w 2 := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]
  rfl

theorem selfSplitAt_bound₃ (w : Fin 4 → ℝ) (t₄ t₃ t₂ : ℝ) :
    splitAt 2 (splitAt 0 (splitAt 0 w t₄) t₃) t₂ 3 = w 3 := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]
  rfl

/-- **Merging the line groups of `S₊`.** -/
theorem integral_simplex_selfSplit {f : (Fin 8 → ℝ) → E}
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet 7)) :
    IntegrableOn (fun y => selfMerged f (simplexPoint y)) (simplexSet 3) ∧
    ∫ x in simplexSet 7, f (simplexPoint x) = ∫ y in simplexSet 3, selfMerged f (simplexPoint y) := by
  set h₀ : (Fin 8 → ℝ) → E := fun u => f (u ∘ selfPerm)
  have hinv : ∀ u : Fin 8 → ℝ, (u ∘ ⇑selfPerm⁻¹) ∘ ⇑selfPerm = u := fun u => by
    funext k; simp
  have hcomp : (fun x => h₀ (simplexPoint x ∘ ⇑selfPerm⁻¹)) = fun x => f (simplexPoint x) := by
    funext x; simp only [h₀, hinv]
  have hf₀ : IntegrableOn (fun x => h₀ (simplexPoint x)) (simplexSet 7) := by
    rw [← integrableOn_simplex_comp_perm_iff selfPerm⁻¹ h₀, hcomp]
    exact hf
  have e₀ : ∫ x in simplexSet 7, f (simplexPoint x) = ∫ x in simplexSet 7, h₀ (simplexPoint x) := by
    rw [← integral_simplex_comp_perm selfPerm⁻¹ h₀, hcomp]
  set h₁ : (Fin 7 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 3, h₀ (splitAt 3 v t)
  obtain ⟨I₁, e₁⟩ := integral_simplex_splitAt (m := 6) (by norm_num) 3 (f := h₀) hf₀
  set h₂ : (Fin 6 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 2, h₁ (splitAt 2 v t)
  obtain ⟨I₂, e₂⟩ := integral_simplex_splitAt (m := 5) (by norm_num) 2 (f := h₁) I₁
  set h₃ : (Fin 5 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 0, h₂ (splitAt 0 v t)
  obtain ⟨I₃, e₃⟩ := integral_simplex_splitAt (m := 4) (by norm_num) 0 (f := h₂) I₂
  obtain ⟨I₄, e₄⟩ := integral_simplex_splitAt (m := 3) (by norm_num) 0 (f := h₃) I₃
  have hpt : ∀ w : Fin 4 → ℝ, ∫ t in (0 : ℝ)..w 0, h₃ (splitAt 0 w t) = selfMerged f w := by
    intro w
    simp only [h₃, h₂, h₁, h₀, selfSplitAt_bound₁, selfSplitAt_bound₂, selfSplitAt_bound₃,
      selfSplitAt_chain, selfMerged]
  simp only [hpt] at I₄ e₄
  exact ⟨I₄, by rw [e₀, e₁, e₂, e₃, e₄]⟩

end QED.TwoLoop.UnitSCReduce

end
