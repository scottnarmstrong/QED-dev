/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SimplexMerge

/-!
# Merging the four line pairs of the ladder

The eight Feynman parameters of the Pauli–Villars form of the ladder come in four pairs: the
outer electron pair `(z₀, z₃)`, the inner electron pair `(z₁, z₂)`, the outer photon `(z₄, z₆)`
and the inner photon `(z₅, z₇)` (lines `4, 5` at mass `m_γ`, lines `6, 7` at mass `Λ`). For every
`f` integrable on `Δ₇` (`integral_simplex_ladderSplit`):
`∫_{Δ₇} f(z) = ∫_{w ∈ Δ₃} ∫₀^{w₀} ∫₀^{w₁} ∫₀^{w₂} ∫₀^{w₃} f(t₄, t₃, w₁ - t₃, w₀ - t₄, t₂, t₁, w₂ - t₂, w₃ - t₁)`,
`w = (z_A, z_B, z_a, z_b)` the barycentric point of the merged pairs, and the merged integrand
is integrable on `Δ₃`. A permutation of the coordinates followed by four applications of
`QED.Integration.SimplexMerge.integral_simplex_splitAt`.
-/

@[expose] public section

open MeasureTheory Set

namespace QED.TwoLoop.UnitLGraphReduce

open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.SimplexMerge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The point of `ℝ⁸` with group sums `w = (z_A, z_B, z_a, z_b)` and splits
`z₀ = t₄`, `z₁ = t₃`, `z₄ = t₂`, `z₅ = t₁`. -/
def ladderSplit (w : Fin 4 → ℝ) (t₄ t₃ t₂ t₁ : ℝ) : Fin 8 → ℝ :=
  ![t₄, t₃, w 1 - t₃, w 0 - t₄, t₂, t₁, w 2 - t₂, w 3 - t₁]

/-- The merged integrand
`∫₀^{w₀} ∫₀^{w₁} ∫₀^{w₂} ∫₀^{w₃} f(ladderSplit w t₄ t₃ t₂ t₁) dt₁ dt₂ dt₃ dt₄`. -/
noncomputable def ladderMerged (f : (Fin 8 → ℝ) → E) (w : Fin 4 → ℝ) : E :=
  ∫ t₄ in (0 : ℝ)..w 0, ∫ t₃ in (0 : ℝ)..w 1, ∫ t₂ in (0 : ℝ)..w 2, ∫ t₁ in (0 : ℝ)..w 3,
    f (ladderSplit w t₄ t₃ t₂ t₁)

/-- The reordering of the coordinates: `z = u ∘ ladderPerm` for
`u = (t₄, t₃, t₂, t₁, w₀ - t₄, w₁ - t₃, w₂ - t₂, w₃ - t₁)`. -/
def ladderPerm : Equiv.Perm (Fin 8) where
  toFun := ![0, 1, 5, 4, 2, 3, 6, 7]
  invFun := ![0, 1, 4, 5, 3, 2, 6, 7]
  left_inv := by decide
  right_inv := by decide

theorem splitAt_chain (w : Fin 4 → ℝ) (t₄ t₃ t₂ t₁ : ℝ) :
    splitAt 3 (splitAt 2 (splitAt 1 (splitAt 0 w t₄) t₃) t₂) t₁ ∘ ladderPerm =
      ladderSplit w t₄ t₃ t₂ t₁ := by
  funext k
  fin_cases k <;> simp [splitAt, ladderPerm, ladderSplit, Fin.snoc, Function.update] <;> rfl

theorem splitAt_bound₁ (w : Fin 4 → ℝ) (t₄ : ℝ) : splitAt 0 w t₄ 1 = w 1 := by
  simp [splitAt, Fin.snoc, Function.update]

theorem splitAt_bound₂ (w : Fin 4 → ℝ) (t₄ t₃ : ℝ) : splitAt 1 (splitAt 0 w t₄) t₃ 2 = w 2 := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]
  rfl

theorem splitAt_bound₃ (w : Fin 4 → ℝ) (t₄ t₃ t₂ : ℝ) :
    splitAt 2 (splitAt 1 (splitAt 0 w t₄) t₃) t₂ 3 = w 3 := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]
  rfl

/-- **Merging the four line pairs of the ladder.** -/
theorem integral_simplex_ladderSplit {f : (Fin 8 → ℝ) → E}
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet 7)) :
    IntegrableOn (fun y => ladderMerged f (simplexPoint y)) (simplexSet 3) ∧
    ∫ x in simplexSet 7, f (simplexPoint x) = ∫ y in simplexSet 3, ladderMerged f (simplexPoint y) := by
  set h₀ : (Fin 8 → ℝ) → E := fun u => f (u ∘ ladderPerm)
  have hinv : ∀ u : Fin 8 → ℝ, (u ∘ ⇑ladderPerm⁻¹) ∘ ⇑ladderPerm = u := fun u => by
    funext k; simp
  have hcomp : (fun x => h₀ (simplexPoint x ∘ ⇑ladderPerm⁻¹)) = fun x => f (simplexPoint x) := by
    funext x; simp only [h₀, hinv]
  have hf₀ : IntegrableOn (fun x => h₀ (simplexPoint x)) (simplexSet 7) := by
    rw [← integrableOn_simplex_comp_perm_iff ladderPerm⁻¹ h₀, hcomp]
    exact hf
  have e₀ : ∫ x in simplexSet 7, f (simplexPoint x) = ∫ x in simplexSet 7, h₀ (simplexPoint x) := by
    rw [← integral_simplex_comp_perm ladderPerm⁻¹ h₀, hcomp]
  set h₁ : (Fin 7 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 3, h₀ (splitAt 3 v t)
  obtain ⟨I₁, e₁⟩ := integral_simplex_splitAt (m := 6) (by norm_num) 3 (f := h₀) hf₀
  set h₂ : (Fin 6 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 2, h₁ (splitAt 2 v t)
  obtain ⟨I₂, e₂⟩ := integral_simplex_splitAt (m := 5) (by norm_num) 2 (f := h₁) I₁
  set h₃ : (Fin 5 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 1, h₂ (splitAt 1 v t)
  obtain ⟨I₃, e₃⟩ := integral_simplex_splitAt (m := 4) (by norm_num) 1 (f := h₂) I₂
  obtain ⟨I₄, e₄⟩ := integral_simplex_splitAt (m := 3) (by norm_num) 0 (f := h₃) I₃
  have hpt : ∀ w : Fin 4 → ℝ, ∫ t in (0 : ℝ)..w 0, h₃ (splitAt 0 w t) = ladderMerged f w := by
    intro w
    simp only [h₃, h₂, h₁, h₀, splitAt_bound₁, splitAt_bound₂, splitAt_bound₃, splitAt_chain,
      ladderMerged]
  simp only [hpt] at I₄ e₄
  exact ⟨I₄, by rw [e₀, e₁, e₂, e₃, e₄]⟩

end QED.TwoLoop.UnitLGraphReduce

end
