/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Integration.SimplexMerge

/-!
# Merging the line groups of the `δ₂, δ_m` counterterm classes

Section 5.2 of `docs/TWO-LOOP-UNITS.md`, the `δ₂, δ_m` half of the unit `S`. The eight Feynman
parameters of the product data of the `δ₂, δ_m` classes (`QED.TwoLoop.CountertermLimit.kindsD2In`)
are `z = (z₀, z₁, z₂, z₃, z₄, z₅, z₆, z₇)`: the outgoing electron `z₀`, the doubled incoming
electron `(z₁, z₂)`, the photon pair `z₃` (mass `m_γ`), `z₄` (mass `Λ`) and the three lines
`(z₅, z₆, z₇)` of the auxiliary loop. For every `f` integrable on `Δ₇`
(`integral_simplex_ctSplit`):
`∫_{Δ₇} f(z) = ∫_{w ∈ Δ₂} ∫₀^{w₀} ∫₀^{w₂} ∫₀^{w₁} ∫₀^{w₁ - t₃} ∫₀^{w₀ - t₅}
  f(t₅, t₁, w₀ - t₅ - t₁, t₄, w₂ - t₄, t₃, t₂, w₁ - t₃ - t₂)`,
`w = (e, T, r)` the barycentric point of the merged groups `e = z₀ + z₁ + z₂` (the electrons),
`T = z₅ + z₆ + z₇` (the auxiliary loop) and `r = z₃ + z₄` (the photon pair); the merged integrand
is integrable on `Δ₂`. A permutation of the coordinates followed by five applications of
`QED.Integration.SimplexMerge.integral_simplex_splitAt` (the analogue of
`QED/TwoLoop/UnitSCReduceSMerge.lean`).
-/

@[expose] public section

open MeasureTheory Set

namespace QED.TwoLoop.UnitSCCt

open QED.Integration.Feynman (simplexSet simplexPoint)
open QED.Integration.SimplexMerge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The point of `ℝ⁸` with group sums `w = (e, T, r)` and splits
`z₀ = t₅`, `z₁ = t₁`, `z₃ = t₄`, `z₅ = t₃`, `z₆ = t₂`. -/
def ctSplit (w : Fin 3 → ℝ) (t₅ t₄ t₃ t₂ t₁ : ℝ) : Fin 8 → ℝ :=
  ![t₅, t₁, w 0 - t₅ - t₁, t₄, w 2 - t₄, t₃, t₂, w 1 - t₃ - t₂]

/-- The merged integrand
`∫₀^{w₀} ∫₀^{w₂} ∫₀^{w₁} ∫₀^{w₁ - t₃} ∫₀^{w₀ - t₅} f(ctSplit w t₅ t₄ t₃ t₂ t₁)`. -/
noncomputable def ctMerged (f : (Fin 8 → ℝ) → E) (w : Fin 3 → ℝ) : E :=
  ∫ t₅ in (0 : ℝ)..w 0, ∫ t₄ in (0 : ℝ)..w 2, ∫ t₃ in (0 : ℝ)..w 1,
    ∫ t₂ in (0 : ℝ)..(w 1 - t₃), ∫ t₁ in (0 : ℝ)..(w 0 - t₅), f (ctSplit w t₅ t₄ t₃ t₂ t₁)

/-- The reordering of the coordinates: `z = u ∘ ctPerm` for
`u = (t₅, t₃, t₄, t₁, w₂ - t₄, t₂, w₁ - t₃ - t₂, w₀ - t₅ - t₁)`. -/
def ctPerm : Equiv.Perm (Fin 8) where
  toFun := ![0, 3, 7, 2, 4, 1, 5, 6]
  invFun := ![0, 5, 3, 1, 4, 6, 7, 2]
  left_inv := by decide
  right_inv := by decide

theorem ctSplitAt_chain (w : Fin 3 → ℝ) (t₅ t₄ t₃ t₂ t₁ : ℝ) :
    splitAt 3 (splitAt 5 (splitAt 1 (splitAt 2 (splitAt 0 w t₅) t₄) t₃) t₂) t₁ ∘ ctPerm =
      ctSplit w t₅ t₄ t₃ t₂ t₁ := by
  funext k
  fin_cases k <;> simp [splitAt, ctPerm, ctSplit, Fin.snoc, Function.update] <;> rfl

theorem ctSplitAt_bound₁ (w : Fin 3 → ℝ) (t₅ : ℝ) : splitAt 0 w t₅ 2 = w 2 := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]
  rfl

theorem ctSplitAt_bound₂ (w : Fin 3 → ℝ) (t₅ t₄ : ℝ) :
    splitAt 2 (splitAt 0 w t₅) t₄ 1 = w 1 := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]

theorem ctSplitAt_bound₃ (w : Fin 3 → ℝ) (t₅ t₄ t₃ : ℝ) :
    splitAt 1 (splitAt 2 (splitAt 0 w t₅) t₄) t₃ 5 = w 1 - t₃ := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]

theorem ctSplitAt_bound₄ (w : Fin 3 → ℝ) (t₅ t₄ t₃ t₂ : ℝ) :
    splitAt 5 (splitAt 1 (splitAt 2 (splitAt 0 w t₅) t₄) t₃) t₂ 3 = w 0 - t₅ := by
  simp [splitAt, Fin.snoc, Function.update, Fin.ext_iff]

/-- **Merging the line groups of the `δ₂, δ_m` classes.** -/
theorem integral_simplex_ctSplit {f : (Fin 8 → ℝ) → E}
    (hf : IntegrableOn (fun x => f (simplexPoint x)) (simplexSet 7)) :
    IntegrableOn (fun y => ctMerged f (simplexPoint y)) (simplexSet 2) ∧
    ∫ x in simplexSet 7, f (simplexPoint x) = ∫ y in simplexSet 2, ctMerged f (simplexPoint y) := by
  set h₀ : (Fin 8 → ℝ) → E := fun u => f (u ∘ ctPerm)
  have hinv : ∀ u : Fin 8 → ℝ, (u ∘ ⇑ctPerm⁻¹) ∘ ⇑ctPerm = u := fun u => by
    funext k; simp
  have hcomp : (fun x => h₀ (simplexPoint x ∘ ⇑ctPerm⁻¹)) = fun x => f (simplexPoint x) := by
    funext x; simp only [h₀, hinv]
  have hf₀ : IntegrableOn (fun x => h₀ (simplexPoint x)) (simplexSet 7) := by
    rw [← integrableOn_simplex_comp_perm_iff ctPerm⁻¹ h₀, hcomp]
    exact hf
  have e₀ : ∫ x in simplexSet 7, f (simplexPoint x) = ∫ x in simplexSet 7, h₀ (simplexPoint x) := by
    rw [← integral_simplex_comp_perm ctPerm⁻¹ h₀, hcomp]
  set h₁ : (Fin 7 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 3, h₀ (splitAt 3 v t)
  obtain ⟨I₁, e₁⟩ := integral_simplex_splitAt (m := 6) (by norm_num) 3 (f := h₀) hf₀
  set h₂ : (Fin 6 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 5, h₁ (splitAt 5 v t)
  obtain ⟨I₂, e₂⟩ := integral_simplex_splitAt (m := 5) (by norm_num) 5 (f := h₁) I₁
  set h₃ : (Fin 5 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 1, h₂ (splitAt 1 v t)
  obtain ⟨I₃, e₃⟩ := integral_simplex_splitAt (m := 4) (by norm_num) 1 (f := h₂) I₂
  set h₄ : (Fin 4 → ℝ) → E := fun v => ∫ t in (0 : ℝ)..v 2, h₃ (splitAt 2 v t)
  obtain ⟨I₄, e₄⟩ := integral_simplex_splitAt (m := 3) (by norm_num) 2 (f := h₃) I₃
  obtain ⟨I₅, e₅⟩ := integral_simplex_splitAt (m := 2) (by norm_num) 0 (f := h₄) I₄
  have hpt : ∀ w : Fin 3 → ℝ, ∫ t in (0 : ℝ)..w 0, h₄ (splitAt 0 w t) = ctMerged f w := by
    intro w
    simp only [h₄, h₃, h₂, h₁, h₀, ctSplitAt_bound₁, ctSplitAt_bound₂, ctSplitAt_bound₃,
      ctSplitAt_bound₄, ctSplitAt_chain, ctMerged]
  simp only [hpt] at I₅ e₅
  exact ⟨I₅, by rw [e₀, e₁, e₂, e₃, e₄, e₅]⟩

end QED.TwoLoop.UnitSCCt

end
