/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.LevelOneCharge
import QED.Frozen.TwoLoop.OnePIFunctionEqOnePIFunction
import QED.WickModel.Compatibility
import QED.Wick.Classification
import QED.Wick.ClassificationSmall
import QED.ChainProof.QuickMeaning

/-!
# (X₁) piece F: the order-`e` vertex part is the tree

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece F (assembly). The Dyson decomposition `QED.GradedProof.X1C.dysonFive`
contains the vertex part (G₈ᵥ) of order `1` (`n = 0`). It is the tree `e γ^μ`, at every `ε` and
all momenta (`vertexPart_zero_apply`), by the order bookkeeping of
`QED.GradedProof.vertexPart_one_apply` one order lower.
-/

@[expose] public section

open Complex Filter Topology Matrix
open QED.WickModel (Params Contraction IsOnePI fermionSign)
open QED.Graded

namespace QED.GradedProof.X1F

open QED.GradedProof

open scoped Classical in
/-- **The order-`≤ 1` vertex is the tree** `i e γ^μ`. -/
theorem onePIFunction_one_one_one (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    QED.WickModel.onePIFunction P 1 1 1 (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) =
      I * (P.e : ℂ) * Dirac.gamma μ i j := by
  unfold QED.WickModel.onePIFunction
  rw [Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ hκ =>
    (QED.WickModel.sum_isOnePI_contractionEquiv P
      ((Finset.mem_filter.1 hκ).2.trans (by norm_num)) p' p μ i j).symm)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [Finset.sum_eq_zero fun κ _ => Wick.sum_isOnePI_eq_zero Wick.not_isOnePI_of_fin_zero _]
  rw [Finset.sum_eq_single_of_mem (fun _ => .gauge)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩) fun κ hκ hne => ?_]
  · have h := congrFun (congrFun (Wick.sum_isOnePI_gauge P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m P.mγ P.Λ
      P.ε p' p μ) i) j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [h]
    simp
  · obtain ⟨k, rfl⟩ : ∃ k, κ = fun _ => k :=
      ⟨κ 0, funext fun t => by rw [Subsingleton.elim t 0]⟩
    have hk := (Finset.mem_filter.1 hκ).2
    cases k
    · exact absurd rfl hne
    · simp [Wick.VertexKind.order] at hk
    · simp [Wick.VertexKind.order] at hk
    · exact Wick.sum_isOnePI_eq_zero
        (fun C => (Wick.isEmpty_contraction_of_not_two_dvd (by decide)).elim C) _

open scoped Classical in
/-- The order-`0` vertex function vanishes. -/
theorem onePIFunction_one_one_zero (P : Params) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    QED.WickModel.onePIFunction P 1 1 0 (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) = 0 := by
  unfold QED.WickModel.onePIFunction
  rw [Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ hκ =>
    (QED.WickModel.sum_isOnePI_contractionEquiv P
      ((Finset.mem_filter.1 hκ).2.trans (by norm_num)) p' p μ i j).symm)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [Finset.sum_eq_zero fun κ _ => Wick.sum_isOnePI_eq_zero Wick.not_isOnePI_of_fin_zero _]
  simp

open scoped Classical in
/-- **The order-`1` vertex part is the order-`1` part of (X₂₈)** at the parameters `ctParams`. -/
theorem onePIPart_one_vertex (Q : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (pOut pIn : Fin 1 → Fin 4 → ℝ)
    (kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) (μ : Fin 1 → Fin 4) :
    onePIPart Q Φ D 1 1 1 pOut pIn kIn αOut βIn μ =
      QED.WickModel.onePIFunction (ctParams Q Φ D) 1 1 1 pOut pIn kIn αOut βIn μ -
        QED.WickModel.onePIFunction (ctParams Q Φ D) 1 1 0 pOut pIn kIn αOut βIn μ := by
  rw [← QED.WickModel.onePIFunction₂_eq_onePIFunction _ 1 1 1 (by norm_num),
    ← QED.WickModel.onePIFunction₂_eq_onePIFunction _ 1 1 0 (by norm_num)]
  have key := QED.ChainProof.Quick.sum_range_filter_order_sub (fun N => (N.factorial : ℂ)⁻¹)
    (fun N κ => ∑ C ∈ (Finset.univ : Finset (Contraction 1 1 κ)).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) *
        QED.WickModel.contractionValue₂ (ctParams Q Φ D) C pOut pIn kIn αOut βIn μ) 0
  refine Eq.trans ?_ key.symm
  unfold onePIPart
  rw [selectedPart_eq_sum_order_of_le_three Q Φ D 1 1 (fun C => IsOnePI C) 1 (by norm_num)]
  refine Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ hκ => ?_)
  by_cases h1 : ∑ t, (κ t).order = 1
  · rw [ite_eq_left h1, ite_eq_left h1]
    refine Finset.sum_congr rfl fun C hC => ?_
    rw [contractionValue_zero_eq_of_reaches Q Φ D C
      (reaches_of_one_one (by omega) C (Finset.mem_filter.1 hC).2)]
  · rw [ite_eq_right h1, ite_eq_right h1]

/-- **The order-`e` graded vertex is the tree** `e γ^μ`, at every regulator and all momenta. -/
theorem vertexPart_zero_apply (Q : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (p' p : Fin 4 → ℝ) (μ i j : Fin 4) :
    vertexPart Q Φ D f 0 p' p μ i j = (Q.e : ℂ) * Dirac.gamma μ i j := by
  simp only [vertexPart, Matrix.of_apply]
  rw [show 2 * 0 + 1 = 1 from rfl, onePIPart_one_vertex Q { Φ with openLine := f } D,
    onePIFunction_one_one_one, onePIFunction_one_one_zero]
  simp only [ctParams, sub_zero]
  field_simp

end QED.GradedProof.X1F

end
