/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.OnePIPart
public import QED.Frozen.Graded.ConnectedPart
public import QED.Frozen.Lepton.OnePIFunction
public import QED.Frozen.WickModel.ConnectedFunction
public import QED.GradedProof.Embed
public import QED.GradedProof.LoopCycle
import QED.ChainProof.QuickMeaning
import QED.TwoLoop.OneLoopEmbedding
import QED.TwoLoop.LoopBound

/-!
# The embedding goals with one-loop counterterms only

Helper proofs of the Phase 5 Stage 2 goals (E-G₁) `QED.Graded.onePIPart_eq_onePIFunction₂_sub`
and (E-G₅) `QED.Graded.connectedPart_eq_connectedFunction_sub` (decision D-57), as
`QED.GradedProof.onePIPart_eq_onePIFunction₂_sub'` and
`QED.GradedProof.connectedPart_eq_connectedFunction_sub'`.

* `contractionValue_eq_zero_of_level`: with no data at the levels `≥ 1`, a term (G₅) with a
  nonzero grading vanishes, since one of its vertex factors (V₁₉) has all coefficients `0`.
* So the order part (G₆) is a sum at the zero grading (`selectedPart_eq_sum_order`), and in the
  ranges of the goals every counterterm vertex lies on an external fermion line
  (`ctReaches_of_isOnePI`, `ctReaches_of_connected`), where the graded value is (F₇) with the
  counterterms of `P` (`contractionValue_zero_eq`).
* For (E-G₅), at T1's flavours (F₇) is (T₁₀) (`rfl`), which with at most one loop is (X₂₇).
-/

@[expose] public section

open Complex
open QED.WickModel (Params Contraction IsOnePI ExternalsAttached VerticesConnected fermionSign)
open QED.Graded

namespace QED.GradedProof

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- A counterterm vertex factor (V₁₉) with all coefficients `0` vanishes. -/
theorem vertexFactor_zero (e m : ℝ) (α β : Wick.FermionVertex κ → Fin 4)
    (lor : Wick.PhotonSlot κ → Fin 4) (kψ : Wick.FermionVertex κ → Fin 4 → ℝ)
    (kA : Wick.PhotonSlot κ → Fin 4 → ℝ) (t : Fin N) (h : κ t ≠ .gauge) :
    Wick.vertexFactor e 0 0 0 0 m α β lor kψ kA t = 0 := by
  unfold Wick.vertexFactor
  split <;> rename_i h' <;> simp_all

/-- A graded amplitude (G₃) with a counterterm vertex whose level has no data vanishes. -/
theorem contractionAmplitude_eq_zero (P : Params) {F : Type} (Φ : Lepton.Flavors F)
    (D : Counterterms F) (C : Contraction nf nA κ) (φ : Flavoring F κ) (g : Grading κ)
    (t : CtVertex κ) (h : ∀ f, D.d₁ f (g t) = 0 ∧ D.d₂ f (g t) = 0 ∧ D.dm f (g t) = 0)
    (h₃ : D.d₃ (g t) = 0) (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : QED.WickModel.Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionAmplitude P Φ D C φ g pIn kIn k αOut βIn μ = 0 := by
  unfold contractionAmplitude
  refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun β _ =>
    Finset.sum_eq_zero fun lor _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ t.1), zero_mul, zero_mul, mul_zero]
  have h' : ∀ f, D.d₁ f (g ⟨t.1, t.2⟩) = 0 ∧ D.d₂ f (g ⟨t.1, t.2⟩) = 0 ∧
      D.dm f (g ⟨t.1, t.2⟩) = 0 := h
  dsimp only
  simp only [t.2, ↓reduceDIte, (h' _).1, (h' _).2.1, (h' _).2.2, h₃, mul_zero]
  exact vertexFactor_zero _ _ _ _ _ _ _ _ t.2

/-- **With no data at the levels `≥ 1`, a term with a nonzero grading vanishes.** -/
theorem contractionValue_eq_zero_of_level (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F)
    (hD : ∀ f k, 1 ≤ k → D.d₁ f k = 0 ∧ D.d₂ f k = 0 ∧ D.dm f k = 0)
    (hD₃ : ∀ k, 1 ≤ k → D.d₃ k = 0) (C : Contraction nf nA κ) (g : Grading κ) (hg : g ≠ 0)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    contractionValue P Φ D C g pOut pIn kIn αOut βIn μ = 0 := by
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hg
  have hk : 1 ≤ g t := Nat.one_le_iff_ne_zero.2 ht
  have hr : ∀ k, regulatedAmplitude P Φ D C g pIn kIn k αOut βIn μ = 0 := fun k =>
    Finset.sum_eq_zero fun φ _ => by
      rw [contractionAmplitude_eq_zero P Φ D C φ g t (fun f => hD f _ hk) (hD₃ _ hk), mul_zero]
  unfold contractionValue
  simp only [hr, mul_zero]
  simp [QED.TwoLoop.jointEnergyFirstIntegral]

open scoped Classical in
/-- (E-G₁) **The graded 1PI part with one-loop counterterms only is the order part of (F₈).** -/
theorem onePIPart_eq_onePIFunction₂_sub' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (hmass : Φ.mass Φ.openLine = P.m)
    (h₁ : P.δ₁ = P.e ^ 2 * D.d₁ Φ.openLine 0) (h₂ : P.δ₂ = P.e ^ 2 * D.d₂ Φ.openLine 0)
    (hm : P.δm = P.e ^ 2 * D.dm Φ.openLine 0) (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0)
    (hD : ∀ f k, 1 ≤ k → D.d₁ f k = 0 ∧ D.d₂ f k = 0 ∧ D.dm f k = 0)
    (hD₃ : ∀ k, 1 ≤ k → D.d₃ k = 0) (nf nA K : ℕ) (hnf : 1 ≤ nf)
    (hK : K + 1 ≤ 2 * nf + nA + 3) (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    onePIPart P Φ D nf nA (K + 1) pOut pIn kIn αOut βIn μ =
      Lepton.onePIFunction₂ P Φ nf nA (K + 1) pOut pIn kIn αOut βIn μ -
        Lepton.onePIFunction₂ P Φ nf nA K pOut pIn kIn αOut βIn μ := by
  have key := QED.ChainProof.Quick.sum_range_filter_order_sub (fun N => (N.factorial : ℂ)⁻¹)
    (fun N κ => ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter IsOnePI,
      ((fermionSign C : ℤ) : ℂ) * Lepton.contractionValue₂ P Φ C pOut pIn kIn αOut βIn μ) K
  unfold Lepton.onePIFunction₂
  refine Eq.trans ?_ key.symm
  unfold onePIPart
  rw [selectedPart_eq_sum_order P Φ D nf nA (fun C => IsOnePI C) (K + 1) pOut pIn kIn αOut βIn μ
    fun g _ hg C _ => contractionValue_eq_zero_of_level P Φ D hD hD₃ C g hg _ _ _ _ _ _]
  refine Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ hκ => ?_)
  by_cases h : ∑ t, (κ t).order = K + 1
  · rw [ite_eq_left h, ite_eq_left h]
    refine Finset.sum_congr rfl fun C hC => ?_
    have hR := ctReaches_of_isOnePI (Finset.mem_filter.1 hC).2 hnf (by omega)
    rw [contractionValue_zero_eq P P Φ D C hR rfl rfl rfl rfl (fun _ _ => h₁)
      (fun _ _ => ⟨h₂, hm, hmass.symm⟩) (fun _ _ => h₃)]
  · rw [ite_eq_right h, ite_eq_right h]

open scoped Classical in
/-- (E-G₅) **The graded connected part with T1's flavours and one-loop counterterms only is the
order part of (X₂₉).** -/
theorem connectedPart_eq_connectedFunction_sub' (P : Params) (D : Counterterms (Fin 3))
    (h₁ : P.δ₁ = P.e ^ 2 * D.d₁ 0 0) (h₂ : P.δ₂ = P.e ^ 2 * D.d₂ 0 0)
    (hm : P.δm = P.e ^ 2 * D.dm 0 0) (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0)
    (hD : ∀ f k, 1 ≤ k → D.d₁ f k = 0 ∧ D.d₂ f k = 0 ∧ D.dm f k = 0)
    (hD₃ : ∀ k, 1 ≤ k → D.d₃ k = 0) (nf nA K : ℕ) (hK : K + 1 ≤ 2 * nf + nA + 1)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) :
    connectedPart P ⟨P.mass, P.loopCoeff, 0⟩ D nf nA (K + 1) pOut pIn kIn αOut βIn μ =
      WickModel.connectedFunction P nf nA (K + 1) pOut pIn kIn αOut βIn μ -
        WickModel.connectedFunction P nf nA K pOut pIn kIn αOut βIn μ := by
  have key := QED.ChainProof.Quick.sum_range_filter_order_sub (fun N => (N.factorial : ℂ)⁻¹)
    (fun N κ => ∑ C ∈ (Finset.univ : Finset (Contraction nf nA κ)).filter
      (fun C => ExternalsAttached C ∧ VerticesConnected C),
      ((fermionSign C : ℤ) : ℂ) * WickModel.contractionValue P C pOut pIn kIn αOut βIn μ) K
  unfold WickModel.connectedFunction
  refine Eq.trans ?_ key.symm
  unfold connectedPart
  rw [selectedPart_eq_sum_order P ⟨P.mass, P.loopCoeff, 0⟩ D nf nA
    (fun C => ExternalsAttached C ∧ VerticesConnected C) (K + 1) pOut pIn kIn αOut βIn μ
    fun g _ hg C _ => contractionValue_eq_zero_of_level P _ D hD hD₃ C g hg _ _ _ _ _ _]
  refine Finset.sum_congr rfl fun N _ => congrArg _ (Finset.sum_congr rfl fun κ hκ => ?_)
  by_cases h : ∑ t, (κ t).order = K + 1
  · rw [ite_eq_left h, ite_eq_left h]
    refine Finset.sum_congr (Finset.ext fun C => by simp only [Finset.mem_filter]) fun C hC => ?_
    obtain ⟨hA, hV⟩ := (Finset.mem_filter.1 hC).2
    have hR := ctReaches_of_connected hA hV (by omega)
    rw [contractionValue_zero_eq P P ⟨P.mass, P.loopCoeff, 0⟩ D C hR rfl rfl rfl rfl
      (fun _ _ => h₁) (fun _ _ => ⟨h₂, hm, rfl⟩) (fun _ _ => h₃),
      QED.ChainProof.contractionValue₂_params',
      QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one P C
        (QED.TwoLoop.LoopBound.loopCount_le_one_of_connected h.le hK hA hV)]
  · rw [ite_eq_right h, ite_eq_right h]

end QED.GradedProof

end
