/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CValIn
public import QED.GradedProof.X0Reduce
public import QED.Frozen.Graded.SelfEnergyPartTwoExistsUnique
public import QED.Frozen.Graded.VacuumPolarizationPartTwoExistsUnique
public import QED.Frozen.Graded.JointEnergyFirstIntegrableConnectedPartFive

/-!
# (X₁) piece C: (T₉′) of the order-`e⁴` pieces and of the order-`e⁵` vertex graphs

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C. The value lemmas `contractionValue_glueIn`, `contractionValue_glueOut`,
`contractionValue_glueP` take (T₉′) of each piece integrand at every bridge index (`hT₁`,
`hT₂`). This file states those inputs, in exactly that form, for the pieces covered by sealed
goals, from the hypotheses of (X₁):

* `t9_selfEnergy_four`: a 1PI self-energy contraction at graded order `4` (the sealed (G-Σ₂),
  first clause; its Pauli–Villars sums are over all flavours, `t9_sum_coeff`, `t9_sum_coeff_mass`
  derive them from the block sums of (X₁));
* `t9_vacuumPolarization_four`: a 1PI two-photon contraction at graded order `4` (the sealed
  (G-Π₂), first clause);
* `t9_vertex_five`: an attached connected vertex contraction at graded order `5` (the sealed
  (X₀));
* `t9_grading_eq_zero`: below graded order `4` the grading is `0` (a counterterm vertex of level
  `≥ 1` has graded order `≥ 4`).

Trees need nothing: `QED.GradedProof.X0.jointEnergyFirstIntegrable_of_loopCount_eq_zero`.
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Params Contraction loopCount lineMomentum₂ IsOnePI VerticesConnected
  ExternalsAttached)
open QED.Graded

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-! ### The Pauli–Villars sums over all flavours -/

section PV

variable {F : Type} [Fintype F] [DecidableEq F] (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)

include hrep in
/-- A sum that vanishes on every class of an idempotent `rep` vanishes. -/
theorem t9_sum_eq_zero_of_blocks (c : F → ℝ)
    (h : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), c f = 0) :
    ∑ f, c f = 0 := by
  rw [← Finset.sum_fiberwise Finset.univ rep c]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : rep b = b
  · exact h b hb
  · refine Finset.sum_eq_zero fun f hf => absurd ?_ hb
    have hf' : rep f = b := (Finset.mem_filter.1 hf).2
    rw [← hf', hrep]

include hrep in
/-- The first Pauli–Villars condition over all flavours. -/
theorem t9_sum_coeff (Φ : Lepton.Flavors F)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0) :
    ∑ f, Φ.coeff f = 0 :=
  t9_sum_eq_zero_of_blocks rep hrep _ hPV₁

include hrep in
/-- The second Pauli–Villars condition over all flavours. -/
theorem t9_sum_coeff_mass (Φ : Lepton.Flavors F)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0) :
    ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0 :=
  t9_sum_eq_zero_of_blocks rep hrep _ hPV₂

end PV

/-! ### Small graded orders -/

/-- **Below graded order `4` the grading is `0`.** -/
theorem t9_grading_eq_zero {g : Grading κ} (hg : gradedOrder κ g ≤ 3) : g = 0 := by
  by_contra h0
  obtain ⟨t, ht⟩ := QED.GradedProof.exists_level_of_ne_zero h0
  have h1 := Finset.single_le_sum (f := fun t : CtVertex κ => 2 * g t) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ t)
  have h2 := Finset.single_le_sum (f := fun t => (κ t).order) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ t.1)
  have h3 : 2 ≤ (κ t.1).order := by
    have := t.2
    revert this
    cases κ t.1 <;> decide
  unfold gradedOrder at hg
  omega

theorem t9_fin_one_eq (α : Fin 1 → Fin 4) : α = ![α 0] := by
  funext i
  fin_cases i
  rfl

/-! ### The sealed sources -/

variable (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
  (D : Counterterms F)

/-- **(T₉′) of a 1PI self-energy piece of graded order `4`** (sealed (G-Σ₂), first clause), in
the form of `hT₂` of `contractionValue_glueIn` and `contractionValue_glueOut`. -/
theorem t9_selfEnergy_four (hε : 0 < P.ε) (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (C : Contraction 1 0 κ) (hC : IsOnePI C) (g : Grading κ) (hg : gradedOrder κ g = 4)
    (p : Fin 4 → ℝ) (αOut βIn : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![p] ![]
        (lineMomentum₂ C ![p] ![p] ![] ℓ) αOut βIn ![] := by
  rw [t9_fin_one_eq αOut, t9_fin_one_eq βIn]
  exact (selfEnergyPart_two_existsUnique P Φ D Φ.openLine m₀ hm₀ hmass hmγ hΛ
    (t9_sum_coeff rep hrep Φ hPV₁) (t9_sum_coeff_mass rep hrep Φ hPV₂)).1 P.ε hε N κ g hg C hC
    p (αOut 0) (βIn 0)

/-- **(T₉′) of a 1PI vacuum-polarization piece of graded order `4`** (sealed (G-Π₂), first
clause), in the form of `hT₂` of `contractionValue_glueP`. -/
theorem t9_vacuumPolarization_four (hε : 0 < P.ε) (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    (C : Contraction 0 2 κ) (hC : IsOnePI C) (g : Grading κ) (hg : gradedOrder κ g = 4)
    (k : Fin 4 → ℝ) (μ ν : Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![] ![k, -k]
        (lineMomentum₂ C ![] ![] ![k, -k] ℓ) ![] ![] ![μ, ν] :=
  (vacuumPolarizationPart_two_existsUnique P Φ D rep m₀ hm₀ hmass hmγ hΛ hrep hPV₁ hPV₂ hD).1
    P.ε hε N κ g hg C hC k μ ν

/-- **(T₉′) of an attached connected vertex contraction of graded order `5`** (sealed (X₀)), in
the form of `hT₁` of the value lemmas. -/
theorem t9_vertex_five (hε : 0 < P.ε) (rep : F → F) (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : ∀ f, D.d₁ f 0 = D.d₁ (rep f) 0 ∧ D.d₂ f 0 = D.d₂ (rep f) 0 ∧
      D.dm f 0 = D.dm (rep f) 0)
    (C : Contraction 1 1 κ) (hA : ExternalsAttached C) (hV : VerticesConnected C)
    (g : Grading κ) (hg : gradedOrder κ g = 5) {r' r q : Fin 4 → ℝ} (hmom : r' = r + q)
    (αOut βIn μ : Fin 1 → Fin 4) :
    QED.TwoLoop.jointEnergyFirstIntegrable (loopCount C) fun ℓ =>
      twoPiInv (loopCount C) * regulatedAmplitude P Φ D C g ![r] ![q]
        (lineMomentum₂ C ![r'] ![r] ![q] ℓ) αOut βIn μ :=
  jointEnergyFirstIntegrable_connectedPart_five P Φ D rep hε hrep hPV₁ hPV₂ hD g hg C ⟨hA, hV⟩
    ![r'] ![r] ![q] (by simpa using hmom) αOut βIn μ

end QED.GradedProof.X1C

end
