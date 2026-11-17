/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.ContractionValue
public import QED.Frozen.TwoLoop.LoopCount
public import QED.Frozen.WickModel.ContractionValue
import QED.TwoLoop.ChordLoopLine
import QED.TwoLoop.JointIntegral

/-!
# One-loop contractions have their packet 6a value

The content of packet T1's theorem goal (T₁₃) (decision D-38): for a contraction with at most one
chord, the value (T₁₀) is the frozen value (X₂₇).

* `QED.TwoLoop.lineMomentum₂_eq_lineMomentum`: when the chords are the loop lines and every chord
  carries `ℓ`, the routing (T₄) is the one-loop routing (X₂₂) at `ℓ`.
* `QED.TwoLoop.regulatedAmplitude_eq_regulatedAmplitude₂`: (T₈) at the routing (X₂₂) is (X₂₆).
* `QED.TwoLoop.contractionValue₂_eq_contractionValue_of_loopCount_le_one`: (T₁₃) with explicit
  binders.
-/

public section

open Complex

namespace QED.TwoLoop

open QED.WickModel

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

open scoped Classical in
/-- **The routing with loop momenta is the one-loop routing** when the chords are the loop lines
and every chord carries `ℓ`. -/
theorem lineMomentum₂_eq_lineMomentum {C : Contraction nf nA κ}
    (hiff : ∀ f : Line C, IsChord f ↔ IsLoopLine f) {L : ℕ} (ℓ' : Fin L → Fin 4 → ℝ)
    (ℓ : Fin 4 → ℝ) (hℓ : ∀ g : Line C, IsChord g → chordMomentum ℓ' g = ℓ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) :
    lineMomentum₂ C pOut pIn kIn ℓ' = lineMomentum C pOut pIn kIn ℓ := by
  funext f
  unfold lineMomentum₂ lineMomentum
  by_cases hf : IsChord f
  · rw [ite_eq_left hf, ite_eq_left ((hiff f).1 hf), hℓ f hf]
  · rw [ite_eq_right hf, ite_eq_right (mt (hiff f).2 hf)]
    have hS : {g : Line C | g = f ∨ IsChord g} = {g | g = f ∨ IsLoopLine g} := by
      ext g
      simp [hiff]
    rw [hS]
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    refine Finset.sum_congr (Finset.filter_congr fun g _ => hiff g) fun g hg => ?_
    have hg : IsChord g := (hiff g).2 (by simpa using hg)
    rw [hℓ g hg]

/-- (T₈) at the one-loop routing (X₂₂) is (X₂₆). -/
theorem regulatedAmplitude_eq_regulatedAmplitude₂ (P : Params) (C : Contraction nf nA κ)
    (pOut pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    regulatedAmplitude P C pOut pIn kIn ℓ αOut βIn μ =
      regulatedAmplitude₂ P C pIn kIn (lineMomentum C pOut pIn kIn ℓ) αOut βIn μ :=
  rfl

open scoped Classical in
/-- **(T₁₃) One-loop contractions have their packet 6a value**: for every contraction with at
most one chord, connected or not, the value (T₁₀) is the frozen value (X₂₇). -/
theorem contractionValue₂_eq_contractionValue_of_loopCount_le_one (P : Params)
    (C : Contraction nf nA κ) (hC : loopCount C ≤ 1) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) :
    contractionValue₂ P C pOut pIn kIn αOut βIn μ =
      contractionValue P C pOut pIn kIn αOut βIn μ := by
  have hiff := isChord_iff_isLoopLine hC
  have key : ∀ L, loopCount C = L →
      jointEnergyFirstIntegral L (fun ℓ : Fin L → Fin 4 → ℝ =>
        (((2 * Real.pi) ^ (4 * L) : ℝ) : ℂ)⁻¹ *
          regulatedAmplitude₂ P C pIn kIn (lineMomentum₂ C pOut pIn kIn ℓ) αOut βIn μ) =
        contractionValue P C pOut pIn kIn αOut βIn μ := by
    intro L hL
    obtain rfl | rfl : L = 0 ∨ L = 1 := by omega
    · have hnc : ∀ g : Line C, ¬ IsChord g := by
        intro g hg
        have := card_chordsBelow_lt hg
        omega
      rw [jointEnergyFirstIntegral_zero, lineMomentum₂_eq_lineMomentum hiff _ 0
        (fun g hg => absurd hg (hnc g))]
      unfold contractionValue
      rw [ite_eq_right (fun ⟨f, hf⟩ => hnc f ((hiff f).2 hf))]
      simp only [mul_zero, pow_zero, Complex.ofReal_one, inv_one, one_mul]
      exact (regulatedAmplitude_eq_regulatedAmplitude₂ P C pOut pIn kIn 0 αOut βIn μ).symm
    · obtain ⟨g, hg⟩ : ∃ g : Line C, IsChord g := by
        by_contra h
        push Not at h
        unfold loopCount at hL
        simp [h] at hL
      unfold contractionValue
      rw [ite_eq_left ⟨g, (hiff g).1 hg⟩, ← jointEnergyFirstIntegral_one_eq]
      refine congrArg (jointEnergyFirstIntegral 1) (funext fun ℓ => ?_)
      rw [mul_one, lineMomentum₂_eq_lineMomentum hiff ℓ (ℓ 0) fun g hg => ?_]
      · exact congrArg _ (regulatedAmplitude_eq_regulatedAmplitude₂ P C pOut pIn kIn (ℓ 0) αOut
          βIn μ).symm
      · have h := card_chordsBelow_lt hg
        rw [hL] at h
        unfold chordMomentum
        rw [dite_eq_left h]
        congr 1
        exact Subsingleton.elim _ _
  exact key _ rfl

end QED.TwoLoop

end
