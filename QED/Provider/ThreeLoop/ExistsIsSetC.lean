/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetC
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.TwoLoop.LoopCount
public import QED.TwoLoop.EnumerationGauge5
public import QED.TwoLoop.EnumerationDecide
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Provider for `QED.ThreeLoop.exists_isSetC`

Proves the frozen theorem goal (MC₁) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.ThreeLoop.exists_isSetC`, with the binder convention of decision D-13 (no binders).
The representative `QED.Provider.ThreeLoop.SetCRep.repC` of seven gauge vertices is the two-loop
ladder with the one-loop bubble on its outer photon: open line `y → 4 → 3 → 2 → 1 → 0 → x`, bubble
`5 ⇄ 6`, external photon at `2`, inner rung `1 — 3`, outer rung `0 — 5`, `6 — 4`. It has no
counterterm vertex, so (Sc₃) holds for every grading; that it satisfies (Sc₃), is 1PI (X₁₈) and has
three loops (T₂) is checked by kernel evaluation, through the decision procedures of
`QED.TwoLoop.Enumeration`. This module must never import the frozen anchor.
-/

@[expose] public section

namespace QED.Provider.ThreeLoop.SetCRep

open QED.WickModel QED.TwoLoop.Enumeration QED.ThreeLoop

/-- The fermion vertex of the gauge vertex `t`. -/
def fv7 (t : Fin 7) : Wick.FermionVertex (gauges 7) := ⟨t, fun h => Wick.VertexKind.noConfusion h⟩

/-- The photon field of the gauge vertex `t`. -/
def ps7 (t : Fin 7) : Wick.PhotonSlot (gauges 7) := ⟨t, ⟨0, Nat.one_pos⟩⟩

/-- The fermion pairing: open line `y → 4 → 3 → 2 → 1 → 0 → x`; bubble `5 ⇄ 6`. -/
def sigmaC : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 7)) :=
  [Sum.inl 0, .inr (fv7 0), .inr (fv7 1), .inr (fv7 2), .inr (fv7 3), .inr (fv7 4)].formPerm *
    [Sum.inr (fv7 5), .inr (fv7 6)].formPerm

/-- The photon pairing: external photon at `2`; inner rung `1 — 3`; outer rung `0 — 5`, `6 — 4`. -/
def tauC : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot (gauges 7)) :=
  Equiv.swap (.inl 0) (.inr (ps7 2)) * Equiv.swap (.inr (ps7 1)) (.inr (ps7 3)) *
    Equiv.swap (.inr (ps7 0)) (.inr (ps7 5)) * Equiv.swap (.inr (ps7 6)) (.inr (ps7 4))

theorem tauC_invol : ∀ b, tauC (tauC b) = b ∧ tauC b ≠ b := by decide +kernel

/-- The set (c) representative. -/
def repC : Contraction 1 1 (gauges 7) := ⟨(sigmaC, tauC), tauC_invol⟩

theorem repC_isSetC (g : Graded.Grading (gauges 7)) : IsSetC repC g := by
  refine ⟨fun t _ => absurd rfl t.2, Or.inr (Or.inl ⟨fv7 5, fv7 6, ?_⟩)⟩
  decide +kernel

theorem repC_isOnePI : IsOnePI repC := by decide +kernel

theorem repC_loopCount : loopCount repC = 3 := by
  rw [loopCount_eq_card]
  decide +kernel

end QED.Provider.ThreeLoop.SetCRep

namespace QED.Provider.ThreeLoop

open QED.WickModel QED.ThreeLoop SetCRep

/-- (MC₁) (decision D-13 convention; no binders). -/
theorem exists_isSetC :
    ∃ C : Contraction 1 1 (fun _ : Fin 7 => Wick.VertexKind.gauge),
      ∀ g : Graded.Grading (fun _ : Fin 7 => Wick.VertexKind.gauge),
        IsOnePI C ∧ IsSetC C g ∧ loopCount C = 3 :=
  ⟨repC, fun g => ⟨repC_isOnePI, repC_isSetC g, repC_loopCount⟩⟩

end QED.Provider.ThreeLoop

end
