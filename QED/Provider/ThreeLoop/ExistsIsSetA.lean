/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.TwoLoop.LoopCount
public import QED.TwoLoop.EnumerationGauge5
public import QED.TwoLoop.EnumerationDecide
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Provider for `QED.ThreeLoop.exists_isSetA`

Proves the frozen theorem goal (MA₁) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.ThreeLoop.exists_isSetA`, with the binder convention of decision D-13 (no binders).
The representative `QED.Provider.ThreeLoop.SetARep.repA` of seven gauge vertices is the one-loop
vertex with the vertex-type two-loop bubble on its photon: open line `y → 0 → 1 → 2 → x`, fermion
loop `3 → 4 → 5 → 6 → 3`, external photon at `1`, photon lines `2 — 3`, `0 — 5`, `4 — 6`. That it
satisfies (A₁), is 1PI (X₁₈) and has three loops (T₂) is checked by kernel evaluation, through the
decision procedures of `QED.TwoLoop.Enumeration`. This module must never import the frozen anchor.
-/

@[expose] public section

namespace QED.Provider.ThreeLoop.SetARep

open QED.WickModel QED.TwoLoop.Enumeration QED.ThreeLoop

/-- The fermion vertex of the gauge vertex `t`. -/
def fv7 (t : Fin 7) : Wick.FermionVertex (gauges 7) := ⟨t, fun h => Wick.VertexKind.noConfusion h⟩

/-- The photon field of the gauge vertex `t`. -/
def ps7 (t : Fin 7) : Wick.PhotonSlot (gauges 7) := ⟨t, ⟨0, Nat.one_pos⟩⟩

/-- The fermion pairing: open line `y → 0 → 1 → 2 → x`; loop `3 → 4 → 5 → 6 → 3`. -/
def sigmaA : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 7)) :=
  [Sum.inl 0, .inr (fv7 2), .inr (fv7 1), .inr (fv7 0)].formPerm *
    [Sum.inr (fv7 3), .inr (fv7 4), .inr (fv7 5), .inr (fv7 6)].formPerm

/-- The photon pairing: external photon at `1`; photon lines `2 — 3`, `0 — 5`, `4 — 6`. -/
def tauA : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot (gauges 7)) :=
  Equiv.swap (.inl 0) (.inr (ps7 1)) * Equiv.swap (.inr (ps7 2)) (.inr (ps7 3)) *
    Equiv.swap (.inr (ps7 0)) (.inr (ps7 5)) * Equiv.swap (.inr (ps7 4)) (.inr (ps7 6))

theorem tauA_invol : ∀ b, tauA (tauA b) = b ∧ tauA b ≠ b := by decide +kernel

/-- The set (a) representative. -/
def repA : Contraction 1 1 (gauges 7) := ⟨(sigmaA, tauA), tauA_invol⟩

theorem repA_isSetA : IsSetA repA := by
  refine ⟨fv7 2, fv7 1, fv7 0, ps7 2, ps7 1, ps7 0, ps7 3, ps7 5, ?_⟩
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl, ?_, ?_, Or.inr ⟨fv7 3, fv7 5, ?_⟩⟩
  all_goals decide +kernel

theorem repA_isOnePI : IsOnePI repA := by decide +kernel

theorem repA_loopCount : loopCount repA = 3 := by
  rw [loopCount_eq_card]
  decide +kernel

end QED.Provider.ThreeLoop.SetARep

namespace QED.Provider.ThreeLoop

open QED.WickModel QED.ThreeLoop SetARep

/-- (MA₁) (decision D-13 convention; no binders). -/
theorem exists_isSetA :
    ∃ C : Contraction 1 1 (fun _ : Fin 7 => Wick.VertexKind.gauge),
      IsOnePI C ∧ IsSetA C ∧ loopCount C = 3 :=
  ⟨repA, repA_isOnePI, repA_isSetA, repA_loopCount⟩

end QED.Provider.ThreeLoop

end
