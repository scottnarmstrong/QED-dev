/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.WickModel.IsOnePI
public import QED.Frozen.TwoLoop.LoopCount
public import QED.TwoLoop.EnumerationDecide
public import QED.TwoLoop.EnumerationRelabel

/-!
# A genuine three-loop set (b) contraction (M₄)

Helper proof of the Phase 5 Stage 1a theorem goal (M₄) `QED.VPChain.exists_isVPChain_two`
(decision D-53): the bubble–bubble representative `QED.ChainProof.Quick.repBB` of seven gauge
vertices, with the open line `y → 0 → 1 → 2 → x`, the external photon at `1`, the bubbles `3 ⇄ 4`
and `5 ⇄ 6`, and the photon lines `2 — 3`, `4 — 5`, `6 — 0`, satisfies the chain predicate (C₁) with
`n = 2`, is 1PI (X₁₈) and has three loops (T₂). Each fact is checked by kernel evaluation, through
the decision procedures of `QED.TwoLoop.Enumeration`.

* `QED.ChainProof.exists_isVPChain_two'`: the exact statement of (M₄).
-/

@[expose] public section

namespace QED.ChainProof.Quick

open QED.WickModel QED.TwoLoop.Enumeration QED.VPChain

/-- The fermion vertex of the gauge vertex `t`. -/
def fv7 (t : Fin 7) : Wick.FermionVertex (gauges 7) := ⟨t, fun h => Wick.VertexKind.noConfusion h⟩

/-- The photon field of the gauge vertex `t`. -/
def ps7 (t : Fin 7) : Wick.PhotonSlot (gauges 7) := ⟨t, ⟨0, Nat.one_pos⟩⟩

/-- The fermion pairing: open line `y → 0 → 1 → 2 → x`; bubbles `3 ⇄ 4`, `5 ⇄ 6`. -/
def sigmaBB : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex (gauges 7)) :=
  [Sum.inl 0, .inr (fv7 2), .inr (fv7 1), .inr (fv7 0)].formPerm *
    [Sum.inr (fv7 3), .inr (fv7 4)].formPerm * [Sum.inr (fv7 5), .inr (fv7 6)].formPerm

/-- The photon pairing: external photon at `1`; photon lines `2 — 3`, `4 — 5`, `6 — 0`. -/
def tauBB : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot (gauges 7)) :=
  Equiv.swap (.inl 0) (.inr (ps7 1)) * Equiv.swap (.inr (ps7 2)) (.inr (ps7 3)) *
    Equiv.swap (.inr (ps7 4)) (.inr (ps7 5)) * Equiv.swap (.inr (ps7 6)) (.inr (ps7 0))

theorem tauBB_invol : ∀ b, tauBB (tauBB b) = b ∧ tauBB b ≠ b := by decide +kernel

/-- The bubble–bubble representative of set (b). -/
def repBB : Contraction 1 1 (gauges 7) := ⟨(sigmaBB, tauBB), tauBB_invol⟩

theorem repBB_isVPChain : IsVPChain 2 repBB := by
  refine ⟨fv7 2, fv7 1, fv7 0, ps7 1, ![ps7 2, ps7 4, ps7 6], ![ps7 3, ps7 5, ps7 0], ?_⟩
  decide +kernel

theorem repBB_isOnePI : IsOnePI repBB := by decide +kernel

theorem repBB_loopCount : loopCount repBB = 3 := by
  rw [loopCount_eq_card]
  decide +kernel

end QED.ChainProof.Quick

namespace QED.ChainProof

open QED.WickModel QED.VPChain Quick

/-- (M₄) **Set (b) has a genuine three-loop member.** -/
theorem exists_isVPChain_two' :
    ∃ C : Contraction 1 1 (fun _ : Fin 7 => Wick.VertexKind.gauge),
      IsOnePI C ∧ IsVPChain 2 C ∧ loopCount C = 3 :=
  ⟨repBB, repBB_isOnePI, repBB_isVPChain, repBB_loopCount⟩

end QED.ChainProof

end
