/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.WickVertex

/-!
# Three gauge vertices

Names for the vertex sequence of three `gauge` vertices, which carries the one-loop part of the
Wick vertex `QED.Wick.wickVertex` (packet 5, decision D-20): the sequence `gauge3`, its fermion
vertices `fv t`, and its photon fields `ps t`. The vertex-correction contractions are described by
the predicate `IsChain C a b c`. The fermion line runs from the external `Ψ̄(y)` through the
vertices `c`, `b`, `a` to the external `Ψ(x)`; the external photon attaches at `b`; and an internal
photon joins `a` and `c`.
-/

@[expose] public section

namespace QED.Wick

/-- The vertex sequence of three `gauge` vertices. -/
abbrev gauge3 : Fin 3 → VertexKind := fun _ => .gauge

/-- Vertex `t` of `gauge3` as a fermion vertex. -/
def fv (t : Fin 3) : FermionVertex gauge3 := ⟨t, by simp⟩

/-- The photon field of vertex `t` of `gauge3`. -/
def ps (t : Fin 3) : PhotonSlot gauge3 := ⟨t, ⟨0, by simp [VertexKind.photonSlots]⟩⟩

/-- The contraction `C` of `gauge3` is the vertex correction with fermion order `c → b → a`: the
external `Ψ(x)` is contracted with `Ψ̄_a`, `Ψ_a` with `Ψ̄_b`, `Ψ_b` with `Ψ̄_c`, and `Ψ_c` with the
external `Ψ̄(y)`; the external `A(z)` is contracted with the photon of `b`, and the photons of `a`
and `c` with each other. -/
def IsChain (C : Contraction gauge3) (a b c : Fin 3) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    C.1.1 none = some (fv a) ∧ C.1.1 (some (fv a)) = some (fv b) ∧
    C.1.1 (some (fv b)) = some (fv c) ∧ C.1.1 (some (fv c)) = none ∧
    C.1.2 none = some (ps b) ∧ C.1.2 (some (ps a)) = some (ps c)

end QED.Wick

end
