/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.EnumWitness
public import QED.TwoLoop.EnumerationDecide

/-!
# The nine representatives of the set (b) chain family

Helper for obligation O3-4 of `docs/HIGHER-LOOP-PLAN.md` (decision D-53). The contractions
satisfying (C₁) `QED.VPChain.IsVPChain 2` fall into nine relabelling classes; this file gives a
representative of each, with its chain witness, and checks by kernel evaluation that it satisfies
the body of (C₁), is one-particle irreducible, and has the stated loop number and fermionic sign.

Vertices are numbered `c = 0`, `b = 1`, `a = 2` along the open line `Ψ̄(y) → c → b → a → Ψ(x)`
(external photon at `b`), followed by the vertices of the first insertion (the one next to `a`)
and then of the second. A bubble insertion has two gauge vertices, the first (`u`) facing `a`; a
`δ₃` insertion is one `photonCt` vertex whose field `s` faces `a` (the other field `s.rev` faces
`c`).

* `repBB` (seven gauge vertices; bubbles `3 ⇄ 4`, `5 ⇄ 6`): three loops, sign `+1`.
* `repBD s` (bubble `3 ⇄ 4`, `photonCt` at `5`): two loops, sign `-1`; `s : Fin 2`.
* `repDB s` (`photonCt` at `3`, bubble `4 ⇄ 5`): two loops, sign `-1`.
* `repDD s₀ s₁` (`photonCt` at `3` and `4`): one loop, sign `+1`.

They are collected by vertex number in `QED.ChainProof.Enum.repsOf N` (`N = 5, 6, 7`), with
their properties in `repsOf_props`. The representatives of the drafter's check
(`Check/Rep.lean` of the Stage 1a scratch) are `repBB`, `repBD 0` and `repDD 0 0`.
-/

@[expose] public section

namespace QED.ChainProof.Enum

open QED.WickModel QED.TwoLoop.Enumeration

/-! ### Fields and pairings -/

/-- The fermion vertex `t` of `κ`. -/
def fv {N : ℕ} (κ : Fin N → Wick.VertexKind) (t : Fin N) (h : κ t ≠ .photonCt := by decide) :
    Wick.FermionVertex κ := ⟨t, h⟩

/-- The photon field of a gauge vertex `t` of `κ`. -/
def pg {N : ℕ} (κ : Fin N → Wick.VertexKind) (t : Fin N) (h : 0 < (κ t).photonSlots := by decide) :
    Wick.PhotonSlot κ := ⟨t, ⟨0, h⟩⟩

/-- The photon field `s` of a `photonCt` vertex `t` of `κ`. -/
def pc {N : ℕ} (κ : Fin N → Wick.VertexKind) (t : Fin N) (s : Fin 2)
    (h : (κ t).photonSlots = 2 := by decide) : Wick.PhotonSlot κ := ⟨t, Fin.cast h.symm s⟩

/-- The open line `Ψ̄(y) → c → b → a → Ψ(x)`: `x ↦ a ↦ b ↦ c ↦ x` on the `Ψ̄`-to-`Ψ` pairing. -/
def openPerm {N : ℕ} {κ : Fin N → Wick.VertexKind} (a b c : Wick.FermionVertex κ) :
    Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ) :=
  [Sum.inl 0, .inr a, .inr b, .inr c].formPerm

/-- The pairing of the external photon with `sb` and the three chain lines. -/
def chainTau {N : ℕ} {κ : Fin N → Wick.VertexKind} (sb : Wick.PhotonSlot κ)
    (src dst : Fin 3 → Wick.PhotonSlot κ) : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ) :=
  Equiv.swap (.inl 0) (.inr sb) * Equiv.swap (.inr (src 0)) (.inr (dst 0)) *
    Equiv.swap (.inr (src 1)) (.inr (dst 1)) * Equiv.swap (.inr (src 2)) (.inr (dst 2))

/-! ### Kind sequences -/

/-- Seven gauge vertices. -/
def kBB : Fin 7 → Wick.VertexKind := fun _ => .gauge

/-- Five gauge vertices and a `photonCt` vertex at `5`. -/
def kBD : Fin 6 → Wick.VertexKind := ![.gauge, .gauge, .gauge, .gauge, .gauge, .photonCt]

/-- Five gauge vertices and a `photonCt` vertex at `3`. -/
def kDB : Fin 6 → Wick.VertexKind := ![.gauge, .gauge, .gauge, .photonCt, .gauge, .gauge]

/-- Three gauge vertices and `photonCt` vertices at `3` and `4`. -/
def kDD : Fin 5 → Wick.VertexKind := ![.gauge, .gauge, .gauge, .photonCt, .photonCt]

/-! ### The witnesses -/

/-- The witness of `repBB`: lines `2 — 3`, `4 — 5`, `6 — 0`. -/
def wBB : ChainWitness 2 kBB :=
  ⟨fv kBB 2, fv kBB 1, fv kBB 0, pg kBB 1, ![pg kBB 2, pg kBB 4, pg kBB 6],
    ![pg kBB 3, pg kBB 5, pg kBB 0]⟩

/-- The witness of `repBD s`: lines `2 — 3`, `4 — 5ₛ`, `5ₛ' — 0`. -/
def wBD (s : Fin 2) : ChainWitness 2 kBD :=
  ⟨fv kBD 2, fv kBD 1, fv kBD 0, pg kBD 1, ![pg kBD 2, pg kBD 4, pc kBD 5 s.rev],
    ![pg kBD 3, pc kBD 5 s, pg kBD 0]⟩

/-- The witness of `repDB s`: lines `2 — 3ₛ`, `3ₛ' — 4`, `5 — 0`. -/
def wDB (s : Fin 2) : ChainWitness 2 kDB :=
  ⟨fv kDB 2, fv kDB 1, fv kDB 0, pg kDB 1, ![pg kDB 2, pc kDB 3 s.rev, pg kDB 5],
    ![pc kDB 3 s, pg kDB 4, pg kDB 0]⟩

/-- The witness of `repDD s₀ s₁`: lines `2 — 3ₛ₀`, `3ₛ₀' — 4ₛ₁`, `4ₛ₁' — 0`. -/
def wDD (s₀ s₁ : Fin 2) : ChainWitness 2 kDD :=
  ⟨fv kDD 2, fv kDD 1, fv kDD 0, pg kDD 1, ![pg kDD 2, pc kDD 3 s₀.rev, pc kDD 4 s₁.rev],
    ![pc kDD 3 s₀, pc kDD 4 s₁, pg kDD 0]⟩

/-! ### The representatives -/

theorem tauBB_invol : ∀ x, chainTau wBB.sb wBB.src wBB.dst (chainTau wBB.sb wBB.src wBB.dst x) = x ∧
    chainTau wBB.sb wBB.src wBB.dst x ≠ x := by
  decide +kernel

theorem tauBD_invol : ∀ s x, chainTau (wBD s).sb (wBD s).src (wBD s).dst
    (chainTau (wBD s).sb (wBD s).src (wBD s).dst x) = x ∧
    chainTau (wBD s).sb (wBD s).src (wBD s).dst x ≠ x := by
  decide +kernel

theorem tauDB_invol : ∀ s x, chainTau (wDB s).sb (wDB s).src (wDB s).dst
    (chainTau (wDB s).sb (wDB s).src (wDB s).dst x) = x ∧
    chainTau (wDB s).sb (wDB s).src (wDB s).dst x ≠ x := by
  decide +kernel

theorem tauDD_invol : ∀ s₀ s₁ x, chainTau (wDD s₀ s₁).sb (wDD s₀ s₁).src (wDD s₀ s₁).dst
    (chainTau (wDD s₀ s₁).sb (wDD s₀ s₁).src (wDD s₀ s₁).dst x) = x ∧
    chainTau (wDD s₀ s₁).sb (wDD s₀ s₁).src (wDD s₀ s₁).dst x ≠ x := by
  decide +kernel

/-- **Bubble–bubble.** -/
def repBB : Contraction 1 1 kBB :=
  ⟨(openPerm wBB.a wBB.b wBB.c * [Sum.inr (fv kBB 3), .inr (fv kBB 4)].formPerm *
      [Sum.inr (fv kBB 5), .inr (fv kBB 6)].formPerm,
    chainTau wBB.sb wBB.src wBB.dst), tauBB_invol⟩

/-- **Bubble–`δ₃`**, field `s` of the `photonCt` vertex towards `a`. -/
def repBD (s : Fin 2) : Contraction 1 1 kBD :=
  ⟨(openPerm (wBD s).a (wBD s).b (wBD s).c * [Sum.inr (fv kBD 3), .inr (fv kBD 4)].formPerm,
    chainTau (wBD s).sb (wBD s).src (wBD s).dst), tauBD_invol s⟩

/-- **`δ₃`–bubble**, field `s` of the `photonCt` vertex towards `a`. -/
def repDB (s : Fin 2) : Contraction 1 1 kDB :=
  ⟨(openPerm (wDB s).a (wDB s).b (wDB s).c * [Sum.inr (fv kDB 4), .inr (fv kDB 5)].formPerm,
    chainTau (wDB s).sb (wDB s).src (wDB s).dst), tauDB_invol s⟩

/-- **`δ₃`–`δ₃`**, fields `s₀`, `s₁` of the two `photonCt` vertices towards `a`. -/
def repDD (s₀ s₁ : Fin 2) : Contraction 1 1 kDD :=
  ⟨(openPerm (wDD s₀ s₁).a (wDD s₀ s₁).b (wDD s₀ s₁).c,
    chainTau (wDD s₀ s₁).sb (wDD s₀ s₁).src (wDD s₀ s₁).dst), tauDD_invol s₀ s₁⟩

/-! ### The body of (C₁) -/

theorem chainBody_iff {N : ℕ} {κ : Fin N → Wick.VertexKind} (n : ℕ) (C : Contraction 1 1 κ)
    (W : ChainWitness n κ) :
    ChainBody n C W ↔
      κ W.a.1 = .gauge ∧ κ W.b.1 = .gauge ∧ κ W.c.1 = .gauge ∧
      C.1.1 (.inl 0) = .inr W.a ∧ C.1.1 (.inr W.a) = .inr W.b ∧ C.1.1 (.inr W.b) = .inr W.c ∧
      C.1.1 (.inr W.c) = .inl 0 ∧ W.sb.1 = W.b.1 ∧ C.1.2 (.inl 0) = .inr W.sb ∧
      (W.src 0).1 = W.a.1 ∧ (W.dst (Fin.last n)).1 = W.c.1 ∧
      (∀ i, C.1.2 (.inr (W.src i)) = .inr (W.dst i)) ∧
      (∀ i : Fin n, InsClause C (W.dst i.castSucc) (W.src i.succ)) ∧
      ∀ t : Fin N, t = W.a.1 ∨ t = W.b.1 ∨ t = W.c.1 ∨
        ∃ i : Fin n, t = (W.dst i.castSucc).1 ∨ t = (W.src i.succ).1 := by
  constructor
  · rintro ⟨ka, kb, kc, s0a, sab, sbc, sc0, sbv, tsb, src0, dstn, line, ins, exh⟩
    exact ⟨ka, kb, kc, s0a, sab, sbc, sc0, sbv, tsb, src0, dstn, line, ins, exh⟩
  · rintro ⟨ka, kb, kc, s0a, sab, sbc, sc0, sbv, tsb, src0, dstn, line, ins, exh⟩
    exact ⟨ka, kb, kc, s0a, sab, sbc, sc0, sbv, tsb, src0, dstn, line, ins, exh⟩

theorem chainBody_repBB : ChainBody 2 repBB wBB := by
  rw [chainBody_iff]
  unfold InsClause
  decide +kernel

theorem chainBody_repBD (s : Fin 2) : ChainBody 2 (repBD s) (wBD s) := by
  rw [chainBody_iff]
  unfold InsClause
  fin_cases s <;> decide +kernel

theorem chainBody_repDB (s : Fin 2) : ChainBody 2 (repDB s) (wDB s) := by
  rw [chainBody_iff]
  unfold InsClause
  fin_cases s <;> decide +kernel

theorem chainBody_repDD (s₀ s₁ : Fin 2) : ChainBody 2 (repDD s₀ s₁) (wDD s₀ s₁) := by
  rw [chainBody_iff]
  unfold InsClause
  fin_cases s₀ <;> fin_cases s₁ <;> decide +kernel

/-! ### One-particle irreducibility, loops and signs -/

theorem isOnePI_repBB : IsOnePI repBB := by decide +kernel

theorem isOnePI_repBD : ∀ s, IsOnePI (repBD s) := by decide +kernel

theorem isOnePI_repDB : ∀ s, IsOnePI (repDB s) := by decide +kernel

theorem isOnePI_repDD : ∀ s₀ s₁, IsOnePI (repDD s₀ s₁) := by decide +kernel

theorem loopCount_repBB : loopCount repBB = 3 := by
  rw [loopCount_eq_card]
  decide +kernel

theorem loopCount_repBD (s : Fin 2) : loopCount (repBD s) = 2 := by
  rw [loopCount_eq_card]
  revert s
  decide +kernel

theorem loopCount_repDB (s : Fin 2) : loopCount (repDB s) = 2 := by
  rw [loopCount_eq_card]
  revert s
  decide +kernel

theorem loopCount_repDD (s₀ s₁ : Fin 2) : loopCount (repDD s₀ s₁) = 1 := by
  rw [loopCount_eq_card]
  revert s₀ s₁
  decide +kernel

theorem fermionSign_repBB : fermionSign repBB = 1 := by decide +kernel

theorem fermionSign_repBD : ∀ s, fermionSign (repBD s) = -1 := by decide +kernel

theorem fermionSign_repDB : ∀ s, fermionSign (repDB s) = -1 := by decide +kernel

theorem fermionSign_repDD : ∀ s₀ s₁, fermionSign (repDD s₀ s₁) = 1 := by decide +kernel

end QED.ChainProof.Enum

end
