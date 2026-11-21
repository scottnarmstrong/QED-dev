/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.Graded.GradedOrder
public import QED.ChainProof.EnumReps

/-!
# The nine representatives of the set (a) family

Helper for the Phase 5 Stage 3a enumeration (decision D-58, the obligation stated in the
docstring of (A₁) `QED.ThreeLoop.IsSetA`). The graded contractions `(κ, g, C)` of graded order
`7` satisfying (A₁) fall into nine relabelling classes; this file gives a representative of each,
with its grading and its (A₁) witness, and checks by kernel evaluation that it satisfies (A₁), is
one-particle irreducible, has graded order `7`, and has the stated loop number and fermionic sign.

Vertices are numbered as in `QED.ChainProof.Enum` (set (b)): `c = 0`, `b = 1`, `a = 2` along the
open line `Ψ̄(y) → c → b → a → Ψ(x)` (external photon at `b`), then the insertion. In a closed
loop, `u = 3` carries the field `x` (photon partner of `a`) and `w = 4` the field `y` (photon
partner of `c`); the loop is listed as the cycle `[3, …]` of the fermion pairing.

* `repVA`, `repVB`, `repVC` (seven `gauge` vertices; internal photon `5 ⇄ 6`; loops
  `[3, 4, 5, 6]`, `[3, 5, 4, 6]`, `[3, 5, 6, 4]`): the two-loop bubble with a self-energy on one
  line (`VA`, `VC`) and the vertex-type bubble (`VB`); three loops, grading `0`.
* `repFA`, `repFB` (`fermionCt` at `5`; loops `[3, 4, 5]`, `[3, 5, 4]`): the level-`0` `δ₂`, `δ_m`
  counterterm on one or the other line of the one-loop bubble; two loops, grading `0`.
* `repGW`, `repGU` (`gaugeCt` at `w = 4`, resp. `u = 3`; loop `[3, 4]`): the level-`0` `δ₁`
  counterterm at the field `y`, resp. `x`; two loops, grading `0`.
* `repP s` (`photonCt` at `3`, `x` its field `s`, `y` its field `s.rev`): the level-`1` photon
  counterterm; one loop, grading `1` at vertex `3`.

The (A₁) witnesses are `witV`, …, `witP s` (`SetAWitness`).
-/

@[expose] public section

namespace QED.ChainProof.SetALink

open QED.WickModel QED.TwoLoop.Enumeration QED.ChainProof.Enum

/-! ### Witnesses -/

/-- The data of (A₁) for a contraction: the open line `a, b, c`, the photon fields `sa`, `sb`,
`sc` of its vertices, and the ends `x`, `y` of the insertion. -/
structure SetAWitness {N : ℕ} (κ : Fin N → Wick.VertexKind) where
  /-- the vertex contracted with the external `Ψ(x)` -/
  a : Wick.FermionVertex κ
  /-- the middle vertex of the open line -/
  b : Wick.FermionVertex κ
  /-- the vertex contracted with the external `Ψ̄(y)` -/
  c : Wick.FermionVertex κ
  /-- the photon field of `a` -/
  sa : Wick.PhotonSlot κ
  /-- the photon field of `b`, contracted with the external photon -/
  sb : Wick.PhotonSlot κ
  /-- the photon field of `c` -/
  sc : Wick.PhotonSlot κ
  /-- the insertion field paired with `sa` -/
  x : Wick.PhotonSlot κ
  /-- the insertion field paired with `sc` -/
  y : Wick.PhotonSlot κ

/-- The pairing of the external photon with `sb`, of `sa` with `x` and of `sc` with `y`. -/
def openTau {N : ℕ} {κ : Fin N → Wick.VertexKind} (W : SetAWitness κ) :
    Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ) :=
  Equiv.swap (.inl 0) (.inr W.sb) * Equiv.swap (.inr W.sa) (.inr W.x) *
    Equiv.swap (.inr W.sc) (.inr W.y)

/-! ### Kind sequences -/

/-- Seven gauge vertices. -/
def kV : Fin 7 → Wick.VertexKind := fun _ => .gauge

/-- Five gauge vertices and a `fermionCt` vertex at `5`. -/
def kF : Fin 6 → Wick.VertexKind := ![.gauge, .gauge, .gauge, .gauge, .gauge, .fermionCt]

/-- Four gauge vertices and a `gaugeCt` vertex at `4` (the vertex `w`). -/
def kGW : Fin 5 → Wick.VertexKind := ![.gauge, .gauge, .gauge, .gauge, .gaugeCt]

/-- Four gauge vertices and a `gaugeCt` vertex at `3` (the vertex `u`). -/
def kGU : Fin 5 → Wick.VertexKind := ![.gauge, .gauge, .gauge, .gaugeCt, .gauge]

/-- Three gauge vertices and a `photonCt` vertex at `3`. -/
def kP : Fin 4 → Wick.VertexKind := ![.gauge, .gauge, .gauge, .photonCt]

/-! ### The witnesses -/

/-- The witness of `repVA`, `repVB`, `repVC`. -/
def witV : SetAWitness kV :=
  ⟨fv kV 2, fv kV 1, fv kV 0, pg kV 2, pg kV 1, pg kV 0, pg kV 3, pg kV 4⟩

/-- The witness of `repFA`, `repFB`. -/
def witF : SetAWitness kF :=
  ⟨fv kF 2, fv kF 1, fv kF 0, pg kF 2, pg kF 1, pg kF 0, pg kF 3, pg kF 4⟩

/-- The witness of `repGW`. -/
def witGW : SetAWitness kGW :=
  ⟨fv kGW 2, fv kGW 1, fv kGW 0, pg kGW 2, pg kGW 1, pg kGW 0, pg kGW 3, pg kGW 4⟩

/-- The witness of `repGU`. -/
def witGU : SetAWitness kGU :=
  ⟨fv kGU 2, fv kGU 1, fv kGU 0, pg kGU 2, pg kGU 1, pg kGU 0, pg kGU 3, pg kGU 4⟩

/-- The witness of `repP s`: `x` is the field `s` of the `photonCt` vertex, `y` the other. -/
def witP (s : Fin 2) : SetAWitness kP :=
  ⟨fv kP 2, fv kP 1, fv kP 0, pg kP 2, pg kP 1, pg kP 0, pc kP 3 s, pc kP 3 s.rev⟩

/-! ### The photon pairings -/

/-- The photon pairing of `repVA`, `repVB`, `repVC`: the open pairs and the internal photon. -/
def tauV : Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot kV) :=
  openTau witV * Equiv.swap (.inr (pg kV 5)) (.inr (pg kV 6))

theorem tauV_invol : ∀ x, tauV (tauV x) = x ∧ tauV x ≠ x := by
  decide +kernel

theorem tauF_invol : ∀ x, openTau witF (openTau witF x) = x ∧ openTau witF x ≠ x := by
  decide +kernel

theorem tauGW_invol : ∀ x, openTau witGW (openTau witGW x) = x ∧ openTau witGW x ≠ x := by
  decide +kernel

theorem tauGU_invol : ∀ x, openTau witGU (openTau witGU x) = x ∧ openTau witGU x ≠ x := by
  decide +kernel

theorem tauP_invol : ∀ s x, openTau (witP s) (openTau (witP s) x) = x ∧
    openTau (witP s) x ≠ x := by
  decide +kernel

/-! ### The representatives -/

/-- **`VA`**: the self-energy on the line `w → u` of the bubble (loop `3 → 4 → 5 → 6 → 3`). -/
def repVA : Contraction 1 1 kV :=
  ⟨(openPerm witV.a witV.b witV.c *
      [Sum.inr (fv kV 3), .inr (fv kV 4), .inr (fv kV 5), .inr (fv kV 6)].formPerm, tauV),
    tauV_invol⟩

/-- **`VB`**: the vertex-type two-loop bubble (loop `3 → 5 → 4 → 6 → 3`). -/
def repVB : Contraction 1 1 kV :=
  ⟨(openPerm witV.a witV.b witV.c *
      [Sum.inr (fv kV 3), .inr (fv kV 5), .inr (fv kV 4), .inr (fv kV 6)].formPerm, tauV),
    tauV_invol⟩

/-- **`VC`**: the self-energy on the line `u → w` of the bubble (loop `3 → 5 → 6 → 4 → 3`). -/
def repVC : Contraction 1 1 kV :=
  ⟨(openPerm witV.a witV.b witV.c *
      [Sum.inr (fv kV 3), .inr (fv kV 5), .inr (fv kV 6), .inr (fv kV 4)].formPerm, tauV),
    tauV_invol⟩

/-- **`FA`**: the fermion counterterm on the line `w → u` (loop `3 → 4 → 5 → 3`). -/
def repFA : Contraction 1 1 kF :=
  ⟨(openPerm witF.a witF.b witF.c *
      [Sum.inr (fv kF 3), .inr (fv kF 4), .inr (fv kF 5)].formPerm, openTau witF), tauF_invol⟩

/-- **`FB`**: the fermion counterterm on the line `u → w` (loop `3 → 5 → 4 → 3`). -/
def repFB : Contraction 1 1 kF :=
  ⟨(openPerm witF.a witF.b witF.c *
      [Sum.inr (fv kF 3), .inr (fv kF 5), .inr (fv kF 4)].formPerm, openTau witF), tauF_invol⟩

/-- **`GW`**: the vertex counterterm at `y` (loop `3 ⇄ 4`, `gaugeCt` at `4`). -/
def repGW : Contraction 1 1 kGW :=
  ⟨(openPerm witGW.a witGW.b witGW.c * [Sum.inr (fv kGW 3), .inr (fv kGW 4)].formPerm,
    openTau witGW), tauGW_invol⟩

/-- **`GU`**: the vertex counterterm at `x` (loop `3 ⇄ 4`, `gaugeCt` at `3`). -/
def repGU : Contraction 1 1 kGU :=
  ⟨(openPerm witGU.a witGU.b witGU.c * [Sum.inr (fv kGU 3), .inr (fv kGU 4)].formPerm,
    openTau witGU), tauGU_invol⟩

/-- **`P s`**: the photon counterterm, its field `s` towards `a`. -/
def repP (s : Fin 2) : Contraction 1 1 kP :=
  ⟨(openPerm (witP s).a (witP s).b (witP s).c, openTau (witP s)), tauP_invol s⟩

/-- The grading of `repP s`: level `1` at the `photonCt` vertex. -/
def gradP : Graded.Grading kP := fun _ => 1

/-! ### Graded order -/

theorem gradedOrder_kV : Graded.gradedOrder kV 0 = 7 := by decide +kernel

theorem gradedOrder_kF : Graded.gradedOrder kF 0 = 7 := by decide +kernel

theorem gradedOrder_kGW : Graded.gradedOrder kGW 0 = 7 := by decide +kernel

theorem gradedOrder_kGU : Graded.gradedOrder kGU 0 = 7 := by decide +kernel

theorem gradedOrder_kP : Graded.gradedOrder kP gradP = 7 := by decide +kernel

/-! ### The predicate (A₁) -/

theorem isSetA_repVA : QED.ThreeLoop.IsSetA repVA := by
  refine ⟨witV.a, witV.b, witV.c, witV.sa, witV.sb, witV.sc, witV.x, witV.y, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, rfl, by decide +kernel,
    by decide +kernel, Or.inr ⟨fv kV 3, fv kV 4, rfl, rfl, ?_⟩⟩
  decide +kernel

theorem isSetA_repVB : QED.ThreeLoop.IsSetA repVB := by
  refine ⟨witV.a, witV.b, witV.c, witV.sa, witV.sb, witV.sc, witV.x, witV.y, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, rfl, by decide +kernel,
    by decide +kernel, Or.inr ⟨fv kV 3, fv kV 4, rfl, rfl, ?_⟩⟩
  decide +kernel

theorem isSetA_repVC : QED.ThreeLoop.IsSetA repVC := by
  refine ⟨witV.a, witV.b, witV.c, witV.sa, witV.sb, witV.sc, witV.x, witV.y, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, rfl, by decide +kernel,
    by decide +kernel, Or.inr ⟨fv kV 3, fv kV 4, rfl, rfl, ?_⟩⟩
  decide +kernel

theorem isSetA_repFA : QED.ThreeLoop.IsSetA repFA := by
  refine ⟨witF.a, witF.b, witF.c, witF.sa, witF.sb, witF.sc, witF.x, witF.y, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, rfl, by decide +kernel,
    by decide +kernel, Or.inr ⟨fv kF 3, fv kF 4, rfl, rfl, ?_⟩⟩
  decide +kernel

theorem isSetA_repFB : QED.ThreeLoop.IsSetA repFB := by
  refine ⟨witF.a, witF.b, witF.c, witF.sa, witF.sb, witF.sc, witF.x, witF.y, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, rfl, by decide +kernel,
    by decide +kernel, Or.inr ⟨fv kF 3, fv kF 4, rfl, rfl, ?_⟩⟩
  decide +kernel

theorem isSetA_repGW : QED.ThreeLoop.IsSetA repGW := by
  refine ⟨witGW.a, witGW.b, witGW.c, witGW.sa, witGW.sb, witGW.sc, witGW.x, witGW.y, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, rfl, by decide +kernel,
    by decide +kernel, Or.inr ⟨fv kGW 3, fv kGW 4, rfl, rfl, ?_⟩⟩
  decide +kernel

theorem isSetA_repGU : QED.ThreeLoop.IsSetA repGU := by
  refine ⟨witGU.a, witGU.b, witGU.c, witGU.sa, witGU.sb, witGU.sc, witGU.x, witGU.y, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, by decide +kernel, rfl, rfl, by decide +kernel,
    by decide +kernel, Or.inr ⟨fv kGU 3, fv kGU 4, rfl, rfl, ?_⟩⟩
  decide +kernel

theorem isSetA_repP (s : Fin 2) : QED.ThreeLoop.IsSetA (repP s) := by
  refine ⟨(witP s).a, (witP s).b, (witP s).c, (witP s).sa, (witP s).sb, (witP s).sc,
    (witP s).x, (witP s).y, ?_⟩
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl, ?_, ?_, Or.inl ⟨rfl, rfl, ?_, ?_⟩⟩
  all_goals revert s; decide +kernel

/-! ### One-particle irreducibility, loops and signs -/

theorem isOnePI_repVA : IsOnePI repVA := by decide +kernel

theorem isOnePI_repVB : IsOnePI repVB := by decide +kernel

theorem isOnePI_repVC : IsOnePI repVC := by decide +kernel

theorem isOnePI_repFA : IsOnePI repFA := by decide +kernel

theorem isOnePI_repFB : IsOnePI repFB := by decide +kernel

theorem isOnePI_repGW : IsOnePI repGW := by decide +kernel

theorem isOnePI_repGU : IsOnePI repGU := by decide +kernel

theorem isOnePI_repP : ∀ s, IsOnePI (repP s) := by decide +kernel

theorem loopCount_repVA : loopCount repVA = 3 := by
  rw [loopCount_eq_card]
  decide +kernel

theorem loopCount_repVB : loopCount repVB = 3 := by
  rw [loopCount_eq_card]
  decide +kernel

theorem loopCount_repVC : loopCount repVC = 3 := by
  rw [loopCount_eq_card]
  decide +kernel

theorem loopCount_repFA : loopCount repFA = 2 := by
  rw [loopCount_eq_card]
  decide +kernel

theorem loopCount_repFB : loopCount repFB = 2 := by
  rw [loopCount_eq_card]
  decide +kernel

theorem loopCount_repGW : loopCount repGW = 2 := by
  rw [loopCount_eq_card]
  decide +kernel

theorem loopCount_repGU : loopCount repGU = 2 := by
  rw [loopCount_eq_card]
  decide +kernel

theorem loopCount_repP (s : Fin 2) : loopCount (repP s) = 1 := by
  rw [loopCount_eq_card]
  revert s
  decide +kernel

theorem fermionSign_repVA : fermionSign repVA = -1 := by decide +kernel

theorem fermionSign_repVB : fermionSign repVB = -1 := by decide +kernel

theorem fermionSign_repVC : fermionSign repVC = -1 := by decide +kernel

theorem fermionSign_repFA : fermionSign repFA = -1 := by decide +kernel

theorem fermionSign_repFB : fermionSign repFB = -1 := by decide +kernel

theorem fermionSign_repGW : fermionSign repGW = -1 := by decide +kernel

theorem fermionSign_repGU : fermionSign repGU = -1 := by decide +kernel

theorem fermionSign_repP : ∀ s, fermionSign (repP s) = 1 := by decide +kernel

end QED.ChainProof.SetALink

end
