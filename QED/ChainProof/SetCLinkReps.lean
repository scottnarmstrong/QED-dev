/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.EnumReps
public import QED.Frozen.ThreeLoop.IsSetC
public import QED.Frozen.Graded.GradedOrder
public import QED.Frozen.Wick.VertexKindOrder

/-!
# Set (c), model link: the 56 representatives of the set (c) family

Helper for the set (c) headline (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(decision D-58), the enumeration step (question Q7: the orbit counts are proof obligations, not
frozen goals). Set (c) at graded order `7` has 39 graphs and 56 relabelling orbits; this file gives
one representative `(κ, g, C)` of each orbit and checks by kernel evaluation that it is
one-particle irreducible, satisfies (Sc₃) `QED.ThreeLoop.IsSetC`, has graded order `7`, and has
the stated fermionic sign (its coefficient in the family vertex, the `1/N!` being cancelled by
the `N!` relabellings of the orbit).

Vertices are numbered along the open line from the external `Ψ(x)`: the fermion pairing runs
`Ψ(x) → 0 → 1 → ⋯ → L - 1 → Ψ̄(y)`; the element follows (a bubble `L ⇄ L + 1`, or a `photonCt`
vertex `L` whose field `s` faces the first end of the photon line carrying it).

* **`repB i`**, `i : Fin 12` (seven `gauge` vertices): the six two-loop vertex skeletons other
  than the vacuum-polarization one, with the bubble on either photon line (`skE`, …, `skT`):
  ladder, crossed, two corner, two self-energy graphs. Sign `-1`.
* **`repD i s`**, `i : Fin 12`, `s : Fin 2` (five `gauge` vertices and a level-`0` `photonCt`):
  the same with the `δ₃` element. 24 orbits, sign `+1`.
* **`repCB0`, …, `repCB4`** and **`repCD0 s`, …, `repCD4 s`**: the one-loop vertex with one
  level-`0` counterterm on its open line (`fermionCt` on either internal line, `gaugeCt` at
  either end or in the middle) and the bubble or `δ₃` on its photon. 5 and 10 orbits, signs
  `-1` and `+1`.
* **`repS0`, …, `repS4`**: the one-loop vertex with one level-`1` counterterm on its open
  line and no element (the VP-share counterterm graphs). Sign `+1`.

So `12 + 24 + 5 + 10 + 5 = 56` orbits, from `12 + 12 + 5 + 5 + 5 = 39` graphs. That every
1PI set (c) contraction of graded order `7` is a relabelling of exactly one of these (the
classification) is a separate step.
-/

@[expose] public section

open QED.WickModel QED.TwoLoop.Enumeration
open QED.ChainProof.Enum (fv pg pc)

namespace QED.ChainProof.SetCLink

/-! ### Builders -/

/-- The fermion pairing with open line `Ψ(x) → line → Ψ̄(y)` and closed loop `loop`. -/
def mkSigma {N : ℕ} {κ : Fin N → Wick.VertexKind} (line loop : List (Wick.FermionVertex κ)) :
    Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ) :=
  (Sum.inl 0 :: line.map Sum.inr).formPerm * (loop.map Sum.inr).formPerm

/-- The photon pairing: the external photon with `ext`, and the listed internal lines. -/
def mkTau {N : ℕ} {κ : Fin N → Wick.VertexKind} (ext : Wick.PhotonSlot κ)
    (lines : List (Wick.PhotonSlot κ × Wick.PhotonSlot κ)) :
    Equiv.Perm (Fin 1 ⊕ Wick.PhotonSlot κ) :=
  Equiv.swap (.inl 0) (.inr ext) * (lines.map fun l => Equiv.swap (.inr l.1) (.inr l.2)).prod

/-! ### The two-loop skeletons -/

/-- The position of the external photon on the five-vertex open line, by skeleton. Skeletons
`0, 1` ladder, `2, 3` crossed, `4, 5` and `8, 9` corner, `6, 7` and `10, 11` self-energy; in each
pair the element is on the other photon line. -/
def skE : Fin 12 → Fin 5 := ![2, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3]

/-- The ends of the photon line carrying the element (`skP — skQ`) and of the other photon line
(`skR — skT`). -/
def skP : Fin 12 → Fin 5 := ![0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1]

/-- See `skP`. -/
def skQ : Fin 12 → Fin 5 := ![4, 3, 3, 4, 3, 4, 4, 3, 2, 4, 4, 2]

/-- See `skP`. -/
def skR : Fin 12 → Fin 5 := ![1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0]

/-- See `skP`. -/
def skT : Fin 12 → Fin 5 := ![3, 4, 4, 3, 4, 3, 3, 4, 4, 2, 2, 4]

/-- Five gauge vertices on the open line and a bubble. -/
def kB : Fin 7 → Wick.VertexKind := fun _ => .gauge

/-- Five gauge vertices on the open line and a `photonCt` vertex. -/
def kD : Fin 6 → Wick.VertexKind := ![.gauge, .gauge, .gauge, .gauge, .gauge, .photonCt]

/-- The level-`0` grading. -/
def gZero {N : ℕ} (κ : Fin N → Wick.VertexKind) : Graded.Grading κ := fun _ => 0

/-- The level-`1` grading. -/
def gOne {N : ℕ} (κ : Fin N → Wick.VertexKind) : Graded.Grading κ := fun _ => 1

/-- The fermion vertex `t` of `kB`. -/
def fvB (t : Fin 7) : Wick.FermionVertex kB := ⟨t, fun h => Wick.VertexKind.noConfusion h⟩

/-- The photon field of vertex `t` of `kB`. -/
def pgB (t : Fin 7) : Wick.PhotonSlot kB := ⟨t, ⟨0, Nat.one_pos⟩⟩

/-- The photon field of the open-line vertex `t` of `kB`. -/
def plB (t : Fin 5) : Wick.PhotonSlot kB := pgB (Fin.castLE (by norm_num) t)

theorem kD_photonSlots : ∀ t : Fin 5, 0 < (kD (Fin.castSucc t)).photonSlots := by decide

/-- The photon field of the open-line vertex `t` of `kD`. -/
def plD (t : Fin 5) : Wick.PhotonSlot kD := ⟨Fin.castSucc t, ⟨0, kD_photonSlots t⟩⟩

theorem tauB_invol : ∀ (i : Fin 12) x,
    mkTau (plB (skE i)) [(plB (skP i), pgB 5), (pgB 6, plB (skQ i)), (plB (skR i), plB (skT i))]
      (mkTau (plB (skE i))
        [(plB (skP i), pgB 5), (pgB 6, plB (skQ i)), (plB (skR i), plB (skT i))] x) = x ∧
    mkTau (plB (skE i))
      [(plB (skP i), pgB 5), (pgB 6, plB (skQ i)), (plB (skR i), plB (skT i))] x ≠ x := by
  decide +kernel

/-- **The bubble on a two-loop skeleton** (12 orbits). -/
def repB (i : Fin 12) : Contraction 1 1 kB :=
  ⟨(mkSigma [fvB 0, fvB 1, fvB 2, fvB 3, fvB 4] [fvB 5, fvB 6],
    mkTau (plB (skE i)) [(plB (skP i), pgB 5), (pgB 6, plB (skQ i)),
      (plB (skR i), plB (skT i))]), tauB_invol i⟩

theorem tauD_invol : ∀ (i : Fin 12) (s : Fin 2) x,
    mkTau (plD (skE i)) [(plD (skP i), pc kD 5 s), (pc kD 5 s.rev, plD (skQ i)),
      (plD (skR i), plD (skT i))]
      (mkTau (plD (skE i)) [(plD (skP i), pc kD 5 s), (pc kD 5 s.rev, plD (skQ i)),
        (plD (skR i), plD (skT i))] x) = x ∧
    mkTau (plD (skE i)) [(plD (skP i), pc kD 5 s), (pc kD 5 s.rev, plD (skQ i)),
      (plD (skR i), plD (skT i))] x ≠ x := by
  decide +kernel

/-- **The `δ₃` element on a two-loop skeleton**, field `s` towards `skP i` (24 orbits). -/
def repD (i : Fin 12) (s : Fin 2) : Contraction 1 1 kD :=
  ⟨(mkSigma [fv kD 0, fv kD 1, fv kD 2, fv kD 3, fv kD 4] [],
    mkTau (plD (skE i)) [(plD (skP i), pc kD 5 s), (pc kD 5 s.rev, plD (skQ i)),
      (plD (skR i), plD (skT i))]), tauD_invol i s⟩

/-! ### Checks for the two-loop skeletons -/

theorem isOnePI_repB : ∀ i, IsOnePI (repB i) := by decide +kernel

theorem isOnePI_repD : ∀ i s, IsOnePI (repD i s) := by decide +kernel

theorem fermionSign_repB : ∀ i, fermionSign (repB i) = -1 := by decide +kernel

theorem fermionSign_repD : ∀ i s, fermionSign (repD i s) = 1 := by decide +kernel

theorem gradedOrder_kB (g : Graded.Grading kB) : Graded.gradedOrder kB g = 7 := by
  unfold Graded.gradedOrder
  have : ∀ t : Graded.CtVertex kB, False := fun t => t.2 rfl
  simp only [Finset.univ_eq_empty_iff.mpr ⟨this⟩, Finset.sum_empty, add_zero]
  decide +kernel

theorem gradedOrder_kD : Graded.gradedOrder kD (gZero kD) = 7 := by decide +kernel

theorem isSetC_repB (i : Fin 12) (g : Graded.Grading kB) : ThreeLoop.IsSetC (repB i) g := by
  refine ⟨fun t _ => absurd rfl t.2, Or.inr (Or.inl ⟨fvB 5, fvB 6, ?_⟩)⟩
  revert i
  decide +kernel

theorem isSetC_repD (i : Fin 12) (s : Fin 2) : ThreeLoop.IsSetC (repD i s) (gZero kD) := by
  refine ⟨fun _ _ => rfl, Or.inl ⟨5, rfl, ?_⟩⟩
  revert i s
  decide +kernel

/-! ### One counterterm on the open line of the one-loop vertex -/
/-- Placement `0` (`fermionCt` on the internal line from `0`), with a bubble. -/
def kCB0 : Fin 6 → Wick.VertexKind := ![.gauge, .fermionCt, .gauge, .gauge, .gauge, .gauge]

/-- Placement `0`, with a `photonCt` vertex. -/
def kCD0 : Fin 5 → Wick.VertexKind := ![.gauge, .fermionCt, .gauge, .gauge, .photonCt]

/-- Placement `0`, with no element (the VP-share counterterm graph). -/
def kS0 : Fin 4 → Wick.VertexKind := ![.gauge, .fermionCt, .gauge, .gauge]

/-- **Placement `0` with the bubble.** -/
def repCB0 : Contraction 1 1 kCB0 :=
  ⟨(mkSigma [fv kCB0 0, fv kCB0 1, fv kCB0 2, fv kCB0 3] [fv kCB0 4, fv kCB0 5],
    mkTau (pg kCB0 2) [(pg kCB0 0, pg kCB0 4), (pg kCB0 5, pg kCB0 3)]),
    by decide +kernel⟩

theorem tauCD0_invol : ∀ (s : Fin 2) x,
    mkTau (pg kCD0 2) [(pg kCD0 0, pc kCD0 4 s), (pc kCD0 4 s.rev, pg kCD0 3)]
      (mkTau (pg kCD0 2)
        [(pg kCD0 0, pc kCD0 4 s), (pc kCD0 4 s.rev, pg kCD0 3)] x) = x ∧
    mkTau (pg kCD0 2)
      [(pg kCD0 0, pc kCD0 4 s), (pc kCD0 4 s.rev, pg kCD0 3)] x ≠ x := by
  decide +kernel

/-- **Placement `0` with the `δ₃` element**, field `s` towards `0`. -/
def repCD0 (s : Fin 2) : Contraction 1 1 kCD0 :=
  ⟨(mkSigma [fv kCD0 0, fv kCD0 1, fv kCD0 2, fv kCD0 3] [],
    mkTau (pg kCD0 2) [(pg kCD0 0, pc kCD0 4 s), (pc kCD0 4 s.rev, pg kCD0 3)]),
    tauCD0_invol s⟩

/-- **Placement `0` with a level-`1` counterterm and no element.** -/
def repS0 : Contraction 1 1 kS0 :=
  ⟨(mkSigma [fv kS0 0, fv kS0 1, fv kS0 2, fv kS0 3] [], mkTau (pg kS0 2) [(pg kS0 0, pg kS0 3)]),
    by decide +kernel⟩

theorem isOnePI_repCB0 : IsOnePI repCB0 := by decide +kernel

theorem isOnePI_repCD0 : ∀ s, IsOnePI (repCD0 s) := by decide +kernel

theorem isOnePI_repS0 : IsOnePI repS0 := by decide +kernel

theorem fermionSign_repCB0 : fermionSign repCB0 = -1 := by decide +kernel

theorem fermionSign_repCD0 : ∀ s, fermionSign (repCD0 s) = 1 := by decide +kernel

theorem fermionSign_repS0 : fermionSign repS0 = 1 := by decide +kernel

theorem gradedOrder_kCB0 : Graded.gradedOrder kCB0 (gZero kCB0) = 7 := by decide +kernel

theorem gradedOrder_kCD0 : Graded.gradedOrder kCD0 (gZero kCD0) = 7 := by decide +kernel

theorem gradedOrder_kS0 : Graded.gradedOrder kS0 (gOne kS0) = 7 := by decide +kernel

theorem isSetC_repCB0 : ThreeLoop.IsSetC repCB0 (gZero kCB0) := by
  refine ⟨fun _ _ => rfl, Or.inr (Or.inl ⟨fv kCB0 4, fv kCB0 5, ?_⟩)⟩
  decide +kernel

theorem isSetC_repCD0 (s : Fin 2) : ThreeLoop.IsSetC (repCD0 s) (gZero kCD0) := by
  refine ⟨fun _ _ => rfl, Or.inl ⟨4, rfl, ?_⟩⟩
  revert s
  decide +kernel

theorem isSetC_repS0 : ThreeLoop.IsSetC repS0 (gOne kS0) := by
  refine ⟨by decide, Or.inr (Or.inr ?_)⟩
  decide +kernel

/-- Placement `1` (`fermionCt` on the internal line towards `3`), with a bubble. -/
def kCB1 : Fin 6 → Wick.VertexKind := ![.gauge, .gauge, .fermionCt, .gauge, .gauge, .gauge]

/-- Placement `1`, with a `photonCt` vertex. -/
def kCD1 : Fin 5 → Wick.VertexKind := ![.gauge, .gauge, .fermionCt, .gauge, .photonCt]

/-- Placement `1`, with no element (the VP-share counterterm graph). -/
def kS1 : Fin 4 → Wick.VertexKind := ![.gauge, .gauge, .fermionCt, .gauge]

/-- **Placement `1` with the bubble.** -/
def repCB1 : Contraction 1 1 kCB1 :=
  ⟨(mkSigma [fv kCB1 0, fv kCB1 1, fv kCB1 2, fv kCB1 3] [fv kCB1 4, fv kCB1 5],
    mkTau (pg kCB1 1) [(pg kCB1 0, pg kCB1 4), (pg kCB1 5, pg kCB1 3)]),
    by decide +kernel⟩

theorem tauCD1_invol : ∀ (s : Fin 2) x,
    mkTau (pg kCD1 1) [(pg kCD1 0, pc kCD1 4 s), (pc kCD1 4 s.rev, pg kCD1 3)]
      (mkTau (pg kCD1 1)
        [(pg kCD1 0, pc kCD1 4 s), (pc kCD1 4 s.rev, pg kCD1 3)] x) = x ∧
    mkTau (pg kCD1 1)
      [(pg kCD1 0, pc kCD1 4 s), (pc kCD1 4 s.rev, pg kCD1 3)] x ≠ x := by
  decide +kernel

/-- **Placement `1` with the `δ₃` element**, field `s` towards `0`. -/
def repCD1 (s : Fin 2) : Contraction 1 1 kCD1 :=
  ⟨(mkSigma [fv kCD1 0, fv kCD1 1, fv kCD1 2, fv kCD1 3] [],
    mkTau (pg kCD1 1) [(pg kCD1 0, pc kCD1 4 s), (pc kCD1 4 s.rev, pg kCD1 3)]),
    tauCD1_invol s⟩

/-- **Placement `1` with a level-`1` counterterm and no element.** -/
def repS1 : Contraction 1 1 kS1 :=
  ⟨(mkSigma [fv kS1 0, fv kS1 1, fv kS1 2, fv kS1 3] [], mkTau (pg kS1 1) [(pg kS1 0, pg kS1 3)]),
    by decide +kernel⟩

theorem isOnePI_repCB1 : IsOnePI repCB1 := by decide +kernel

theorem isOnePI_repCD1 : ∀ s, IsOnePI (repCD1 s) := by decide +kernel

theorem isOnePI_repS1 : IsOnePI repS1 := by decide +kernel

theorem fermionSign_repCB1 : fermionSign repCB1 = -1 := by decide +kernel

theorem fermionSign_repCD1 : ∀ s, fermionSign (repCD1 s) = 1 := by decide +kernel

theorem fermionSign_repS1 : fermionSign repS1 = 1 := by decide +kernel

theorem gradedOrder_kCB1 : Graded.gradedOrder kCB1 (gZero kCB1) = 7 := by decide +kernel

theorem gradedOrder_kCD1 : Graded.gradedOrder kCD1 (gZero kCD1) = 7 := by decide +kernel

theorem gradedOrder_kS1 : Graded.gradedOrder kS1 (gOne kS1) = 7 := by decide +kernel

theorem isSetC_repCB1 : ThreeLoop.IsSetC repCB1 (gZero kCB1) := by
  refine ⟨fun _ _ => rfl, Or.inr (Or.inl ⟨fv kCB1 4, fv kCB1 5, ?_⟩)⟩
  decide +kernel

theorem isSetC_repCD1 (s : Fin 2) : ThreeLoop.IsSetC (repCD1 s) (gZero kCD1) := by
  refine ⟨fun _ _ => rfl, Or.inl ⟨4, rfl, ?_⟩⟩
  revert s
  decide +kernel

theorem isSetC_repS1 : ThreeLoop.IsSetC repS1 (gOne kS1) := by
  refine ⟨by decide, Or.inr (Or.inr ?_)⟩
  decide +kernel

/-- Placement `2` (`gaugeCt` at the end `0`, carrying the photon line), with a bubble. -/
def kCB2 : Fin 5 → Wick.VertexKind := ![.gaugeCt, .gauge, .gauge, .gauge, .gauge]

/-- Placement `2`, with a `photonCt` vertex. -/
def kCD2 : Fin 4 → Wick.VertexKind := ![.gaugeCt, .gauge, .gauge, .photonCt]

/-- Placement `2`, with no element (the VP-share counterterm graph). -/
def kS2 : Fin 3 → Wick.VertexKind := ![.gaugeCt, .gauge, .gauge]

/-- **Placement `2` with the bubble.** -/
def repCB2 : Contraction 1 1 kCB2 :=
  ⟨(mkSigma [fv kCB2 0, fv kCB2 1, fv kCB2 2] [fv kCB2 3, fv kCB2 4],
    mkTau (pg kCB2 1) [(pg kCB2 0, pg kCB2 3), (pg kCB2 4, pg kCB2 2)]),
    by decide +kernel⟩

theorem tauCD2_invol : ∀ (s : Fin 2) x,
    mkTau (pg kCD2 1) [(pg kCD2 0, pc kCD2 3 s), (pc kCD2 3 s.rev, pg kCD2 2)]
      (mkTau (pg kCD2 1)
        [(pg kCD2 0, pc kCD2 3 s), (pc kCD2 3 s.rev, pg kCD2 2)] x) = x ∧
    mkTau (pg kCD2 1)
      [(pg kCD2 0, pc kCD2 3 s), (pc kCD2 3 s.rev, pg kCD2 2)] x ≠ x := by
  decide +kernel

/-- **Placement `2` with the `δ₃` element**, field `s` towards `0`. -/
def repCD2 (s : Fin 2) : Contraction 1 1 kCD2 :=
  ⟨(mkSigma [fv kCD2 0, fv kCD2 1, fv kCD2 2] [],
    mkTau (pg kCD2 1) [(pg kCD2 0, pc kCD2 3 s), (pc kCD2 3 s.rev, pg kCD2 2)]),
    tauCD2_invol s⟩

/-- **Placement `2` with a level-`1` counterterm and no element.** -/
def repS2 : Contraction 1 1 kS2 :=
  ⟨(mkSigma [fv kS2 0, fv kS2 1, fv kS2 2] [], mkTau (pg kS2 1) [(pg kS2 0, pg kS2 2)]),
    by decide +kernel⟩

theorem isOnePI_repCB2 : IsOnePI repCB2 := by decide +kernel

theorem isOnePI_repCD2 : ∀ s, IsOnePI (repCD2 s) := by decide +kernel

theorem isOnePI_repS2 : IsOnePI repS2 := by decide +kernel

theorem fermionSign_repCB2 : fermionSign repCB2 = -1 := by decide +kernel

theorem fermionSign_repCD2 : ∀ s, fermionSign (repCD2 s) = 1 := by decide +kernel

theorem fermionSign_repS2 : fermionSign repS2 = 1 := by decide +kernel

theorem gradedOrder_kCB2 : Graded.gradedOrder kCB2 (gZero kCB2) = 7 := by decide +kernel

theorem gradedOrder_kCD2 : Graded.gradedOrder kCD2 (gZero kCD2) = 7 := by decide +kernel

theorem gradedOrder_kS2 : Graded.gradedOrder kS2 (gOne kS2) = 7 := by decide +kernel

theorem isSetC_repCB2 : ThreeLoop.IsSetC repCB2 (gZero kCB2) := by
  refine ⟨fun _ _ => rfl, Or.inr (Or.inl ⟨fv kCB2 3, fv kCB2 4, ?_⟩)⟩
  decide +kernel

theorem isSetC_repCD2 (s : Fin 2) : ThreeLoop.IsSetC (repCD2 s) (gZero kCD2) := by
  refine ⟨fun _ _ => rfl, Or.inl ⟨3, rfl, ?_⟩⟩
  revert s
  decide +kernel

theorem isSetC_repS2 : ThreeLoop.IsSetC repS2 (gOne kS2) := by
  refine ⟨by decide, Or.inr (Or.inr ?_)⟩
  decide +kernel

/-- Placement `3` (`gaugeCt` in the middle, carrying the external photon), with a bubble. -/
def kCB3 : Fin 5 → Wick.VertexKind := ![.gauge, .gaugeCt, .gauge, .gauge, .gauge]

/-- Placement `3`, with a `photonCt` vertex. -/
def kCD3 : Fin 4 → Wick.VertexKind := ![.gauge, .gaugeCt, .gauge, .photonCt]

/-- Placement `3`, with no element (the VP-share counterterm graph). -/
def kS3 : Fin 3 → Wick.VertexKind := ![.gauge, .gaugeCt, .gauge]

/-- **Placement `3` with the bubble.** -/
def repCB3 : Contraction 1 1 kCB3 :=
  ⟨(mkSigma [fv kCB3 0, fv kCB3 1, fv kCB3 2] [fv kCB3 3, fv kCB3 4],
    mkTau (pg kCB3 1) [(pg kCB3 0, pg kCB3 3), (pg kCB3 4, pg kCB3 2)]),
    by decide +kernel⟩

theorem tauCD3_invol : ∀ (s : Fin 2) x,
    mkTau (pg kCD3 1) [(pg kCD3 0, pc kCD3 3 s), (pc kCD3 3 s.rev, pg kCD3 2)]
      (mkTau (pg kCD3 1)
        [(pg kCD3 0, pc kCD3 3 s), (pc kCD3 3 s.rev, pg kCD3 2)] x) = x ∧
    mkTau (pg kCD3 1)
      [(pg kCD3 0, pc kCD3 3 s), (pc kCD3 3 s.rev, pg kCD3 2)] x ≠ x := by
  decide +kernel

/-- **Placement `3` with the `δ₃` element**, field `s` towards `0`. -/
def repCD3 (s : Fin 2) : Contraction 1 1 kCD3 :=
  ⟨(mkSigma [fv kCD3 0, fv kCD3 1, fv kCD3 2] [],
    mkTau (pg kCD3 1) [(pg kCD3 0, pc kCD3 3 s), (pc kCD3 3 s.rev, pg kCD3 2)]),
    tauCD3_invol s⟩

/-- **Placement `3` with a level-`1` counterterm and no element.** -/
def repS3 : Contraction 1 1 kS3 :=
  ⟨(mkSigma [fv kS3 0, fv kS3 1, fv kS3 2] [], mkTau (pg kS3 1) [(pg kS3 0, pg kS3 2)]),
    by decide +kernel⟩

theorem isOnePI_repCB3 : IsOnePI repCB3 := by decide +kernel

theorem isOnePI_repCD3 : ∀ s, IsOnePI (repCD3 s) := by decide +kernel

theorem isOnePI_repS3 : IsOnePI repS3 := by decide +kernel

theorem fermionSign_repCB3 : fermionSign repCB3 = -1 := by decide +kernel

theorem fermionSign_repCD3 : ∀ s, fermionSign (repCD3 s) = 1 := by decide +kernel

theorem fermionSign_repS3 : fermionSign repS3 = 1 := by decide +kernel

theorem gradedOrder_kCB3 : Graded.gradedOrder kCB3 (gZero kCB3) = 7 := by decide +kernel

theorem gradedOrder_kCD3 : Graded.gradedOrder kCD3 (gZero kCD3) = 7 := by decide +kernel

theorem gradedOrder_kS3 : Graded.gradedOrder kS3 (gOne kS3) = 7 := by decide +kernel

theorem isSetC_repCB3 : ThreeLoop.IsSetC repCB3 (gZero kCB3) := by
  refine ⟨fun _ _ => rfl, Or.inr (Or.inl ⟨fv kCB3 3, fv kCB3 4, ?_⟩)⟩
  decide +kernel

theorem isSetC_repCD3 (s : Fin 2) : ThreeLoop.IsSetC (repCD3 s) (gZero kCD3) := by
  refine ⟨fun _ _ => rfl, Or.inl ⟨3, rfl, ?_⟩⟩
  revert s
  decide +kernel

theorem isSetC_repS3 : ThreeLoop.IsSetC repS3 (gOne kS3) := by
  refine ⟨by decide, Or.inr (Or.inr ?_)⟩
  decide +kernel

/-- Placement `4` (`gaugeCt` at the end `2`, carrying the photon line), with a bubble. -/
def kCB4 : Fin 5 → Wick.VertexKind := ![.gauge, .gauge, .gaugeCt, .gauge, .gauge]

/-- Placement `4`, with a `photonCt` vertex. -/
def kCD4 : Fin 4 → Wick.VertexKind := ![.gauge, .gauge, .gaugeCt, .photonCt]

/-- Placement `4`, with no element (the VP-share counterterm graph). -/
def kS4 : Fin 3 → Wick.VertexKind := ![.gauge, .gauge, .gaugeCt]

/-- **Placement `4` with the bubble.** -/
def repCB4 : Contraction 1 1 kCB4 :=
  ⟨(mkSigma [fv kCB4 0, fv kCB4 1, fv kCB4 2] [fv kCB4 3, fv kCB4 4],
    mkTau (pg kCB4 1) [(pg kCB4 0, pg kCB4 3), (pg kCB4 4, pg kCB4 2)]),
    by decide +kernel⟩

theorem tauCD4_invol : ∀ (s : Fin 2) x,
    mkTau (pg kCD4 1) [(pg kCD4 0, pc kCD4 3 s), (pc kCD4 3 s.rev, pg kCD4 2)]
      (mkTau (pg kCD4 1)
        [(pg kCD4 0, pc kCD4 3 s), (pc kCD4 3 s.rev, pg kCD4 2)] x) = x ∧
    mkTau (pg kCD4 1)
      [(pg kCD4 0, pc kCD4 3 s), (pc kCD4 3 s.rev, pg kCD4 2)] x ≠ x := by
  decide +kernel

/-- **Placement `4` with the `δ₃` element**, field `s` towards `0`. -/
def repCD4 (s : Fin 2) : Contraction 1 1 kCD4 :=
  ⟨(mkSigma [fv kCD4 0, fv kCD4 1, fv kCD4 2] [],
    mkTau (pg kCD4 1) [(pg kCD4 0, pc kCD4 3 s), (pc kCD4 3 s.rev, pg kCD4 2)]),
    tauCD4_invol s⟩

/-- **Placement `4` with a level-`1` counterterm and no element.** -/
def repS4 : Contraction 1 1 kS4 :=
  ⟨(mkSigma [fv kS4 0, fv kS4 1, fv kS4 2] [], mkTau (pg kS4 1) [(pg kS4 0, pg kS4 2)]),
    by decide +kernel⟩

theorem isOnePI_repCB4 : IsOnePI repCB4 := by decide +kernel

theorem isOnePI_repCD4 : ∀ s, IsOnePI (repCD4 s) := by decide +kernel

theorem isOnePI_repS4 : IsOnePI repS4 := by decide +kernel

theorem fermionSign_repCB4 : fermionSign repCB4 = -1 := by decide +kernel

theorem fermionSign_repCD4 : ∀ s, fermionSign (repCD4 s) = 1 := by decide +kernel

theorem fermionSign_repS4 : fermionSign repS4 = 1 := by decide +kernel

theorem gradedOrder_kCB4 : Graded.gradedOrder kCB4 (gZero kCB4) = 7 := by decide +kernel

theorem gradedOrder_kCD4 : Graded.gradedOrder kCD4 (gZero kCD4) = 7 := by decide +kernel

theorem gradedOrder_kS4 : Graded.gradedOrder kS4 (gOne kS4) = 7 := by decide +kernel

theorem isSetC_repCB4 : ThreeLoop.IsSetC repCB4 (gZero kCB4) := by
  refine ⟨fun _ _ => rfl, Or.inr (Or.inl ⟨fv kCB4 3, fv kCB4 4, ?_⟩)⟩
  decide +kernel

theorem isSetC_repCD4 (s : Fin 2) : ThreeLoop.IsSetC (repCD4 s) (gZero kCD4) := by
  refine ⟨fun _ _ => rfl, Or.inl ⟨3, rfl, ?_⟩⟩
  revert s
  decide +kernel

theorem isSetC_repS4 : ThreeLoop.IsSetC repS4 (gOne kS4) := by
  refine ⟨by decide, Or.inr (Or.inr ?_)⟩
  decide +kernel

end QED.ChainProof.SetCLink

end
