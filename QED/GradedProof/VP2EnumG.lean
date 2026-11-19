/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2Enum

/-!
# The 1PI two-photon contractions of four gauge vertices

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 1, for the kind
sequence `gggg` of four `gauge` vertices: the 72 two-loop vacuum-polarization contractions, one
closed fermion loop through the four vertices with the two external photons at two of them and
one internal photon joining the other two. The 15 photon pairings are split into five chunks
of three (the first chunk pairs the two external photons with each other, so it has no 1PI
contraction), and each chunk is classified by its own kernel check (`decide +kernel`), to keep
every check small.

## Main statements

* `QED.GradedProof.VP2.isOnePI2_iff_gggg`: a two-photon contraction of `gggg` is 1PI iff it is
  one of the 72 of `onePI2_gggg`.
-/

@[expose] public section

namespace QED.GradedProof.VP2

open QED.WickModel QED.TwoLoop.Enumeration QED.GradedProof.SE2

/-! ### Chunk 0 -/

/-- The photon pairings of chunk 0. -/
def invsG0 : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gggg)) :=
  [photonPerm2 k_gggg
        [(.inl 0, .inl 1),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))],
    photonPerm2 k_gggg
        [(.inl 0, .inl 1),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))],
    photonPerm2 k_gggg
        [(.inl 0, .inl 1),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]]

theorem invsG0_invol : ∀ τ ∈ invsG0, IsInvol2 τ := by decide +kernel

/-- The 1PI contractions with a photon pairing of chunk 0. -/
def onePIG0 : List (Contraction 0 2 k_gggg) :=
  []

theorem onePIG0_tau : ∀ D ∈ onePIG0, D.1.2 ∈ invsG0 := by decide +kernel

theorem classifyG0 : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_gggg),
    ∀ C ∈ withSigma2 invsG0 invsG0_invol σ, IsOnePI C ↔ ∃ D ∈ onePIG0, D = C := by
  decide +kernel

/-! ### Chunk 1 -/

/-- The photon pairings of chunk 1. -/
def invsG1 : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gggg)) :=
  [photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))],
    photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))],
    photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]]

theorem invsG1_invol : ∀ τ ∈ invsG1, IsInvol2 τ := by decide +kernel

/-- The 1PI contractions with a photon pairing of chunk 1. -/
def onePIG1 : List (Contraction 0 2 k_gggg) :=
  [⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩]

theorem onePIG1_tau : ∀ D ∈ onePIG1, D.1.2 ∈ invsG1 := by decide +kernel

theorem classifyG1 : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_gggg),
    ∀ C ∈ withSigma2 invsG1 invsG1_invol σ, IsOnePI C ↔ ∃ D ∈ onePIG1, D = C := by
  decide +kernel

/-! ### Chunk 2 -/

/-- The photon pairings of chunk 2. -/
def invsG2 : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gggg)) :=
  [photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))],
    photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))],
    photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]]

theorem invsG2_invol : ∀ τ ∈ invsG2, IsInvol2 τ := by decide +kernel

/-- The 1PI contractions with a photon pairing of chunk 2. -/
def onePIG2 : List (Contraction 0 2 k_gggg) :=
  [⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 1 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩]

theorem onePIG2_tau : ∀ D ∈ onePIG2, D.1.2 ∈ invsG2 := by decide +kernel

theorem classifyG2 : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_gggg),
    ∀ C ∈ withSigma2 invsG2 invsG2_invol σ, IsOnePI C ↔ ∃ D ∈ onePIG2, D = C := by
  decide +kernel

/-! ### Chunk 3 -/

/-- The photon pairings of chunk 3. -/
def invsG3 : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gggg)) :=
  [photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))],
    photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))],
    photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]]

theorem invsG3_invol : ∀ τ ∈ invsG3, IsInvol2 τ := by decide +kernel

/-- The 1PI contractions with a photon pairing of chunk 3. -/
def onePIG3 : List (Contraction 0 2 k_gggg) :=
  [⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 2 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩]

theorem onePIG3_tau : ∀ D ∈ onePIG3, D.1.2 ∈ invsG3 := by decide +kernel

theorem classifyG3 : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_gggg),
    ∀ C ∈ withSigma2 invsG3 invsG3_invol σ, IsOnePI C ↔ ∃ D ∈ onePIG3, D = C := by
  decide +kernel

/-! ### Chunk 4 -/

/-- The photon pairings of chunk 4. -/
def invsG4 : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gggg)) :=
  [photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))],
    photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))],
    photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]]

theorem invsG4_invol : ∀ τ ∈ invsG4, IsInvol2 τ := by decide +kernel

/-- The 1PI contractions with a photon pairing of chunk 4. -/
def onePIG4 : List (Contraction 0 2 k_gggg) :=
  [⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 0 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm2 k_gggg
        [(.inl 0, .inr (psK k_gggg 3 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 0 0), .inr (psK k_gggg 1 0))]), by decide +kernel⟩]

theorem onePIG4_tau : ∀ D ∈ onePIG4, D.1.2 ∈ invsG4 := by decide +kernel

theorem classifyG4 : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_gggg),
    ∀ C ∈ withSigma2 invsG4 invsG4_invol σ, IsOnePI C ↔ ∃ D ∈ onePIG4, D = C := by
  decide +kernel

/-! ### The 72 contractions -/

/-- The 1PI two-photon contractions of `gggg`, by chunk. -/
def onePI2_gggg : List (Contraction 0 2 k_gggg) :=
  onePIG0 ++ onePIG1 ++ onePIG2 ++ onePIG3 ++ onePIG4

theorem invsG_complete' : ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gggg), IsInvol2 τ →
    τ ∈ invsG0 ++ invsG1 ++ invsG2 ++ invsG3 ++ invsG4 := by
  decide +kernel

theorem invsG_complete (τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gggg)) (h : IsInvol2 τ) :
    τ ∈ invsG0 ∨ τ ∈ invsG1 ∨ τ ∈ invsG2 ∨ τ ∈ invsG3 ∨ τ ∈ invsG4 := by
  have := invsG_complete' τ h
  simp only [List.mem_append] at this
  tauto

theorem mem_withSigma2_of_mem {N : ℕ} {κ : Fin N → Wick.VertexKind}
    {invs : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot κ))} (hinv : ∀ τ ∈ invs, IsInvol2 τ)
    (C : Contraction 0 2 κ) (h : C.1.2 ∈ invs) : C ∈ withSigma2 invs hinv C.1.1 :=
  List.mem_map.mpr ⟨⟨C.1.2, h⟩, List.mem_attach _ _, rfl⟩

/-- A two-photon contraction of `gggg` is 1PI iff it is one of the 72 listed. -/
theorem isOnePI2_iff_gggg (C : Contraction 0 2 k_gggg) : IsOnePI C ↔ C ∈ onePI2_gggg := by
  simp only [onePI2_gggg, List.mem_append]
  constructor
  · intro hC
    rcases invsG_complete C.1.2 C.2 with h | h | h | h | h
    · obtain ⟨D, hD, rfl⟩ := (classifyG0 _ C (mem_withSigma2_of_mem _ C h)).mp hC
      tauto
    · obtain ⟨D, hD, rfl⟩ := (classifyG1 _ C (mem_withSigma2_of_mem _ C h)).mp hC
      tauto
    · obtain ⟨D, hD, rfl⟩ := (classifyG2 _ C (mem_withSigma2_of_mem _ C h)).mp hC
      tauto
    · obtain ⟨D, hD, rfl⟩ := (classifyG3 _ C (mem_withSigma2_of_mem _ C h)).mp hC
      tauto
    · obtain ⟨D, hD, rfl⟩ := (classifyG4 _ C (mem_withSigma2_of_mem _ C h)).mp hC
      tauto
  · rintro ((((h | h) | h) | h) | h)
    · exact (classifyG0 _ C (mem_withSigma2_of_mem _ C (onePIG0_tau C h))).mpr ⟨C, h, rfl⟩
    · exact (classifyG1 _ C (mem_withSigma2_of_mem _ C (onePIG1_tau C h))).mpr ⟨C, h, rfl⟩
    · exact (classifyG2 _ C (mem_withSigma2_of_mem _ C (onePIG2_tau C h))).mpr ⟨C, h, rfl⟩
    · exact (classifyG3 _ C (mem_withSigma2_of_mem _ C (onePIG3_tau C h))).mpr ⟨C, h, rfl⟩
    · exact (classifyG4 _ C (mem_withSigma2_of_mem _ C (onePIG4_tau C h))).mpr ⟨C, h, rfl⟩

end QED.GradedProof.VP2

end
