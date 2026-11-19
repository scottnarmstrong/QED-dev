/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Enum

/-!
# The 1PI two-photon contractions of order four: counterterm kinds

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 1: the finite
enumeration. For the two-photon function (`nf = 0`, `nA = 2`) and every kind sequence `κ` of
total order (V₁) exactly `4` with two or three vertices
(`QED.GradedProof.SE2.filter_order_eq_four_two`, `…_three`), this file lists the 1PI
contractions (X₁₈). The candidate lists were produced by a re-implementation of the frozen
definitions (the generator `gen.py` of the Stage 2 scratch notes); nothing of it is trusted:
every statement is checked by the kernel (`decide +kernel`).

* `gC`, `Cg`: 2 each, the one-loop bubble with one vertex a `gaugeCt` vertex;
* `ggf`, `gfg`, `fgg`: 4 each, the one-loop bubble with the `fermionCt` vertex on one of its two
  electron lines;
* `ff`, `fp`, `pf`, `pp`, `ggp`, `gpg`, `pgg`: none (a `photonCt` vertex can only sit on an
  external leg, which is a bridge).

The four `gauge` vertices `gggg` are in `QED/GradedProof/VP2EnumG.lean`.

## Main statements

* `QED.GradedProof.VP2.isOnePI2_iff_<κ>`: a two-photon contraction of `κ` is 1PI iff it is
  listed.
-/

@[expose] public section

namespace QED.GradedProof.VP2

open QED.WickModel QED.TwoLoop.Enumeration QED.GradedProof.SE2

variable {N : ℕ}

/-- The fermion pairing with the closed loops `l₁ → l₂ → ⋯ → l₁` and no external fermion. -/
def fermionPerm0 (κ : Fin N → Wick.VertexKind) (loops : List (List (Wick.FermionVertex κ))) :
    Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex κ) :=
  (loops.map fun l => (l.reverse.map Sum.inr).formPerm).prod

/-- The photon pairing given by a list of transpositions of the fields, with two external
photons. -/
def photonPerm2 (κ : Fin N → Wick.VertexKind)
    (pairs : List ((Fin 2 ⊕ Wick.PhotonSlot κ) × (Fin 2 ⊕ Wick.PhotonSlot κ))) :
    Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot κ) :=
  (pairs.map fun p => Equiv.swap p.1 p.2).prod

/-- A fixed-point-free involution of the photon fields. -/
def IsInvol2 {κ : Fin N → Wick.VertexKind} (τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot κ)) : Prop :=
  ∀ b, τ (τ b) = b ∧ τ b ≠ b

instance {κ : Fin N → Wick.VertexKind} : DecidablePred (IsInvol2 (κ := κ)) := fun τ => by
  unfold IsInvol2; infer_instance

/-- The contractions with fermion pairing `σ` and a photon pairing from the list `invs`. -/
def withSigma2 {κ : Fin N → Wick.VertexKind}
    (invs : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot κ))) (hinv : ∀ τ ∈ invs, IsInvol2 τ)
    (σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex κ)) : List (Contraction 0 2 κ) :=
  invs.attach.map fun τ => ⟨(σ, τ.1), fun b => hinv τ.1 τ.2 b⟩

theorem mem_withSigma2 {κ : Fin N → Wick.VertexKind}
    {invs : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot κ))} (hinv : ∀ τ ∈ invs, IsInvol2 τ)
    (hcomp : ∀ τ, IsInvol2 τ → τ ∈ invs) (C : Contraction 0 2 κ) :
    C ∈ withSigma2 invs hinv C.1.1 :=
  List.mem_map.mpr ⟨⟨C.1.2, hcomp _ C.2⟩, List.mem_attach _ _, rfl⟩

/-! ### `gC` -/

/-- The photon pairings of `gC` with two external photons. -/
def invs2_gC : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gC)) :=
  [photonPerm2 k_gC
        [(.inl 0, .inl 1),
         (.inr (psK k_gC 0 0), .inr (psK k_gC 1 0))],
    photonPerm2 k_gC
        [(.inl 0, .inr (psK k_gC 0 0)),
         (.inl 1, .inr (psK k_gC 1 0))],
    photonPerm2 k_gC
        [(.inl 0, .inr (psK k_gC 1 0)),
         (.inl 1, .inr (psK k_gC 0 0))]]

theorem invs2_gC_invol : ∀ τ ∈ invs2_gC, IsInvol2 τ := by decide +kernel

theorem invs2_gC_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gC), IsInvol2 τ → τ ∈ invs2_gC := by
  decide +kernel

/-- The 1PI two-photon contractions of `gC`. -/
def onePI2_gC : List (Contraction 0 2 k_gC) :=
  [⟨(fermionPerm0 k_gC [[fvK k_gC 0, fvK k_gC 1]],
      photonPerm2 k_gC
        [(.inl 0, .inr (psK k_gC 0 0)),
         (.inl 1, .inr (psK k_gC 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gC [[fvK k_gC 0, fvK k_gC 1]],
      photonPerm2 k_gC
        [(.inl 0, .inr (psK k_gC 1 0)),
         (.inl 1, .inr (psK k_gC 0 0))]), by decide +kernel⟩]

theorem classify2_gC : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_gC),
    ∀ C ∈ withSigma2 invs2_gC invs2_gC_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_gC, D = C := by
  decide +kernel

/-- A two-photon contraction of `gC` is 1PI iff it is one of the 2 listed. -/
theorem isOnePI2_iff_gC (C : Contraction 0 2 k_gC) : IsOnePI C ↔ C ∈ onePI2_gC :=
  (classify2_gC C.1.1 C (mem_withSigma2 _ invs2_gC_complete C)).trans (by simp)

/-! ### `Cg` -/

/-- The photon pairings of `Cg` with two external photons. -/
def invs2_Cg : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_Cg)) :=
  [photonPerm2 k_Cg
        [(.inl 0, .inl 1),
         (.inr (psK k_Cg 0 0), .inr (psK k_Cg 1 0))],
    photonPerm2 k_Cg
        [(.inl 0, .inr (psK k_Cg 0 0)),
         (.inl 1, .inr (psK k_Cg 1 0))],
    photonPerm2 k_Cg
        [(.inl 0, .inr (psK k_Cg 1 0)),
         (.inl 1, .inr (psK k_Cg 0 0))]]

theorem invs2_Cg_invol : ∀ τ ∈ invs2_Cg, IsInvol2 τ := by decide +kernel

theorem invs2_Cg_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_Cg), IsInvol2 τ → τ ∈ invs2_Cg := by
  decide +kernel

/-- The 1PI two-photon contractions of `Cg`. -/
def onePI2_Cg : List (Contraction 0 2 k_Cg) :=
  [⟨(fermionPerm0 k_Cg [[fvK k_Cg 0, fvK k_Cg 1]],
      photonPerm2 k_Cg
        [(.inl 0, .inr (psK k_Cg 0 0)),
         (.inl 1, .inr (psK k_Cg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_Cg [[fvK k_Cg 0, fvK k_Cg 1]],
      photonPerm2 k_Cg
        [(.inl 0, .inr (psK k_Cg 1 0)),
         (.inl 1, .inr (psK k_Cg 0 0))]), by decide +kernel⟩]

theorem classify2_Cg : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_Cg),
    ∀ C ∈ withSigma2 invs2_Cg invs2_Cg_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_Cg, D = C := by
  decide +kernel

/-- A two-photon contraction of `Cg` is 1PI iff it is one of the 2 listed. -/
theorem isOnePI2_iff_Cg (C : Contraction 0 2 k_Cg) : IsOnePI C ↔ C ∈ onePI2_Cg :=
  (classify2_Cg C.1.1 C (mem_withSigma2 _ invs2_Cg_complete C)).trans (by simp)

/-! ### `ff` -/

/-- The photon pairings of `ff` with two external photons. -/
def invs2_ff : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_ff)) :=
  [photonPerm2 k_ff
        [(.inl 0, .inl 1)]]

theorem invs2_ff_invol : ∀ τ ∈ invs2_ff, IsInvol2 τ := by decide +kernel

theorem invs2_ff_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_ff), IsInvol2 τ → τ ∈ invs2_ff := by
  decide +kernel

/-- The 1PI two-photon contractions of `ff`. -/
def onePI2_ff : List (Contraction 0 2 k_ff) :=
  []

theorem classify2_ff : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_ff),
    ∀ C ∈ withSigma2 invs2_ff invs2_ff_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_ff, D = C := by
  decide +kernel

/-- A two-photon contraction of `ff` is 1PI iff it is one of the 0 listed. -/
theorem isOnePI2_iff_ff (C : Contraction 0 2 k_ff) : IsOnePI C ↔ C ∈ onePI2_ff :=
  (classify2_ff C.1.1 C (mem_withSigma2 _ invs2_ff_complete C)).trans (by simp)

/-! ### `fp` -/

/-- The photon pairings of `fp` with two external photons. -/
def invs2_fp : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_fp)) :=
  [photonPerm2 k_fp
        [(.inl 0, .inl 1),
         (.inr (psK k_fp 1 0), .inr (psK k_fp 1 1))],
    photonPerm2 k_fp
        [(.inl 0, .inr (psK k_fp 1 0)),
         (.inl 1, .inr (psK k_fp 1 1))],
    photonPerm2 k_fp
        [(.inl 0, .inr (psK k_fp 1 1)),
         (.inl 1, .inr (psK k_fp 1 0))]]

theorem invs2_fp_invol : ∀ τ ∈ invs2_fp, IsInvol2 τ := by decide +kernel

theorem invs2_fp_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_fp), IsInvol2 τ → τ ∈ invs2_fp := by
  decide +kernel

/-- The 1PI two-photon contractions of `fp`. -/
def onePI2_fp : List (Contraction 0 2 k_fp) :=
  []

theorem classify2_fp : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_fp),
    ∀ C ∈ withSigma2 invs2_fp invs2_fp_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_fp, D = C := by
  decide +kernel

/-- A two-photon contraction of `fp` is 1PI iff it is one of the 0 listed. -/
theorem isOnePI2_iff_fp (C : Contraction 0 2 k_fp) : IsOnePI C ↔ C ∈ onePI2_fp :=
  (classify2_fp C.1.1 C (mem_withSigma2 _ invs2_fp_complete C)).trans (by simp)

/-! ### `pf` -/

/-- The photon pairings of `pf` with two external photons. -/
def invs2_pf : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_pf)) :=
  [photonPerm2 k_pf
        [(.inl 0, .inl 1),
         (.inr (psK k_pf 0 0), .inr (psK k_pf 0 1))],
    photonPerm2 k_pf
        [(.inl 0, .inr (psK k_pf 0 0)),
         (.inl 1, .inr (psK k_pf 0 1))],
    photonPerm2 k_pf
        [(.inl 0, .inr (psK k_pf 0 1)),
         (.inl 1, .inr (psK k_pf 0 0))]]

theorem invs2_pf_invol : ∀ τ ∈ invs2_pf, IsInvol2 τ := by decide +kernel

theorem invs2_pf_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_pf), IsInvol2 τ → τ ∈ invs2_pf := by
  decide +kernel

/-- The 1PI two-photon contractions of `pf`. -/
def onePI2_pf : List (Contraction 0 2 k_pf) :=
  []

theorem classify2_pf : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_pf),
    ∀ C ∈ withSigma2 invs2_pf invs2_pf_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_pf, D = C := by
  decide +kernel

/-- A two-photon contraction of `pf` is 1PI iff it is one of the 0 listed. -/
theorem isOnePI2_iff_pf (C : Contraction 0 2 k_pf) : IsOnePI C ↔ C ∈ onePI2_pf :=
  (classify2_pf C.1.1 C (mem_withSigma2 _ invs2_pf_complete C)).trans (by simp)

/-! ### `pp` -/

/-- The photon pairings of `pp` with two external photons. -/
def invs2_pp : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_pp)) :=
  [photonPerm2 k_pp
        [(.inl 0, .inl 1),
         (.inr (psK k_pp 0 0), .inr (psK k_pp 0 1)),
         (.inr (psK k_pp 1 0), .inr (psK k_pp 1 1))],
    photonPerm2 k_pp
        [(.inl 0, .inl 1),
         (.inr (psK k_pp 0 0), .inr (psK k_pp 1 0)),
         (.inr (psK k_pp 0 1), .inr (psK k_pp 1 1))],
    photonPerm2 k_pp
        [(.inl 0, .inl 1),
         (.inr (psK k_pp 0 0), .inr (psK k_pp 1 1)),
         (.inr (psK k_pp 0 1), .inr (psK k_pp 1 0))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 0 0)),
         (.inl 1, .inr (psK k_pp 0 1)),
         (.inr (psK k_pp 1 0), .inr (psK k_pp 1 1))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 0 0)),
         (.inl 1, .inr (psK k_pp 1 0)),
         (.inr (psK k_pp 0 1), .inr (psK k_pp 1 1))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 0 0)),
         (.inl 1, .inr (psK k_pp 1 1)),
         (.inr (psK k_pp 0 1), .inr (psK k_pp 1 0))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 0 1)),
         (.inl 1, .inr (psK k_pp 0 0)),
         (.inr (psK k_pp 1 0), .inr (psK k_pp 1 1))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 0 1)),
         (.inl 1, .inr (psK k_pp 1 0)),
         (.inr (psK k_pp 0 0), .inr (psK k_pp 1 1))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 0 1)),
         (.inl 1, .inr (psK k_pp 1 1)),
         (.inr (psK k_pp 0 0), .inr (psK k_pp 1 0))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 1 0)),
         (.inl 1, .inr (psK k_pp 0 0)),
         (.inr (psK k_pp 0 1), .inr (psK k_pp 1 1))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 1 0)),
         (.inl 1, .inr (psK k_pp 0 1)),
         (.inr (psK k_pp 0 0), .inr (psK k_pp 1 1))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 1 0)),
         (.inl 1, .inr (psK k_pp 1 1)),
         (.inr (psK k_pp 0 0), .inr (psK k_pp 0 1))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 1 1)),
         (.inl 1, .inr (psK k_pp 0 0)),
         (.inr (psK k_pp 0 1), .inr (psK k_pp 1 0))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 1 1)),
         (.inl 1, .inr (psK k_pp 0 1)),
         (.inr (psK k_pp 0 0), .inr (psK k_pp 1 0))],
    photonPerm2 k_pp
        [(.inl 0, .inr (psK k_pp 1 1)),
         (.inl 1, .inr (psK k_pp 1 0)),
         (.inr (psK k_pp 0 0), .inr (psK k_pp 0 1))]]

theorem invs2_pp_invol : ∀ τ ∈ invs2_pp, IsInvol2 τ := by decide +kernel

theorem invs2_pp_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_pp), IsInvol2 τ → τ ∈ invs2_pp := by
  decide +kernel

/-- The 1PI two-photon contractions of `pp`. -/
def onePI2_pp : List (Contraction 0 2 k_pp) :=
  []

theorem classify2_pp : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_pp),
    ∀ C ∈ withSigma2 invs2_pp invs2_pp_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_pp, D = C := by
  decide +kernel

/-- A two-photon contraction of `pp` is 1PI iff it is one of the 0 listed. -/
theorem isOnePI2_iff_pp (C : Contraction 0 2 k_pp) : IsOnePI C ↔ C ∈ onePI2_pp :=
  (classify2_pp C.1.1 C (mem_withSigma2 _ invs2_pp_complete C)).trans (by simp)

/-! ### `ggf` -/

/-- The photon pairings of `ggf` with two external photons. -/
def invs2_ggf : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_ggf)) :=
  [photonPerm2 k_ggf
        [(.inl 0, .inl 1),
         (.inr (psK k_ggf 0 0), .inr (psK k_ggf 1 0))],
    photonPerm2 k_ggf
        [(.inl 0, .inr (psK k_ggf 0 0)),
         (.inl 1, .inr (psK k_ggf 1 0))],
    photonPerm2 k_ggf
        [(.inl 0, .inr (psK k_ggf 1 0)),
         (.inl 1, .inr (psK k_ggf 0 0))]]

theorem invs2_ggf_invol : ∀ τ ∈ invs2_ggf, IsInvol2 τ := by decide +kernel

theorem invs2_ggf_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_ggf), IsInvol2 τ → τ ∈ invs2_ggf := by
  decide +kernel

/-- The 1PI two-photon contractions of `ggf`. -/
def onePI2_ggf : List (Contraction 0 2 k_ggf) :=
  [⟨(fermionPerm0 k_ggf [[fvK k_ggf 0, fvK k_ggf 2, fvK k_ggf 1]],
      photonPerm2 k_ggf
        [(.inl 0, .inr (psK k_ggf 0 0)),
         (.inl 1, .inr (psK k_ggf 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_ggf [[fvK k_ggf 0, fvK k_ggf 1, fvK k_ggf 2]],
      photonPerm2 k_ggf
        [(.inl 0, .inr (psK k_ggf 0 0)),
         (.inl 1, .inr (psK k_ggf 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_ggf [[fvK k_ggf 0, fvK k_ggf 2, fvK k_ggf 1]],
      photonPerm2 k_ggf
        [(.inl 0, .inr (psK k_ggf 1 0)),
         (.inl 1, .inr (psK k_ggf 0 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_ggf [[fvK k_ggf 0, fvK k_ggf 1, fvK k_ggf 2]],
      photonPerm2 k_ggf
        [(.inl 0, .inr (psK k_ggf 1 0)),
         (.inl 1, .inr (psK k_ggf 0 0))]), by decide +kernel⟩]

theorem classify2_ggf : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_ggf),
    ∀ C ∈ withSigma2 invs2_ggf invs2_ggf_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_ggf, D = C := by
  decide +kernel

/-- A two-photon contraction of `ggf` is 1PI iff it is one of the 4 listed. -/
theorem isOnePI2_iff_ggf (C : Contraction 0 2 k_ggf) : IsOnePI C ↔ C ∈ onePI2_ggf :=
  (classify2_ggf C.1.1 C (mem_withSigma2 _ invs2_ggf_complete C)).trans (by simp)

/-! ### `ggp` -/

/-- The photon pairings of `ggp` with two external photons. -/
def invs2_ggp : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_ggp)) :=
  [photonPerm2 k_ggp
        [(.inl 0, .inl 1),
         (.inr (psK k_ggp 0 0), .inr (psK k_ggp 1 0)),
         (.inr (psK k_ggp 2 0), .inr (psK k_ggp 2 1))],
    photonPerm2 k_ggp
        [(.inl 0, .inl 1),
         (.inr (psK k_ggp 0 0), .inr (psK k_ggp 2 0)),
         (.inr (psK k_ggp 1 0), .inr (psK k_ggp 2 1))],
    photonPerm2 k_ggp
        [(.inl 0, .inl 1),
         (.inr (psK k_ggp 0 0), .inr (psK k_ggp 2 1)),
         (.inr (psK k_ggp 1 0), .inr (psK k_ggp 2 0))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 0 0)),
         (.inl 1, .inr (psK k_ggp 1 0)),
         (.inr (psK k_ggp 2 0), .inr (psK k_ggp 2 1))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 0 0)),
         (.inl 1, .inr (psK k_ggp 2 0)),
         (.inr (psK k_ggp 1 0), .inr (psK k_ggp 2 1))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 0 0)),
         (.inl 1, .inr (psK k_ggp 2 1)),
         (.inr (psK k_ggp 1 0), .inr (psK k_ggp 2 0))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 1 0)),
         (.inl 1, .inr (psK k_ggp 0 0)),
         (.inr (psK k_ggp 2 0), .inr (psK k_ggp 2 1))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 1 0)),
         (.inl 1, .inr (psK k_ggp 2 0)),
         (.inr (psK k_ggp 0 0), .inr (psK k_ggp 2 1))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 1 0)),
         (.inl 1, .inr (psK k_ggp 2 1)),
         (.inr (psK k_ggp 0 0), .inr (psK k_ggp 2 0))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 2 0)),
         (.inl 1, .inr (psK k_ggp 0 0)),
         (.inr (psK k_ggp 1 0), .inr (psK k_ggp 2 1))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 2 0)),
         (.inl 1, .inr (psK k_ggp 1 0)),
         (.inr (psK k_ggp 0 0), .inr (psK k_ggp 2 1))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 2 0)),
         (.inl 1, .inr (psK k_ggp 2 1)),
         (.inr (psK k_ggp 0 0), .inr (psK k_ggp 1 0))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 2 1)),
         (.inl 1, .inr (psK k_ggp 0 0)),
         (.inr (psK k_ggp 1 0), .inr (psK k_ggp 2 0))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 2 1)),
         (.inl 1, .inr (psK k_ggp 1 0)),
         (.inr (psK k_ggp 0 0), .inr (psK k_ggp 2 0))],
    photonPerm2 k_ggp
        [(.inl 0, .inr (psK k_ggp 2 1)),
         (.inl 1, .inr (psK k_ggp 2 0)),
         (.inr (psK k_ggp 0 0), .inr (psK k_ggp 1 0))]]

theorem invs2_ggp_invol : ∀ τ ∈ invs2_ggp, IsInvol2 τ := by decide +kernel

theorem invs2_ggp_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_ggp), IsInvol2 τ → τ ∈ invs2_ggp := by
  decide +kernel

/-- The 1PI two-photon contractions of `ggp`. -/
def onePI2_ggp : List (Contraction 0 2 k_ggp) :=
  []

theorem classify2_ggp : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_ggp),
    ∀ C ∈ withSigma2 invs2_ggp invs2_ggp_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_ggp, D = C := by
  decide +kernel

/-- A two-photon contraction of `ggp` is 1PI iff it is one of the 0 listed. -/
theorem isOnePI2_iff_ggp (C : Contraction 0 2 k_ggp) : IsOnePI C ↔ C ∈ onePI2_ggp :=
  (classify2_ggp C.1.1 C (mem_withSigma2 _ invs2_ggp_complete C)).trans (by simp)

/-! ### `gfg` -/

/-- The photon pairings of `gfg` with two external photons. -/
def invs2_gfg : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gfg)) :=
  [photonPerm2 k_gfg
        [(.inl 0, .inl 1),
         (.inr (psK k_gfg 0 0), .inr (psK k_gfg 2 0))],
    photonPerm2 k_gfg
        [(.inl 0, .inr (psK k_gfg 0 0)),
         (.inl 1, .inr (psK k_gfg 2 0))],
    photonPerm2 k_gfg
        [(.inl 0, .inr (psK k_gfg 2 0)),
         (.inl 1, .inr (psK k_gfg 0 0))]]

theorem invs2_gfg_invol : ∀ τ ∈ invs2_gfg, IsInvol2 τ := by decide +kernel

theorem invs2_gfg_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gfg), IsInvol2 τ → τ ∈ invs2_gfg := by
  decide +kernel

/-- The 1PI two-photon contractions of `gfg`. -/
def onePI2_gfg : List (Contraction 0 2 k_gfg) :=
  [⟨(fermionPerm0 k_gfg [[fvK k_gfg 0, fvK k_gfg 2, fvK k_gfg 1]],
      photonPerm2 k_gfg
        [(.inl 0, .inr (psK k_gfg 0 0)),
         (.inl 1, .inr (psK k_gfg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gfg [[fvK k_gfg 0, fvK k_gfg 1, fvK k_gfg 2]],
      photonPerm2 k_gfg
        [(.inl 0, .inr (psK k_gfg 0 0)),
         (.inl 1, .inr (psK k_gfg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gfg [[fvK k_gfg 0, fvK k_gfg 2, fvK k_gfg 1]],
      photonPerm2 k_gfg
        [(.inl 0, .inr (psK k_gfg 2 0)),
         (.inl 1, .inr (psK k_gfg 0 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_gfg [[fvK k_gfg 0, fvK k_gfg 1, fvK k_gfg 2]],
      photonPerm2 k_gfg
        [(.inl 0, .inr (psK k_gfg 2 0)),
         (.inl 1, .inr (psK k_gfg 0 0))]), by decide +kernel⟩]

theorem classify2_gfg : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_gfg),
    ∀ C ∈ withSigma2 invs2_gfg invs2_gfg_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_gfg, D = C := by
  decide +kernel

/-- A two-photon contraction of `gfg` is 1PI iff it is one of the 4 listed. -/
theorem isOnePI2_iff_gfg (C : Contraction 0 2 k_gfg) : IsOnePI C ↔ C ∈ onePI2_gfg :=
  (classify2_gfg C.1.1 C (mem_withSigma2 _ invs2_gfg_complete C)).trans (by simp)

/-! ### `gpg` -/

/-- The photon pairings of `gpg` with two external photons. -/
def invs2_gpg : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gpg)) :=
  [photonPerm2 k_gpg
        [(.inl 0, .inl 1),
         (.inr (psK k_gpg 0 0), .inr (psK k_gpg 1 0)),
         (.inr (psK k_gpg 1 1), .inr (psK k_gpg 2 0))],
    photonPerm2 k_gpg
        [(.inl 0, .inl 1),
         (.inr (psK k_gpg 0 0), .inr (psK k_gpg 1 1)),
         (.inr (psK k_gpg 1 0), .inr (psK k_gpg 2 0))],
    photonPerm2 k_gpg
        [(.inl 0, .inl 1),
         (.inr (psK k_gpg 0 0), .inr (psK k_gpg 2 0)),
         (.inr (psK k_gpg 1 0), .inr (psK k_gpg 1 1))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 0 0)),
         (.inl 1, .inr (psK k_gpg 1 0)),
         (.inr (psK k_gpg 1 1), .inr (psK k_gpg 2 0))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 0 0)),
         (.inl 1, .inr (psK k_gpg 1 1)),
         (.inr (psK k_gpg 1 0), .inr (psK k_gpg 2 0))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 0 0)),
         (.inl 1, .inr (psK k_gpg 2 0)),
         (.inr (psK k_gpg 1 0), .inr (psK k_gpg 1 1))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 1 0)),
         (.inl 1, .inr (psK k_gpg 0 0)),
         (.inr (psK k_gpg 1 1), .inr (psK k_gpg 2 0))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 1 0)),
         (.inl 1, .inr (psK k_gpg 1 1)),
         (.inr (psK k_gpg 0 0), .inr (psK k_gpg 2 0))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 1 0)),
         (.inl 1, .inr (psK k_gpg 2 0)),
         (.inr (psK k_gpg 0 0), .inr (psK k_gpg 1 1))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 1 1)),
         (.inl 1, .inr (psK k_gpg 0 0)),
         (.inr (psK k_gpg 1 0), .inr (psK k_gpg 2 0))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 1 1)),
         (.inl 1, .inr (psK k_gpg 1 0)),
         (.inr (psK k_gpg 0 0), .inr (psK k_gpg 2 0))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 1 1)),
         (.inl 1, .inr (psK k_gpg 2 0)),
         (.inr (psK k_gpg 0 0), .inr (psK k_gpg 1 0))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 2 0)),
         (.inl 1, .inr (psK k_gpg 0 0)),
         (.inr (psK k_gpg 1 0), .inr (psK k_gpg 1 1))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 2 0)),
         (.inl 1, .inr (psK k_gpg 1 0)),
         (.inr (psK k_gpg 0 0), .inr (psK k_gpg 1 1))],
    photonPerm2 k_gpg
        [(.inl 0, .inr (psK k_gpg 2 0)),
         (.inl 1, .inr (psK k_gpg 1 1)),
         (.inr (psK k_gpg 0 0), .inr (psK k_gpg 1 0))]]

theorem invs2_gpg_invol : ∀ τ ∈ invs2_gpg, IsInvol2 τ := by decide +kernel

theorem invs2_gpg_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_gpg), IsInvol2 τ → τ ∈ invs2_gpg := by
  decide +kernel

/-- The 1PI two-photon contractions of `gpg`. -/
def onePI2_gpg : List (Contraction 0 2 k_gpg) :=
  []

theorem classify2_gpg : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_gpg),
    ∀ C ∈ withSigma2 invs2_gpg invs2_gpg_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_gpg, D = C := by
  decide +kernel

/-- A two-photon contraction of `gpg` is 1PI iff it is one of the 0 listed. -/
theorem isOnePI2_iff_gpg (C : Contraction 0 2 k_gpg) : IsOnePI C ↔ C ∈ onePI2_gpg :=
  (classify2_gpg C.1.1 C (mem_withSigma2 _ invs2_gpg_complete C)).trans (by simp)

/-! ### `fgg` -/

/-- The photon pairings of `fgg` with two external photons. -/
def invs2_fgg : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_fgg)) :=
  [photonPerm2 k_fgg
        [(.inl 0, .inl 1),
         (.inr (psK k_fgg 1 0), .inr (psK k_fgg 2 0))],
    photonPerm2 k_fgg
        [(.inl 0, .inr (psK k_fgg 1 0)),
         (.inl 1, .inr (psK k_fgg 2 0))],
    photonPerm2 k_fgg
        [(.inl 0, .inr (psK k_fgg 2 0)),
         (.inl 1, .inr (psK k_fgg 1 0))]]

theorem invs2_fgg_invol : ∀ τ ∈ invs2_fgg, IsInvol2 τ := by decide +kernel

theorem invs2_fgg_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_fgg), IsInvol2 τ → τ ∈ invs2_fgg := by
  decide +kernel

/-- The 1PI two-photon contractions of `fgg`. -/
def onePI2_fgg : List (Contraction 0 2 k_fgg) :=
  [⟨(fermionPerm0 k_fgg [[fvK k_fgg 0, fvK k_fgg 2, fvK k_fgg 1]],
      photonPerm2 k_fgg
        [(.inl 0, .inr (psK k_fgg 1 0)),
         (.inl 1, .inr (psK k_fgg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_fgg [[fvK k_fgg 0, fvK k_fgg 1, fvK k_fgg 2]],
      photonPerm2 k_fgg
        [(.inl 0, .inr (psK k_fgg 1 0)),
         (.inl 1, .inr (psK k_fgg 2 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_fgg [[fvK k_fgg 0, fvK k_fgg 2, fvK k_fgg 1]],
      photonPerm2 k_fgg
        [(.inl 0, .inr (psK k_fgg 2 0)),
         (.inl 1, .inr (psK k_fgg 1 0))]), by decide +kernel⟩,
    ⟨(fermionPerm0 k_fgg [[fvK k_fgg 0, fvK k_fgg 1, fvK k_fgg 2]],
      photonPerm2 k_fgg
        [(.inl 0, .inr (psK k_fgg 2 0)),
         (.inl 1, .inr (psK k_fgg 1 0))]), by decide +kernel⟩]

theorem classify2_fgg : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_fgg),
    ∀ C ∈ withSigma2 invs2_fgg invs2_fgg_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_fgg, D = C := by
  decide +kernel

/-- A two-photon contraction of `fgg` is 1PI iff it is one of the 4 listed. -/
theorem isOnePI2_iff_fgg (C : Contraction 0 2 k_fgg) : IsOnePI C ↔ C ∈ onePI2_fgg :=
  (classify2_fgg C.1.1 C (mem_withSigma2 _ invs2_fgg_complete C)).trans (by simp)

/-! ### `pgg` -/

/-- The photon pairings of `pgg` with two external photons. -/
def invs2_pgg : List (Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_pgg)) :=
  [photonPerm2 k_pgg
        [(.inl 0, .inl 1),
         (.inr (psK k_pgg 0 0), .inr (psK k_pgg 0 1)),
         (.inr (psK k_pgg 1 0), .inr (psK k_pgg 2 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inl 1),
         (.inr (psK k_pgg 0 0), .inr (psK k_pgg 1 0)),
         (.inr (psK k_pgg 0 1), .inr (psK k_pgg 2 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inl 1),
         (.inr (psK k_pgg 0 0), .inr (psK k_pgg 2 0)),
         (.inr (psK k_pgg 0 1), .inr (psK k_pgg 1 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 0 0)),
         (.inl 1, .inr (psK k_pgg 0 1)),
         (.inr (psK k_pgg 1 0), .inr (psK k_pgg 2 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 0 0)),
         (.inl 1, .inr (psK k_pgg 1 0)),
         (.inr (psK k_pgg 0 1), .inr (psK k_pgg 2 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 0 0)),
         (.inl 1, .inr (psK k_pgg 2 0)),
         (.inr (psK k_pgg 0 1), .inr (psK k_pgg 1 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 0 1)),
         (.inl 1, .inr (psK k_pgg 0 0)),
         (.inr (psK k_pgg 1 0), .inr (psK k_pgg 2 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 0 1)),
         (.inl 1, .inr (psK k_pgg 1 0)),
         (.inr (psK k_pgg 0 0), .inr (psK k_pgg 2 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 0 1)),
         (.inl 1, .inr (psK k_pgg 2 0)),
         (.inr (psK k_pgg 0 0), .inr (psK k_pgg 1 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 1 0)),
         (.inl 1, .inr (psK k_pgg 0 0)),
         (.inr (psK k_pgg 0 1), .inr (psK k_pgg 2 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 1 0)),
         (.inl 1, .inr (psK k_pgg 0 1)),
         (.inr (psK k_pgg 0 0), .inr (psK k_pgg 2 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 1 0)),
         (.inl 1, .inr (psK k_pgg 2 0)),
         (.inr (psK k_pgg 0 0), .inr (psK k_pgg 0 1))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 2 0)),
         (.inl 1, .inr (psK k_pgg 0 0)),
         (.inr (psK k_pgg 0 1), .inr (psK k_pgg 1 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 2 0)),
         (.inl 1, .inr (psK k_pgg 0 1)),
         (.inr (psK k_pgg 0 0), .inr (psK k_pgg 1 0))],
    photonPerm2 k_pgg
        [(.inl 0, .inr (psK k_pgg 2 0)),
         (.inl 1, .inr (psK k_pgg 1 0)),
         (.inr (psK k_pgg 0 0), .inr (psK k_pgg 0 1))]]

theorem invs2_pgg_invol : ∀ τ ∈ invs2_pgg, IsInvol2 τ := by decide +kernel

theorem invs2_pgg_complete :
    ∀ τ : Equiv.Perm (Fin 2 ⊕ Wick.PhotonSlot k_pgg), IsInvol2 τ → τ ∈ invs2_pgg := by
  decide +kernel

/-- The 1PI two-photon contractions of `pgg`. -/
def onePI2_pgg : List (Contraction 0 2 k_pgg) :=
  []

theorem classify2_pgg : ∀ σ : Equiv.Perm (Fin 0 ⊕ Wick.FermionVertex k_pgg),
    ∀ C ∈ withSigma2 invs2_pgg invs2_pgg_invol σ, IsOnePI C ↔ ∃ D ∈ onePI2_pgg, D = C := by
  decide +kernel

/-- A two-photon contraction of `pgg` is 1PI iff it is one of the 0 listed. -/
theorem isOnePI2_iff_pgg (C : Contraction 0 2 k_pgg) : IsOnePI C ↔ C ∈ onePI2_pgg :=
  (classify2_pgg C.1.1 C (mem_withSigma2 _ invs2_pgg_complete C)).trans (by simp)


end QED.GradedProof.VP2

end
