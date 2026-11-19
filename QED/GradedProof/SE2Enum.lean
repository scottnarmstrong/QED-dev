/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.EnumerationCounterterm
public import QED.TwoLoop.EnumerationOrderFive
public import QED.Frozen.Wick.VertexKindFintype

/-!
# The 1PI one-fermion contractions of order four

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), step 1: the finite enumeration. For the one-fermion function (`nf = 1`,
`nA = 0`) and every kind sequence `κ` whose vertices have total order (V₁) exactly `4`, this file
lists the 1PI contractions (X₁₈). The candidate lists were produced by a faithful Python
re-implementation of the frozen definitions (the generator `gen_se2.py` of the Stage 2 scratch
notes); nothing of it is trusted: every statement is checked by the kernel (`decide +kernel`).

The kind sequences of total order `4` (named by their kinds: `g` gauge, `C` gaugeCt, `f`
fermionCt, `p` photonCt) are `gC`, `Cg`, `ff`, `fp`, `pf`, `pp` (two vertices), `ggf`, `gfg`,
`fgg`, `ggp`, `gpg`, `pgg` (three vertices) and `gggg` (four vertices)
(`filter_order_eq_four_*`). Their 1PI contractions:

* `gC`, `Cg`: 2 each, the one-loop self-energy with one vertex a `gaugeCt` vertex;
* `ggf`, `gfg`, `fgg`: 2 each, the one-loop self-energy with the `fermionCt` vertex on the
  internal electron line;
* `ggp`, `gpg`, `pgg`: 4 each, the one-loop self-energy with the `photonCt` vertex on the
  internal photon line (two ways to join its two photon fields);
* `gggg`: 72, the rainbow, crossed and vacuum-polarization graphs, 24 each;
* `ff`, `fp`, `pf`, `pp`: none (trees or disconnected).

## Main statements

* `QED.GradedProof.SE2.filter_order_eq_four_*`: the kind sequences of total order `4`.
* `QED.GradedProof.SE2.isOnePI_iff_<κ>`: a contraction of `κ` is 1PI iff it is listed.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Enumeration

variable {N : ℕ}

/-- The fermion pairing with open line `y → v₁ → ⋯ → v_k → x` and closed loops
`l₁ → l₂ → ⋯ → l₁`, the arrows giving the fermion flow. -/
def fermionPermL (κ : Fin N → Wick.VertexKind) (openLine : List (Wick.FermionVertex κ))
    (loops : List (List (Wick.FermionVertex κ))) : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ) :=
  (Sum.inl 0 :: openLine.reverse.map Sum.inr).formPerm *
    (loops.map fun l => (l.reverse.map Sum.inr).formPerm).prod

/-- The photon pairing with the internal lines `pairs` and no external photon. -/
def photonPerm0 (κ : Fin N → Wick.VertexKind)
    (pairs : List (Wick.PhotonSlot κ × Wick.PhotonSlot κ)) :
    Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot κ) :=
  (pairs.map fun p => Equiv.swap (.inr p.1) (.inr p.2)).prod

/-- A fixed-point-free involution of the photon fields. -/
def IsInvol0 {κ : Fin N → Wick.VertexKind} (τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot κ)) : Prop :=
  ∀ b, τ (τ b) = b ∧ τ b ≠ b

instance {κ : Fin N → Wick.VertexKind} : DecidablePred (IsInvol0 (κ := κ)) := fun τ => by
  unfold IsInvol0; infer_instance

/-- The contractions with fermion pairing `σ` and a photon pairing from the list `invs`. -/
def withSigma0 {κ : Fin N → Wick.VertexKind}
    (invs : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot κ))) (hinv : ∀ τ ∈ invs, IsInvol0 τ)
    (σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex κ)) : List (Contraction 1 0 κ) :=
  invs.attach.map fun τ => ⟨(σ, τ.1), fun b => hinv τ.1 τ.2 b⟩

theorem mem_withSigma0 {κ : Fin N → Wick.VertexKind}
    {invs : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot κ))} (hinv : ∀ τ ∈ invs, IsInvol0 τ)
    (hcomp : ∀ τ, IsInvol0 τ → τ ∈ invs) (C : Contraction 1 0 κ) :
    C ∈ withSigma0 invs hinv C.1.1 :=
  List.mem_map.mpr ⟨⟨C.1.2, hcomp _ C.2⟩, List.mem_attach _ _, rfl⟩

/-! ### `gC` -/

/-- The kind sequence `gC`. -/
def k_gC : Fin 2 → Wick.VertexKind := ![.gauge, .gaugeCt]

/-- The photon pairings of `gC`. -/
def invs_gC : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_gC)) :=
  [photonPerm0 k_gC
        [(psK k_gC 0 0, psK k_gC 1 0)]]

theorem invs_gC_invol : ∀ τ ∈ invs_gC, IsInvol0 τ := by decide +kernel

theorem invs_gC_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_gC), IsInvol0 τ → τ ∈ invs_gC := by
  decide +kernel

/-- The 1PI contractions of `gC`. -/
def onePI_gC : List (Contraction 1 0 k_gC) :=
  [⟨(fermionPermL k_gC [fvK k_gC 1, fvK k_gC 0] [],
      photonPerm0 k_gC
        [(psK k_gC 0 0, psK k_gC 1 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gC [fvK k_gC 0, fvK k_gC 1] [],
      photonPerm0 k_gC
        [(psK k_gC 0 0, psK k_gC 1 0)]), by decide +kernel⟩]

theorem onePI_gC_nodup : (onePI_gC).Nodup := by decide +kernel

theorem classify_gC : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_gC),
    ∀ C ∈ withSigma0 invs_gC invs_gC_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_gC, D = C := by
  decide +kernel

/-- A contraction of `gC` is 1PI iff it is one of the 2 listed. -/
theorem isOnePI_iff_gC (C : Contraction 1 0 k_gC) : IsOnePI C ↔ C ∈ onePI_gC :=
  (classify_gC C.1.1 C (mem_withSigma0 _ invs_gC_complete C)).trans (by simp)

/-! ### `Cg` -/

/-- The kind sequence `Cg`. -/
def k_Cg : Fin 2 → Wick.VertexKind := ![.gaugeCt, .gauge]

/-- The photon pairings of `Cg`. -/
def invs_Cg : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_Cg)) :=
  [photonPerm0 k_Cg
        [(psK k_Cg 0 0, psK k_Cg 1 0)]]

theorem invs_Cg_invol : ∀ τ ∈ invs_Cg, IsInvol0 τ := by decide +kernel

theorem invs_Cg_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_Cg), IsInvol0 τ → τ ∈ invs_Cg := by
  decide +kernel

/-- The 1PI contractions of `Cg`. -/
def onePI_Cg : List (Contraction 1 0 k_Cg) :=
  [⟨(fermionPermL k_Cg [fvK k_Cg 1, fvK k_Cg 0] [],
      photonPerm0 k_Cg
        [(psK k_Cg 0 0, psK k_Cg 1 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_Cg [fvK k_Cg 0, fvK k_Cg 1] [],
      photonPerm0 k_Cg
        [(psK k_Cg 0 0, psK k_Cg 1 0)]), by decide +kernel⟩]

theorem onePI_Cg_nodup : (onePI_Cg).Nodup := by decide +kernel

theorem classify_Cg : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_Cg),
    ∀ C ∈ withSigma0 invs_Cg invs_Cg_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_Cg, D = C := by
  decide +kernel

/-- A contraction of `Cg` is 1PI iff it is one of the 2 listed. -/
theorem isOnePI_iff_Cg (C : Contraction 1 0 k_Cg) : IsOnePI C ↔ C ∈ onePI_Cg :=
  (classify_Cg C.1.1 C (mem_withSigma0 _ invs_Cg_complete C)).trans (by simp)

/-! ### `ff` -/

/-- The kind sequence `ff`. -/
def k_ff : Fin 2 → Wick.VertexKind := ![.fermionCt, .fermionCt]

/-- The photon pairings of `ff`. -/
def invs_ff : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_ff)) :=
  [photonPerm0 k_ff
        []]

theorem invs_ff_invol : ∀ τ ∈ invs_ff, IsInvol0 τ := by decide +kernel

theorem invs_ff_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_ff), IsInvol0 τ → τ ∈ invs_ff := by
  decide +kernel

/-- The 1PI contractions of `ff`. -/
def onePI_ff : List (Contraction 1 0 k_ff) :=
  []

theorem onePI_ff_nodup : (onePI_ff).Nodup := by decide +kernel

theorem classify_ff : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_ff),
    ∀ C ∈ withSigma0 invs_ff invs_ff_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_ff, D = C := by
  decide +kernel

/-- A contraction of `ff` is 1PI iff it is one of the 0 listed. -/
theorem isOnePI_iff_ff (C : Contraction 1 0 k_ff) : IsOnePI C ↔ C ∈ onePI_ff :=
  (classify_ff C.1.1 C (mem_withSigma0 _ invs_ff_complete C)).trans (by simp)

/-! ### `fp` -/

/-- The kind sequence `fp`. -/
def k_fp : Fin 2 → Wick.VertexKind := ![.fermionCt, .photonCt]

/-- The photon pairings of `fp`. -/
def invs_fp : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_fp)) :=
  [photonPerm0 k_fp
        [(psK k_fp 1 0, psK k_fp 1 1)]]

theorem invs_fp_invol : ∀ τ ∈ invs_fp, IsInvol0 τ := by decide +kernel

theorem invs_fp_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_fp), IsInvol0 τ → τ ∈ invs_fp := by
  decide +kernel

/-- The 1PI contractions of `fp`. -/
def onePI_fp : List (Contraction 1 0 k_fp) :=
  []

theorem onePI_fp_nodup : (onePI_fp).Nodup := by decide +kernel

theorem classify_fp : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_fp),
    ∀ C ∈ withSigma0 invs_fp invs_fp_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_fp, D = C := by
  decide +kernel

/-- A contraction of `fp` is 1PI iff it is one of the 0 listed. -/
theorem isOnePI_iff_fp (C : Contraction 1 0 k_fp) : IsOnePI C ↔ C ∈ onePI_fp :=
  (classify_fp C.1.1 C (mem_withSigma0 _ invs_fp_complete C)).trans (by simp)

/-! ### `pf` -/

/-- The kind sequence `pf`. -/
def k_pf : Fin 2 → Wick.VertexKind := ![.photonCt, .fermionCt]

/-- The photon pairings of `pf`. -/
def invs_pf : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_pf)) :=
  [photonPerm0 k_pf
        [(psK k_pf 0 0, psK k_pf 0 1)]]

theorem invs_pf_invol : ∀ τ ∈ invs_pf, IsInvol0 τ := by decide +kernel

theorem invs_pf_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_pf), IsInvol0 τ → τ ∈ invs_pf := by
  decide +kernel

/-- The 1PI contractions of `pf`. -/
def onePI_pf : List (Contraction 1 0 k_pf) :=
  []

theorem onePI_pf_nodup : (onePI_pf).Nodup := by decide +kernel

theorem classify_pf : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_pf),
    ∀ C ∈ withSigma0 invs_pf invs_pf_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_pf, D = C := by
  decide +kernel

/-- A contraction of `pf` is 1PI iff it is one of the 0 listed. -/
theorem isOnePI_iff_pf (C : Contraction 1 0 k_pf) : IsOnePI C ↔ C ∈ onePI_pf :=
  (classify_pf C.1.1 C (mem_withSigma0 _ invs_pf_complete C)).trans (by simp)

/-! ### `pp` -/

/-- The kind sequence `pp`. -/
def k_pp : Fin 2 → Wick.VertexKind := ![.photonCt, .photonCt]

/-- The photon pairings of `pp`. -/
def invs_pp : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_pp)) :=
  [photonPerm0 k_pp
        [(psK k_pp 0 0, psK k_pp 0 1),
         (psK k_pp 1 0, psK k_pp 1 1)],
    photonPerm0 k_pp
        [(psK k_pp 0 0, psK k_pp 1 0),
         (psK k_pp 0 1, psK k_pp 1 1)],
    photonPerm0 k_pp
        [(psK k_pp 0 0, psK k_pp 1 1),
         (psK k_pp 0 1, psK k_pp 1 0)]]

theorem invs_pp_invol : ∀ τ ∈ invs_pp, IsInvol0 τ := by decide +kernel

theorem invs_pp_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_pp), IsInvol0 τ → τ ∈ invs_pp := by
  decide +kernel

/-- The 1PI contractions of `pp`. -/
def onePI_pp : List (Contraction 1 0 k_pp) :=
  []

theorem onePI_pp_nodup : (onePI_pp).Nodup := by decide +kernel

theorem classify_pp : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_pp),
    ∀ C ∈ withSigma0 invs_pp invs_pp_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_pp, D = C := by
  decide +kernel

/-- A contraction of `pp` is 1PI iff it is one of the 0 listed. -/
theorem isOnePI_iff_pp (C : Contraction 1 0 k_pp) : IsOnePI C ↔ C ∈ onePI_pp :=
  (classify_pp C.1.1 C (mem_withSigma0 _ invs_pp_complete C)).trans (by simp)

/-! ### `ggf` -/

/-- The kind sequence `ggf`. -/
def k_ggf : Fin 3 → Wick.VertexKind := ![.gauge, .gauge, .fermionCt]

/-- The photon pairings of `ggf`. -/
def invs_ggf : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_ggf)) :=
  [photonPerm0 k_ggf
        [(psK k_ggf 0 0, psK k_ggf 1 0)]]

theorem invs_ggf_invol : ∀ τ ∈ invs_ggf, IsInvol0 τ := by decide +kernel

theorem invs_ggf_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_ggf), IsInvol0 τ → τ ∈ invs_ggf := by
  decide +kernel

/-- The 1PI contractions of `ggf`. -/
def onePI_ggf : List (Contraction 1 0 k_ggf) :=
  [⟨(fermionPermL k_ggf [fvK k_ggf 1, fvK k_ggf 2, fvK k_ggf 0] [],
      photonPerm0 k_ggf
        [(psK k_ggf 0 0, psK k_ggf 1 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_ggf [fvK k_ggf 0, fvK k_ggf 2, fvK k_ggf 1] [],
      photonPerm0 k_ggf
        [(psK k_ggf 0 0, psK k_ggf 1 0)]), by decide +kernel⟩]

theorem onePI_ggf_nodup : (onePI_ggf).Nodup := by decide +kernel

theorem classify_ggf : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_ggf),
    ∀ C ∈ withSigma0 invs_ggf invs_ggf_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_ggf, D = C := by
  decide +kernel

/-- A contraction of `ggf` is 1PI iff it is one of the 2 listed. -/
theorem isOnePI_iff_ggf (C : Contraction 1 0 k_ggf) : IsOnePI C ↔ C ∈ onePI_ggf :=
  (classify_ggf C.1.1 C (mem_withSigma0 _ invs_ggf_complete C)).trans (by simp)

/-! ### `ggp` -/

/-- The kind sequence `ggp`. -/
def k_ggp : Fin 3 → Wick.VertexKind := ![.gauge, .gauge, .photonCt]

/-- The photon pairings of `ggp`. -/
def invs_ggp : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_ggp)) :=
  [photonPerm0 k_ggp
        [(psK k_ggp 0 0, psK k_ggp 1 0),
         (psK k_ggp 2 0, psK k_ggp 2 1)],
    photonPerm0 k_ggp
        [(psK k_ggp 0 0, psK k_ggp 2 0),
         (psK k_ggp 1 0, psK k_ggp 2 1)],
    photonPerm0 k_ggp
        [(psK k_ggp 0 0, psK k_ggp 2 1),
         (psK k_ggp 1 0, psK k_ggp 2 0)]]

theorem invs_ggp_invol : ∀ τ ∈ invs_ggp, IsInvol0 τ := by decide +kernel

theorem invs_ggp_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_ggp), IsInvol0 τ → τ ∈ invs_ggp := by
  decide +kernel

/-- The 1PI contractions of `ggp`. -/
def onePI_ggp : List (Contraction 1 0 k_ggp) :=
  [⟨(fermionPermL k_ggp [fvK k_ggp 1, fvK k_ggp 0] [],
      photonPerm0 k_ggp
        [(psK k_ggp 0 0, psK k_ggp 2 0),
         (psK k_ggp 1 0, psK k_ggp 2 1)]), by decide +kernel⟩,
    ⟨(fermionPermL k_ggp [fvK k_ggp 1, fvK k_ggp 0] [],
      photonPerm0 k_ggp
        [(psK k_ggp 0 0, psK k_ggp 2 1),
         (psK k_ggp 1 0, psK k_ggp 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_ggp [fvK k_ggp 0, fvK k_ggp 1] [],
      photonPerm0 k_ggp
        [(psK k_ggp 0 0, psK k_ggp 2 0),
         (psK k_ggp 1 0, psK k_ggp 2 1)]), by decide +kernel⟩,
    ⟨(fermionPermL k_ggp [fvK k_ggp 0, fvK k_ggp 1] [],
      photonPerm0 k_ggp
        [(psK k_ggp 0 0, psK k_ggp 2 1),
         (psK k_ggp 1 0, psK k_ggp 2 0)]), by decide +kernel⟩]

theorem onePI_ggp_nodup : (onePI_ggp).Nodup := by decide +kernel

theorem classify_ggp : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_ggp),
    ∀ C ∈ withSigma0 invs_ggp invs_ggp_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_ggp, D = C := by
  decide +kernel

/-- A contraction of `ggp` is 1PI iff it is one of the 4 listed. -/
theorem isOnePI_iff_ggp (C : Contraction 1 0 k_ggp) : IsOnePI C ↔ C ∈ onePI_ggp :=
  (classify_ggp C.1.1 C (mem_withSigma0 _ invs_ggp_complete C)).trans (by simp)

/-! ### `gfg` -/

/-- The kind sequence `gfg`. -/
def k_gfg : Fin 3 → Wick.VertexKind := ![.gauge, .fermionCt, .gauge]

/-- The photon pairings of `gfg`. -/
def invs_gfg : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_gfg)) :=
  [photonPerm0 k_gfg
        [(psK k_gfg 0 0, psK k_gfg 2 0)]]

theorem invs_gfg_invol : ∀ τ ∈ invs_gfg, IsInvol0 τ := by decide +kernel

theorem invs_gfg_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_gfg), IsInvol0 τ → τ ∈ invs_gfg := by
  decide +kernel

/-- The 1PI contractions of `gfg`. -/
def onePI_gfg : List (Contraction 1 0 k_gfg) :=
  [⟨(fermionPermL k_gfg [fvK k_gfg 2, fvK k_gfg 1, fvK k_gfg 0] [],
      photonPerm0 k_gfg
        [(psK k_gfg 0 0, psK k_gfg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gfg [fvK k_gfg 0, fvK k_gfg 1, fvK k_gfg 2] [],
      photonPerm0 k_gfg
        [(psK k_gfg 0 0, psK k_gfg 2 0)]), by decide +kernel⟩]

theorem onePI_gfg_nodup : (onePI_gfg).Nodup := by decide +kernel

theorem classify_gfg : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_gfg),
    ∀ C ∈ withSigma0 invs_gfg invs_gfg_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_gfg, D = C := by
  decide +kernel

/-- A contraction of `gfg` is 1PI iff it is one of the 2 listed. -/
theorem isOnePI_iff_gfg (C : Contraction 1 0 k_gfg) : IsOnePI C ↔ C ∈ onePI_gfg :=
  (classify_gfg C.1.1 C (mem_withSigma0 _ invs_gfg_complete C)).trans (by simp)

/-! ### `gpg` -/

/-- The kind sequence `gpg`. -/
def k_gpg : Fin 3 → Wick.VertexKind := ![.gauge, .photonCt, .gauge]

/-- The photon pairings of `gpg`. -/
def invs_gpg : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_gpg)) :=
  [photonPerm0 k_gpg
        [(psK k_gpg 0 0, psK k_gpg 1 0),
         (psK k_gpg 1 1, psK k_gpg 2 0)],
    photonPerm0 k_gpg
        [(psK k_gpg 0 0, psK k_gpg 1 1),
         (psK k_gpg 1 0, psK k_gpg 2 0)],
    photonPerm0 k_gpg
        [(psK k_gpg 0 0, psK k_gpg 2 0),
         (psK k_gpg 1 0, psK k_gpg 1 1)]]

theorem invs_gpg_invol : ∀ τ ∈ invs_gpg, IsInvol0 τ := by decide +kernel

theorem invs_gpg_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_gpg), IsInvol0 τ → τ ∈ invs_gpg := by
  decide +kernel

/-- The 1PI contractions of `gpg`. -/
def onePI_gpg : List (Contraction 1 0 k_gpg) :=
  [⟨(fermionPermL k_gpg [fvK k_gpg 2, fvK k_gpg 0] [],
      photonPerm0 k_gpg
        [(psK k_gpg 0 0, psK k_gpg 1 0),
         (psK k_gpg 1 1, psK k_gpg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gpg [fvK k_gpg 2, fvK k_gpg 0] [],
      photonPerm0 k_gpg
        [(psK k_gpg 0 0, psK k_gpg 1 1),
         (psK k_gpg 1 0, psK k_gpg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gpg [fvK k_gpg 0, fvK k_gpg 2] [],
      photonPerm0 k_gpg
        [(psK k_gpg 0 0, psK k_gpg 1 0),
         (psK k_gpg 1 1, psK k_gpg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gpg [fvK k_gpg 0, fvK k_gpg 2] [],
      photonPerm0 k_gpg
        [(psK k_gpg 0 0, psK k_gpg 1 1),
         (psK k_gpg 1 0, psK k_gpg 2 0)]), by decide +kernel⟩]

theorem onePI_gpg_nodup : (onePI_gpg).Nodup := by decide +kernel

theorem classify_gpg : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_gpg),
    ∀ C ∈ withSigma0 invs_gpg invs_gpg_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_gpg, D = C := by
  decide +kernel

/-- A contraction of `gpg` is 1PI iff it is one of the 4 listed. -/
theorem isOnePI_iff_gpg (C : Contraction 1 0 k_gpg) : IsOnePI C ↔ C ∈ onePI_gpg :=
  (classify_gpg C.1.1 C (mem_withSigma0 _ invs_gpg_complete C)).trans (by simp)

/-! ### `fgg` -/

/-- The kind sequence `fgg`. -/
def k_fgg : Fin 3 → Wick.VertexKind := ![.fermionCt, .gauge, .gauge]

/-- The photon pairings of `fgg`. -/
def invs_fgg : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_fgg)) :=
  [photonPerm0 k_fgg
        [(psK k_fgg 1 0, psK k_fgg 2 0)]]

theorem invs_fgg_invol : ∀ τ ∈ invs_fgg, IsInvol0 τ := by decide +kernel

theorem invs_fgg_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_fgg), IsInvol0 τ → τ ∈ invs_fgg := by
  decide +kernel

/-- The 1PI contractions of `fgg`. -/
def onePI_fgg : List (Contraction 1 0 k_fgg) :=
  [⟨(fermionPermL k_fgg [fvK k_fgg 2, fvK k_fgg 0, fvK k_fgg 1] [],
      photonPerm0 k_fgg
        [(psK k_fgg 1 0, psK k_fgg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_fgg [fvK k_fgg 1, fvK k_fgg 0, fvK k_fgg 2] [],
      photonPerm0 k_fgg
        [(psK k_fgg 1 0, psK k_fgg 2 0)]), by decide +kernel⟩]

theorem onePI_fgg_nodup : (onePI_fgg).Nodup := by decide +kernel

theorem classify_fgg : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_fgg),
    ∀ C ∈ withSigma0 invs_fgg invs_fgg_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_fgg, D = C := by
  decide +kernel

/-- A contraction of `fgg` is 1PI iff it is one of the 2 listed. -/
theorem isOnePI_iff_fgg (C : Contraction 1 0 k_fgg) : IsOnePI C ↔ C ∈ onePI_fgg :=
  (classify_fgg C.1.1 C (mem_withSigma0 _ invs_fgg_complete C)).trans (by simp)

/-! ### `pgg` -/

/-- The kind sequence `pgg`. -/
def k_pgg : Fin 3 → Wick.VertexKind := ![.photonCt, .gauge, .gauge]

/-- The photon pairings of `pgg`. -/
def invs_pgg : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_pgg)) :=
  [photonPerm0 k_pgg
        [(psK k_pgg 0 0, psK k_pgg 0 1),
         (psK k_pgg 1 0, psK k_pgg 2 0)],
    photonPerm0 k_pgg
        [(psK k_pgg 0 0, psK k_pgg 1 0),
         (psK k_pgg 0 1, psK k_pgg 2 0)],
    photonPerm0 k_pgg
        [(psK k_pgg 0 0, psK k_pgg 2 0),
         (psK k_pgg 0 1, psK k_pgg 1 0)]]

theorem invs_pgg_invol : ∀ τ ∈ invs_pgg, IsInvol0 τ := by decide +kernel

theorem invs_pgg_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_pgg), IsInvol0 τ → τ ∈ invs_pgg := by
  decide +kernel

/-- The 1PI contractions of `pgg`. -/
def onePI_pgg : List (Contraction 1 0 k_pgg) :=
  [⟨(fermionPermL k_pgg [fvK k_pgg 2, fvK k_pgg 1] [],
      photonPerm0 k_pgg
        [(psK k_pgg 0 0, psK k_pgg 1 0),
         (psK k_pgg 0 1, psK k_pgg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_pgg [fvK k_pgg 2, fvK k_pgg 1] [],
      photonPerm0 k_pgg
        [(psK k_pgg 0 0, psK k_pgg 2 0),
         (psK k_pgg 0 1, psK k_pgg 1 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_pgg [fvK k_pgg 1, fvK k_pgg 2] [],
      photonPerm0 k_pgg
        [(psK k_pgg 0 0, psK k_pgg 1 0),
         (psK k_pgg 0 1, psK k_pgg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_pgg [fvK k_pgg 1, fvK k_pgg 2] [],
      photonPerm0 k_pgg
        [(psK k_pgg 0 0, psK k_pgg 2 0),
         (psK k_pgg 0 1, psK k_pgg 1 0)]), by decide +kernel⟩]

theorem onePI_pgg_nodup : (onePI_pgg).Nodup := by decide +kernel

theorem classify_pgg : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_pgg),
    ∀ C ∈ withSigma0 invs_pgg invs_pgg_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_pgg, D = C := by
  decide +kernel

/-- A contraction of `pgg` is 1PI iff it is one of the 4 listed. -/
theorem isOnePI_iff_pgg (C : Contraction 1 0 k_pgg) : IsOnePI C ↔ C ∈ onePI_pgg :=
  (classify_pgg C.1.1 C (mem_withSigma0 _ invs_pgg_complete C)).trans (by simp)

/-! ### `gggg` -/

/-- The kind sequence `gggg`. -/
def k_gggg : Fin 4 → Wick.VertexKind := ![.gauge, .gauge, .gauge, .gauge]

/-- The photon pairings of `gggg`. -/
def invs_gggg : List (Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_gggg)) :=
  [photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)],
    photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)],
    photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]]

theorem invs_gggg_invol : ∀ τ ∈ invs_gggg, IsInvol0 τ := by decide +kernel

theorem invs_gggg_complete :
    ∀ τ : Equiv.Perm (Fin 0 ⊕ Wick.PhotonSlot k_gggg), IsInvol0 τ → τ ∈ invs_gggg := by
  decide +kernel

/-- The 1PI contractions of `gggg`. -/
def onePI_gggg : List (Contraction 1 0 k_gggg) :=
  [⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 0] [[fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 0] [[fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 0] [[fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 0] [[fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 0] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 0] [[fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 0] [[fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 1] [[fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 1] [[fvK k_gggg 2, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 0, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 2, fvK k_gggg 0, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 1] [[fvK k_gggg 0, fvK k_gggg 2]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 1] [[fvK k_gggg 0, fvK k_gggg 2]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 0, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 3, fvK k_gggg 0, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 1] [[fvK k_gggg 0, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 1] [[fvK k_gggg 0, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 2] [[fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 2] [[fvK k_gggg 1, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 0, fvK k_gggg 3, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 2] [[fvK k_gggg 0, fvK k_gggg 1]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 2] [[fvK k_gggg 0, fvK k_gggg 1]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 0, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 1, fvK k_gggg 0, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 0, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 3, fvK k_gggg 0, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 2] [[fvK k_gggg 0, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 2] [[fvK k_gggg 0, fvK k_gggg 3]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 3, fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 3] [[fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 3] [[fvK k_gggg 1, fvK k_gggg 2]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 0, fvK k_gggg 2, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 3] [[fvK k_gggg 0, fvK k_gggg 1]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 3] [[fvK k_gggg 0, fvK k_gggg 1]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 0, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 1, fvK k_gggg 0, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 3] [[fvK k_gggg 0, fvK k_gggg 2]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 3] [[fvK k_gggg 0, fvK k_gggg 2]],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 0, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 0, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 2 0),
         (psK k_gggg 1 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 1 0),
         (psK k_gggg 2 0, psK k_gggg 3 0)]), by decide +kernel⟩,
    ⟨(fermionPermL k_gggg [fvK k_gggg 2, fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 3] [],
      photonPerm0 k_gggg
        [(psK k_gggg 0 0, psK k_gggg 3 0),
         (psK k_gggg 1 0, psK k_gggg 2 0)]), by decide +kernel⟩]

theorem onePI_gggg_nodup : (onePI_gggg).Nodup := by decide +kernel

theorem classify_gggg : ∀ σ : Equiv.Perm (Fin 1 ⊕ Wick.FermionVertex k_gggg),
    ∀ C ∈ withSigma0 invs_gggg invs_gggg_invol σ, IsOnePI C ↔ ∃ D ∈ onePI_gggg, D = C := by
  decide +kernel

/-- A contraction of `gggg` is 1PI iff it is one of the 72 listed. -/
theorem isOnePI_iff_gggg (C : Contraction 1 0 k_gggg) : IsOnePI C ↔ C ∈ onePI_gggg :=
  (classify_gggg C.1.1 C (mem_withSigma0 _ invs_gggg_complete C)).trans (by simp)

/-! ### The kind sequences of order four -/

theorem filter_order_eq_four_zero :
    (Finset.univ : Finset (Fin 0 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 4) = ∅ := by decide +kernel

theorem filter_order_eq_four_one :
    (Finset.univ : Finset (Fin 1 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 4) = ∅ := by decide +kernel

theorem filter_order_eq_four_two :
    (Finset.univ : Finset (Fin 2 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 4) = [k_gC, k_Cg, k_ff, k_fp, k_pf, k_pp].toFinset := by
  decide +kernel

theorem filter_order_eq_four_three :
    (Finset.univ : Finset (Fin 3 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 4) =
      [k_ggf, k_ggp, k_gfg, k_gpg, k_fgg, k_pgg].toFinset := by
  decide +kernel

theorem filter_order_eq_four_four :
    (Finset.univ : Finset (Fin 4 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 4) = {k_gggg} := by decide +kernel

/-- A kind sequence of total order `4` has at most four vertices. -/
theorem le_four_of_sum_order {κ : Fin N → Wick.VertexKind} (h : ∑ t, (κ t).order = 4) :
    N ≤ 4 :=
  h ▸ le_sum_order κ

/-- The kind sequences of two vertices and total order `4`. -/
theorem mem_two {κ : Fin 2 → Wick.VertexKind} (h : ∑ t, (κ t).order = 4) :
    κ = k_gC ∨ κ = k_Cg ∨ κ = k_ff ∨ κ = k_fp ∨ κ = k_pf ∨ κ = k_pp := by
  have hm : κ ∈ (Finset.univ : Finset (Fin 2 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 4) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  rw [filter_order_eq_four_two] at hm
  simpa using hm

/-- The kind sequences of three vertices and total order `4`. -/
theorem mem_three {κ : Fin 3 → Wick.VertexKind} (h : ∑ t, (κ t).order = 4) :
    κ = k_ggf ∨ κ = k_ggp ∨ κ = k_gfg ∨ κ = k_gpg ∨ κ = k_fgg ∨ κ = k_pgg := by
  have hm : κ ∈ (Finset.univ : Finset (Fin 3 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 4) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  rw [filter_order_eq_four_three] at hm
  simpa using hm

/-- The kind sequence of four vertices and total order `4`. -/
theorem eq_four {κ : Fin 4 → Wick.VertexKind} (h : ∑ t, (κ t).order = 4) : κ = k_gggg := by
  have hm : κ ∈ (Finset.univ : Finset (Fin 4 → Wick.VertexKind)).filter
      (fun κ => ∑ t, (κ t).order = 4) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  rw [filter_order_eq_four_four] at hm
  simpa using hm

/-- No kind sequence of at most one vertex has total order `4`. -/
theorem not_le_one {κ : Fin N → Wick.VertexKind} (hN : N ≤ 1) : ∑ t, (κ t).order ≠ 4 := by
  intro h
  obtain _ | _ | N := N
  · have hm : κ ∈ (Finset.univ : Finset (Fin 0 → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order = 4) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [filter_order_eq_four_zero] at hm
    simp at hm
  · have hm : κ ∈ (Finset.univ : Finset (Fin 1 → Wick.VertexKind)).filter
        (fun κ => ∑ t, (κ t).order = 4) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [filter_order_eq_four_one] at hm
    simp at hm
  · omega

end QED.GradedProof.SE2

end
