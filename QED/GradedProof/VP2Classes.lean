/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.VP2EnumG
public import QED.TwoLoop.RelabelCountertermClasses

/-!
# The seven classes of 1PI two-photon contractions of order four

Helper level for the Phase 5 Stage 2 goal (G-Π₂)
`QED.Graded.vacuumPolarizationPart_two_existsUnique` (decision D-57), step 1. Every 1PI
contraction of the two-photon function (`nf = 0`, `nA = 2`) whose vertices have total order
(V₁) exactly `4` is a relabelling across kind sequences (`relabelK`) of one of seven
representatives. Each has one closed fermion loop `[l₁, …, l_k]` (the fermion pairing
`fermionPerm0`, with `σ (l_{i+1}) = l_i`), the external photon `0` at vertex `0`:

| class | kinds | loop | external photon `1` at | internal photon |
| --- | --- | --- | --- | --- |
| `VA` | `gggg` | `0 1 2 3` | `1` | `(2 3)` |
| `VB` | `gggg` | `0 1 2 3` | `2` | `(1 3)` |
| `VC` | `gggg` | `0 1 2 3` | `3` | `(1 2)` |
| `G0` (`δ₁` at external photon `1`) | `gC` | `0 1` | `1` | — |
| `G1` (`δ₁` at external photon `0`) | `gC` | `0 1` | `0`, photon `0` at `1` | — |
| `F0` (`δ₂`, `δ_m`) | `ggf` | `0 1 2` | `1` | — |
| `F1` (`δ₂`, `δ_m`, other line) | `ggf` | `0 2 1` | `1` | — |

`VA`, `VC` are the two-loop bubbles with a self-energy insertion on one of the two electron
lines, `VB` the one with the internal photon across the loop; `F0`, `F1` carry the fermion
counterterm on one or the other electron line of the one-loop bubble. In `G1` the photons are
swapped: external photon `0` at the `gaugeCt` vertex `1`, external photon `1` at `0`.

The representatives and the relabellings were found by the generator of the Stage 2 scratch
notes; nothing is trusted: `onePI2_<κ>_eq_relabelK` (checked by `decide +kernel`) writes each
list of `VP2Enum`, `VP2EnumG` as the list of relabelled representatives.

## Main statements

* `QED.GradedProof.VP2.forall_of_order_four2`: a property of the listed contractions holds for
  every 1PI two-photon contraction of total order `4`.
* `QED.GradedProof.VP2.induction_of_order_four2`: a property of the seven representatives that
  passes to relabellings of 1PI contractions holds for every 1PI two-photon contraction of total
  order `4`.
-/

@[expose] public section

namespace QED.GradedProof.VP2

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel QED.GradedProof.SE2

/-! ### The representatives -/

/-- The class representative `VA`. -/
def repVA : Contraction 0 2 k_gggg :=
  ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
    photonPerm2 k_gggg
      [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 1 0)),
         (.inr (psK k_gggg 2 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩

/-- The class representative `VB`. -/
def repVB : Contraction 0 2 k_gggg :=
  ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
    photonPerm2 k_gggg
      [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 2 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 3 0))]), by decide +kernel⟩

/-- The class representative `VC`. -/
def repVC : Contraction 0 2 k_gggg :=
  ⟨(fermionPerm0 k_gggg [[fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3]],
    photonPerm2 k_gggg
      [(.inl 0, .inr (psK k_gggg 0 0)),
         (.inl 1, .inr (psK k_gggg 3 0)),
         (.inr (psK k_gggg 1 0), .inr (psK k_gggg 2 0))]), by decide +kernel⟩

/-- The class representative `G0`. -/
def repG0 : Contraction 0 2 k_gC :=
  ⟨(fermionPerm0 k_gC [[fvK k_gC 0, fvK k_gC 1]],
    photonPerm2 k_gC
      [(.inl 0, .inr (psK k_gC 0 0)),
         (.inl 1, .inr (psK k_gC 1 0))]), by decide +kernel⟩

/-- The class representative `G1`. -/
def repG1 : Contraction 0 2 k_gC :=
  ⟨(fermionPerm0 k_gC [[fvK k_gC 0, fvK k_gC 1]],
    photonPerm2 k_gC
      [(.inl 0, .inr (psK k_gC 1 0)),
         (.inl 1, .inr (psK k_gC 0 0))]), by decide +kernel⟩

/-- The class representative `F0`. -/
def repF0 : Contraction 0 2 k_ggf :=
  ⟨(fermionPerm0 k_ggf [[fvK k_ggf 0, fvK k_ggf 1, fvK k_ggf 2]],
    photonPerm2 k_ggf
      [(.inl 0, .inr (psK k_ggf 0 0)),
         (.inl 1, .inr (psK k_ggf 1 0))]), by decide +kernel⟩

/-- The class representative `F1`. -/
def repF1 : Contraction 0 2 k_ggf :=
  ⟨(fermionPerm0 k_ggf [[fvK k_ggf 0, fvK k_ggf 2, fvK k_ggf 1]],
    photonPerm2 k_ggf
      [(.inl 0, .inr (psK k_ggf 0 0)),
         (.inl 1, .inr (psK k_ggf 1 0))]), by decide +kernel⟩

theorem repVA_isOnePI : IsOnePI repVA := (isOnePI2_iff_gggg _).mpr (by decide +kernel)
theorem repVB_isOnePI : IsOnePI repVB := (isOnePI2_iff_gggg _).mpr (by decide +kernel)
theorem repVC_isOnePI : IsOnePI repVC := (isOnePI2_iff_gggg _).mpr (by decide +kernel)
theorem repG0_isOnePI : IsOnePI repG0 := (isOnePI2_iff_gC _).mpr (by decide +kernel)
theorem repG1_isOnePI : IsOnePI repG1 := (isOnePI2_iff_gC _).mpr (by decide +kernel)
theorem repF0_isOnePI : IsOnePI repF0 := (isOnePI2_iff_ggf _).mpr (by decide +kernel)
theorem repF1_isOnePI : IsOnePI repF1 := (isOnePI2_iff_ggf _).mpr (by decide +kernel)

/-- Every representative has one closed fermion loop, of sign `-1`. -/
theorem fermionSign_reps2 : fermionSign repVA = -1 ∧ fermionSign repVB = -1 ∧
    fermionSign repVC = -1 ∧ fermionSign repG0 = -1 ∧ fermionSign repG1 = -1 ∧
    fermionSign repF0 = -1 ∧ fermionSign repF1 = -1 := by
  decide +kernel

theorem loopCount_repVA : loopCount repVA = 2 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repVB : loopCount repVB = 2 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repVC : loopCount repVC = 2 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repG0 : loopCount repG0 = 1 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repG1 : loopCount repG1 = 1 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repF0 : loopCount repF0 = 1 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repF1 : loopCount repF1 = 1 := by rw [loopCount_eq_card]; decide +kernel

/-! ### Each list is the list of relabelled representatives -/

/-- The 1PI two-photon contractions of `gC` are relabellings of the representatives. -/
theorem onePI2_gC_eq_relabelK : onePI2_gC =
    [relabelK (permK ![0, 1] ![0, 1]) (by decide +kernel) repG0,
      relabelK (permK ![0, 1] ![0, 1]) (by decide +kernel) repG1] := by
  decide +kernel

/-- The 1PI two-photon contractions of `Cg` are relabellings of the representatives. -/
theorem onePI2_Cg_eq_relabelK : onePI2_Cg =
    [relabelK (permK ![1, 0] ![1, 0]) (by decide +kernel) repG1,
      relabelK (permK ![1, 0] ![1, 0]) (by decide +kernel) repG0] := by
  decide +kernel

/-- The 1PI two-photon contractions of `ggf` are relabellings of the representatives. -/
theorem onePI2_ggf_eq_relabelK : onePI2_ggf =
    [relabelK (permK ![0, 1, 2] ![0, 1, 2]) (by decide +kernel) repF1,
      relabelK (permK ![0, 1, 2] ![0, 1, 2]) (by decide +kernel) repF0,
      relabelK (permK ![1, 0, 2] ![1, 0, 2]) (by decide +kernel) repF0,
      relabelK (permK ![1, 0, 2] ![1, 0, 2]) (by decide +kernel) repF1] := by
  decide +kernel

/-- The 1PI two-photon contractions of `gfg` are relabellings of the representatives. -/
theorem onePI2_gfg_eq_relabelK : onePI2_gfg =
    [relabelK (permK ![0, 2, 1] ![0, 2, 1]) (by decide +kernel) repF0,
      relabelK (permK ![0, 2, 1] ![0, 2, 1]) (by decide +kernel) repF1,
      relabelK (permK ![2, 0, 1] ![1, 2, 0]) (by decide +kernel) repF1,
      relabelK (permK ![2, 0, 1] ![1, 2, 0]) (by decide +kernel) repF0] := by
  decide +kernel

/-- The 1PI two-photon contractions of `fgg` are relabellings of the representatives. -/
theorem onePI2_fgg_eq_relabelK : onePI2_fgg =
    [relabelK (permK ![1, 2, 0] ![2, 0, 1]) (by decide +kernel) repF1,
      relabelK (permK ![1, 2, 0] ![2, 0, 1]) (by decide +kernel) repF0,
      relabelK (permK ![2, 1, 0] ![2, 1, 0]) (by decide +kernel) repF0,
      relabelK (permK ![2, 1, 0] ![2, 1, 0]) (by decide +kernel) repF1] := by
  decide +kernel

/-- Chunk 1 of the 1PI contractions of `gggg` as relabellings of the representatives. -/
theorem onePIG1_eq_relabelK : onePIG1 =
    [relabelK (permK ![0, 3, 2, 1] ![0, 3, 2, 1]) (by decide +kernel) repVC,
      relabelK (permK ![0, 2, 3, 1] ![0, 3, 1, 2]) (by decide +kernel) repVC,
      relabelK (permK ![0, 1, 3, 2] ![0, 1, 3, 2]) (by decide +kernel) repVA,
      relabelK (permK ![0, 3, 1, 2] ![0, 2, 3, 1]) (by decide +kernel) repVB,
      relabelK (permK ![0, 1, 2, 3] ![0, 1, 2, 3]) (by decide +kernel) repVA,
      relabelK (permK ![0, 2, 1, 3] ![0, 2, 1, 3]) (by decide +kernel) repVB,
      relabelK (permK ![0, 3, 2, 1] ![0, 3, 2, 1]) (by decide +kernel) repVB,
      relabelK (permK ![0, 2, 3, 1] ![0, 3, 1, 2]) (by decide +kernel) repVA,
      relabelK (permK ![0, 1, 3, 2] ![0, 1, 3, 2]) (by decide +kernel) repVC,
      relabelK (permK ![0, 3, 1, 2] ![0, 2, 3, 1]) (by decide +kernel) repVC,
      relabelK (permK ![0, 1, 2, 3] ![0, 1, 2, 3]) (by decide +kernel) repVB,
      relabelK (permK ![0, 2, 1, 3] ![0, 2, 1, 3]) (by decide +kernel) repVA,
      relabelK (permK ![0, 3, 2, 1] ![0, 3, 2, 1]) (by decide +kernel) repVA,
      relabelK (permK ![0, 2, 3, 1] ![0, 3, 1, 2]) (by decide +kernel) repVB,
      relabelK (permK ![0, 1, 3, 2] ![0, 1, 3, 2]) (by decide +kernel) repVB,
      relabelK (permK ![0, 3, 1, 2] ![0, 2, 3, 1]) (by decide +kernel) repVA,
      relabelK (permK ![0, 1, 2, 3] ![0, 1, 2, 3]) (by decide +kernel) repVC,
      relabelK (permK ![0, 2, 1, 3] ![0, 2, 1, 3]) (by decide +kernel) repVC] := by
  decide +kernel

/-- Chunk 2 of the 1PI contractions of `gggg` as relabellings of the representatives. -/
theorem onePIG2_eq_relabelK : onePIG2 =
    [relabelK (permK ![1, 0, 3, 2] ![1, 0, 3, 2]) (by decide +kernel) repVA,
      relabelK (permK ![1, 0, 2, 3] ![1, 0, 2, 3]) (by decide +kernel) repVA,
      relabelK (permK ![1, 3, 2, 0] ![3, 0, 2, 1]) (by decide +kernel) repVC,
      relabelK (permK ![1, 2, 0, 3] ![2, 0, 1, 3]) (by decide +kernel) repVB,
      relabelK (permK ![1, 2, 3, 0] ![3, 0, 1, 2]) (by decide +kernel) repVC,
      relabelK (permK ![1, 3, 0, 2] ![2, 0, 3, 1]) (by decide +kernel) repVB,
      relabelK (permK ![1, 0, 3, 2] ![1, 0, 3, 2]) (by decide +kernel) repVC,
      relabelK (permK ![1, 0, 2, 3] ![1, 0, 2, 3]) (by decide +kernel) repVB,
      relabelK (permK ![1, 3, 2, 0] ![3, 0, 2, 1]) (by decide +kernel) repVB,
      relabelK (permK ![1, 2, 0, 3] ![2, 0, 1, 3]) (by decide +kernel) repVA,
      relabelK (permK ![1, 2, 3, 0] ![3, 0, 1, 2]) (by decide +kernel) repVA,
      relabelK (permK ![1, 3, 0, 2] ![2, 0, 3, 1]) (by decide +kernel) repVC,
      relabelK (permK ![1, 0, 3, 2] ![1, 0, 3, 2]) (by decide +kernel) repVB,
      relabelK (permK ![1, 0, 2, 3] ![1, 0, 2, 3]) (by decide +kernel) repVC,
      relabelK (permK ![1, 3, 2, 0] ![3, 0, 2, 1]) (by decide +kernel) repVA,
      relabelK (permK ![1, 2, 0, 3] ![2, 0, 1, 3]) (by decide +kernel) repVC,
      relabelK (permK ![1, 2, 3, 0] ![3, 0, 1, 2]) (by decide +kernel) repVB,
      relabelK (permK ![1, 3, 0, 2] ![2, 0, 3, 1]) (by decide +kernel) repVA] := by
  decide +kernel

/-- Chunk 3 of the 1PI contractions of `gggg` as relabellings of the representatives. -/
theorem onePIG3_eq_relabelK : onePIG3 =
    [relabelK (permK ![2, 1, 0, 3] ![2, 1, 0, 3]) (by decide +kernel) repVB,
      relabelK (permK ![2, 3, 1, 0] ![3, 2, 0, 1]) (by decide +kernel) repVC,
      relabelK (permK ![2, 0, 1, 3] ![1, 2, 0, 3]) (by decide +kernel) repVA,
      relabelK (permK ![2, 0, 3, 1] ![1, 3, 0, 2]) (by decide +kernel) repVA,
      relabelK (permK ![2, 3, 0, 1] ![2, 3, 0, 1]) (by decide +kernel) repVB,
      relabelK (permK ![2, 1, 3, 0] ![3, 1, 0, 2]) (by decide +kernel) repVC,
      relabelK (permK ![2, 1, 0, 3] ![2, 1, 0, 3]) (by decide +kernel) repVA,
      relabelK (permK ![2, 3, 1, 0] ![3, 2, 0, 1]) (by decide +kernel) repVB,
      relabelK (permK ![2, 0, 1, 3] ![1, 2, 0, 3]) (by decide +kernel) repVB,
      relabelK (permK ![2, 0, 3, 1] ![1, 3, 0, 2]) (by decide +kernel) repVC,
      relabelK (permK ![2, 3, 0, 1] ![2, 3, 0, 1]) (by decide +kernel) repVC,
      relabelK (permK ![2, 1, 3, 0] ![3, 1, 0, 2]) (by decide +kernel) repVA,
      relabelK (permK ![2, 1, 0, 3] ![2, 1, 0, 3]) (by decide +kernel) repVC,
      relabelK (permK ![2, 3, 1, 0] ![3, 2, 0, 1]) (by decide +kernel) repVA,
      relabelK (permK ![2, 0, 1, 3] ![1, 2, 0, 3]) (by decide +kernel) repVC,
      relabelK (permK ![2, 0, 3, 1] ![1, 3, 0, 2]) (by decide +kernel) repVB,
      relabelK (permK ![2, 3, 0, 1] ![2, 3, 0, 1]) (by decide +kernel) repVA,
      relabelK (permK ![2, 1, 3, 0] ![3, 1, 0, 2]) (by decide +kernel) repVB] := by
  decide +kernel

/-- Chunk 4 of the 1PI contractions of `gggg` as relabellings of the representatives. -/
theorem onePIG4_eq_relabelK : onePIG4 =
    [relabelK (permK ![3, 2, 1, 0] ![3, 2, 1, 0]) (by decide +kernel) repVC,
      relabelK (permK ![3, 1, 0, 2] ![2, 1, 3, 0]) (by decide +kernel) repVB,
      relabelK (permK ![3, 2, 0, 1] ![2, 3, 1, 0]) (by decide +kernel) repVB,
      relabelK (permK ![3, 1, 2, 0] ![3, 1, 2, 0]) (by decide +kernel) repVC,
      relabelK (permK ![3, 0, 1, 2] ![1, 2, 3, 0]) (by decide +kernel) repVA,
      relabelK (permK ![3, 0, 2, 1] ![1, 3, 2, 0]) (by decide +kernel) repVA,
      relabelK (permK ![3, 2, 1, 0] ![3, 2, 1, 0]) (by decide +kernel) repVB,
      relabelK (permK ![3, 1, 0, 2] ![2, 1, 3, 0]) (by decide +kernel) repVA,
      relabelK (permK ![3, 2, 0, 1] ![2, 3, 1, 0]) (by decide +kernel) repVC,
      relabelK (permK ![3, 1, 2, 0] ![3, 1, 2, 0]) (by decide +kernel) repVA,
      relabelK (permK ![3, 0, 1, 2] ![1, 2, 3, 0]) (by decide +kernel) repVB,
      relabelK (permK ![3, 0, 2, 1] ![1, 3, 2, 0]) (by decide +kernel) repVC,
      relabelK (permK ![3, 2, 1, 0] ![3, 2, 1, 0]) (by decide +kernel) repVA,
      relabelK (permK ![3, 1, 0, 2] ![2, 1, 3, 0]) (by decide +kernel) repVC,
      relabelK (permK ![3, 2, 0, 1] ![2, 3, 1, 0]) (by decide +kernel) repVA,
      relabelK (permK ![3, 1, 2, 0] ![3, 1, 2, 0]) (by decide +kernel) repVB,
      relabelK (permK ![3, 0, 1, 2] ![1, 2, 3, 0]) (by decide +kernel) repVC,
      relabelK (permK ![3, 0, 2, 1] ![1, 3, 2, 0]) (by decide +kernel) repVB] := by
  decide +kernel

theorem onePIG0_eq_nil : onePIG0 = [] := rfl

/-! ### Every 1PI two-photon contraction of order four -/

section Cases

variable (Q : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 0 2 κ → Prop)

/-- **A property of the listed contractions holds for every 1PI two-photon contraction of total
order `4`.** -/
theorem forall_of_order_four2 (hgC : ∀ C ∈ onePI2_gC, Q C) (hCg : ∀ C ∈ onePI2_Cg, Q C)
    (hggf : ∀ C ∈ onePI2_ggf, Q C) (hgfg : ∀ C ∈ onePI2_gfg, Q C)
    (hfgg : ∀ C ∈ onePI2_fgg, Q C) (hgggg : ∀ C ∈ onePI2_gggg, Q C) {N : ℕ}
    {κ : Fin N → Wick.VertexKind} (h : ∑ t, (κ t).order = 4) (C : Contraction 0 2 κ)
    (hC : IsOnePI C) : Q C := by
  have hN := le_four_of_sum_order h
  obtain _ | _ | _ | _ | _ | N := N
  · exact absurd h (not_le_one (by omega))
  · exact absurd h (not_le_one le_rfl)
  · rcases mem_two h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hgC C ((isOnePI2_iff_gC C).mp hC)
    · exact hCg C ((isOnePI2_iff_Cg C).mp hC)
    · exact absurd ((isOnePI2_iff_ff C).mp hC) (by simp [onePI2_ff])
    · exact absurd ((isOnePI2_iff_fp C).mp hC) (by simp [onePI2_fp])
    · exact absurd ((isOnePI2_iff_pf C).mp hC) (by simp [onePI2_pf])
    · exact absurd ((isOnePI2_iff_pp C).mp hC) (by simp [onePI2_pp])
  · rcases mem_three h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hggf C ((isOnePI2_iff_ggf C).mp hC)
    · exact absurd ((isOnePI2_iff_ggp C).mp hC) (by simp [onePI2_ggp])
    · exact hgfg C ((isOnePI2_iff_gfg C).mp hC)
    · exact absurd ((isOnePI2_iff_gpg C).mp hC) (by simp [onePI2_gpg])
    · exact hfgg C ((isOnePI2_iff_fgg C).mp hC)
    · exact absurd ((isOnePI2_iff_pgg C).mp hC) (by simp [onePI2_pgg])
  · obtain rfl := eq_four h
    exact hgggg C ((isOnePI2_iff_gggg C).mp hC)
  · omega

/-- **Every 1PI two-photon contraction of total order `4` is a relabelling of one of the seven
representatives**, as an induction principle: a property that holds for the representatives and
passes to relabellings of 1PI contractions holds for all of them. -/
theorem induction_of_order_four2
    (hrel : ∀ {N : ℕ} {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
      (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 0 2 κ), IsOnePI C → Q C →
        Q (relabelK π hκ C))
    (hVA : Q repVA) (hVB : Q repVB) (hVC : Q repVC) (hG0 : Q repG0) (hG1 : Q repG1)
    (hF0 : Q repF0) (hF1 : Q repF1) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (h : ∑ t, (κ t).order = 4) (C : Contraction 0 2 κ) (hC : IsOnePI C) : Q C := by
  refine forall_of_order_four2 Q ?_ ?_ ?_ ?_ ?_ ?_ h C hC <;>
  · first
    | rw [onePI2_gC_eq_relabelK] | rw [onePI2_Cg_eq_relabelK] | rw [onePI2_ggf_eq_relabelK]
    | rw [onePI2_gfg_eq_relabelK] | rw [onePI2_fgg_eq_relabelK]
    | rw [onePI2_gggg, onePIG0_eq_nil, onePIG1_eq_relabelK, onePIG2_eq_relabelK,
        onePIG3_eq_relabelK, onePIG4_eq_relabelK]
    simp only [List.nil_append, List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true]
    repeat' constructor
    all_goals first
      | with_reducible exact hrel _ _ _ repVA_isOnePI hVA
      | with_reducible exact hrel _ _ _ repVB_isOnePI hVB
      | with_reducible exact hrel _ _ _ repVC_isOnePI hVC
      | with_reducible exact hrel _ _ _ repG0_isOnePI hG0
      | with_reducible exact hrel _ _ _ repG1_isOnePI hG1
      | with_reducible exact hrel _ _ _ repF0_isOnePI hF0
      | with_reducible exact hrel _ _ _ repF1_isOnePI hF1

end Cases

end QED.GradedProof.VP2

end
