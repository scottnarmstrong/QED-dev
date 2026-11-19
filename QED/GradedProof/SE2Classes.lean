/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.SE2Enum
public import QED.GradedProof.Embed
public import QED.TwoLoop.RelabelCountertermClasses
public import QED.LeptonProof.HMSimple

/-!
# The eight classes of 1PI one-fermion contractions of order four

Helper level for the Phase 5 Stage 2 goal (G-Σ₂) `QED.Graded.selfEnergyPart_two_existsUnique`
(decision D-57), step 1. Every 1PI contraction of the one-fermion function (`nf = 1`, `nA = 0`)
whose vertices have total order (V₁) exactly `4` is a relabelling across kind sequences
(`relabelK`) of one of eight representatives, with vertices numbered along the fermion flow
`v₁, v₂, …` from the incoming `Ψ̄(y)` to the outgoing `Ψ(x)`:

| class | kinds | open line | closed loop | photon lines | loops |
| --- | --- | --- | --- | --- | --- |
| `R` (rainbow) | `gggg` | `0 1 2 3` | — | `(0 3) (1 2)` | 2 |
| `X` (crossed) | `gggg` | `0 1 2 3` | — | `(0 2) (1 3)` | 2 |
| `V` (vacuum polarization) | `gggg` | `0 1` | `2 → 3 → 2` | `(0 2) (1 3)` | 2 |
| `F` (`δ₂`, `δ_m` on the internal line) | `ggf` | `0 2 1` | — | `(0 1)` | 1 |
| `P0` (`δ₃`, slot `0` towards `v₁`) | `ggp` | `0 1` | — | `(0 2₀) (1 2₁)` | 1 |
| `P1` (`δ₃`, slot `1` towards `v₁`) | `ggp` | `0 1` | — | `(0 2₁) (1 2₀)` | 1 |
| `C1` (`δ₁` at `v₁`) | `gC` | `1 0` | — | `(0 1)` | 1 |
| `C2` (`δ₁` at `v₂`) | `gC` | `0 1` | — | `(0 1)` | 1 |

The representatives and the relabellings were found by the generator of the Stage 2 scratch
notes; nothing is trusted: `onePI_<κ>_eq_relabelK` (checked by `decide +kernel`) writes each
list of `QED/GradedProof/SE2Enum.lean` as the list of relabelled representatives.

Every listed contraction is simple (`QED.Lepton.Proof.HM.IsSimple`: at most one closed loop,
made of gauge vertices) and has its counterterm vertices on the open line
(`QED.GradedProof.CtReaches`), by a finite check (`goodB_*`). So no closed loop carries a
counterterm at this order.

## Main statements

* `QED.GradedProof.SE2.forall_of_order_four`: a property of the listed contractions holds for
  every 1PI contraction of total order `4`.
* `QED.GradedProof.SE2.induction_of_order_four`: a property of the eight representatives that
  passes to relabellings of 1PI contractions holds for every 1PI contraction of total order `4`.
* `QED.GradedProof.SE2.isSimple_of_order_four`, `ctReaches_of_order_four`.
-/

@[expose] public section

namespace QED.GradedProof.SE2

open QED.WickModel QED.TwoLoop.Enumeration QED.TwoLoop.Relabel QED.Lepton.Proof.HM

/-! ### The representatives -/

/-- The rainbow graph `R`. -/
def repR : Contraction 1 0 k_gggg :=
  ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3] [],
    photonPerm0 k_gggg [(psK k_gggg 0 0, psK k_gggg 3 0), (psK k_gggg 1 0, psK k_gggg 2 0)]),
    by decide +kernel⟩

/-- The crossed graph `X`. -/
def repX : Contraction 1 0 k_gggg :=
  ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 1, fvK k_gggg 2, fvK k_gggg 3] [],
    photonPerm0 k_gggg [(psK k_gggg 0 0, psK k_gggg 2 0), (psK k_gggg 1 0, psK k_gggg 3 0)]),
    by decide +kernel⟩

/-- The vacuum-polarization graph `V`. -/
def repV : Contraction 1 0 k_gggg :=
  ⟨(fermionPermL k_gggg [fvK k_gggg 0, fvK k_gggg 1] [[fvK k_gggg 2, fvK k_gggg 3]],
    photonPerm0 k_gggg [(psK k_gggg 0 0, psK k_gggg 2 0), (psK k_gggg 1 0, psK k_gggg 3 0)]),
    by decide +kernel⟩

/-- The `fermionCt` vertex on the internal electron line, `F`. -/
def repF : Contraction 1 0 k_ggf :=
  ⟨(fermionPermL k_ggf [fvK k_ggf 0, fvK k_ggf 2, fvK k_ggf 1] [],
    photonPerm0 k_ggf [(psK k_ggf 0 0, psK k_ggf 1 0)]), by decide +kernel⟩

/-- The `photonCt` vertex on the internal photon line, slot `0` towards `v₁`: `P0`. -/
def repP0 : Contraction 1 0 k_ggp :=
  ⟨(fermionPermL k_ggp [fvK k_ggp 0, fvK k_ggp 1] [],
    photonPerm0 k_ggp [(psK k_ggp 0 0, psK k_ggp 2 0), (psK k_ggp 1 0, psK k_ggp 2 1)]),
    by decide +kernel⟩

/-- The `photonCt` vertex on the internal photon line, slot `1` towards `v₁`: `P1`. -/
def repP1 : Contraction 1 0 k_ggp :=
  ⟨(fermionPermL k_ggp [fvK k_ggp 0, fvK k_ggp 1] [],
    photonPerm0 k_ggp [(psK k_ggp 0 0, psK k_ggp 2 1), (psK k_ggp 1 0, psK k_ggp 2 0)]),
    by decide +kernel⟩

/-- The `gaugeCt` vertex at `v₁`: `C1`. -/
def repC1 : Contraction 1 0 k_gC :=
  ⟨(fermionPermL k_gC [fvK k_gC 1, fvK k_gC 0] [],
    photonPerm0 k_gC [(psK k_gC 0 0, psK k_gC 1 0)]), by decide +kernel⟩

/-- The `gaugeCt` vertex at `v₂`: `C2`. -/
def repC2 : Contraction 1 0 k_gC :=
  ⟨(fermionPermL k_gC [fvK k_gC 0, fvK k_gC 1] [],
    photonPerm0 k_gC [(psK k_gC 0 0, psK k_gC 1 0)]), by decide +kernel⟩

theorem repR_isOnePI : IsOnePI repR := (isOnePI_iff_gggg _).mpr (by decide +kernel)
theorem repX_isOnePI : IsOnePI repX := (isOnePI_iff_gggg _).mpr (by decide +kernel)
theorem repV_isOnePI : IsOnePI repV := (isOnePI_iff_gggg _).mpr (by decide +kernel)
theorem repF_isOnePI : IsOnePI repF := (isOnePI_iff_ggf _).mpr (by decide +kernel)
theorem repP0_isOnePI : IsOnePI repP0 := (isOnePI_iff_ggp _).mpr (by decide +kernel)
theorem repP1_isOnePI : IsOnePI repP1 := (isOnePI_iff_ggp _).mpr (by decide +kernel)
theorem repC1_isOnePI : IsOnePI repC1 := (isOnePI_iff_gC _).mpr (by decide +kernel)
theorem repC2_isOnePI : IsOnePI repC2 := (isOnePI_iff_gC _).mpr (by decide +kernel)

/-- The fermionic signs: `-1` for the vacuum-polarization graph, `+1` otherwise. -/
theorem fermionSign_reps : fermionSign repR = 1 ∧ fermionSign repX = 1 ∧ fermionSign repV = -1 ∧
    fermionSign repF = 1 ∧ fermionSign repP0 = 1 ∧ fermionSign repP1 = 1 ∧
    fermionSign repC1 = 1 ∧ fermionSign repC2 = 1 := by
  decide +kernel

theorem loopCount_repR : loopCount repR = 2 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repX : loopCount repX = 2 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repV : loopCount repV = 2 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repF : loopCount repF = 1 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repP0 : loopCount repP0 = 1 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repP1 : loopCount repP1 = 1 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repC1 : loopCount repC1 = 1 := by rw [loopCount_eq_card]; decide +kernel
theorem loopCount_repC2 : loopCount repC2 = 1 := by rw [loopCount_eq_card]; decide +kernel

/-! ### Each list is the list of relabelled representatives -/

/-- The 1PI contractions of `gC` are relabellings of the representatives. -/
theorem onePI_gC_eq_relabelK : onePI_gC =
    [relabelK (permK ![0, 1] ![0, 1]) (by decide +kernel) repC1,
      relabelK (permK ![0, 1] ![0, 1]) (by decide +kernel) repC2] := by
  decide +kernel

/-- The 1PI contractions of `Cg` are relabellings of the representatives. -/
theorem onePI_Cg_eq_relabelK : onePI_Cg =
    [relabelK (permK ![1, 0] ![1, 0]) (by decide +kernel) repC2,
      relabelK (permK ![1, 0] ![1, 0]) (by decide +kernel) repC1] := by
  decide +kernel

/-- The 1PI contractions of `ggf` are relabellings of the representatives. -/
theorem onePI_ggf_eq_relabelK : onePI_ggf =
    [relabelK (permK ![1, 0, 2] ![1, 0, 2]) (by decide +kernel) repF,
      relabelK (permK ![0, 1, 2] ![0, 1, 2]) (by decide +kernel) repF] := by
  decide +kernel

/-- The 1PI contractions of `ggp` are relabellings of the representatives. -/
theorem onePI_ggp_eq_relabelK : onePI_ggp =
    [relabelK (permK ![1, 0, 2] ![1, 0, 2]) (by decide +kernel) repP1,
      relabelK (permK ![1, 0, 2] ![1, 0, 2]) (by decide +kernel) repP0,
      relabelK (permK ![0, 1, 2] ![0, 1, 2]) (by decide +kernel) repP0,
      relabelK (permK ![0, 1, 2] ![0, 1, 2]) (by decide +kernel) repP1] := by
  decide +kernel

/-- The 1PI contractions of `gfg` are relabellings of the representatives. -/
theorem onePI_gfg_eq_relabelK : onePI_gfg =
    [relabelK (permK ![2, 0, 1] ![1, 2, 0]) (by decide +kernel) repF,
      relabelK (permK ![0, 2, 1] ![0, 2, 1]) (by decide +kernel) repF] := by
  decide +kernel

/-- The 1PI contractions of `gpg` are relabellings of the representatives. -/
theorem onePI_gpg_eq_relabelK : onePI_gpg =
    [relabelK (permK ![2, 0, 1] ![1, 2, 0]) (by decide +kernel) repP1,
      relabelK (permK ![2, 0, 1] ![1, 2, 0]) (by decide +kernel) repP0,
      relabelK (permK ![0, 2, 1] ![0, 2, 1]) (by decide +kernel) repP0,
      relabelK (permK ![0, 2, 1] ![0, 2, 1]) (by decide +kernel) repP1] := by
  decide +kernel

/-- The 1PI contractions of `fgg` are relabellings of the representatives. -/
theorem onePI_fgg_eq_relabelK : onePI_fgg =
    [relabelK (permK ![2, 1, 0] ![2, 1, 0]) (by decide +kernel) repF,
      relabelK (permK ![1, 2, 0] ![2, 0, 1]) (by decide +kernel) repF] := by
  decide +kernel

/-- The 1PI contractions of `pgg` are relabellings of the representatives. -/
theorem onePI_pgg_eq_relabelK : onePI_pgg =
    [relabelK (permK ![2, 1, 0] ![2, 1, 0]) (by decide +kernel) repP1,
      relabelK (permK ![2, 1, 0] ![2, 1, 0]) (by decide +kernel) repP0,
      relabelK (permK ![1, 2, 0] ![2, 0, 1]) (by decide +kernel) repP0,
      relabelK (permK ![1, 2, 0] ![2, 0, 1]) (by decide +kernel) repP1] := by
  decide +kernel

/-- The first 36 1PI contractions of `gggg` are relabellings of the representatives (the list
is split in two halves to keep the kernel check small). -/
theorem onePI_gggg_take_eq_relabelK : onePI_gggg.take 36 =
    [relabelK (permK ![1, 0, 3, 2] ![1, 0, 3, 2]) (by decide +kernel) repV,
      relabelK (permK ![1, 0, 2, 3] ![1, 0, 2, 3]) (by decide +kernel) repV,
      relabelK (permK ![3, 2, 1, 0] ![3, 2, 1, 0]) (by decide +kernel) repX,
      relabelK (permK ![3, 2, 1, 0] ![3, 2, 1, 0]) (by decide +kernel) repR,
      relabelK (permK ![2, 3, 1, 0] ![3, 2, 0, 1]) (by decide +kernel) repR,
      relabelK (permK ![2, 3, 1, 0] ![3, 2, 0, 1]) (by decide +kernel) repX,
      relabelK (permK ![1, 3, 2, 0] ![3, 0, 2, 1]) (by decide +kernel) repR,
      relabelK (permK ![1, 3, 2, 0] ![3, 0, 2, 1]) (by decide +kernel) repX,
      relabelK (permK ![2, 0, 3, 1] ![1, 3, 0, 2]) (by decide +kernel) repV,
      relabelK (permK ![2, 0, 1, 3] ![1, 2, 0, 3]) (by decide +kernel) repV,
      relabelK (permK ![3, 1, 2, 0] ![3, 1, 2, 0]) (by decide +kernel) repX,
      relabelK (permK ![3, 1, 2, 0] ![3, 1, 2, 0]) (by decide +kernel) repR,
      relabelK (permK ![1, 2, 3, 0] ![3, 0, 1, 2]) (by decide +kernel) repR,
      relabelK (permK ![1, 2, 3, 0] ![3, 0, 1, 2]) (by decide +kernel) repX,
      relabelK (permK ![2, 1, 3, 0] ![3, 1, 0, 2]) (by decide +kernel) repX,
      relabelK (permK ![2, 1, 3, 0] ![3, 1, 0, 2]) (by decide +kernel) repR,
      relabelK (permK ![3, 0, 2, 1] ![1, 3, 2, 0]) (by decide +kernel) repV,
      relabelK (permK ![3, 0, 1, 2] ![1, 2, 3, 0]) (by decide +kernel) repV,
      relabelK (permK ![0, 1, 2, 3] ![0, 1, 2, 3]) (by decide +kernel) repV,
      relabelK (permK ![0, 1, 3, 2] ![0, 1, 3, 2]) (by decide +kernel) repV,
      relabelK (permK ![0, 3, 2, 1] ![0, 3, 2, 1]) (by decide +kernel) repR,
      relabelK (permK ![0, 3, 2, 1] ![0, 3, 2, 1]) (by decide +kernel) repX,
      relabelK (permK ![0, 2, 3, 1] ![0, 3, 1, 2]) (by decide +kernel) repR,
      relabelK (permK ![0, 2, 3, 1] ![0, 3, 1, 2]) (by decide +kernel) repX,
      relabelK (permK ![3, 2, 0, 1] ![2, 3, 1, 0]) (by decide +kernel) repR,
      relabelK (permK ![3, 2, 0, 1] ![2, 3, 1, 0]) (by decide +kernel) repX,
      relabelK (permK ![2, 0, 3, 1] ![1, 3, 0, 2]) (by decide +kernel) repX,
      relabelK (permK ![2, 0, 3, 1] ![1, 3, 0, 2]) (by decide +kernel) repR,
      relabelK (permK ![3, 1, 2, 0] ![3, 1, 2, 0]) (by decide +kernel) repV,
      relabelK (permK ![3, 1, 0, 2] ![2, 1, 3, 0]) (by decide +kernel) repV,
      relabelK (permK ![2, 3, 0, 1] ![2, 3, 0, 1]) (by decide +kernel) repX,
      relabelK (permK ![2, 3, 0, 1] ![2, 3, 0, 1]) (by decide +kernel) repR,
      relabelK (permK ![2, 1, 3, 0] ![3, 1, 0, 2]) (by decide +kernel) repV,
      relabelK (permK ![2, 1, 0, 3] ![2, 1, 0, 3]) (by decide +kernel) repV,
      relabelK (permK ![3, 0, 2, 1] ![1, 3, 2, 0]) (by decide +kernel) repX,
      relabelK (permK ![3, 0, 2, 1] ![1, 3, 2, 0]) (by decide +kernel) repR] := by
  decide +kernel

/-- The last 36 1PI contractions of `gggg` are relabellings of the representatives. -/
theorem onePI_gggg_drop_eq_relabelK : onePI_gggg.drop 36 =
    [relabelK (permK ![0, 1, 3, 2] ![0, 1, 3, 2]) (by decide +kernel) repR,
      relabelK (permK ![0, 1, 3, 2] ![0, 1, 3, 2]) (by decide +kernel) repX,
      relabelK (permK ![0, 2, 1, 3] ![0, 2, 1, 3]) (by decide +kernel) repV,
      relabelK (permK ![0, 2, 3, 1] ![0, 3, 1, 2]) (by decide +kernel) repV,
      relabelK (permK ![0, 3, 1, 2] ![0, 2, 3, 1]) (by decide +kernel) repX,
      relabelK (permK ![0, 3, 1, 2] ![0, 2, 3, 1]) (by decide +kernel) repR,
      relabelK (permK ![1, 0, 3, 2] ![1, 0, 3, 2]) (by decide +kernel) repX,
      relabelK (permK ![1, 0, 3, 2] ![1, 0, 3, 2]) (by decide +kernel) repR,
      relabelK (permK ![3, 2, 1, 0] ![3, 2, 1, 0]) (by decide +kernel) repV,
      relabelK (permK ![3, 2, 0, 1] ![2, 3, 1, 0]) (by decide +kernel) repV,
      relabelK (permK ![3, 1, 0, 2] ![2, 1, 3, 0]) (by decide +kernel) repR,
      relabelK (permK ![3, 1, 0, 2] ![2, 1, 3, 0]) (by decide +kernel) repX,
      relabelK (permK ![1, 3, 0, 2] ![2, 0, 3, 1]) (by decide +kernel) repX,
      relabelK (permK ![1, 3, 0, 2] ![2, 0, 3, 1]) (by decide +kernel) repR,
      relabelK (permK ![1, 2, 0, 3] ![2, 0, 1, 3]) (by decide +kernel) repV,
      relabelK (permK ![1, 2, 3, 0] ![3, 0, 1, 2]) (by decide +kernel) repV,
      relabelK (permK ![3, 0, 1, 2] ![1, 2, 3, 0]) (by decide +kernel) repR,
      relabelK (permK ![3, 0, 1, 2] ![1, 2, 3, 0]) (by decide +kernel) repX,
      relabelK (permK ![0, 1, 2, 3] ![0, 1, 2, 3]) (by decide +kernel) repX,
      relabelK (permK ![0, 1, 2, 3] ![0, 1, 2, 3]) (by decide +kernel) repR,
      relabelK (permK ![0, 2, 1, 3] ![0, 2, 1, 3]) (by decide +kernel) repX,
      relabelK (permK ![0, 2, 1, 3] ![0, 2, 1, 3]) (by decide +kernel) repR,
      relabelK (permK ![0, 3, 1, 2] ![0, 2, 3, 1]) (by decide +kernel) repV,
      relabelK (permK ![0, 3, 2, 1] ![0, 3, 2, 1]) (by decide +kernel) repV,
      relabelK (permK ![1, 0, 2, 3] ![1, 0, 2, 3]) (by decide +kernel) repR,
      relabelK (permK ![1, 0, 2, 3] ![1, 0, 2, 3]) (by decide +kernel) repX,
      relabelK (permK ![2, 3, 0, 1] ![2, 3, 0, 1]) (by decide +kernel) repV,
      relabelK (permK ![2, 3, 1, 0] ![3, 2, 0, 1]) (by decide +kernel) repV,
      relabelK (permK ![2, 1, 0, 3] ![2, 1, 0, 3]) (by decide +kernel) repR,
      relabelK (permK ![2, 1, 0, 3] ![2, 1, 0, 3]) (by decide +kernel) repX,
      relabelK (permK ![1, 3, 0, 2] ![2, 0, 3, 1]) (by decide +kernel) repV,
      relabelK (permK ![1, 3, 2, 0] ![3, 0, 2, 1]) (by decide +kernel) repV,
      relabelK (permK ![1, 2, 0, 3] ![2, 0, 1, 3]) (by decide +kernel) repX,
      relabelK (permK ![1, 2, 0, 3] ![2, 0, 1, 3]) (by decide +kernel) repR,
      relabelK (permK ![2, 0, 1, 3] ![1, 2, 0, 3]) (by decide +kernel) repR,
      relabelK (permK ![2, 0, 1, 3] ![1, 2, 0, 3]) (by decide +kernel) repX] := by
  decide +kernel

/-! ### Every 1PI contraction of order four -/

section Cases

variable (Q : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 0 κ → Prop)

/-- **A property of the listed contractions holds for every 1PI one-fermion contraction of total
order `4`.** -/
theorem forall_of_order_four (hgC : ∀ C ∈ onePI_gC, Q C) (hCg : ∀ C ∈ onePI_Cg, Q C)
    (hggf : ∀ C ∈ onePI_ggf, Q C) (hgfg : ∀ C ∈ onePI_gfg, Q C) (hfgg : ∀ C ∈ onePI_fgg, Q C)
    (hggp : ∀ C ∈ onePI_ggp, Q C) (hgpg : ∀ C ∈ onePI_gpg, Q C) (hpgg : ∀ C ∈ onePI_pgg, Q C)
    (hgggg : ∀ C ∈ onePI_gggg, Q C) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (h : ∑ t, (κ t).order = 4) (C : Contraction 1 0 κ) (hC : IsOnePI C) : Q C := by
  have hN := le_four_of_sum_order h
  obtain _ | _ | _ | _ | _ | N := N
  · exact absurd h (not_le_one (by omega))
  · exact absurd h (not_le_one le_rfl)
  · rcases mem_two h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hgC C ((isOnePI_iff_gC C).mp hC)
    · exact hCg C ((isOnePI_iff_Cg C).mp hC)
    · exact absurd ((isOnePI_iff_ff C).mp hC) (by simp [onePI_ff])
    · exact absurd ((isOnePI_iff_fp C).mp hC) (by simp [onePI_fp])
    · exact absurd ((isOnePI_iff_pf C).mp hC) (by simp [onePI_pf])
    · exact absurd ((isOnePI_iff_pp C).mp hC) (by simp [onePI_pp])
  · rcases mem_three h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hggf C ((isOnePI_iff_ggf C).mp hC)
    · exact hggp C ((isOnePI_iff_ggp C).mp hC)
    · exact hgfg C ((isOnePI_iff_gfg C).mp hC)
    · exact hgpg C ((isOnePI_iff_gpg C).mp hC)
    · exact hfgg C ((isOnePI_iff_fgg C).mp hC)
    · exact hpgg C ((isOnePI_iff_pgg C).mp hC)
  · obtain rfl := eq_four h
    exact hgggg C ((isOnePI_iff_gggg C).mp hC)
  · omega

/-- **Every 1PI one-fermion contraction of total order `4` is a relabelling of one of the eight
representatives**, as an induction principle: a property that holds for the representatives and
passes to relabellings of 1PI contractions holds for all of them. -/
theorem induction_of_order_four
    (hrel : ∀ {N : ℕ} {κ κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N))
      (hκ : ∀ t, κ' (π t) = κ t) (C : Contraction 1 0 κ), IsOnePI C → Q C →
        Q (relabelK π hκ C))
    (hR : Q repR) (hX : Q repX) (hV : Q repV) (hF : Q repF) (hP0 : Q repP0) (hP1 : Q repP1)
    (hC1 : Q repC1) (hC2 : Q repC2) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    (h : ∑ t, (κ t).order = 4) (C : Contraction 1 0 κ) (hC : IsOnePI C) : Q C := by
  refine forall_of_order_four Q ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h C hC <;>
  · first
    | rw [onePI_gC_eq_relabelK] | rw [onePI_Cg_eq_relabelK] | rw [onePI_ggf_eq_relabelK]
    | rw [onePI_gfg_eq_relabelK] | rw [onePI_fgg_eq_relabelK] | rw [onePI_ggp_eq_relabelK]
    | rw [onePI_gpg_eq_relabelK] | rw [onePI_pgg_eq_relabelK]
    | rw [← List.take_append_drop 36 onePI_gggg, onePI_gggg_take_eq_relabelK,
        onePI_gggg_drop_eq_relabelK]
    simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true]
    repeat' constructor
    all_goals first
      | with_reducible exact hrel _ _ _ repR_isOnePI hR
      | with_reducible exact hrel _ _ _ repX_isOnePI hX
      | with_reducible exact hrel _ _ _ repV_isOnePI hV
      | with_reducible exact hrel _ _ _ repF_isOnePI hF
      | with_reducible exact hrel _ _ _ repP0_isOnePI hP0
      | with_reducible exact hrel _ _ _ repP1_isOnePI hP1
      | with_reducible exact hrel _ _ _ repC1_isOnePI hC1
      | with_reducible exact hrel _ _ _ repC2_isOnePI hC2

end Cases

/-! ### Simple, with the counterterms on the open line -/

section Good

variable {N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- The Boolean test: simple (`SimpleB`), and every counterterm vertex with fermion fields
reaches an external field within six steps (`OpenB`). -/
def GoodB (C : Contraction 1 0 κ) : Prop :=
  SimpleB C ∧ ∀ t : Wick.FermionVertex κ, κ t.1 ≠ .gauge → OpenB C t

instance (C : Contraction 1 0 κ) : Decidable (GoodB C) := by
  unfold GoodB; infer_instance

theorem isSimple_of_goodB {C : Contraction 1 0 κ} (h : GoodB C) : IsSimple C :=
  isSimple_of_simpleB h.1

theorem ctReaches_of_goodB {C : Contraction 1 0 κ} (h : GoodB C) : CtReaches C := fun t ht => by
  obtain ⟨i, hi⟩ := onOpen_of_openB (h.2 t ht)
  exact ⟨i, hi.symm⟩

theorem goodB_gC : ∀ C ∈ onePI_gC, GoodB C := by decide +kernel
theorem goodB_Cg : ∀ C ∈ onePI_Cg, GoodB C := by decide +kernel
theorem goodB_ggf : ∀ C ∈ onePI_ggf, GoodB C := by decide +kernel
theorem goodB_gfg : ∀ C ∈ onePI_gfg, GoodB C := by decide +kernel
theorem goodB_fgg : ∀ C ∈ onePI_fgg, GoodB C := by decide +kernel
theorem goodB_ggp : ∀ C ∈ onePI_ggp, GoodB C := by decide +kernel
theorem goodB_gpg : ∀ C ∈ onePI_gpg, GoodB C := by decide +kernel
theorem goodB_pgg : ∀ C ∈ onePI_pgg, GoodB C := by decide +kernel
theorem goodB_gggg : ∀ C ∈ onePI_gggg, GoodB C := by decide +kernel

/-- Every 1PI one-fermion contraction of total order `4` passes the Boolean test. -/
theorem goodB_of_order_four (h : ∑ t, (κ t).order = 4) (C : Contraction 1 0 κ)
    (hC : IsOnePI C) : GoodB C :=
  forall_of_order_four (fun C => GoodB C) goodB_gC goodB_Cg goodB_ggf goodB_gfg goodB_fgg
    goodB_ggp goodB_gpg goodB_pgg goodB_gggg h C hC

/-- **Every 1PI one-fermion contraction of total order `4` is simple**: at most one closed
fermion loop, made of gauge vertices. -/
theorem isSimple_of_order_four (h : ∑ t, (κ t).order = 4) (C : Contraction 1 0 κ)
    (hC : IsOnePI C) : IsSimple C :=
  isSimple_of_goodB (goodB_of_order_four h C hC)

/-- **No closed loop of a 1PI one-fermion contraction of total order `4` carries a
counterterm.** -/
theorem ctReaches_of_order_four (h : ∑ t, (κ t).order = 4) (C : Contraction 1 0 κ)
    (hC : IsOnePI C) : CtReaches C :=
  ctReaches_of_goodB (goodB_of_order_four h C hC)

end Good

end QED.GradedProof.SE2

end
