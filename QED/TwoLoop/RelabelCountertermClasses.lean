/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.RelabelCountertermValue
public import QED.TwoLoop.FurryPair

/-!
# The counterterm contractions of the order-`e⁵` vertex with coefficient one per class

Item 2 of section 3 of `docs/TWO-LOOP-ENUMERATION.md` (obligation O2-2, section 3.3 of
`docs/TWO-LOOP-DERIVATION.md`). The counterterm part of the order-`e⁵` vertex is
`(4!)⁻¹` times the values of the `8 × 12` listed 1PI contractions with one `fermionCt` or one
`photonCt` vertex, plus `(3!)⁻¹` times the values of the `3 × 6` listed 1PI contractions with one
`gaugeCt` vertex. Every listed contraction is a relabelling across kind sequences
(`relabelK`, `κ' (π t) = κ t`) of one of seven class representatives, and each class has exactly
`N!` members over the `N` sequences with the same kinds: `6` (resp. `2`) per sequence, so `24`
for each of the four classes with `N = 4` and `6` for each of the three with `N = 3`. With the
relabelling invariance of the value (`contractionValue₂_relabelK_of_isOnePI`), under momentum
conservation, the `N!` cancels the `1/N!` and the counterterm part is the sum of the values of the
seven representatives with coefficient one.

The classes (`CtClass`), with vertices numbered along the fermion flow `v₁, v₂, …`:

* `d2In`, `d2Out`: `δ₂`, `δ_m` on the incoming, resp. outgoing, internal electron line;
* `d3Slot0`, `d3Slot1`: `δ₃` on the internal photon, with slot `0`, resp. `1`, of the `photonCt`
  vertex towards `v₁` (the two field pairings, together the `δ₃` class of section 3.2);
* `d1At1`, `d1At2`, `d1At3`: `δ₁` at `v₁`, at the external-photon vertex `v₂`, at `v₃`.

The representatives and the relabellings were found by a search over the enumeration of
`scripts/numerics/two_loop_enumeration.py`, which also finds each listed contraction to be the
relabelling of exactly one representative by exactly one permutation (no automorphism). Nothing
of this is trusted in Lean: `onePI_<κ>_eq_relabelK` (checked by `decide +kernel`) writes each list
as the list of relabelled representatives, which is all the proof uses.

## Main statements

* `QED.TwoLoop.Relabel.countertermPart_eq`: under `pOut 0 = pIn 0 + kIn 0`, the counterterm part
  of `onePIFunction₂_five_sub_four` is `∑ c : CtClass, contractionValue₂ P c.rep …`.
* `QED.TwoLoop.Relabel.onePIFunction₂_five_sub_four_eq_classes`: the order-`e⁵` vertex is the sum
  over the seven classes `L, X, C₊, C₋, S₊, S₋, VP` of five gauge vertices with their signs plus
  the sum over the seven counterterm classes, each with coefficient one.
* `QED.TwoLoop.Relabel.onePIFunction₂_five_sub_four_eq_all_classes`: the same with all nine
  classes of five gauge vertices (the Furry pair not cancelled).
-/

@[expose] public section

namespace QED.TwoLoop.Relabel

open QED.WickModel QED.TwoLoop.Enumeration

/-- A permutation of `Fin N` given by a function and its inverse, both checked by `decide`. -/
def permK {N : ℕ} (f g : Fin N → Fin N) (h₁ : ∀ x, g (f x) = x := by decide)
    (h₂ : ∀ x, f (g x) = x := by decide) : Equiv.Perm (Fin N) :=
  ⟨f, g, h₁, h₂⟩

/-- The value of a relabelled 1PI contraction, under momentum conservation. -/
theorem value_relabelK (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) {N : ℕ} {κ : Fin N → Wick.VertexKind}
    {C : Contraction 1 1 κ} (hC : IsOnePI C) (αOut βIn μ : Fin 1 → Fin 4)
    {κ' : Fin N → Wick.VertexKind} (π : Equiv.Perm (Fin N)) (hκ : ∀ t, κ' (π t) = κ t) :
    contractionValue₂ P (relabelK π hκ C) pOut pIn kIn αOut βIn μ =
      contractionValue₂ P C pOut pIn kIn αOut βIn μ :=
  contractionValue₂_relabelK_of_isOnePI P π hκ hC (by simp only [Fin.sum_univ_one, hmom])
    αOut βIn μ

/-! ### The representatives -/

/-- The representative of the class `δ₂`, `δ_m` on the incoming internal electron line: fermion
flow `0 → 3 → 1 → 2` with the `fermionCt` vertex `3` between `v₁ = 0` and the external-photon
vertex `1`; photon line `0 — 2`. -/
def repD2In : Contraction 1 1 k_gggf :=
  ⟨(fermionPermK k_gggf [fvK k_gggf 0, fvK k_gggf 3, fvK k_gggf 1, fvK k_gggf 2],
    photonPermK k_gggf (psK k_gggf 1 0)
        [(psK k_gggf 0 0, psK k_gggf 2 0)]), by decide +kernel⟩

theorem repD2In_mem : repD2In ∈ onePI_gggf := by decide +kernel

theorem repD2In_isOnePI : IsOnePI repD2In := (isOnePI_iff_gggf _).mpr repD2In_mem

/-- The representative of the class `δ₂`, `δ_m` on the outgoing internal electron line: fermion
flow `0 → 1 → 3 → 2` with the `fermionCt` vertex `3` between the external-photon vertex `1` and
`v₃ = 2`; photon line `0 — 2`. -/
def repD2Out : Contraction 1 1 k_gggf :=
  ⟨(fermionPermK k_gggf [fvK k_gggf 0, fvK k_gggf 1, fvK k_gggf 3, fvK k_gggf 2],
    photonPermK k_gggf (psK k_gggf 1 0)
        [(psK k_gggf 0 0, psK k_gggf 2 0)]), by decide +kernel⟩

theorem repD2Out_mem : repD2Out ∈ onePI_gggf := by decide +kernel

theorem repD2Out_isOnePI : IsOnePI repD2Out := (isOnePI_iff_gggf _).mpr repD2Out_mem

/-- The representative of the class `δ₃` on the internal photon, slot `0` of the `photonCt`
vertex `3` towards `v₁`: fermion flow `0 → 1 → 2`, external photon at `1`, photon lines `0 — 3₀`
and `2 — 3₁`. -/
def repD3Slot0 : Contraction 1 1 k_gggp :=
  ⟨(fermionPermK k_gggp [fvK k_gggp 0, fvK k_gggp 1, fvK k_gggp 2],
    photonPermK k_gggp (psK k_gggp 1 0)
        [(psK k_gggp 2 0, psK k_gggp 3 1), (psK k_gggp 0 0, psK k_gggp 3 0)]), by decide +kernel⟩

theorem repD3Slot0_mem : repD3Slot0 ∈ onePI_gggp := by decide +kernel

theorem repD3Slot0_isOnePI : IsOnePI repD3Slot0 := (isOnePI_iff_gggp _).mpr repD3Slot0_mem

/-- The representative of the class `δ₃` on the internal photon, slot `1` of the `photonCt`
vertex `3` towards `v₁`: fermion flow `0 → 1 → 2`, external photon at `1`, photon lines `0 — 3₁`
and `2 — 3₀`. -/
def repD3Slot1 : Contraction 1 1 k_gggp :=
  ⟨(fermionPermK k_gggp [fvK k_gggp 0, fvK k_gggp 1, fvK k_gggp 2],
    photonPermK k_gggp (psK k_gggp 1 0)
        [(psK k_gggp 2 0, psK k_gggp 3 0), (psK k_gggp 0 0, psK k_gggp 3 1)]), by decide +kernel⟩

theorem repD3Slot1_mem : repD3Slot1 ∈ onePI_gggp := by decide +kernel

theorem repD3Slot1_isOnePI : IsOnePI repD3Slot1 := (isOnePI_iff_gggp _).mpr repD3Slot1_mem

/-- The representative of the class `δ₁` at `v₁`: fermion flow `2 → 0 → 1` with the `gaugeCt`
vertex `2` first, external photon at `0`, photon line `2 — 1`. -/
def repD1At1 : Contraction 1 1 k_ggC :=
  ⟨(fermionPermK k_ggC [fvK k_ggC 2, fvK k_ggC 0, fvK k_ggC 1],
    photonPermK k_ggC (psK k_ggC 0 0)
        [(psK k_ggC 1 0, psK k_ggC 2 0)]), by decide +kernel⟩

theorem repD1At1_mem : repD1At1 ∈ onePI_ggC := by decide +kernel

theorem repD1At1_isOnePI : IsOnePI repD1At1 := (isOnePI_iff_ggC _).mpr repD1At1_mem

/-- The representative of the class `δ₁` at `v₂`, the external-photon vertex: fermion flow `0 →
2 → 1`, external photon at the `gaugeCt` vertex `2`, photon line `0 — 1`. -/
def repD1At2 : Contraction 1 1 k_ggC :=
  ⟨(fermionPermK k_ggC [fvK k_ggC 0, fvK k_ggC 2, fvK k_ggC 1],
    photonPermK k_ggC (psK k_ggC 2 0)
        [(psK k_ggC 0 0, psK k_ggC 1 0)]), by decide +kernel⟩

theorem repD1At2_mem : repD1At2 ∈ onePI_ggC := by decide +kernel

theorem repD1At2_isOnePI : IsOnePI repD1At2 := (isOnePI_iff_ggC _).mpr repD1At2_mem

/-- The representative of the class `δ₁` at `v₃`: fermion flow `0 → 1 → 2` with the `gaugeCt`
vertex `2` last, external photon at `1`, photon line `0 — 2`. -/
def repD1At3 : Contraction 1 1 k_ggC :=
  ⟨(fermionPermK k_ggC [fvK k_ggC 0, fvK k_ggC 1, fvK k_ggC 2],
    photonPermK k_ggC (psK k_ggC 1 0)
        [(psK k_ggC 0 0, psK k_ggC 2 0)]), by decide +kernel⟩

theorem repD1At3_mem : repD1At3 ∈ onePI_ggC := by decide +kernel

theorem repD1At3_isOnePI : IsOnePI repD1At3 := (isOnePI_iff_ggC _).mpr repD1At3_mem

/-! ### The classes -/

/-- The seven classes of 1PI vertex graphs of order `e⁵` with one counterterm vertex. -/
inductive CtClass
  /-- `δ₂`, `δ_m` on the incoming internal electron line -/
  | d2In
  /-- `δ₂`, `δ_m` on the outgoing internal electron line -/
  | d2Out
  /-- `δ₃` on the internal photon, slot `0` of the `photonCt` vertex towards `v₁` -/
  | d3Slot0
  /-- `δ₃` on the internal photon, slot `1` of the `photonCt` vertex towards `v₁` -/
  | d3Slot1
  /-- `δ₁` at `v₁` -/
  | d1At1
  /-- `δ₁` at the external-photon vertex `v₂` -/
  | d1At2
  /-- `δ₁` at `v₃` -/
  | d1At3
  deriving DecidableEq

instance : Fintype CtClass :=
  ⟨{.d2In, .d2Out, .d3Slot0, .d3Slot1, .d1At1, .d1At2, .d1At3}, fun x => by cases x <;> simp⟩

/-- The number of vertices of the representative. -/
def CtClass.N : CtClass → ℕ
  | .d2In | .d2Out | .d3Slot0 | .d3Slot1 => 4
  | .d1At1 | .d1At2 | .d1At3 => 3

/-- The kind sequence of the representative. -/
def CtClass.kinds : (c : CtClass) → Fin c.N → Wick.VertexKind
  | .d2In | .d2Out => k_gggf
  | .d3Slot0 | .d3Slot1 => k_gggp
  | .d1At1 | .d1At2 | .d1At3 => k_ggC

/-- The representative of the class. -/
def CtClass.rep : (c : CtClass) → Contraction 1 1 c.kinds
  | .d2In => repD2In
  | .d2Out => repD2Out
  | .d3Slot0 => repD3Slot0
  | .d3Slot1 => repD3Slot1
  | .d1At1 => repD1At1
  | .d1At2 => repD1At2
  | .d1At3 => repD1At3

theorem CtClass.rep_isOnePI : ∀ c : CtClass, IsOnePI c.rep
  | .d2In => repD2In_isOnePI
  | .d2Out => repD2Out_isOnePI
  | .d3Slot0 => repD3Slot0_isOnePI
  | .d3Slot1 => repD3Slot1_isOnePI
  | .d1At1 => repD1At1_isOnePI
  | .d1At2 => repD1At2_isOnePI
  | .d1At3 => repD1At3_isOnePI

theorem sum_ctClass (P : Params) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ) (αOut βIn μ : Fin 1 → Fin 4) :
    ∑ c : CtClass, contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ =
      contractionValue₂ P repD2In pOut pIn kIn αOut βIn μ +
        contractionValue₂ P repD2Out pOut pIn kIn αOut βIn μ +
        contractionValue₂ P repD3Slot0 pOut pIn kIn αOut βIn μ +
        contractionValue₂ P repD3Slot1 pOut pIn kIn αOut βIn μ +
        contractionValue₂ P repD1At1 pOut pIn kIn αOut βIn μ +
        contractionValue₂ P repD1At2 pOut pIn kIn αOut βIn μ +
        contractionValue₂ P repD1At3 pOut pIn kIn αOut βIn μ := by
  rw [show (Finset.univ : Finset CtClass) =
    {.d2In, .d2Out, .d3Slot0, .d3Slot1, .d1At1, .d1At2, .d1At3} from rfl]
  simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton]
  simp only [add_assoc]
  rfl

/-! ### Each list is the list of relabelled representatives -/

/-- The 1PI contractions of `gggf` are relabellings of the representatives. -/
theorem onePI_gggf_eq_relabelK : onePI_gggf =
    [relabelK (permK ![2, 1, 0, 3] ![2, 1, 0, 3]) (by decide +kernel) repD2In,
      relabelK (permK ![1, 2, 0, 3] ![2, 0, 1, 3]) (by decide +kernel) repD2In,
      relabelK (permK ![1, 2, 0, 3] ![2, 0, 1, 3]) (by decide +kernel) repD2Out,
      relabelK (permK ![2, 1, 0, 3] ![2, 1, 0, 3]) (by decide +kernel) repD2Out,
      relabelK (permK ![0, 2, 1, 3] ![0, 2, 1, 3]) (by decide +kernel) repD2In,
      relabelK (permK ![0, 2, 1, 3] ![0, 2, 1, 3]) (by decide +kernel) repD2Out,
      relabelK (permK ![2, 0, 1, 3] ![1, 2, 0, 3]) (by decide +kernel) repD2Out,
      relabelK (permK ![2, 0, 1, 3] ![1, 2, 0, 3]) (by decide +kernel) repD2In,
      relabelK (permK ![0, 1, 2, 3] ![0, 1, 2, 3]) (by decide +kernel) repD2Out,
      relabelK (permK ![0, 1, 2, 3] ![0, 1, 2, 3]) (by decide +kernel) repD2In,
      relabelK (permK ![1, 0, 2, 3] ![1, 0, 2, 3]) (by decide +kernel) repD2Out,
      relabelK (permK ![1, 0, 2, 3] ![1, 0, 2, 3]) (by decide +kernel) repD2In] := by
  decide +kernel

/-- The 1PI contractions of `ggfg` are relabellings of the representatives. -/
theorem onePI_ggfg_eq_relabelK : onePI_ggfg =
    [relabelK (permK ![3, 1, 0, 2] ![2, 1, 3, 0]) (by decide +kernel) repD2In,
      relabelK (permK ![1, 3, 0, 2] ![2, 0, 3, 1]) (by decide +kernel) repD2Out,
      relabelK (permK ![3, 1, 0, 2] ![2, 1, 3, 0]) (by decide +kernel) repD2Out,
      relabelK (permK ![1, 3, 0, 2] ![2, 0, 3, 1]) (by decide +kernel) repD2In,
      relabelK (permK ![0, 3, 1, 2] ![0, 2, 3, 1]) (by decide +kernel) repD2Out,
      relabelK (permK ![0, 3, 1, 2] ![0, 2, 3, 1]) (by decide +kernel) repD2In,
      relabelK (permK ![3, 0, 1, 2] ![1, 2, 3, 0]) (by decide +kernel) repD2In,
      relabelK (permK ![3, 0, 1, 2] ![1, 2, 3, 0]) (by decide +kernel) repD2Out,
      relabelK (permK ![0, 1, 3, 2] ![0, 1, 3, 2]) (by decide +kernel) repD2Out,
      relabelK (permK ![0, 1, 3, 2] ![0, 1, 3, 2]) (by decide +kernel) repD2In,
      relabelK (permK ![1, 0, 3, 2] ![1, 0, 3, 2]) (by decide +kernel) repD2Out,
      relabelK (permK ![1, 0, 3, 2] ![1, 0, 3, 2]) (by decide +kernel) repD2In] := by
  decide +kernel

/-- The 1PI contractions of `gfgg` are relabellings of the representatives. -/
theorem onePI_gfgg_eq_relabelK : onePI_gfgg =
    [relabelK (permK ![3, 2, 0, 1] ![2, 3, 1, 0]) (by decide +kernel) repD2Out,
      relabelK (permK ![2, 3, 0, 1] ![2, 3, 0, 1]) (by decide +kernel) repD2Out,
      relabelK (permK ![3, 2, 0, 1] ![2, 3, 1, 0]) (by decide +kernel) repD2In,
      relabelK (permK ![2, 3, 0, 1] ![2, 3, 0, 1]) (by decide +kernel) repD2In,
      relabelK (permK ![0, 3, 2, 1] ![0, 3, 2, 1]) (by decide +kernel) repD2In,
      relabelK (permK ![0, 3, 2, 1] ![0, 3, 2, 1]) (by decide +kernel) repD2Out,
      relabelK (permK ![3, 0, 2, 1] ![1, 3, 2, 0]) (by decide +kernel) repD2In,
      relabelK (permK ![3, 0, 2, 1] ![1, 3, 2, 0]) (by decide +kernel) repD2Out,
      relabelK (permK ![0, 2, 3, 1] ![0, 3, 1, 2]) (by decide +kernel) repD2In,
      relabelK (permK ![0, 2, 3, 1] ![0, 3, 1, 2]) (by decide +kernel) repD2Out,
      relabelK (permK ![2, 0, 3, 1] ![1, 3, 0, 2]) (by decide +kernel) repD2In,
      relabelK (permK ![2, 0, 3, 1] ![1, 3, 0, 2]) (by decide +kernel) repD2Out] := by
  decide +kernel

/-- The 1PI contractions of `fggg` are relabellings of the representatives. -/
theorem onePI_fggg_eq_relabelK : onePI_fggg =
    [relabelK (permK ![3, 2, 1, 0] ![3, 2, 1, 0]) (by decide +kernel) repD2Out,
      relabelK (permK ![2, 3, 1, 0] ![3, 2, 0, 1]) (by decide +kernel) repD2In,
      relabelK (permK ![2, 3, 1, 0] ![3, 2, 0, 1]) (by decide +kernel) repD2Out,
      relabelK (permK ![3, 2, 1, 0] ![3, 2, 1, 0]) (by decide +kernel) repD2In,
      relabelK (permK ![1, 3, 2, 0] ![3, 0, 2, 1]) (by decide +kernel) repD2In,
      relabelK (permK ![3, 1, 2, 0] ![3, 1, 2, 0]) (by decide +kernel) repD2Out,
      relabelK (permK ![1, 3, 2, 0] ![3, 0, 2, 1]) (by decide +kernel) repD2Out,
      relabelK (permK ![3, 1, 2, 0] ![3, 1, 2, 0]) (by decide +kernel) repD2In,
      relabelK (permK ![1, 2, 3, 0] ![3, 0, 1, 2]) (by decide +kernel) repD2In,
      relabelK (permK ![2, 1, 3, 0] ![3, 1, 0, 2]) (by decide +kernel) repD2Out,
      relabelK (permK ![1, 2, 3, 0] ![3, 0, 1, 2]) (by decide +kernel) repD2Out,
      relabelK (permK ![2, 1, 3, 0] ![3, 1, 0, 2]) (by decide +kernel) repD2In] := by
  decide +kernel

/-- The 1PI contractions of `gggp` are relabellings of the representatives. -/
theorem onePI_gggp_eq_relabelK : onePI_gggp =
    [relabelK (permK ![2, 1, 0, 3] ![2, 1, 0, 3]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![2, 1, 0, 3] ![2, 1, 0, 3]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![1, 2, 0, 3] ![2, 0, 1, 3]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![1, 2, 0, 3] ![2, 0, 1, 3]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 2, 1, 3] ![0, 2, 1, 3]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 2, 1, 3] ![0, 2, 1, 3]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![2, 0, 1, 3] ![1, 2, 0, 3]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![2, 0, 1, 3] ![1, 2, 0, 3]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 1, 2, 3] ![0, 1, 2, 3]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 1, 2, 3] ![0, 1, 2, 3]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![1, 0, 2, 3] ![1, 0, 2, 3]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![1, 0, 2, 3] ![1, 0, 2, 3]) (by decide +kernel) repD3Slot1] := by
  decide +kernel

/-- The 1PI contractions of `ggpg` are relabellings of the representatives. -/
theorem onePI_ggpg_eq_relabelK : onePI_ggpg =
    [relabelK (permK ![3, 1, 0, 2] ![2, 1, 3, 0]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![3, 1, 0, 2] ![2, 1, 3, 0]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![1, 3, 0, 2] ![2, 0, 3, 1]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![1, 3, 0, 2] ![2, 0, 3, 1]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 3, 1, 2] ![0, 2, 3, 1]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 3, 1, 2] ![0, 2, 3, 1]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![3, 0, 1, 2] ![1, 2, 3, 0]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![3, 0, 1, 2] ![1, 2, 3, 0]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 1, 3, 2] ![0, 1, 3, 2]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 1, 3, 2] ![0, 1, 3, 2]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![1, 0, 3, 2] ![1, 0, 3, 2]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![1, 0, 3, 2] ![1, 0, 3, 2]) (by decide +kernel) repD3Slot1] := by
  decide +kernel

/-- The 1PI contractions of `gpgg` are relabellings of the representatives. -/
theorem onePI_gpgg_eq_relabelK : onePI_gpgg =
    [relabelK (permK ![3, 2, 0, 1] ![2, 3, 1, 0]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![3, 2, 0, 1] ![2, 3, 1, 0]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![2, 3, 0, 1] ![2, 3, 0, 1]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![2, 3, 0, 1] ![2, 3, 0, 1]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 3, 2, 1] ![0, 3, 2, 1]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 3, 2, 1] ![0, 3, 2, 1]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![3, 0, 2, 1] ![1, 3, 2, 0]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![3, 0, 2, 1] ![1, 3, 2, 0]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 2, 3, 1] ![0, 3, 1, 2]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![0, 2, 3, 1] ![0, 3, 1, 2]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![2, 0, 3, 1] ![1, 3, 0, 2]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![2, 0, 3, 1] ![1, 3, 0, 2]) (by decide +kernel) repD3Slot1] := by
  decide +kernel

/-- The 1PI contractions of `pggg` are relabellings of the representatives. -/
theorem onePI_pggg_eq_relabelK : onePI_pggg =
    [relabelK (permK ![3, 2, 1, 0] ![3, 2, 1, 0]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![3, 2, 1, 0] ![3, 2, 1, 0]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![2, 3, 1, 0] ![3, 2, 0, 1]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![2, 3, 1, 0] ![3, 2, 0, 1]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![1, 3, 2, 0] ![3, 0, 2, 1]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![1, 3, 2, 0] ![3, 0, 2, 1]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![3, 1, 2, 0] ![3, 1, 2, 0]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![3, 1, 2, 0] ![3, 1, 2, 0]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![1, 2, 3, 0] ![3, 0, 1, 2]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![1, 2, 3, 0] ![3, 0, 1, 2]) (by decide +kernel) repD3Slot1,
      relabelK (permK ![2, 1, 3, 0] ![3, 1, 0, 2]) (by decide +kernel) repD3Slot0,
      relabelK (permK ![2, 1, 3, 0] ![3, 1, 0, 2]) (by decide +kernel) repD3Slot1] := by
  decide +kernel

/-- The 1PI contractions of `ggC` are relabellings of the representatives. -/
theorem onePI_ggC_eq_relabelK : onePI_ggC =
    [relabelK (permK ![1, 0, 2] ![1, 0, 2]) (by decide +kernel) repD1At1,
      relabelK (permK ![1, 0, 2] ![1, 0, 2]) (by decide +kernel) repD1At2,
      relabelK (permK ![0, 1, 2] ![0, 1, 2]) (by decide +kernel) repD1At2,
      relabelK (permK ![0, 1, 2] ![0, 1, 2]) (by decide +kernel) repD1At1,
      relabelK (permK ![0, 1, 2] ![0, 1, 2]) (by decide +kernel) repD1At3,
      relabelK (permK ![1, 0, 2] ![1, 0, 2]) (by decide +kernel) repD1At3] := by
  decide +kernel

/-- The 1PI contractions of `gCg` are relabellings of the representatives. -/
theorem onePI_gCg_eq_relabelK : onePI_gCg =
    [relabelK (permK ![2, 0, 1] ![1, 2, 0]) (by decide +kernel) repD1At2,
      relabelK (permK ![2, 0, 1] ![1, 2, 0]) (by decide +kernel) repD1At1,
      relabelK (permK ![0, 2, 1] ![0, 2, 1]) (by decide +kernel) repD1At3,
      relabelK (permK ![2, 0, 1] ![1, 2, 0]) (by decide +kernel) repD1At3,
      relabelK (permK ![0, 2, 1] ![0, 2, 1]) (by decide +kernel) repD1At2,
      relabelK (permK ![0, 2, 1] ![0, 2, 1]) (by decide +kernel) repD1At1] := by
  decide +kernel

/-- The 1PI contractions of `Cgg` are relabellings of the representatives. -/
theorem onePI_Cgg_eq_relabelK : onePI_Cgg =
    [relabelK (permK ![2, 1, 0] ![2, 1, 0]) (by decide +kernel) repD1At3,
      relabelK (permK ![1, 2, 0] ![2, 0, 1]) (by decide +kernel) repD1At3,
      relabelK (permK ![2, 1, 0] ![2, 1, 0]) (by decide +kernel) repD1At1,
      relabelK (permK ![2, 1, 0] ![2, 1, 0]) (by decide +kernel) repD1At2,
      relabelK (permK ![1, 2, 0] ![2, 0, 1]) (by decide +kernel) repD1At1,
      relabelK (permK ![1, 2, 0] ![2, 0, 1]) (by decide +kernel) repD1At2] := by
  decide +kernel

/-! ### The values of the lists -/

theorem listValue_gggf (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    listValue P onePI_gggf pOut pIn kIn αOut βIn μ =
      6 * contractionValue₂ P repD2In pOut pIn kIn αOut βIn μ +
      6 * contractionValue₂ P repD2Out pOut pIn kIn αOut βIn μ := by
  rw [listValue, onePI_gggf_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    value_relabelK P hmom repD2In_isOnePI,
    value_relabelK P hmom repD2Out_isOnePI]
  ring

theorem listValue_ggfg (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    listValue P onePI_ggfg pOut pIn kIn αOut βIn μ =
      6 * contractionValue₂ P repD2In pOut pIn kIn αOut βIn μ +
      6 * contractionValue₂ P repD2Out pOut pIn kIn αOut βIn μ := by
  rw [listValue, onePI_ggfg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    value_relabelK P hmom repD2In_isOnePI,
    value_relabelK P hmom repD2Out_isOnePI]
  ring

theorem listValue_gfgg (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    listValue P onePI_gfgg pOut pIn kIn αOut βIn μ =
      6 * contractionValue₂ P repD2In pOut pIn kIn αOut βIn μ +
      6 * contractionValue₂ P repD2Out pOut pIn kIn αOut βIn μ := by
  rw [listValue, onePI_gfgg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    value_relabelK P hmom repD2In_isOnePI,
    value_relabelK P hmom repD2Out_isOnePI]
  ring

theorem listValue_fggg (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    listValue P onePI_fggg pOut pIn kIn αOut βIn μ =
      6 * contractionValue₂ P repD2In pOut pIn kIn αOut βIn μ +
      6 * contractionValue₂ P repD2Out pOut pIn kIn αOut βIn μ := by
  rw [listValue, onePI_fggg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    value_relabelK P hmom repD2In_isOnePI,
    value_relabelK P hmom repD2Out_isOnePI]
  ring

theorem listValue_gggp (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    listValue P onePI_gggp pOut pIn kIn αOut βIn μ =
      6 * contractionValue₂ P repD3Slot0 pOut pIn kIn αOut βIn μ +
      6 * contractionValue₂ P repD3Slot1 pOut pIn kIn αOut βIn μ := by
  rw [listValue, onePI_gggp_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    value_relabelK P hmom repD3Slot0_isOnePI,
    value_relabelK P hmom repD3Slot1_isOnePI]
  ring

theorem listValue_ggpg (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    listValue P onePI_ggpg pOut pIn kIn αOut βIn μ =
      6 * contractionValue₂ P repD3Slot0 pOut pIn kIn αOut βIn μ +
      6 * contractionValue₂ P repD3Slot1 pOut pIn kIn αOut βIn μ := by
  rw [listValue, onePI_ggpg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    value_relabelK P hmom repD3Slot0_isOnePI,
    value_relabelK P hmom repD3Slot1_isOnePI]
  ring

theorem listValue_gpgg (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    listValue P onePI_gpgg pOut pIn kIn αOut βIn μ =
      6 * contractionValue₂ P repD3Slot0 pOut pIn kIn αOut βIn μ +
      6 * contractionValue₂ P repD3Slot1 pOut pIn kIn αOut βIn μ := by
  rw [listValue, onePI_gpgg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    value_relabelK P hmom repD3Slot0_isOnePI,
    value_relabelK P hmom repD3Slot1_isOnePI]
  ring

theorem listValue_pggg (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    listValue P onePI_pggg pOut pIn kIn αOut βIn μ =
      6 * contractionValue₂ P repD3Slot0 pOut pIn kIn αOut βIn μ +
      6 * contractionValue₂ P repD3Slot1 pOut pIn kIn αOut βIn μ := by
  rw [listValue, onePI_pggg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    value_relabelK P hmom repD3Slot0_isOnePI,
    value_relabelK P hmom repD3Slot1_isOnePI]
  ring

theorem listValue_ggC (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    listValue P onePI_ggC pOut pIn kIn αOut βIn μ =
      2 * contractionValue₂ P repD1At1 pOut pIn kIn αOut βIn μ +
      2 * contractionValue₂ P repD1At2 pOut pIn kIn αOut βIn μ +
      2 * contractionValue₂ P repD1At3 pOut pIn kIn αOut βIn μ := by
  rw [listValue, onePI_ggC_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    value_relabelK P hmom repD1At1_isOnePI,
    value_relabelK P hmom repD1At2_isOnePI,
    value_relabelK P hmom repD1At3_isOnePI]
  ring

theorem listValue_gCg (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    listValue P onePI_gCg pOut pIn kIn αOut βIn μ =
      2 * contractionValue₂ P repD1At1 pOut pIn kIn αOut βIn μ +
      2 * contractionValue₂ P repD1At2 pOut pIn kIn αOut βIn μ +
      2 * contractionValue₂ P repD1At3 pOut pIn kIn αOut βIn μ := by
  rw [listValue, onePI_gCg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    value_relabelK P hmom repD1At1_isOnePI,
    value_relabelK P hmom repD1At2_isOnePI,
    value_relabelK P hmom repD1At3_isOnePI]
  ring

theorem listValue_Cgg (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    listValue P onePI_Cgg pOut pIn kIn αOut βIn μ =
      2 * contractionValue₂ P repD1At1 pOut pIn kIn αOut βIn μ +
      2 * contractionValue₂ P repD1At2 pOut pIn kIn αOut βIn μ +
      2 * contractionValue₂ P repD1At3 pOut pIn kIn αOut βIn μ := by
  rw [listValue, onePI_Cgg_eq_relabelK]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    value_relabelK P hmom repD1At1_isOnePI,
    value_relabelK P hmom repD1At2_isOnePI,
    value_relabelK P hmom repD1At3_isOnePI]
  ring

/-! ### Coefficient one per class -/

/-- **The counterterm part with coefficient one per class**: under momentum conservation
`pOut 0 = pIn 0 + kIn 0`, the counterterm part of the order-`e⁵` vertex
(`onePIFunction₂_five_sub_four`) is the sum of the values of the seven class representatives. -/
theorem countertermPart_eq (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    (Nat.factorial 4 : ℂ)⁻¹ * (listValue P onePI_gggf pOut pIn kIn αOut βIn μ +
          listValue P onePI_gggp pOut pIn kIn αOut βIn μ +
          listValue P onePI_ggfg pOut pIn kIn αOut βIn μ +
          listValue P onePI_ggpg pOut pIn kIn αOut βIn μ +
          listValue P onePI_gfgg pOut pIn kIn αOut βIn μ +
          listValue P onePI_gpgg pOut pIn kIn αOut βIn μ +
          listValue P onePI_fggg pOut pIn kIn αOut βIn μ +
          listValue P onePI_pggg pOut pIn kIn αOut βIn μ) +
        (Nat.factorial 3 : ℂ)⁻¹ * (listValue P onePI_ggC pOut pIn kIn αOut βIn μ +
          listValue P onePI_gCg pOut pIn kIn αOut βIn μ +
          listValue P onePI_Cgg pOut pIn kIn αOut βIn μ) =
      ∑ c : CtClass, contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ := by
  rw [sum_ctClass, listValue_gggf P hmom, listValue_gggp P hmom, listValue_ggfg P hmom,
    listValue_ggpg P hmom, listValue_gfgg P hmom, listValue_gpgg P hmom, listValue_fggg P hmom,
    listValue_pggg P hmom, listValue_ggC P hmom, listValue_gCg P hmom, listValue_Cgg P hmom,
    show (Nat.factorial 4 : ℂ) = 24 by norm_num [Nat.factorial],
    show (Nat.factorial 3 : ℂ) = 6 by norm_num [Nat.factorial]]
  ring

/-- **The order-`e⁵` vertex with coefficient one per class** (obligations O2-2, O2-3): under
momentum conservation `pOut 0 = pIn 0 + kIn 0`, `onePIFunction₂ P 1 1 5 - onePIFunction₂ P 1 1 4`
is the signed sum of the values of the seven classes `L, X, C₊, C₋, S₊, S₋, VP` of five gauge
vertices plus the sum of the values of the seven counterterm classes, each with coefficient one
(the Furry pair cancels, `QED.TwoLoop.Furry.furry_pair`). -/
theorem onePIFunction₂_five_sub_four_eq_classes (P : Params) {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    (hmom : pOut 0 = pIn 0 + kIn 0) (αOut βIn μ : Fin 1 → Fin 4) :
    onePIFunction₂ P 1 1 5 pOut pIn kIn αOut βIn μ -
        onePIFunction₂ P 1 1 4 pOut pIn kIn αOut βIn μ =
      ∑ c ∈ Furry.nonFurry, (c.sign : ℂ) * contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ +
        ∑ c : CtClass, contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ := by
  rw [Furry.onePIFunction₂_five_sub_four_eq_furry P hmom, add_assoc, countertermPart_eq P hmom]

/-- **The order-`e⁵` vertex with coefficient one per class**, all nine classes of five gauge
vertices kept: under momentum conservation, the signed sum over `Class5` plus the sum over
`CtClass`, each with coefficient one. -/
theorem onePIFunction₂_five_sub_four_eq_all_classes (P : Params)
    {pOut pIn kIn : Fin 1 → Fin 4 → ℝ} (hmom : pOut 0 = pIn 0 + kIn 0)
    (αOut βIn μ : Fin 1 → Fin 4) :
    onePIFunction₂ P 1 1 5 pOut pIn kIn αOut βIn μ -
        onePIFunction₂ P 1 1 4 pOut pIn kIn αOut βIn μ =
      ∑ c : Class5, (c.sign : ℂ) * contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ +
        ∑ c : CtClass, contractionValue₂ P c.rep pOut pIn kIn αOut βIn μ := by
  rw [onePIFunction₂_five_sub_four_eq P hmom, add_assoc, countertermPart_eq P hmom]

end QED.TwoLoop.Relabel

end
