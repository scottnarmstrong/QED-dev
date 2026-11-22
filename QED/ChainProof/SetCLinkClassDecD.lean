/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkClassStd

/-!
# The set (c) classification: the finite search, `δ₃` and VP-share branches

Helper for the set (c) headline (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(decision D-58), the enumeration step. Checked by kernel evaluation, one open-line length at a
time:

* `QED.ChainProof.SetCLink.decD_of_le`: for an open line of `L ≤ 5` vertices of kinds `ℓ` (no
  `photonCt`) followed by a `photonCt` vertex, under the order conditions `KFilter`, every 1PI
  contraction in standard form is a level-`0` representative;
* `QED.ChainProof.SetCLink.decS_of_le`: for an open line of `L ≤ 5` vertices and no element,
  under the conditions `SFilter` (one counterterm vertex, orders summing to `5`), every 1PI
  contraction in standard form is a level-`1` representative.
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.TwoLoop.Relabel QED.TwoLoop.Enumeration

/-- The `δ₃` search at open-line length `L`. -/
def DecD (L : ℕ) : Prop :=
  ∀ ℓ : Fin L → Wick.VertexKind, (∀ i, ℓ i ≠ .photonCt) → KFilter (kindsD ℓ) →
    ∀ C ∈ stdContractions (kindsD ℓ) L false, IsOnePI C →
      ∃ R ∈ repsCZ (L + 1), ∃ h : (∀ t, kindsD ℓ ((1 : Equiv.Perm (Fin (L + 1))) t) = R.kinds t),
        C = relabelK 1 h R.rep

theorem decD0 : DecD 0 := by unfold DecD; decide +kernel

theorem decD1 : DecD 1 := by unfold DecD; decide +kernel

theorem decD2 : DecD 2 := by unfold DecD; decide +kernel

theorem decD3 : DecD 3 := by unfold DecD; decide +kernel

theorem decD4 : DecD 4 := by unfold DecD; decide +kernel

theorem decD5 : DecD 5 := by unfold DecD; decide +kernel

/-- **The `δ₃` search**, for every open-line length `L ≤ 5`. -/
theorem decD_of_le {L : ℕ} (hL : L ≤ 5) : DecD L := by
  interval_cases L
  exacts [decD0, decD1, decD2, decD3, decD4, decD5]

/-- The VP-share search at open-line length `L`. -/
def DecS (L : ℕ) : Prop :=
  ∀ ℓ : Fin L → Wick.VertexKind, SFilter ℓ →
    ∀ C ∈ stdContractions ℓ L false, IsOnePI C →
      ∃ R ∈ repsCS L, ∃ h : (∀ t, ℓ ((1 : Equiv.Perm (Fin L)) t) = R.kinds t),
        C = relabelK 1 h R.rep

theorem decS0 : DecS 0 := by unfold DecS; decide +kernel

theorem decS1 : DecS 1 := by unfold DecS; decide +kernel

theorem decS2 : DecS 2 := by unfold DecS; decide +kernel

theorem decS3 : DecS 3 := by unfold DecS; decide +kernel

theorem decS4 : DecS 4 := by unfold DecS; decide +kernel

theorem decS5 : DecS 5 := by unfold DecS; decide +kernel

/-- **The VP-share search**, for every open-line length `L ≤ 5`. -/
theorem decS_of_le {L : ℕ} (hL : L ≤ 5) : DecS L := by
  interval_cases L
  exacts [decS0, decS1, decS2, decS3, decS4, decS5]

end QED.ChainProof.SetCLink

end
