/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCLinkClassStd

/-!
# The set (c) classification: the finite search, bubble branch

Helper for the set (c) headline (HS₆) `QED.ThreeLoop.isFormFactorPair_vertexSetC_pauli_limit`
(decision D-58), the enumeration step. For an open line of `L ≤ 5` vertices of kinds `ℓ` (no
`photonCt`) followed by a bubble, under the order conditions `KFilter` of graded order `7`, every
1PI contraction in standard form (`stdContractions`) is a level-`0` representative, up to the
exchange of the two bubble vertices. Checked by kernel evaluation, one open-line length at a
time.

* `QED.ChainProof.SetCLink.decB_of_le`: the search for every `L ≤ 5`.
-/

@[expose] public section

namespace QED.ChainProof.SetCLink

open QED.WickModel QED.TwoLoop.Relabel QED.TwoLoop.Enumeration

/-- The bubble search at open-line length `L`. -/
def DecB (L : ℕ) : Prop :=
  ∀ ℓ : Fin L → Wick.VertexKind, (∀ i, ℓ i ≠ .photonCt) → KFilter (kindsB ℓ) →
    ∀ C ∈ stdContractions (kindsB ℓ) L true, IsOnePI C →
      ∃ R ∈ repsCZ (L + 2), ∃ ρ ∈ [1, swapLast L],
        ∃ h : (∀ t, kindsB ℓ (ρ t) = R.kinds t), C = relabelK ρ h R.rep

theorem decB0 : DecB 0 := by unfold DecB; decide +kernel

theorem decB1 : DecB 1 := by unfold DecB; decide +kernel

theorem decB2 : DecB 2 := by unfold DecB; decide +kernel

theorem decB3 : DecB 3 := by unfold DecB; decide +kernel

theorem decB4 : DecB 4 := by unfold DecB; decide +kernel

theorem decB5 : DecB 5 := by unfold DecB; decide +kernel

/-- **The bubble search**, for every open-line length `L ≤ 5`. -/
theorem decB_of_le {L : ℕ} (hL : L ≤ 5) : DecB L := by
  interval_cases L
  exacts [decB0, decB1, decB2, decB3, decB4, decB5]

end QED.ChainProof.SetCLink

end
