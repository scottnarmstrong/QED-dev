/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.LoopBound

/-!
# At most two loops below the three-loop order

A contraction with attached externals (X₁₆) and connected vertices (X₁₇) whose total order is
at most `2 nf + nA + 3` has at most two chords (T₁), so `loopCount C ≤ 2` (T₂). This is the
source-facing bound `K ≤ 2 nf + nA + 3` of obligation O2-5 (iii).

The proof is that of `QED.TwoLoop.LoopBound.loopCount_le_one_of_connected` with one more unit
of order: field counting gives `2 E + 2 nf + nA ≤ 2 V + K ≤ 2 V + 2 nf + nA + 3`, so
`E ≤ V + 1`, and at least `V - 1` lines are not chords, so `#chords ≤ (V + 1) - (V - 1) = 2`.
More generally, `2 · loopCount C + 2 nf + nA ≤ ∑ order + 2`
(`QED.TwoLoop.LoopBoundTwo.two_mul_loopCount_add_le`).
-/

public section

namespace QED.TwoLoop.LoopBoundTwo

open QED.WickModel QED.TwoLoop.LoopBound

variable {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}

/-- With attached externals (X₁₆) and connected vertices (X₁₇), twice the number of loops plus
`2 nf + nA` is at most the total order plus two. -/
theorem two_mul_loopCount_add_le {C : Contraction nf nA κ} (hA : ExternalsAttached C)
    (hV : VerticesConnected C) :
    2 * loopCount C + 2 * nf + nA ≤ ∑ t, (κ t).order + 2 := by
  have h1 := two_mul_card_line_le hA
  have h2 := card_le_card_nonChord_add_one hV
  have h3 := loopCount_add_card_nonChord C
  omega

/-- A contraction with attached externals (X₁₆) and connected vertices (X₁₇) of total order at
most `K ≤ 2 nf + nA + 3` has at most two loops. -/
theorem loopCount_le_two_of_connected {K : ℕ} (hκ : ∑ t, (κ t).order ≤ K)
    (hK : K ≤ 2 * nf + nA + 3) {C : Contraction nf nA κ} (hA : ExternalsAttached C)
    (hV : VerticesConnected C) : loopCount C ≤ 2 := by
  have := two_mul_loopCount_add_le hA hV
  omega

/-- **At most two loops below the three-loop order** (O2-5 (iii)). Every 1PI contraction (X₁₈)
of total order at most `K ≤ 2 nf + nA + 3` has at most two loops (T₂). -/
theorem loopCount_le_two_of_order {K : ℕ} (hκ : ∑ t, (κ t).order ≤ K)
    (hK : K ≤ 2 * nf + nA + 3) (C : Contraction nf nA κ) (hC : IsOnePI C) : loopCount C ≤ 2 :=
  loopCount_le_two_of_connected hκ hK hC.1 hC.2.1

end QED.TwoLoop.LoopBoundTwo

end
