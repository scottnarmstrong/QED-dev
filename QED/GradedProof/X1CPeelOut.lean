/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.X1CPeelOutSurj

/-!
# (X₁) piece C: the out-leg hypotheses of `countDyson_dysonFive_t9`

Helper level for the Phase 5 Stage 2 goal (X₁) `QED.Graded.isLSZAmplitudePart_five_self`
(decision D-57), piece C, step C5; the mirror of the last part of `X1CPeelIn`. With
`SelG := peelSelG`, `RedIn := peelRedIn` and `RedOut := peelRedOut` (an out-leg self-energy cut
exists), the hypotheses `hmemO`, `hinjO`, `hsurjO` of `countDyson_dysonFive_t9`, in exactly its
form: `peelOut_hmemO` (`peelOut_hmem`), `peelOut_hinjO` (`countGlueOut_injOn` with
`peelOut_hpeel`), `peelOut_hsurjO` (`peelOut_hsurj`).
-/

@[expose] public section

namespace QED.GradedProof.X1C

open QED.WickModel (Contraction)
open QED.Graded

/-- `hmemO` of `countDyson_dysonFive_t9` for `peelSelG`, `peelRedIn`, `peelRedOut`. -/
theorem peelOut_hmemO {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ)
    (_ : gradedOrder κ g ≤ 5) :
    ∀ x ∈ countIdxSet (fun C g => peelSelG C g ∧ ¬ peelRedIn C g)
        (countOnePI (nf := 1) (nA := 0)) g,
      (peelSelG (glueOut x.2.1 x.2.2.1 x.2.2.2) g ∧
          ¬ peelRedIn (glueOut x.2.1 x.2.2.1 x.2.2.2) g) ∧
        peelRedOut (glueOut x.2.1 x.2.2.1 x.2.2.2) g :=
  peelOut_hmem g

/-- `hinjO` of `countDyson_dysonFive_t9` for `peelSelG`, `peelRedIn`. -/
theorem peelOut_hinjO {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ)
    (_ : gradedOrder κ g ≤ 5) :
    Set.InjOn (fun x : CountIdx 1 1 1 0 κ => glueOut x.2.1 x.2.2.1 x.2.2.2)
      (countIdxSet (fun C g => peelSelG C g ∧ ¬ peelRedIn C g)
        (countOnePI (nf := 1) (nA := 0)) g) :=
  countGlueOut_injOn peelOutSelH g peelOut (peelOut_hpeel g)

/-- `hsurjO` of `countDyson_dysonFive_t9` for `peelSelG`, `peelRedIn`, `peelRedOut`. -/
theorem peelOut_hsurjO {N : ℕ} (κ : Fin N → Wick.VertexKind) (g : Grading κ)
    (_ : gradedOrder κ g ≤ 5) :
    ∀ C : Contraction 1 1 κ, (peelSelG C g ∧ ¬ peelRedIn C g) → peelRedOut C g →
      ∃ x ∈ countIdxSet (fun C g => peelSelG C g ∧ ¬ peelRedIn C g)
          (countOnePI (nf := 1) (nA := 0)) g,
        glueOut x.2.1 x.2.2.1 x.2.2.2 = C :=
  fun C hS hR => peelOut_hsurj g C hS hR

end QED.GradedProof.X1C

end
