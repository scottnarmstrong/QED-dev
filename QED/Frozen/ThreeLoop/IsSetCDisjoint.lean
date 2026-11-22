-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetC
public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.VPChain.IsVPChain
public import QED.Frozen.Graded.GradedOrder
public import QED.Provider.ThreeLoop.IsSetCDisjoint

@[expose] public section

open QED.WickModel (Contraction)

namespace QED.ThreeLoop

/-- (MC₂) **Sets (a), (b), (c) are disjoint at order `7`** (meaning theorem): at graded order `7`
no contraction is both in (Sc₃) and in (A₁), and none is both in (Sc₃) and a two-insertion
chain (C₁) of Stage 1a. (At order `5` the bubble of (A₁) and of (Sc₃) coincide: the order
hypothesis is needed.) -/
theorem isSetC_disjoint {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (g : Graded.Grading κ) (hg : Graded.gradedOrder κ g = 7) :
    ¬ (IsSetC C g ∧ IsSetA C) ∧ ¬ (IsSetC C g ∧ VPChain.IsVPChain 2 C) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.ThreeLoop.isSetC_disjoint
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
