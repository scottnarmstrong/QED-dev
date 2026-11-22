-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsSetD
public import QED.Frozen.ThreeLoop.IsSetA
public import QED.Frozen.ThreeLoop.IsSetC
public import QED.Frozen.VPChain.IsVPChain
public import QED.Provider.ThreeLoop.IsSetDDisjoint

@[expose] public section

open QED.WickModel (Contraction)

namespace QED.ThreeLoop

/-- (MD₂) **Set (d) is disjoint from sets (a), (b), (c)** (meaning theorem): no contraction is
both in (Sd₁) and in (A₁), in a two-insertion chain (C₁), or in (Sc₃) at any grading. In (A₁) and
(C₁) the external photon is on the open line, in (Sd₁) on a closed loop; (Sc₃) has a `photonCt`
vertex, or a closed loop of two vertices only, or no closed loop, while (Sd₁) has only `gauge`
vertices and a loop of at least four. No order hypothesis is needed. -/
theorem isSetD_disjoint {N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction 1 1 κ)
    (g : Graded.Grading κ) :
    ¬ (IsSetD C ∧ IsSetA C) ∧ ¬ (IsSetD C ∧ VPChain.IsVPChain 2 C) ∧
      ¬ (IsSetD C ∧ IsSetC C g) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
