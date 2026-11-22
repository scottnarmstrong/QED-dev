-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.FamilyVertex
public import QED.Frozen.VPChain.VertexChain
public import QED.Provider.Graded.FamilyVertexIsVPChainTwo

@[expose] public section

open QED.WickModel (Params IsOnePI)

namespace QED.Graded

/-- (E-G₄) **The graded set (b) vertex is the frozen chain vertex** (Stage 2 design note,
deferred item D1; the analogue of (E-G₃) for the chains): when the level-`0` photon counterterm is
the `δ₃` of `P` divided by `e²`, the family vertex (Gf₁) of the 1PI two-insertion chains (C₁) at
order `7` is the frozen chain vertex (C₃) at `n = 2`. A chain contraction has total order `7` with
every vertex at level `0`, its only counterterm vertices are `photonCt` vertices (which carry no
fermion field, so the flavourings of (G₁) and (F₁) agree on it), and its `photonCt` factor reads
`e² d₃ 0 = δ₃`. No other datum of `D` or `P` enters. This is one of the bridges needed to add the
set (b) headline (HC₃) to the graded set headlines; adding (HC₃) also needs the flavour relabelling
(E₃) and the meaning theorems (E-G₂). -/
theorem familyVertex_isVPChain_two (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (h₃ : P.δ₃ = P.e ^ 2 * D.d₃ 0)
    (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    familyVertex P Φ D (fun C _ => IsOnePI C ∧ VPChain.IsVPChain 2 C) 7 p' p μ =
      VPChain.vertexChain 2 P Φ p' p μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.familyVertex_isVPChain_two
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
