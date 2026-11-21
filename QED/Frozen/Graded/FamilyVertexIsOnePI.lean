-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.FamilyVertex
public import QED.Frozen.Graded.VertexPart
public import QED.Provider.Graded.FamilyVertexIsOnePI

@[expose] public section

open QED.WickModel (Params IsOnePI)

namespace QED.Graded

/-- (MF₁) **The family vertex with the trivial 1PI selection is the vertex (G₈ᵥ)** (meaning
theorem; the analogue of (M₁)): at order `2n + 1`, (Gf₁) with `Sel C g := IsOnePI C` is (G₈ᵥ) at
the open-line flavour. Expected by `rfl`. -/
theorem familyVertex_isOnePI (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (n : ℕ) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    familyVertex P Φ D (fun C _ => IsOnePI C) (2 * n + 1) p' p μ =
      vertexPart P Φ D Φ.openLine n p' p μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
