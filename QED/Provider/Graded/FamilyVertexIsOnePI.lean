/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.FamilyVertex
public import QED.Frozen.Graded.VertexPart

/-!
# Provider for `QED.Graded.familyVertex_isOnePI`

Proves the frozen theorem goal (MF₁) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.Graded.familyVertex_isOnePI`, with the binder convention of decision D-13: with the
trivial 1PI selection the family vertex (Gf₁) is the vertex (G₈ᵥ) by unfolding (`rfl`). This
module must never import the frozen anchor.
-/

@[expose] public section

open QED.WickModel (Params IsOnePI)
open QED.Graded

namespace QED.Provider.Graded

/-- (MF₁), with implicit data binders (decision D-13). -/
theorem familyVertex_isOnePI {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {n : ℕ} {p' p : Fin 4 → ℝ} {μ : Fin 4} :
    familyVertex P Φ D (fun C _ => IsOnePI C) (2 * n + 1) p' p μ =
      vertexPart P Φ D Φ.openLine n p' p μ :=
  rfl

end QED.Provider.Graded

end
