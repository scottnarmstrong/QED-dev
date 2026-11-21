/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsOnShellSelAt
public import QED.Frozen.Graded.IsOnShellAt

/-!
# Provider for `QED.Graded.isOnShellSelAt_isOnePI_iff`

Proves the frozen theorem goal (MS₁) (Phase 5 Stage 3a/3b packet, decision D-58) as
`QED.Provider.Graded.isOnShellSelAt_isOnePI_iff`, with the binder convention of decision D-13:
with the 1PI selection the condition (Gs₂) is (G₉) by unfolding (`Iff.rfl`). This module must
never import the frozen anchor.
-/

@[expose] public section

open QED.WickModel (Params IsOnePI)
open QED.Graded

namespace QED.Provider.Graded

/-- (MS₁), with implicit data binders (decision D-13). -/
theorem isOnShellSelAt_isOnePI_iff {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {f : F} {n : ℕ} :
    IsOnShellSelAt P Φ D (fun C _ => IsOnePI C) f n ↔ IsOnShellAt P Φ D f n :=
  Iff.rfl

end QED.Provider.Graded

end
