/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsPhotonOnShellAt
public import QED.Frozen.Lepton.IsPhotonOnShell
import QED.GradedProof.LevelOnePhoton

/-!
# Provider for `QED.Graded.isPhotonOnShellAt_one_iff`

Proves the frozen theorem goal `QED.Graded.isPhotonOnShellAt_one_iff` (Phase 5 Stage 2 packet,
decision D-57) as `QED.Provider.Graded.isPhotonOnShellAt_one_iff`, with the binder convention of
decision D-13, from the helper in `QED.GradedProof.LevelOnePhoton`. The anchor is sealed (D-57 seal
note).
-/

public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- The frozen goal with implicit data binders (decision D-13). -/
theorem isPhotonOnShellAt_one_iff {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} :
    IsPhotonOnShellAt P Φ D 1 ↔ Lepton.IsPhotonOnShell { P with δ₃ := P.e ^ 2 * D.d₃ 0 } Φ :=
  QED.GradedProof.isPhotonOnShellAt_one_iff' P Φ D

end QED.Provider.Graded

end
