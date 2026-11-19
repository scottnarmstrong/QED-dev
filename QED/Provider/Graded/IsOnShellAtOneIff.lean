/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsOnShellAt
public import QED.Frozen.WickModel.IsElectronOnShell
import QED.GradedProof.LevelOneElectron

/-!
# Provider for `QED.Graded.isOnShellAt_one_iff`

Proves the frozen theorem goal `QED.Graded.isOnShellAt_one_iff` (Phase 5 Stage 2 packet, decision
D-57) as `QED.Provider.Graded.isOnShellAt_one_iff`, with the binder convention of decision D-13,
from the helper in `QED.GradedProof.LevelOneElectron`. The anchor is sealed (D-57 seal note).
-/

public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem isOnShellAt_one_iff {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {f : F} (hf : 0 < Φ.mass f := by assumption)
    (hmγ : 0 < P.mγ := by assumption) (hΛ : 0 < P.Λ := by assumption) :
    IsOnShellAt P Φ D f 1 ↔
      WickModel.IsElectronOnShell
        { P with m := Φ.mass f, δ₂ := P.e ^ 2 * D.d₂ f 0, δm := P.e ^ 2 * D.dm f 0 }
        hf hmγ hΛ :=
  QED.GradedProof.isOnShellAt_one_iff' P Φ D f hf hmγ hΛ

end QED.Provider.Graded

end
