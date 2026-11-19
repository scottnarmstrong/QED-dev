/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.A1Four
import QED.Polylog.A1FourFine

/-!
# Provider for `QED.TwoLoop.a1Four_bounds_fine`

Proves the frozen theorem goal (U₂′) (decision D-54) as
`QED.Provider.TwoLoop.a1Four_bounds_fine`, from the helper `QED.Polylog.a1Four_bounds_finer`
(kernel-checked bounds on `π`, `ln 2` and `ζ(3)`). This module must never import the frozen anchor.
-/

public section

namespace QED.Provider.TwoLoop

/-- (U₂′) (decision D-13 convention; no binders). -/
theorem a1Four_bounds_fine :
    -0.32847896557919380 < QED.TwoLoop.a1Four ∧ QED.TwoLoop.a1Four < -0.32847896557919376 :=
  QED.Polylog.a1Four_bounds_finer

end QED.Provider.TwoLoop

end
