/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.A1SixSetB
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.ChainProof.QuickValues

/-!
# Provider for `QED.VPChain.integral_chainTwo_eq_a1SixSetB`

Proves the frozen theorem goal `QED.VPChain.integral_chainTwo_eq_a1SixSetB` (Phase 5 Stage 1a
packet, decision D-53) as `QED.Provider.VPChain.integral_chainTwo_eq_a1SixSetB`, with the binder
convention of decision D-13, from the helper in `QED.ChainProof.QuickValues`. This module must never
import the frozen anchor.
-/

public section

namespace QED.Provider.VPChain

open QED.VPChain

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem integral_chainTwo_eq_a1SixSetB :
    IntervalIntegrable (fun x : ℝ => (1 - x) * (2 * ∫ t in (0 : ℝ)..1,
        t * (1 - t) * Real.log (1 + t * (1 - t) * (x ^ 2 / (1 - x)))) ^ 2)
        MeasureTheory.volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - x) * (2 * ∫ t in (0 : ℝ)..1,
        t * (1 - t) * Real.log (1 + t * (1 - t) * (x ^ 2 / (1 - x)))) ^ 2 = a1SixSetB :=
  QED.ChainProof.integral_chainTwo_eq_a1SixSetB'

end QED.Provider.VPChain

end
