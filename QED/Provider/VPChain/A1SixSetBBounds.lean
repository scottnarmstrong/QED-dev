/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.A1SixSetB
import QED.ChainProof.QuickValues

/-!
# Provider for `QED.VPChain.a1SixSetB_bounds`

Proves the frozen theorem goal `QED.VPChain.a1SixSetB_bounds` (Phase 5 Stage 1a packet, decision
D-53) as `QED.Provider.VPChain.a1SixSetB_bounds`, with the binder convention of decision D-13, from
the helper in `QED.ChainProof.QuickValues`. This module must never import the frozen anchor.
-/

public section

namespace QED.Provider.VPChain

open QED.VPChain

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem a1SixSetB_bounds : 0.00255852 < a1SixSetB ∧ a1SixSetB < 0.00255853 :=
  QED.ChainProof.a1SixSetB_bounds'

end QED.Provider.VPChain

end
