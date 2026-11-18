-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.A2Four
public import QED.Frozen.Lepton.A2FourPas
public import QED.Provider.Lepton.A2FourPasEqA2Four

@[expose] public section

namespace QED.Lepton

/-- The two candidate forms agree on `(0, 1)` (an elementary identity; obligation of the
transcription audit if `a2Four` is chosen). -/
theorem a2FourPas_eq_a2Four {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) : a2FourPas y = a2Four y :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Lepton

end
-- FROZEN_ANCHOR_SUFFIX_END
