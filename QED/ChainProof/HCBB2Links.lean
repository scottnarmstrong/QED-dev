/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBB2Joint
public import QED.ChainProof.HCBB2ValueBB
public import QED.ChainProof.HCBB2CovBB

/-!
# The bubble–bubble inputs of `classLinks_of_reps`

Helper level, Phase 5 Stage 1a (O3-6, O3-7, O3-8 for `QED.ChainProof.Enum.repBB`). The three
`repBB` inputs of `QED.ChainProof.HCSide.classLinks_of_reps`, unconditionally: from the
three-loop integrability `QED.ChainProof.HCBB2.bbJointIntegrable`, the value identity
`QED.ChainProof.HCBB2.bbPauliValue` and the covariance `QED.ChainProof.HCBB2.bbCov`.
-/

@[expose] public section

namespace QED.ChainProof.HCBB2

open QED.ChainProof.HCSide QED.ChainProof.HCValue QED.WickModel

/-- **`RepNested repBB (enumPhoton 0)`.** -/
theorem repNested_repBB :
    RepNested QED.ChainProof.Enum.repBB (fun P => enumPhoton 0 P) :=
  repNested_repBB_of bbJointIntegrable (bbNestedAt_of_value bbPauliValue)

/-- **`RepCov repBB`.** -/
theorem repCov_repBB : RepCov QED.ChainProof.Enum.repBB :=
  repCov_repBB_of bbJointIntegrable bbCov

/-- **The three `repBB` inputs of `classLinks_of_reps`.** -/
theorem repBB_links :
    QED.ChainProof.HCLimit.RepLimit QED.ChainProof.Enum.repBB ∧
      RepNested QED.ChainProof.Enum.repBB (fun P => enumPhoton 0 P) ∧
      RepCov QED.ChainProof.Enum.repBB :=
  repBB_links_of bbJointIntegrable bbPauliValue bbCov

end QED.ChainProof.HCBB2

end
