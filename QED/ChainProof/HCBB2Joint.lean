/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.HCBB2Limit
public import QED.ChainProof.RepsIntBBJoint

/-!
# The three-loop integrability of the bubble–bubble class, and `RepLimit repBB`

Helper level, Phase 5 Stage 1a. `QED.ChainProof.HCBB.BBJointIntegrable` is
`QED.ChainProof.RepsIntBB.jointEnergyFirstIntegrable_bbIntegrand` at the parameters
`{P with ε := ε}`, `kext = p' - p`: the Pauli–Villars conditions do not involve `ε`.
Hence `RepLimit repBB` holds with no remaining hypothesis.
-/

@[expose] public section

namespace QED.ChainProof.HCBB2

/-- **The three-loop integrability of the bubble–bubble class.** -/
theorem bbJointIntegrable : QED.ChainProof.HCBB.BBJointIntegrable :=
  fun P hA ε hε _ p _ α β μ =>
    QED.ChainProof.RepsIntBB.jointEnergyFirstIntegrable_bbIntegrand { P with ε := ε } hε
      hA.hPV₁ hA.hPV₂ p _ α β μ

/-- **`RepLimit repBB`**, unconditionally. -/
theorem repLimit_repBB' : QED.ChainProof.HCLimit.RepLimit QED.ChainProof.Enum.repBB :=
  repLimit_repBB bbJointIntegrable

end QED.ChainProof.HCBB2

end
