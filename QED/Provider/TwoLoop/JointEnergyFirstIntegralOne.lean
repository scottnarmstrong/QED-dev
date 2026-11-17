/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.JointEnergyFirstIntegral
public import QED.Frozen.OneLoop.EnergyFirstIntegral
import QED.TwoLoop.JointIntegral

/-!
# Provider for `QED.TwoLoop.jointEnergyFirstIntegral_one`

Proves packet T1's theorem goal (T₁₂) (decision D-38) as
`QED.Provider.TwoLoop.jointEnergyFirstIntegral_one`, with the binder convention of decision D-13.
The content is `QED.TwoLoop.jointEnergyFirstIntegral_one_eq`: the measure-preserving
identification of `Fin 1 → X` with `X` in both stages. This module must never import the frozen
anchor.
-/

public section

namespace QED.Provider.TwoLoop

/-- Packet T1's (T₁₂), with implicit data binders (decision D-13). -/
theorem jointEnergyFirstIntegral_one {F : (Fin 4 → ℝ) → ℂ} :
    QED.TwoLoop.jointEnergyFirstIntegral 1 (fun ℓ => F (ℓ 0)) =
      QED.OneLoop.energyFirstIntegral F :=
  QED.TwoLoop.jointEnergyFirstIntegral_one_eq F

end QED.Provider.TwoLoop

end
