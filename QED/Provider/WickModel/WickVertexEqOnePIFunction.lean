/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.OnePIFunction
public import QED.Frozen.Wick.WickVertex
import QED.WickModel.Compatibility

/-!
# Provider for `QED.WickModel.wickVertex_eq_onePIFunction`

Proves packet 6a's theorem goal (Y₁) (decision D-24) as
`QED.Provider.WickModel.wickVertex_eq_onePIFunction`, with the binder convention of decision D-13.
This module must never import the frozen anchor.

`QED.WickModel.wickVertex_eq_onePIFunction'` transports packet 5's contractions to the general
model along `Option ≃ Fin 1 ⊕ ·`. The transport preserves the sign, the lines, the 1PI property,
the routing and the amplitudes. Packet 5's classification then shows that the only flavoring a
1PI contraction of this order preserves is the all-electron one, with weight `1`.
-/

@[expose] public section

open Complex

namespace QED.Provider.WickModel

/-- Packet 6a's (Y₁), with implicit data binders (decision D-13). -/
theorem wickVertex_eq_onePIFunction {P : QED.WickModel.Params} {p' p : Fin 4 → ℝ}
    {μ i j : Fin 4} :
    QED.Wick.wickVertex P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m P.mγ P.Λ P.ε p' p μ i j =
      QED.WickModel.onePIFunction P 1 1 3 (fun _ => p') (fun _ => p) (fun _ => p' - p)
        (fun _ => i) (fun _ => j) (fun _ => μ) :=
  QED.WickModel.wickVertex_eq_onePIFunction' P p' p μ i j

end QED.Provider.WickModel

end
