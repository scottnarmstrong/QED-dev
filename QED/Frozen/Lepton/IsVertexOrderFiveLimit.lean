/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.VertexOrderFive

@[expose] public section

open Filter Topology
open QED.WickModel (Params)

namespace QED.Lepton

/-- (F₁₀) **The order-`e⁵` vertex as `ε → 0⁺`**, the successor of (HV₂): `V` is the limit of (F₉)
as `ε → 0⁺`, entry by entry, for every `μ`, with `Φ` and all other parameters of `P` fixed. -/
def IsVertexOrderFiveLimit (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F)
    (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ μ i j, Tendsto (fun ε => vertexOrderFive { P with ε := ε } Φ p' p μ i j) (𝓝[>] 0)
    (𝓝 (V μ i j))

end QED.Lepton

end
