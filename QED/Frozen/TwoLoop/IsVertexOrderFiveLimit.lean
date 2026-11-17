/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.VertexOrderFive

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params onePIFunction₂)

namespace QED.TwoLoop

/-- (HV₂) **The order-`e⁵` vertex as `ε → 0⁺`** (decisions D-5, D-37.5): `V` is the limit of the
order-`e⁵` vertex (HV₁) as the Feynman prescription `ε` tends to `0⁺`, entry by entry, for every
`μ`, with all other parameters of `P` fixed; the `ε` stored in `P` is replaced. As in (W₂), the
regulated vertex is defined at fixed `ε`, and the source's vertex function is its limit. -/
def IsVertexOrderFiveLimit (P : Params) (p' p : Fin 4 → ℝ)
    (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ μ i j, Tendsto (fun ε => vertexOrderFive { P with ε := ε } p' p μ i j) (𝓝[>] 0)
    (𝓝 (V μ i j))

end QED.TwoLoop

end
