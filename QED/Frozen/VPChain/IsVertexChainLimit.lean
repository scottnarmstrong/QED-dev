/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.VPChain.VertexChain

@[expose] public section

open Filter Topology
open QED.WickModel (Params)
open QED.Lepton (Flavors)

namespace QED.VPChain

/-- (C₄) **The chain vertex as `ε → 0⁺`** (decisions D-5, D-37.5; the analogue of (HV₂) and
(F₁₀)): `V` is the limit of (C₃) as the Feynman prescription `ε` tends to `0⁺`, entry by entry,
for every `μ`, with `Φ` and all other parameters of `P` fixed; the `ε` stored in `P` is
replaced. -/
def IsVertexChainLimit (n : ℕ) (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F) (p' p : Fin 4 → ℝ) (V : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ μ i j, Tendsto (fun ε => vertexChain n { P with ε := ε } Φ p' p μ i j) (𝓝[>] 0)
    (𝓝 (V μ i j))

end QED.VPChain

end
