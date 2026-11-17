/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.OnePIFunction

@[expose] public section

open Matrix Complex Filter Topology
open QED.WickModel (Params onePIFunction₂)

namespace QED.TwoLoop

/-- (HV₁) **The order-`e⁵` 1PI vertex at fixed `ε`** (decisions D-37.3, D-37.6; the source's
(62.39) at order `e⁵`): `V^{μ,[5]}_ε(p', p)`, `(1/i)` times the part of total order exactly `5`
in `e` of the 1PI function (T₁₁) with one external fermion pair and one external photon, at
outgoing momentum `p'`, incoming momentum `p` and incoming photon momentum `p' - p`. The entry
`(i, j)` has the outgoing spinor index `i` as row and the incoming index `j` as column, as in
(Y₁); so, as for packet 5's vertex (W₂), it is the matrix `V^μ` of (J), (G₀) and (K₀), with
`i V^μ` the 1PI function. Every vertex has order at least `1` (V₁), so a term of order at most
`K` has at most `K` vertices, and the terms of (T₁₁) at `K = 4` are exactly its terms at `K = 5`
of order at most `4`: the difference is the sum over the 1PI contractions of total order exactly
`5`, which have at most two loops. They are the two-loop graphs with five `gauge` vertices (the
vacuum-polarization insertion among them) and the one-loop vertex graphs with one counterterm
vertex; no counterterm vertex has order `5` (D-37.3), so there is no tree term. The counterterms
`δ₁, δ₂, δ_m, δ₃` are those of `P`; when `e ≠ 0` and they satisfy the order-`e²` conditions
(Z₅), (K₀), (Z₈), they are `e²` times numbers independent of `e`, and then (HV₁) is `e⁵` times a
matrix independent of `e` (obligation O2-27, items 1–2, proved in
`QED/TwoLoop/CountertermScaling.lean`). Source-facing are `ε > 0` and on-shell positive-energy
`p`, `p'`. -/
noncomputable def vertexOrderFive (P : Params) (p' p : Fin 4 → ℝ) (μ : Fin 4) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => (1 / I) *
    (onePIFunction₂ P 1 1 5 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ) -
      onePIFunction₂ P 1 1 4 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ))

end QED.TwoLoop

end
