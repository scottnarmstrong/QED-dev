/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFunction

@[expose] public section

open Complex
open QED.WickModel (Params)

namespace QED.Lepton

/-- (F₉) **The order-`e⁵` 1PI vertex at fixed `ε` with the flavours `Φ`**, the successor of
(HV₁): `(1/i)` times the part of total order exactly `5` of (F₈) with one external fermion pair
(of flavour `Φ.openLine`) and one external photon, at outgoing momentum `p'`, incoming momentum
`p` and incoming photon momentum `p' - p`; the row index is outgoing, the column index incoming.
An order-`5` term has at most one closed fermion loop, with two gauge vertices (the one-loop
vacuum polarization inserted in the one-loop vertex) or three (the Furry graphs, with the
external photon on the loop), so each flavour enters only through such a loop. -/
noncomputable def vertexOrderFive (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F)
    (p' p : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => (1 / I) *
    (onePIFunction₂ P Φ 1 1 5 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ) -
      onePIFunction₂ P Φ 1 1 4 (fun _ => p') (fun _ => p) (fun _ => p' - p) (fun _ => i)
        (fun _ => j) (fun _ => μ))

end QED.Lepton

end
