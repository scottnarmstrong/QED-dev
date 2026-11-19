/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.OnePIPart

@[expose] public section

open Complex
open QED.WickModel (Params)

namespace QED.Graded

/-- (G₈ᵥ) **The order-`e^{2n+1}` vertex of flavour `f` at fixed `ε`** (Srednicki (62.39), (G₆′);
successor of (F₉)): `(1/i)` times the order-`(2n+1)` part of the 1PI function with one external
fermion pair of flavour `f` and one external photon, at outgoing momentum `p'`, incoming momentum
`p` and incoming photon momentum `p' - p`; the row index is outgoing, the column index incoming.
At `n = 0` it is the tree vertex `e γ^μ`; for `n ≥ 1` it contains the tree term
`e^{2n} d₁ f (n-1) e γ^μ` of the level-`(n-1)` vertex counterterm. -/
noncomputable def vertexPart (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (n : ℕ) (p' p : Fin 4 → ℝ)
    (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => (1 / I) *
    onePIPart P { Φ with openLine := f } D 1 1 (2 * n + 1) (fun _ => p') (fun _ => p)
      (fun _ => p' - p) (fun _ => i) (fun _ => j) (fun _ => μ)

end QED.Graded

end
