/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelectedPart
public import QED.Frozen.WickModel.ExternalsAttached
public import QED.Frozen.WickModel.VerticesConnected

@[expose] public section

open QED.WickModel (Params ExternalsAttached VerticesConnected)

namespace QED.Graded

/-- (G₆″) **The order-`K` part of the connected function of the graded model**, the successor of
(X₂₉) (decision D-23.1): (G₆) over the contractions whose externals are attached (X₁₆) and whose
vertices are connected (X₁₇). It is amputated by the free external propagators and keeps the
corrections on the external legs, as (X₂₉) does; it is the input of the LSZ amplitude (G-L₁). -/
noncomputable def connectedPart (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  selectedPart P Φ D nf nA (fun C _ => ExternalsAttached C ∧ VerticesConnected C) K pOut pIn kIn
    αOut βIn μ

end QED.Graded

end
