/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelectedPart
public import QED.Frozen.WickModel.IsOnePI

@[expose] public section

open QED.WickModel (Params IsOnePI)

namespace QED.Graded

/-- (G₆′) **The order-`K` part of the 1PI function of the graded model**: (G₆) over the 1PI
contractions (X₁₈). With level-`0` counterterms only and `nf ≥ 1`, `K ≤ 2 nf + nA + 3`, it is the
order-exactly-`K` part of (F₈) (theorem (E-G₁)). -/
noncomputable def onePIPart (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (nf nA K : ℕ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  selectedPart P Φ D nf nA (fun C _ => IsOnePI C) K pOut pIn kIn αOut βIn μ

end QED.Graded

end
