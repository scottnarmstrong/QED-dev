/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.ContractionAmplitude
public import QED.Frozen.Lepton.Preserves
public import QED.Frozen.Lepton.LoopWeight

@[expose] public section

open QED.WickModel (Params Contraction Line)

namespace QED.Lepton

open scoped Classical in
/-- (F₆) The Pauli–Villars regulated amplitude for the line momenta `k`, the successor of (T₈):
the sum, over the flavourings `φ` that `C` preserves (F₃), of the weight (F₄) times the amplitude
(F₅). All flavours of one contraction are summed inside one loop integrand. -/
noncomputable def regulatedAmplitude₂ (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Flavors F)
    {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ φ ∈ (Finset.univ : Finset (Flavoring Φ κ)).filter (Preserves Φ C),
    (loopWeight Φ C φ : ℂ) * contractionAmplitude₂ P Φ C φ pIn kIn k αOut βIn μ

end QED.Lepton

end
