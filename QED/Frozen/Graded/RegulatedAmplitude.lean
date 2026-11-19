/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.Preserves
public import QED.Frozen.Graded.LoopWeight
public import QED.Frozen.Graded.ContractionAmplitude

@[expose] public section

open QED.WickModel (Params Contraction Line)

namespace QED.Graded

open scoped Classical in
/-- (G₄) **The regulated amplitude of a graded contraction**, the successor of (F₆): the sum,
over the flavourings `φ` (G₁) that `C` preserves (G₁″), of the weight (G₁‴) times the amplitude
(G₃). All flavours of one contraction are summed inside one loop integrand, so each closed loop is
Pauli–Villars summed with its weights (D-22, D-49.4), counterterm vertices on it included. -/
noncomputable def regulatedAmplitude (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (g : Grading κ) (pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) : ℂ :=
  ∑ φ ∈ (Finset.univ : Finset (Flavoring F κ)).filter (Preserves Φ C),
    (loopWeight Φ C φ : ℂ) * contractionAmplitude P Φ D C φ g pIn kIn k αOut βIn μ

end QED.Graded

end
