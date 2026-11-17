/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.PsiMomentum
public import QED.Frozen.TwoLoop.PhotonMomentum
public import QED.Frozen.WickModel.Flavoring
public import QED.Frozen.WickModel.ParamsMass
public import QED.Frozen.WickModel.LineEnds
public import QED.Frozen.Wick.VertexFactor
public import QED.Frozen.OneLoop.ElectronPropagator
public import QED.Frozen.OneLoop.PhotonPropagator
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open Complex

namespace QED.WickModel

open scoped Classical in
/-- (T₇) The amplitude of the flavored contraction `(C, φ)` for the line momenta `k`: (X₂₅) with
the momentum of each internal line `f` given by `k f` instead of the one-loop routing (X₂₂), and
the vertex momenta (T₅), (T₆). Everything else is as in (X₂₅): packet 5's vertex factors (V₁₉),
`(1/i) S̃(k)` of mass `P.mass f` for each internal fermion line of flavor `f` (decision D-22),
`(1/i) Δ̃(k)` for each internal photon line (D-5), amputated external propagators, and the sum over
the spinor and Lorentz indices of the vertex fields constrained by the external indices. With
`k = lineMomentum C pOut pIn kIn ℓ` it is (X₂₅). -/
noncomputable def contractionAmplitude₂ (P : Params) {nf nA N : ℕ}
    {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (φ : Flavoring κ)
    (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ) (k : Line C → Fin 4 → ℝ)
    (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ α : Wick.FermionVertex κ → Fin 4, ∑ β : Wick.FermionVertex κ → Fin 4,
    ∑ lor : Wick.PhotonSlot κ → Fin 4,
      (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
          (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
          (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
        ((∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
            (psiMomentum₂ C pIn k) (photonMomentum₂ C kIn k) t) *
          (∏ f : FermionLine C, (1 / I) *
            QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε (k (.inl f))
              (β f.1) (α f.tail)) *
          ∏ g : PhotonLine C, (1 / I) *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr g)) (lor g.1) (lor g.head))

end QED.WickModel

end
