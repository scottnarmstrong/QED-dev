/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.PsiMomentum
public import QED.Frozen.WickModel.PhotonMomentum
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
/-- (X₂₅) The amplitude of the flavored contraction `(C, φ)` at loop momentum `ℓ`, for the spinor
indices `αOut i` (of the `Ψ̄` contracted with `Ψ(xᵢ)`) and `βIn i` (of the `Ψ` contracted with
`Ψ̄(yᵢ)`) and the Lorentz indices `μ j` (of the photon field contracted with `A(zⱼ)`): the sum
over the spinor and Lorentz indices of all vertex fields, constrained by these external indices,
of the product of packet 5's vertex factors (V₁₉) (the gauge vertex is `i e γ^μ` for every
flavor), a factor `(1/i) S̃(k)` of mass `P.mass f` (`m` for `f = 0`) for each internal fermion
line of flavor `f` (the propagator `⟨Ψ_f Ψ̄_f⟩`, (58.19); decision D-22) and `(1/i) Δ̃(k)` for
each internal photon line (decision D-5), with the line momenta of the routing (X₂₂). The
external propagators are amputated (rule 10). The sum over the indices along a closed fermion
loop is its spinor trace. Only `ε > 0`, flavorings preserved by `σ` (X₄), and contractions whose
externals are attached (X₁₆) are source-facing. -/
noncomputable def contractionAmplitude (P : Params) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind}
    (C : Contraction nf nA κ) (φ : Flavoring κ) (pOut pIn : Fin nf → Fin 4 → ℝ)
    (kIn : Fin nA → Fin 4 → ℝ) (ℓ : Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4)
    (μ : Fin nA → Fin 4) : ℂ :=
  ∑ α : Wick.FermionVertex κ → Fin 4, ∑ β : Wick.FermionVertex κ → Fin 4,
    ∑ lor : Wick.PhotonSlot κ → Fin 4,
      (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
          (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
          (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
        ((∏ t, Wick.vertexFactor P.e P.δ₁ P.δ₂ P.δm P.δ₃ P.m α β lor
            (psiMomentum C pOut pIn kIn ℓ) (photonMomentum C pOut pIn kIn ℓ) t) *
          (∏ f : FermionLine C, (1 / I) *
            QED.OneLoop.electronPropagator (P.mass (φ.1 f.1)) P.ε
              (lineMomentum C pOut pIn kIn ℓ (.inl f)) (β f.1) (α f.tail)) *
          ∏ g : PhotonLine C, (1 / I) *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (lineMomentum C pOut pIn kIn ℓ (.inr g))
              (lor g.1) (lor g.head))

end QED.WickModel

end
