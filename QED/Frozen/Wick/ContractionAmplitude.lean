/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Wick.PsiMomentum
public import QED.Frozen.Wick.PhotonMomentum
public import QED.Frozen.Wick.VertexFactor
public import QED.Frozen.OneLoop.ElectronPropagator
public import QED.Frozen.OneLoop.PhotonPropagator
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Option
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Perm

@[expose] public section

open Complex

namespace QED.Wick

open scoped Classical in
/-- (V₂₀) The amplitude of a contraction at loop momentum `ℓ`, for outgoing spinor index `αe`,
incoming spinor index `βe` and photon index `μ`: the sum over the spinor and Lorentz indices of
all vertex fields of the product of the vertex factors (V₁₉), a factor `(1/i) S̃(k)` for each
internal fermion line (the propagator `⟨Ψ Ψ̄⟩`, (58.19)) and `(1/i) Δ̃(k)` for each internal photon
line (decision D-5), with the line momenta of the routing (V₁₆). The external propagators are
amputated: the `Ψ̄` contracted with `Ψ(x)` carries the index `αe`, the `Ψ` contracted with
`Ψ̄(y)` carries `βe`, and the photon field contracted with `A(z)` carries `μ` (rule 10). Only
`ε > 0` is source-facing. -/
noncomputable def contractionAmplitude (e δ₁ δ₂ δm δ₃ m mγ Λ ε : ℝ) {N : ℕ} {κ : Fin N → VertexKind}
    (C : Contraction κ) (p' p ℓ : Fin 4 → ℝ) (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun αe βe => ∑ α : FermionVertex κ → Fin 4, ∑ β : FermionVertex κ → Fin 4,
    ∑ lor : PhotonSlot κ → Fin 4,
      (if (∀ j, C.1.1 none = some j → α j = αe) ∧ (∀ t, C.1.1 (some t) = none → β t = βe) ∧
          (∀ a, C.1.2 none = some a → lor a = μ) then 1 else 0) *
        ((∏ t, vertexFactor e δ₁ δ₂ δm δ₃ m α β lor (psiMomentum C p' p ℓ)
            (photonMomentum C p' p ℓ) t) *
          (∏ f : FermionLine C, (1 / I) *
            QED.OneLoop.electronPropagator m ε (lineMomentum C p' p ℓ (.inl f)) (β f.1)
              (α ((C.1.1 (some f.1)).get (Option.ne_none_iff_isSome.mp f.2)))) *
          ∏ g : PhotonLine C, (1 / I) *
            QED.OneLoop.photonPropagator mγ Λ ε (lineMomentum C p' p ℓ (.inr g)) (lor g.1)
              (lor ((C.1.2 (some g.1)).get
                (Option.isSome_iff_exists.mpr (g.2.imp fun _ h => h.1)))))

end QED.Wick

end
