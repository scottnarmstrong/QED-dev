/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.TwoLoop.PsiMomentum
public import QED.Frozen.TwoLoop.PhotonMomentum
public import QED.Frozen.Lepton.Flavoring
public import QED.Frozen.WickModel.Params
public import QED.Frozen.WickModel.LineEnds
public import QED.Frozen.Wick.VertexFactor
public import QED.Frozen.OneLoop.ElectronPropagator
public import QED.Frozen.OneLoop.PhotonPropagator

@[expose] public section

open Complex
open QED.WickModel (Params Contraction FermionLine PhotonLine Line psiMomentum₂ photonMomentum₂)

namespace QED.Lepton

open scoped Classical in
/-- (F₅) The amplitude of the flavoured contraction `(C, φ)` for the line momenta `k`, the
successor of (T₇): identical to (T₇) except that an internal fermion line of flavour `f` carries
the propagator `(1/i) S̃(k)` of mass `Φ.mass f`. The vertex factors (V₁₉) read `e` and the
counterterms `δ₁, δ₂, δ_m, δ₃` and the mass `m` of the `δ_m` vertex from `P`; the photon
propagator reads `m_γ, Λ, ε` from `P`. The fields `M₁, M₂, c₁, c₂` of `P` are not read: the
flavours are given by `Φ`. Since the `δ_m` vertex uses `P.m` while the open-line propagators use
`Φ.mass Φ.openLine`, the amplitude is meaningful only when `Φ.mass Φ.openLine = P.m`. -/
noncomputable def contractionAmplitude₂ (P : Params) {F : Type} (Φ : Flavors F) {nf nA N : ℕ}
    {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ) (φ : Flavoring Φ κ)
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
            QED.OneLoop.electronPropagator (Φ.mass (φ.1 f.1)) P.ε (k (.inl f))
              (β f.1) (α f.tail)) *
          ∏ g : PhotonLine C, (1 / I) *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr g)) (lor g.1) (lor g.head))

end QED.Lepton

end
