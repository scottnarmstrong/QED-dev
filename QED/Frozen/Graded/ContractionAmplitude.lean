/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.Counterterms
public import QED.Frozen.Graded.Flavoring
public import QED.Frozen.Graded.Grading
public import QED.Frozen.Lepton.Flavors
public import QED.Frozen.WickModel.Params
public import QED.Frozen.TwoLoop.PsiMomentum
public import QED.Frozen.TwoLoop.PhotonMomentum
public import QED.Frozen.WickModel.FermionLineTail
public import QED.Frozen.Wick.VertexFactor
public import QED.Frozen.OneLoop.ElectronPropagator
public import QED.Frozen.OneLoop.PhotonPropagator

@[expose] public section

open Complex
open QED.WickModel (Params Contraction FermionLine PhotonLine Line psiMomentum₂ photonMomentum₂)

namespace QED.Graded

open scoped Classical in
/-- (G₃) **The amplitude of a flavoured, graded contraction** `(C, φ, g)` for the line momenta
`k`, the successor of (F₅) (ruling S1). Identical to (F₅) except for the coefficient and mass
lookups of the vertex factors (V₁₉): vertex `t` of level `k` (G₂′) and flavour `f` (G₁) gets
`δ₁ = e^{2(k+1)} d₁ f k`, `δ₂ = e^{2(k+1)} d₂ f k`, `δ_m = e^{2(k+1)} d_m f k`, mass `m = M_f`
(`Φ.mass f`) and `δ₃ = e^{2(k+1)} d₃ k`, with `e = P.e` (ruling S3). An internal fermion line of
flavour `f` carries `(1/i) S̃(k)` of mass `M_f`; a photon line carries `(1/i) D̃(k)` with
`m_γ, Λ, ε` of `P`. Two values are placeholders that (V₁₉) does not read: the level of a `gauge`
vertex (its factor `i e γ^μ` reads no counterterm) is `0`, and the flavour of a `photonCt` vertex
(its factor reads only `δ₃`) is `Φ.openLine`. The fields `δ₁, δ₂, δm, δ₃, m, M₁, M₂, c₁, c₂` of
`P` are not read: counterterms come from `D`, masses and loop weights from `Φ`. -/
noncomputable def contractionAmplitude (P : Params) {F : Type} (Φ : Lepton.Flavors F)
    (D : Counterterms F) {nf nA N : ℕ} {κ : Fin N → Wick.VertexKind} (C : Contraction nf nA κ)
    (φ : Flavoring F κ) (g : Grading κ) (pIn : Fin nf → Fin 4 → ℝ) (kIn : Fin nA → Fin 4 → ℝ)
    (k : Line C → Fin 4 → ℝ) (αOut βIn : Fin nf → Fin 4) (μ : Fin nA → Fin 4) : ℂ :=
  ∑ α : Wick.FermionVertex κ → Fin 4, ∑ β : Wick.FermionVertex κ → Fin 4,
    ∑ lor : Wick.PhotonSlot κ → Fin 4,
      (if (∀ i t, C.1.1 (.inl i) = .inr t → α t = αOut i) ∧
          (∀ t i, C.1.1 (.inr t) = .inl i → β t = βIn i) ∧
          (∀ j a, C.1.2 (.inl j) = .inr a → lor a = μ j) then 1 else 0) *
        ((∏ t, (let lv : ℕ := if h : κ t = .gauge then 0 else g ⟨t, h⟩
            let fl : F := if h : κ t = .photonCt then Φ.openLine else φ ⟨t, h⟩
            let c : ℝ := P.e ^ (2 * (lv + 1))
            Wick.vertexFactor P.e (c * D.d₁ fl lv) (c * D.d₂ fl lv) (c * D.dm fl lv)
              (c * D.d₃ lv) (Φ.mass fl) α β lor (psiMomentum₂ C pIn k)
              (photonMomentum₂ C kIn k) t)) *
          (∏ f : FermionLine C, (1 / I) *
            QED.OneLoop.electronPropagator (Φ.mass (φ f.1)) P.ε (k (.inl f))
              (β f.1) (α f.tail)) *
          ∏ g' : PhotonLine C, (1 / I) *
            QED.OneLoop.photonPropagator P.mγ P.Λ P.ε (k (.inr g')) (lor g'.1) (lor g'.head))

end QED.Graded

end
