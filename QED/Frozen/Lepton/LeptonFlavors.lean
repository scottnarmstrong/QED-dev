/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.Flavors
public import QED.Frozen.Lepton.HeavyLepton
public import QED.Frozen.WickModel.ParamsMass
public import QED.Frozen.WickModel.ParamsLoopCoeff

@[expose] public section

open QED.WickModel (Params)

namespace QED.Lepton

/-- (L₁) **The flavours of the multi-lepton model** (decision D-49.4): the electron block
`inl i`, with T1's masses `![m, M₁, M₂]` (X₀′) and coefficients `![1, c₁, c₂]` (X₀″) read from
`P`, and for each heavy lepton `ℓ` the block `inr (ℓ, i)`, with masses
`![m_ℓ, M_{ℓ,1}, M_{ℓ,2}]` and coefficients `![1, c_{ℓ,1}, c_{ℓ,2}]`. The open line is the
electron, `inl 0`, of mass `P.m`. With `n = 0` this is T1's flavour set up to the relabelling
`Fin 3 ⊕ Fin 0 × Fin 3 ≃ Fin 3` (theorem (E₃)). -/
def leptonFlavors (P : Params) {n : ℕ} (H : Fin n → HeavyLepton) :
    Flavors (Fin 3 ⊕ Fin n × Fin 3) where
  mass := Sum.elim P.mass fun x => ![(H x.1).m, (H x.1).M₁, (H x.1).M₂] x.2
  coeff := Sum.elim P.loopCoeff fun x => ![1, (H x.1).c₁, (H x.1).c₂] x.2
  openLine := .inl 0

end QED.Lepton

end
