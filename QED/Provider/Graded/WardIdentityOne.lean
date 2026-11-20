/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsOnShellAt
public import QED.Frozen.Graded.IsChargeNormalizedAt
public import QED.GradedProof.WI2Final

/-!
# Provider for `QED.Graded.d₁_eq_d₂_one`

Proves the frozen theorem goal `QED.Graded.d₁_eq_d₂_one` (Phase 5 Stage 2 packet, decision D-57)
as `QED.Provider.Graded.d₁_eq_d₂_one`, with the binder convention of decision D-13, from
`QED.GradedProof.WI2.d₁_eq_d₂_one'`. This module must never import the frozen anchor.
-/

@[expose] public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.Provider.Graded

/-- (WI₂), with implicit data binders and `by assumption` hypotheses (decision D-13). The
hypotheses are found at reducible transparency: the context holds `IsOnShellAt` and
`IsChargeNormalizedAt` at both orders `1` and `2`, and a default-transparency `assumption` would
unfold them while trying the wrong ones. -/
theorem d₁_eq_d₂_one {P : Params} {F : Type} [Fintype F] [DecidableEq F]
    {Φ : Lepton.Flavors F} {D : Counterterms F} {f : F}
    (he : P.e ≠ 0 := by with_reducible assumption)
    (hmass : ∀ g, 0 < Φ.mass g := by with_reducible assumption)
    (hmγ : 0 < P.mγ := by with_reducible assumption)
    (hΛ : 0 < P.Λ := by with_reducible assumption)
    (hPV₁ : ∑ g, Φ.coeff g = 0 := by with_reducible assumption)
    (hPV₂ : ∑ g, Φ.coeff g * Φ.mass g ^ 2 = 0 := by with_reducible assumption)
    (hon₁ : IsOnShellAt P Φ D f 1 := by with_reducible assumption)
    (hK₁ : IsChargeNormalizedAt P Φ D f 1 := by with_reducible assumption)
    (hon₂ : IsOnShellAt P Φ D f 2 := by with_reducible assumption)
    (hK₂ : IsChargeNormalizedAt P Φ D f 2 := by with_reducible assumption) :
    D.d₁ f 1 = D.d₂ f 1 :=
  QED.GradedProof.WI2.d₁_eq_d₂_one' P Φ D f he hmass hmγ hΛ hPV₁ hPV₂ hon₁ hK₁ hon₂ hK₂

end QED.Provider.Graded

end
