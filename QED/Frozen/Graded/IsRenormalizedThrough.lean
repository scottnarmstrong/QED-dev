/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsOnShellAt
public import QED.Frozen.Graded.IsChargeNormalizedAt
public import QED.Frozen.Graded.IsPhotonOnShellAt

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (G₁₂) **Renormalized on shell through order `e^{2n}`** (rulings S2′ (D-55 revised), S4; finding
F1 of the design note). `rep f` is the flavour whose conditions fix the counterterms of
flavour `f`; the flavours with `rep f = f` are the ones renormalized on their own mass shell.
The counterterms of levels `k < n` are constant on the classes of `rep`, and for every order
`2j`, `1 ≤ j ≤ n`: each flavour `f` with `rep f = f` is on shell (G₉) and charge normalized
(G₁₀) at that order, and the photon is on shell (G₁₁). The order-`2j` conditions read the level
`j - 1` linearly through the tree counterterm graphs and the lower levels through the loop
graphs. The adopted provisional ruling S2′ (D-55 revised) is `rep = leptonRep` (G₁₂′) on the
lepton flavours (L₁): each physical lepton is on shell at its own mass and its two regulator
fermions carry its counterterms (with their own masses in `d_m · M_f`). The literal per-flavour
scheme (S2 of D-55) is `rep = id`; it is not used, since its counterterm insertions on closed loops
are not integrable contraction by contraction (D-55 revised). -/
def IsRenormalizedThrough (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (n : ℕ) : Prop :=
  (∀ f k, k < n → D.d₁ f k = D.d₁ (rep f) k ∧ D.d₂ f k = D.d₂ (rep f) k ∧
    D.dm f k = D.dm (rep f) k) ∧
  ∀ j, 1 ≤ j → j ≤ n →
    (∀ f, rep f = f → IsOnShellAt P Φ D f j ∧ IsChargeNormalizedAt P Φ D f j) ∧
      IsPhotonOnShellAt P Φ D j

end QED.Graded

end
