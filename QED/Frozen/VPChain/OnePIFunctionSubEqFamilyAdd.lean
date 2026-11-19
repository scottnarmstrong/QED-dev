-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFamilyFunction
public import QED.Frozen.Lepton.OnePIFunction
public import QED.Frozen.VPChain.IsVPChain
public import QED.Provider.VPChain.OnePIFunctionSubEqFamilyAdd

@[expose] public section

open QED.WickModel (Params)
open QED.Lepton (Flavors onePIFunction₂ onePIFamilyFunction₂)

namespace QED.VPChain

/-- (M₂) **The chains are a part of the order-`e^{2n+3}` vertex terms** (obligations O3-3, R1 of
plan section 8.2): the order-exactly-`(2n + 3)` part of the vertex 1PI function (F₈) (its value at
order `2n + 3` minus its value at order `2n + 2`) is the family function (C₂) of the chains (C₁)
plus the family function of the remaining contractions of total order `2n + 3`. Every chain
contraction has total order exactly `2n + 3`, so the chain vertex (C₃) collects some of the terms
of (F₈) at that order, each with its coefficient `1/N!`, its sign and its value, and nothing else.
For `n ≥ 2` the order-`(2n + 3)` part of (F₈) as a whole lies outside the source-facing scope of
(F₈) and is not a renormalized amplitude (D-37.3); only its chain part is source-facing. -/
theorem onePIFunction₂_sub_eq_family_add (n : ℕ) (P : Params) {F : Type} [Fintype F]
    [DecidableEq F] (Φ : Flavors F) (pOut pIn kIn : Fin 1 → Fin 4 → ℝ)
    (αOut βIn μ : Fin 1 → Fin 4) :
    onePIFunction₂ P Φ 1 1 (2 * n + 3) pOut pIn kIn αOut βIn μ -
        onePIFunction₂ P Φ 1 1 (2 * n + 2) pOut pIn kIn αOut βIn μ =
      onePIFamilyFunction₂ P Φ 1 1 (IsVPChain n) (2 * n + 3) pOut pIn kIn αOut βIn μ +
        onePIFamilyFunction₂ P Φ 1 1
          (fun {_} {κ} C => ¬ IsVPChain n C ∧ ∑ t, (κ t).order = 2 * n + 3) (2 * n + 3)
          pOut pIn kIn αOut βIn μ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.VPChain.onePIFunction₂_sub_eq_family_add
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.VPChain

end
-- FROZEN_ANCHOR_SUFFIX_END
