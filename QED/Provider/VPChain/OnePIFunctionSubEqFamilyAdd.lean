/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Lepton.OnePIFamilyFunction
public import QED.Frozen.Lepton.OnePIFunction
public import QED.Frozen.VPChain.IsVPChain
import QED.ChainProof.QuickMeaning

/-!
# Provider for `QED.VPChain.onePIFunction₂_sub_eq_family_add`

Proves the frozen theorem goal `QED.VPChain.onePIFunction₂_sub_eq_family_add` (Phase 5 Stage 1a
packet, decision D-53) as `QED.Provider.VPChain.onePIFunction₂_sub_eq_family_add`, with the binder
convention of decision D-13, from the helper in `QED.ChainProof.QuickMeaning`. This module must
never import the frozen anchor.
-/

public section

open QED.WickModel (Params)
open QED.Lepton (Flavors onePIFunction₂ onePIFamilyFunction₂)

namespace QED.Provider.VPChain

open QED.VPChain

/-- The frozen goal with implicit data binders and `by assumption` hypotheses (decision D-13). -/
theorem onePIFunction₂_sub_eq_family_add {n : ℕ} {P : Params} {F : Type} [Fintype F]
    [DecidableEq F] {Φ : Flavors F} {pOut pIn kIn : Fin 1 → Fin 4 → ℝ}
    {αOut βIn μ : Fin 1 → Fin 4} :
    onePIFunction₂ P Φ 1 1 (2 * n + 3) pOut pIn kIn αOut βIn μ -
        onePIFunction₂ P Φ 1 1 (2 * n + 2) pOut pIn kIn αOut βIn μ =
      onePIFamilyFunction₂ P Φ 1 1 (IsVPChain n) (2 * n + 3) pOut pIn kIn αOut βIn μ +
        onePIFamilyFunction₂ P Φ 1 1
          (fun {_} {κ} C => ¬ IsVPChain n C ∧ ∑ t, (κ t).order = 2 * n + 3) (2 * n + 3)
          pOut pIn kIn αOut βIn μ :=
  QED.ChainProof.onePIFunction₂_sub_eq_family_add' n P Φ pOut pIn kIn αOut βIn μ

end QED.Provider.VPChain

end
