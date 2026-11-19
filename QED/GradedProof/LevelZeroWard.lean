/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsOnShellAt
public import QED.Frozen.Graded.IsChargeNormalizedAt
public import QED.GradedProof.LevelOneElectron
public import QED.GradedProof.LevelOneCharge
import QED.Frozen.TwoLoop.WardIdentity
import QED.TwoLoop.CountertermScaling

/-!
# The one-loop Ward identity of the graded model

Helper proof of the Phase 5 Stage 2 goal (WI₁′) `QED.Graded.d₁_eq_d₂_zero` (decision D-57), as
`QED.GradedProof.d₁_eq_d₂_zero'`. By (E-G₂ₛ) and (E-G₂ₖ) the order-`e²` conditions of flavour `f`
are T1's (Z₅) and (K₀) at mass `M_f` with `δ₂ = e² d₂ f 0`, `δ_m = e² d_m f 0`,
`Z₁ = 1 + e² d₁ f 0`; the sealed (WI₁) at these parameters (with `δ₁ = e² d₁ f 0`, which (Z₅)
does not read: `QED.TwoLoop.Scaling.isElectronOnShell_iff`) gives `e² d₁ f 0 = e² d₂ f 0`.
-/

@[expose] public section

open QED.WickModel (Params)
open QED.Graded

namespace QED.GradedProof

/-- (WI₁′) **The one-loop Ward identity for flavour `f`**: `d₁ f 0 = d₂ f 0`. -/
theorem d₁_eq_d₂_zero' (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (he : P.e ≠ 0) (hf : 0 < Φ.mass f)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hon : IsOnShellAt P Φ D f 1)
    (hK : IsChargeNormalizedAt P Φ D f 1) :
    D.d₁ f 0 = D.d₂ f 0 := by
  have h1 := (isOnShellAt_one_iff' P Φ D f hf hmγ hΛ).1 hon
  have h2 := (isChargeNormalizedAt_one_iff' P Φ D f hf hmγ hΛ).1 hK
  let a₁ := P.e ^ 2 * D.d₁ f 0
  let a₂ := P.e ^ 2 * D.d₂ f 0
  let a₃ := P.e ^ 2 * D.dm f 0
  let Q : Params := { P with m := Φ.mass f, δ₁ := a₁, δ₂ := a₂, δm := a₃ }
  let Q' : Params := { P with m := Φ.mass f, δ₂ := a₂, δm := a₃ }
  have hon' : QED.WickModel.IsElectronOnShell Q hf hmγ hΛ :=
    (QED.TwoLoop.Scaling.isElectronOnShell_iff Q hf hmγ hΛ).2
      ((QED.TwoLoop.Scaling.isElectronOnShell_iff Q' hf hmγ hΛ).1 h1)
  have h := QED.WickModel.δ₁_eq_δ₂ Q he hf hmγ hΛ hon' h2
  exact mul_left_cancel₀ (pow_ne_zero 2 he) h

end QED.GradedProof

end
