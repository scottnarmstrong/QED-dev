-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsVPShareOnShell
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Provider.ThreeLoop.IsVPShareOnShellWardIdentity

@[expose] public section

open QED.WickModel (Params)

namespace QED.ThreeLoop

/-- (WI-s) **The Ward identity for the VP share** (the analogue of (WI₂) for one family; plan
section 4 (c)): under the hypotheses of (G-ex-s), every VP share has `d₁ˢ = d₂ˢ`. It is the
one-loop Ward identity at a massive photon, integrated against the bubble's spectral weight, with
the `δ₃` partner graphs. It is what makes the longitudinal part of the inserted bubble cancel
in the set (c) sum (question Q-c3). -/
theorem isVPShareOnShell_d₁_eq_d₂ (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (m₀ : ℝ) (he : P.e ≠ 0)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : Graded.IsRenormalizedThrough P Φ D rep 1) (s : ℝ × ℝ × ℝ)
    (hs : IsVPShareOnShell P Φ D s) : s.1 = s.2.1 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.ThreeLoop.isVPShareOnShell_d₁_eq_d₂
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
