-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.ThreeLoop.IsVPShareOnShell
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Provider.ThreeLoop.ExistsUniqueIsVPShareOnShell

@[expose] public section

open QED.WickModel (Params)

namespace QED.ThreeLoop

/-- (G-ex-s) **The VP share exists and is unique** (`SETC-KERNEL-PLAN.md` (G₁₄); the analogue of
(G-ex₂) for one family). Under the hypotheses of (G-ex₂) (common lower mass bound, positive photon
regulators, Pauli–Villars blocks of the scheme `rep`, `D` renormalized through order `e²`), with
`e ≠ 0`, there is exactly one triple `s` satisfying (Sc₂). The conditions are affine in `s` with the
invertible tree coefficients of (G-ex₂); the analytic inputs are the `ε → 0⁺` limit of the
one-loop self-energy with a bubble or level-`0` `δ₃` on its photon, with its covariant form near
the open-line shell and the differentiability of its `Σ` at `z = -M`, and the `ε → 0⁺` limit of
the one-insertion chain vertex at `q = 0` on shell (the vacuum-polarization class of the
order-`e⁵` vertex). -/
theorem existsUnique_isVPShareOnShell (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Graded.Counterterms F) (rep : F → F) (m₀ : ℝ) (he : P.e ≠ 0)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : Graded.IsRenormalizedThrough P Φ D rep 1) :
    ∃! s : ℝ × ℝ × ℝ, IsVPShareOnShell P Φ D s :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.ThreeLoop.existsUnique_isVPShareOnShell
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.ThreeLoop

end
-- FROZEN_ANCHOR_SUFFIX_END
