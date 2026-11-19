-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.CountertermsWithLevel
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Provider.Graded.ExistsUniqueWithLevelOne

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (G-ex₂) **The order-`e⁴` conditions fix the level-`1` counterterms** (memo (G-ex₂); plan
Q5 (ii)). Under the hypotheses of (G-Π₂) on the scheme `rep`, with `e ≠ 0`: if `D` is renormalized
through order `e²` (G₁₂), then there is exactly one choice of level-`1` data `x f = (d₁, d₂, d_m)`,
`y = d₃` such that `D` with that level is renormalized through order `e⁴`. The order-`e⁴`
conditions are affine in the level-`1` data, whose tree graphs have invertible coefficients for
`e ≠ 0` (the generic algebraic step of ruling S10, a planned helper); the analytic inputs are
(G-Σ₂) (the covariant limit near each physical shell and the differentiability of `Σ` at
`z = -M_f`, its third clause), (G-Π₂), and the existence of the `ε → 0⁺` limit of the order-`e⁵`
vertex at `q = 0` on shell. The levels `≥ 2` play no role ((G-loc)). -/
theorem existsUnique_withLevel_one (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ) (he : P.e ≠ 0)
    (hm₀ : 0 < m₀) (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hD : IsRenormalizedThrough P Φ D rep 1) :
    ∃! x : (F → ℝ × ℝ × ℝ) × ℝ, IsRenormalizedThrough P Φ (D.withLevel 1 x.1 x.2) rep 2 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.existsUnique_withLevel_one
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
