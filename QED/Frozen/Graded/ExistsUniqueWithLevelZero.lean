-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.CountertermsWithLevel
public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Provider.Graded.ExistsUniqueWithLevelZero

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (G-ex₁) **The order-`e²` conditions fix the level-`0` counterterms** (memo (G-ex₁); the
graded successor of (Z₆), (Z₉) and (K)). Let `e ≠ 0`, every flavour mass and `m_γ, Λ` be
positive, the flavour coefficients satisfy the two Pauli–Villars conditions `∑_f c_f = 0`,
`∑_f c_f M_f² = 0` (D-22; they make the one-loop flavour-summed bubble integrable), and let `rep`
be idempotent. Then there is exactly one choice of level-`0` data, `x f = (d₁, d₂, d_m)` for every
flavour and `y = d₃`, such that `D` with that level is renormalized through order `e²` (G₁₂). The
other levels of `D` play no role ((G-loc)). By (E-G₂ₛ), (E-G₂ₖ) and (E-G₂ₚ) the solution is, for
each flavour with `rep f = f`, the frozen (Z₆) and (K) solutions at mass `M_f` divided by `e²`, and
the (F₁₁) solution divided by `e²`. Holds for every `rep`: for the adopted ruling S2′
(`leptonRep`, D-55 revised) and for the literal per-flavour scheme (`rep = id`). -/
theorem existsUnique_withLevel_zero (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (he : P.e ≠ 0)
    (hmass : ∀ f, 0 < Φ.mass f) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f) (hPV₁ : ∑ f, Φ.coeff f = 0)
    (hPV₂ : ∑ f, Φ.coeff f * Φ.mass f ^ 2 = 0) :
    ∃! x : (F → ℝ × ℝ × ℝ) × ℝ, IsRenormalizedThrough P Φ (D.withLevel 0 x.1 x.2) rep 1 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.existsUnique_withLevel_zero
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
