-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.IsRenormalizedThrough
public import QED.Frozen.Graded.IsLSZAmplitudePart
public import QED.Provider.Graded.IsLSZAmplitudePartFiveSelf

@[expose] public section

open QED.WickModel (Params)

namespace QED.Graded

/-- (X₁) **Exit test, charge: the order-`e⁵` LSZ amplitude vanishes at `q = 0`** (ruling S8; the
two-loop part of (L₄′) and (63.1)–(63.2)). Under the hypotheses of (G-Π₂), with the open-line
flavour renormalized on its own shell (`rep` fixes it) and `D` renormalized through order `e⁴`:
at every on-shell positive-energy `p`, the order-`5` LSZ amplitude (G-L₁) at `(p, p)` exists and
is `0`. So the charge is not renormalized at two loops in the LSZ form. Every order-`e⁴`
condition of the open-line flavour is exercised: the leg corrections vanish only by the on-shell
conditions at orders `e²` and `e⁴` (order-`e⁴` residue one), the vertex at `q = 0` only by the
charge conditions; the photon-leg terms carry `q² D(q²) Π(q²) → 0` as `q → 0` at `m_γ > 0`. -/
theorem isLSZAmplitudePart_five_self (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (rep : F → F) (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hmass : ∀ g, m₀ ≤ Φ.mass g) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hrep : ∀ f, rep (rep f) = rep f)
    (hPV₁ : ∀ b, rep b = b → ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f = 0)
    (hPV₂ : ∀ b, rep b = b →
      ∑ f ∈ Finset.univ.filter (fun f => rep f = b), Φ.coeff f * Φ.mass f ^ 2 = 0)
    (hopen : rep Φ.openLine = Φ.openLine) (hD : IsRenormalizedThrough P Φ D rep 2)
    (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -Φ.mass Φ.openLine ^ 2) (hp0 : 0 < p 0) :
    (∃ M, IsLSZAmplitudePart P Φ D 5 p p M) ∧ ∀ M, IsLSZAmplitudePart P Φ D 5 p p M → M = 0 :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.Graded.isLSZAmplitudePart_five_self
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.Graded

end
-- FROZEN_ANCHOR_SUFFIX_END
