/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.OneLoop.VertexFunction

@[expose] public section

open Matrix Complex

namespace QED.OneLoop

/-- (K₀) The charge condition of the primary source's (63.1)–(63.2), which defines the charge
`e`: on shell with `q² = 0`, which for positive-energy momenta forces `p' = p` (p. 379),
`ū V^μ(p, p) u = e ū γ^μ u` for every on-shell positive-energy `p`, every `μ`, every column `u`
with `(p̸ + m) u = 0`, and every row `ū` with `ū (p̸ + m) = 0`. These solution spaces are spanned
by `u_s(p)` and `ū_{s'}(p)` ((38.1), (38.16)), so this is (63.1) for all spins `s, s'`. For
`s' ≠ s` the right-hand side vanishes, as noted after (63.2), so the condition asks the left-hand
side to vanish too; (63.2) keeps only `s' = s`. -/
def IsChargeNormalized (e Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) : Prop :=
  ∀ (p : Fin 4 → ℝ) (hp : Minkowski.dot p p = -m ^ 2) (hp0 : 0 < p 0) (μ : Fin 4)
    (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((m : ℂ) • u) →
    w ᵥ* Dirac.slash p = -((m : ℂ) • w) →
    w ⬝ᵥ (vertexFunction e Z₁ m mγ Λ hm hmγ hΛ p p hp hp hp0 hp0 μ *ᵥ u)
      = (e : ℂ) * (w ⬝ᵥ (Dirac.gamma μ *ᵥ u))

end QED.OneLoop

end
