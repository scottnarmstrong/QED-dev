/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.VertexPart

@[expose] public section

open Matrix Filter Topology
open QED.WickModel (Params)

namespace QED.Graded

/-- (G₁₀) **The charge condition for flavour `f` at order `e^{2n+1}`** (Srednicki (63.1)–(63.2);
successor of (K₀); ruling S4: a condition on the graded vertex, with the Ward identity
`d₁ = d₂` a theorem, D-37.2): at `q = 0` the order-`(2n+1)` vertex (G₈ᵥ) between on-shell
flavour-`f` spinors tends to `0` as `ε → 0⁺`. For every on-shell positive-energy `p`
(`p² = -M_f²`), every `μ`, every column `u` with `(p̸ + M_f) u = 0` and every row `w` with
`w (p̸ + M_f) = 0`, `w V^{μ,(2n+1)}_ε(p, p) u → 0`. Since the tree vertex `e γ^μ` is the
order-`1` part, this says that the charge `e` is the full vertex at `q = 0`, order by order. At
`n = 1` it is (K₀) at mass `M_f` with `Z₁ = 1 + e² d₁ f 0` (theorem (E-G₂ₖ)). Source-facing for
`M_f > 0` and `n ≥ 1` (at `n = 0` the order-`1` vertex is the tree vertex and the condition
fails). -/
def IsChargeNormalizedAt (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F) (f : F) (n : ℕ) : Prop :=
  ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -Φ.mass f ^ 2 → 0 < p 0 → ∀ (μ : Fin 4)
    (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((Φ.mass f : ℂ) • u) →
    w ᵥ* Dirac.slash p = -((Φ.mass f : ℂ) • w) →
    Tendsto (fun ε : ℝ => w ⬝ᵥ (vertexPart { P with ε := ε } Φ D f n p p μ *ᵥ u)) (𝓝[>] 0)
      (𝓝 0)

end QED.Graded

end
