/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.FamilyVertex

@[expose] public section

open Matrix Filter Topology
open QED.WickModel (Params Contraction)

namespace QED.Graded

/-- (Gs₃) **The charge condition for flavour `f` at order `e^{2n+1}`, for a selected vertex**
(the text of (G₁₀) with the family vertex (Gf₁) at the flavour `f` in place of (G₈ᵥ)): at `q = 0`
the order-`(2n+1)` selected vertex between on-shell flavour-`f` spinors tends to `0` as
`ε → 0⁺`. With `Sel C g := IsOnePI C` it is (G₁₀) (theorem (MS₂)). For a gauge-invariant family of
vertex graphs together with its level-`(n-1)` tree counterterm graph, it fixes that family's share
of the level-`(n-1)` counterterm `d₁`. -/
def IsChargeNormalizedSelAt (P : Params) {F : Type} [Fintype F] [DecidableEq F]
    (Φ : Lepton.Flavors F) (D : Counterterms F)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 1 κ → Grading κ → Prop)
    (f : F) (n : ℕ) : Prop :=
  ∀ p : Fin 4 → ℝ, Minkowski.dot p p = -Φ.mass f ^ 2 → 0 < p 0 → ∀ (μ : Fin 4)
    (u w : Fin 4 → ℂ), Dirac.slash p *ᵥ u = -((Φ.mass f : ℂ) • u) →
    w ᵥ* Dirac.slash p = -((Φ.mass f : ℂ) • w) →
    Tendsto (fun ε : ℝ =>
        w ⬝ᵥ (familyVertex { P with ε := ε } { Φ with openLine := f } D Sel (2 * n + 1) p p μ *ᵥ
          u)) (𝓝[>] 0) (𝓝 0)

end QED.Graded

end
