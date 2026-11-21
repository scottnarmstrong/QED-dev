/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelfEnergySelPart
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

open Filter Topology
open QED.WickModel (Params Contraction)

namespace QED.Graded

/-- (Gs₂) **The on-shell conditions for flavour `f` at order `e^{2n}`, for a selected
self-energy** (the text of (G₉) with (Gs₁) in place of (G₈ₛ)): on some region
`p² > -(M_f + r)²`, `r > 0`, the `ε → 0⁺` limit of (Gs₁) has the covariant form
`A(p²) p̸ + B(p²) M_f`, entry by entry, and `Σ(z) = A(-z²) z + B(-z²) M_f` satisfies
`Σ(-M_f) = 0` and `Σ'(-M_f) = 0`. With `Sel C g := IsOnePI C` it is (G₉) (theorem (MS₁)). For a
gauge-invariant family of self-energy graphs together with its level-`(n-1)` tree counterterm
graph, it fixes that family's share of the level-`(n-1)` counterterms `d₂`, `d_m` (the conditions
are affine in them). -/
def IsOnShellSelAt (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F)
    (Sel : ∀ {N : ℕ} {κ : Fin N → Wick.VertexKind}, Contraction 1 0 κ → Grading κ → Prop)
    (f : F) (n : ℕ) : Prop :=
  ∃ r > 0, ∃ A B : ℝ → ℂ,
    (∀ p : Fin 4 → ℝ, -(Φ.mass f + r) ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε : ℝ => selfEnergySelPart { P with ε := ε } Φ D Sel f n p α β) (𝓝[>] 0)
        (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
          + (B (Minkowski.dot p p) * Φ.mass f) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) ∧
    A (-Φ.mass f ^ 2) * ((-Φ.mass f : ℝ) : ℂ) + B (-Φ.mass f ^ 2) * Φ.mass f = 0 ∧
    HasDerivAt (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * Φ.mass f) 0 (-Φ.mass f)

end QED.Graded

end
