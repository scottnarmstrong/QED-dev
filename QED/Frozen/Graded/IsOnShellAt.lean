/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Graded.SelfEnergyPart
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

open Filter Topology
open QED.WickModel (Params)

namespace QED.Graded

/-- (G₉) **The on-shell conditions for flavour `f` at order `e^{2n}`** (Srednicki (62.27),
(62.36)–(62.38); successor of (Z₅) in limit form, decision D-25; rulings S2′ (D-55 revised), S10).
With `M = M_f`: on some region `p² > -(M + r)²`, `r > 0`, around the mass shell, the `ε → 0⁺` limit
of the order-`2n` self-energy (G₈ₛ) has the covariant form `A(p²) p̸ + B(p²) M`, entry by entry; and
the function `Σ(z) = A(-z²) z + B(-z²) M` of (Z₄) (`p̸` replaced by its eigenvalue `z`, `p² = -z²`)
satisfies `Σ(-M) = 0` and `Σ'(-M) = 0`. The full self-energy is `∑_n Σ^{(2n)}`, so these are the
on-shell conditions order by order. The form factors are not chosen: for `M > 0` the region contains
`-z²` for `z` near `-M`, and there `A`, `B` are fixed by the limits (every `s` is `p²` for some
`p ≠ 0`, and `p̸`, `1` are independent), so the two conditions do not depend on the choice of `A`,
`B` off the region or of `r`. At `n = 1` this is (Z₅) at mass `M`, with `δ₂ = e² d₂ f 0`,
`δ_m = e² d_m f 0` (theorem (E-G₂ₛ)). Source-facing for `M_f > 0` and `n ≥ 1`. -/
def IsOnShellAt (P : Params) {F : Type} [Fintype F] [DecidableEq F] (Φ : Lepton.Flavors F)
    (D : Counterterms F) (f : F) (n : ℕ) : Prop :=
  ∃ r > 0, ∃ A B : ℝ → ℂ,
    (∀ p : Fin 4 → ℝ, -(Φ.mass f + r) ^ 2 < Minkowski.dot p p → ∀ α β : Fin 4,
      Tendsto (fun ε : ℝ => selfEnergyPart { P with ε := ε } Φ D f n p α β) (𝓝[>] 0)
        (𝓝 ((A (Minkowski.dot p p) • Dirac.slash p
          + (B (Minkowski.dot p p) * Φ.mass f) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) ∧
    A (-Φ.mass f ^ 2) * ((-Φ.mass f : ℝ) : ℂ) + B (-Φ.mass f ^ 2) * Φ.mass f = 0 ∧
    HasDerivAt (fun z : ℝ => A (-z ^ 2) * (z : ℂ) + B (-z ^ 2) * Φ.mass f) 0 (-Φ.mass f)

end QED.Graded

end
