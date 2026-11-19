/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.Algebra.Bar
public import QED.Frozen.Algebra.Spinor
public import QED.Frozen.Algebra.LorentzGen

@[expose] public section

open Matrix Complex

namespace QED.Graded

/-- (G-L₂) **The on-shell form-factor decomposition (63.18) of a spin-indexed amplitude**
(successor of (H₀) for an amplitude given as data): the pair `F = (A, B)` decomposes `M` at the
on-shell momenta `(p', p)` of mass `m` if
`M s' s μ = e ū_{s'}(p') [A γ^μ - (i/m) B S^{μν} q_ν] u_s(p)` for all spins and every `μ`, with
`q = p' - p` and `S^{μν} = (i/4)[γ^μ, γ^ν]`. As for (H₀), the spinors span the solution spaces
((38.1), (38.16)), so for `e ≠ 0` and `q² > 0` there is at most one such pair. -/
def IsSpinFormFactorPair (e m : ℝ) (p' p : Fin 4 → ℝ) (M : Fin 2 → Fin 2 → Fin 4 → ℂ)
    (F : ℂ × ℂ) : Prop :=
  ∀ (s' s : Fin 2) (μ : Fin 4),
    M s' s μ = (e : ℂ) * (Dirac.bar (Dirac.spinor m p' s') ⬝ᵥ
      ((F.1 • Dirac.gamma μ - (I / (m : ℂ) * F.2) •
        ∑ ν, ((Minkowski.lower (p' - p) ν : ℝ) : ℂ) • Dirac.lorentzGen μ ν) *ᵥ
          Dirac.spinor m p s))

end QED.Graded

end
