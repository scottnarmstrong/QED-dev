/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.SelfEnergySlash
public import QED.Frozen.WickModel.SelfEnergyExistsUnique
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.WickModel

/-- (Z₅) **The on-shell conditions for the electron** (62.27), (62.36)–(62.38): `Σ(-m) = 0` and
`Σ'(-m) = 0`, for the function `z ↦ Σ(z)` of (Z₄). The derivative is taken of `Σ` composed with
the clamp of `ℝ` onto the interval `[-m - μ/2, -m + μ/2]`, `μ = min(m_γ, Λ)`, which lies inside
the domain of `Σ` and has `-m` in its interior, so the clamp does not change the derivative at
`-m`. -/
def IsElectronOnShell (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) : Prop :=
  selfEnergySlash P hm hmγ hΛ (-P.m) (by
      rw [abs_neg, abs_of_pos hm]
      exact lt_add_of_pos_right _ (lt_min hmγ hΛ)) = 0 ∧
    HasDerivAt (fun z : ℝ => selfEnergySlash P hm hmγ hΛ
        (Set.projIcc (-P.m - min P.mγ P.Λ / 2) (-P.m + min P.mγ P.Λ / 2)
          (by linarith [lt_min hmγ hΛ]) z)
        (by
          have hμ := lt_min hmγ hΛ
          have h1 := (Set.projIcc (-P.m - min P.mγ P.Λ / 2) (-P.m + min P.mγ P.Λ / 2)
            (by linarith) z).2
          rw [abs_lt]
          constructor <;> linarith [h1.1, h1.2]))
      0 (-P.m)

end QED.WickModel

end
