/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.SelfEnergyAB
public import QED.Frozen.WickModel.SelfEnergyExistsUnique
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.WickModel

/-- (Z₄) **The self-energy as a function of `p̸`** ((62.27), decision D-25): `Σ(z) = A(-z²) z +
B(-z²) m`, the source's `Σ(p̸)` with `p̸` replaced by the real number `z` and `p² = -p̸²` (the
convention of (62.38)), for `|z| < m + min(m_γ, Λ)`, where `-z²` lies in the domain of (Z₃). On
shell `(p̸ + m) u = 0`, so `z = -m` is the eigenvalue of `p̸` on the electron spinors; the real
`z` cover the eigenvalues of `p̸` for timelike `p`. -/
noncomputable def selfEnergySlash (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (z : ℝ) (hz : |z| < P.m + min P.mγ P.Λ) : ℂ :=
  have hs : -(P.m + min P.mγ P.Λ) ^ 2 < -z ^ 2 :=
    neg_lt_neg ((sq_abs z).symm.trans_lt (pow_lt_pow_left₀ hz (abs_nonneg z) two_ne_zero))
  (selfEnergyAB P hm hmγ hΛ ⟨-z ^ 2, hs⟩).1 * z + (selfEnergyAB P hm hmγ hΛ ⟨-z ^ 2, hs⟩).2 * P.m

end QED.WickModel

end
