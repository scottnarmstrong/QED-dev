/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.SelfEnergyExistsUnique
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.WickModel

/-- (Z₃) **The self-energy form factors** (decision D-25): the unique pair `(A, B)` of functions
of `s = p²`, on the region `s > -(m + min(m_γ, Λ))²` below both photon thresholds, with
`Σ(p) = A(p²) p̸ + B(p²) m` for the `ε → 0⁺` limit of the one-loop self-energy (62.27)–(62.28).
It is chosen from the sealed existence-and-uniqueness theorem (Z₁); its characterization is
(Z₃′). -/
noncomputable def selfEnergyAB (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    {s : ℝ // -(P.m + min P.mγ P.Λ) ^ 2 < s} → ℂ × ℂ :=
  (selfEnergy_existsUnique P hm hmγ hΛ).2.exists.choose

end QED.WickModel

end
