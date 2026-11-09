-- FROZEN_ANCHOR_PREFIX_BEGIN
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.WickModel.SelfEnergyExistsUnique
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import QED.Provider.WickModel.ElectronCountertermsExistsUnique

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.WickModel

/-- (Z₆) **The on-shell conditions fix the fermion counterterms** (packet 6b-2 theorem goal;
(62.36)–(62.38); decisions D-23, D-25). For `m, m_γ, Λ > 0` and all other parameters, there is a
unique pair `(δ₂, δ_m)` of real counterterm coefficients for which the electron is on shell
(Z₅); the counterterms stored in `P` are replaced. As the source says after (62.27), the two
conditions fix `Z₂` and `Z_m`. -/
theorem electronCounterterms_existsUnique (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) :
    ∃! d : ℝ × ℝ, IsElectronOnShell { P with δ₂ := d.1, δm := d.2 } hm hmγ hΛ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
