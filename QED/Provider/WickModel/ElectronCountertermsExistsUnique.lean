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
import QED.Frozen.WickModel.SelfEnergyABSpec
import QED.WickModel.ElectronOnShell

/-!
# Provider for `QED.WickModel.electronCounterterms_existsUnique`

Proves packet 6b-2's theorem goal (Z₆) (decision D-27) as
`QED.Provider.WickModel.electronCounterterms_existsUnique`, with the binder convention of decision
D-13. This module must never import the frozen anchor.

By the characterization (Z₃′) and `QED.WickModel.eq_selfEnergyLoop_of_tendsto`, the form
factors of the parameters with counterterms `(δ₂, δ_m)` are `(A_loop - δ₂, B_loop - δ_m)`.
`QED.WickModel.selfEnergyLoop_onShell_iff` solves the on-shell conditions for this closed form,
and `QED.WickModel.hasDerivAt_comp_projIcc_iff` removes the clamp. The unique pair is
`δ₂ = a - 2m²a' + 2m²b'`, `δ_m = b - 2m²a' + 2m²b'` with `a = A_loop`, `b = B_loop` at
`s = -m²`.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6b-2's (Z₆), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem electronCounterterms_existsUnique {P : Params} (hm : 0 < P.m := by assumption)
    (hmγ : 0 < P.mγ := by assumption) (hΛ : 0 < P.Λ := by assumption) :
    ∃! d : ℝ × ℝ, IsElectronOnShell { P with δ₂ := d.1, δm := d.2 } hm hmγ hΛ := by
  have hμ := lt_min hmγ hΛ
  have hab : -P.m - min P.mγ P.Λ / 2 ≤ -P.m + min P.mγ P.Λ / 2 := by linarith
  have hx : -P.m ∈ Set.Ioo (-P.m - min P.mγ P.Λ / 2) (-P.m + min P.mγ P.Λ / 2) := by
    constructor <;> linarith
  have key : ∀ d : ℝ × ℝ, IsElectronOnShell { P with δ₂ := d.1, δm := d.2 } hm hmγ hΛ ↔
      d = (onShellδ₂ P, onShellδm P) := by
    intro d
    have hAB : selfEnergyAB { P with δ₂ := d.1, δm := d.2 } hm hmγ hΛ =
        fun s => (selfEnergyLoopA P s.1 - d.1, selfEnergyLoopB P s.1 - d.2) :=
      eq_selfEnergyLoop_of_tendsto { P with δ₂ := d.1, δm := d.2 } hm hmγ hΛ
        (QED.WickModel.selfEnergyAB_spec { P with δ₂ := d.1, δm := d.2 } hm hmγ hΛ).1
    have hslash : ∀ z hz, selfEnergySlash { P with δ₂ := d.1, δm := d.2 } hm hmγ hΛ z hz =
        (selfEnergyLoopA P (-z ^ 2) - d.1) * z + (selfEnergyLoopB P (-z ^ 2) - d.2) * P.m := by
      intro z hz
      rw [selfEnergySlash, hAB]
    rw [Prod.ext_iff]
    refine Iff.trans ?_ (selfEnergyLoop_onShell_iff P hm hmγ hΛ d.1 d.2)
    unfold IsElectronOnShell
    simp only [hslash]
    exact and_congr Iff.rfl (hasDerivAt_comp_projIcc_iff
      (f := fun z : ℝ => (selfEnergyLoopA P (-z ^ 2) - d.1) * z
        + (selfEnergyLoopB P (-z ^ 2) - d.2) * P.m) hab hx)
  exact ⟨_, (key _).2 rfl, fun d hd => (key d).1 hd⟩

end QED.Provider.WickModel

end
