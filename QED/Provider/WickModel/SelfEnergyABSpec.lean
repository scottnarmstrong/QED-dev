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

/-!
# Provider for `QED.WickModel.selfEnergyAB_spec`

Proves packet 6b-2's characterization (Z₃′) (decision D-27) as
`QED.Provider.WickModel.selfEnergyAB_spec`, with the binder convention of decision D-13. It
follows directly from the existence and uniqueness of the sealed theorem (Z₁). This module must
never import the frozen anchor.
-/

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.Provider.WickModel

open QED.WickModel in
/-- Packet 6b-2's (Z₃′), with implicit data binders and `by assumption` hypotheses
(decision D-13). -/
theorem selfEnergyAB_spec {P : Params} (hm : 0 < P.m := by assumption)
    (hmγ : 0 < P.mγ := by assumption) (hΛ : 0 < P.Λ := by assumption) :
    (∀ (p : Fin 4 → ℝ) (hp : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot p p) (α β : Fin 4),
      Tendsto (fun ε : ℝ => (1 / I) *
          onePIFunction { P with ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![])
        (𝓝[>] 0)
        (𝓝 (((selfEnergyAB P hm hmγ hΛ ⟨_, hp⟩).1 • Dirac.slash p
          + ((selfEnergyAB P hm hmγ hΛ ⟨_, hp⟩).2 * P.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β)))
    ∧ ∀ AB : {s : ℝ // -(P.m + min P.mγ P.Λ) ^ 2 < s} → ℂ × ℂ,
      (∀ (p : Fin 4 → ℝ) (hp : -(P.m + min P.mγ P.Λ) ^ 2 < Minkowski.dot p p) (α β : Fin 4),
        Tendsto (fun ε : ℝ => (1 / I) *
            onePIFunction { P with ε := ε } 1 0 2 ![p] ![p] ![] ![α] ![β] ![])
          (𝓝[>] 0)
          (𝓝 (((AB ⟨_, hp⟩).1 • Dirac.slash p
            + ((AB ⟨_, hp⟩).2 * P.m) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) α β))) →
      AB = selfEnergyAB P hm hmγ hΛ := by
  have h := (QED.WickModel.selfEnergy_existsUnique P hm hmγ hΛ).2
  exact ⟨h.exists.choose_spec, fun AB hAB => h.unique hAB h.exists.choose_spec⟩

end QED.Provider.WickModel

end
