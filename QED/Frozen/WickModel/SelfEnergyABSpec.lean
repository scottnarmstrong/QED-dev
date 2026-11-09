-- FROZEN_ANCHOR_PREFIX_BEGIN
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
public import QED.Provider.WickModel.SelfEnergyABSpec

@[expose] public section

open Complex Filter Topology MeasureTheory

namespace QED.WickModel

/-- (Z₃′) **Characterization of the self-energy form factors.** `selfEnergyAB` has the limit
property of (Z₁), and it is the only pair of functions on the domain that has it. -/
theorem selfEnergyAB_spec (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
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
      AB = selfEnergyAB P hm hmγ hΛ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact QED.Provider.WickModel.selfEnergyAB_spec
  -- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end QED.WickModel

end
-- FROZEN_ANCHOR_SUFFIX_END
