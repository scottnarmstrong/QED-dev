/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.WickModel.VacuumPolarizationExistsUnique
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The photon on-shell condition for the one-loop vacuum polarization

Facts about the one-loop vacuum polarization that fix the photon counterterm `δ₃` ((62.11);
decisions D-23, D-25). They are stated for the loop coefficient
`QED.WickModel.vacuumPolarizationLoop`, so that they apply to any function with the limit
property of (Z₂) `QED.WickModel.vacuumPolarization_existsUnique`.

Write `Π_loop = vacuumPolarizationLoop P`, a real-valued function of `s = k²` that does not
depend on `δ₃`. The vacuum polarization function is `Π(s) = -δ₃ + Π_loop(s)`, so the on-shell
condition `Π(0) = 0` reads `δ₃ = Π_loop(0)`.

## Main statements

* `QED.WickModel.tendsto_onePIFunction_vacuumPolarizationLoop`: the limit property of (Z₂)
  holds for `-δ₃ + Π_loop`.
* `QED.WickModel.eq_vacuumPolarizationLoop_of_tendsto`: any function with the limit property of
  (Z₂) is `-δ₃ + Π_loop`.
* `QED.WickModel.vacuumPolarizationLoop_onShell_iff`: `-δ₃ + Π_loop(0) = 0` holds exactly when
  `δ₃ = Π_loop(0)`.
-/

@[expose] public section

open Complex Filter Topology

namespace QED.WickModel

/-- **The limit of the one-loop vacuum polarization.** For `m > 0`, regulator fermions heavier
than the electron, the Pauli–Villars conditions `1 + c₁ + c₂ = 0`, `m² + c₁ M₁² + c₂ M₂² = 0`
and `k² > -4m²`, `Π^{μν}_ε(k) = (1/i) [i Π^{μν}_ε(k)]` tends as `ε → 0⁺` to
`(-δ₃ + Π_loop(k²)) (k² g^{μν} - k^μ k^ν)`, with `Π_loop = vacuumPolarizationLoop P`. -/
theorem tendsto_onePIFunction_vacuumPolarizationLoop (P : Params) (hm : 0 < P.m)
    (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) {k : Fin 4 → ℝ}
    (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4) :
    Tendsto (fun ε : ℝ => (1 / I) *
        onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν])
      (𝓝[>] 0)
      (𝓝 ((-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (Minkowski.dot k k) : ℂ)) *
        ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))) := by
  have hlim := tendsto_energyFirstIntegral_vacuumPolarizationIntegrand hm hM₁ hM₂ hPV₁ hPV₂ hk
    μ ν
  have h2 := (hlim.const_add (-I * ((P.δ₃ * (Minkowski.dot k k * Minkowski.metric μ ν
    - k μ * k ν) : ℝ) : ℂ))).const_mul (1 / I)
  have hval : (1 / I) * (-I * ((P.δ₃ * (Minkowski.dot k k * Minkowski.metric μ ν
        - k μ * k ν) : ℝ) : ℂ) + I * (vacuumPolarizationLoop P (Minkowski.dot k k) : ℂ)
          * ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ))
      = (-(P.δ₃ : ℂ) + (vacuumPolarizationLoop P (Minkowski.dot k k) : ℂ)) *
        ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ) := by
    field_simp
    push_cast
    ring
  rw [hval] at h2
  refine h2.congr fun ε => ?_
  rw [onePIFunction_vacuumPolarization]
  rfl

/-- **The vacuum polarization function in closed form.** For `m > 0`, regulator fermions heavier
than the electron and the Pauli–Villars conditions `1 + c₁ + c₂ = 0`,
`m² + c₁ M₁² + c₂ M₂² = 0`, a function `Π` on `s > -4m²` with the limit property of (Z₂)
`QED.WickModel.vacuumPolarization_existsUnique` is `-δ₃ + Π_loop`, with
`Π_loop = vacuumPolarizationLoop P`. -/
theorem eq_vacuumPolarizationLoop_of_tendsto (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁)
    (hM₂ : P.m < P.M₂) (hPV₁ : 1 + P.c₁ + P.c₂ = 0)
    (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    {Pol : {s : ℝ // -(4 * P.m ^ 2) < s} → ℂ}
    (hPol : ∀ (k : Fin 4 → ℝ) (hk : -(4 * P.m ^ 2) < Minkowski.dot k k) (μ ν : Fin 4),
      Tendsto (fun ε : ℝ => (1 / I) *
          onePIFunction { P with ε := ε } 0 2 2 ![] ![] ![k, -k] ![] ![] ![μ, ν])
        (𝓝[>] 0)
        (𝓝 (Pol ⟨_, hk⟩ *
          ((Minkowski.dot k k * Minkowski.metric μ ν - k μ * k ν : ℝ) : ℂ)))) :
    Pol = fun s => -(P.δ₃ : ℂ) + (vacuumPolarizationLoop P s.1 : ℂ) :=
  (vacuumPolarization_existsUnique_of_twoPoint P hm hM₁ hM₂ hPV₁ hPV₂).2.unique hPol
    fun _ hk μ ν => tendsto_onePIFunction_vacuumPolarizationLoop P hm hM₁ hM₂ hPV₁ hPV₂ hk μ ν

/-- **The on-shell condition fixes the counterterm.** For real `δ₃`, the vacuum polarization
`-δ₃ + Π_loop(s)`, with `Π_loop = vacuumPolarizationLoop P`, vanishes at `s = 0` exactly when
`δ₃ = Π_loop(0)`. -/
theorem vacuumPolarizationLoop_onShell_iff (P : Params) (δ₃ : ℝ) :
    -(δ₃ : ℂ) + (vacuumPolarizationLoop P 0 : ℂ) = 0 ↔ δ₃ = vacuumPolarizationLoop P 0 := by
  rw [neg_add_eq_zero, ofReal_inj]

end QED.WickModel

end
