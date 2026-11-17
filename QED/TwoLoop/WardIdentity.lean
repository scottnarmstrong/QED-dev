/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Frozen.WickModel.IsElectronOnShell
public import QED.Frozen.WickModel.IsLSZChargeNormalized
public import QED.Frozen.OneLoop.IsChargeNormalized
public import QED.TwoLoop.WardIdentityParametric
import QED.Frozen.WickModel.SelfEnergyABSpec
import QED.Frozen.WickModel.IsLSZChargeNormalizedIff

/-!
# The one-loop Ward identity `δ₁ = δ₂` at fixed regulators

Obligation O2-15 (decision D-37, ruling 2: the Ward identity is proved, not imposed). In the
frozen one-loop model the counterterms are the real numbers `δ₁ = Z₁ - 1` and `δ₂ = Z₂ - 1` of
`QED.WickModel.Params`. The electron on-shell conditions (Z₅) fix `δ₂`, and the charge condition
(K₀) on `Z₁ = 1 + δ₁`, or its LSZ form (L₄), fixes `δ₁` when `e ≠ 0`. At fixed
`m, m_γ, Λ > 0` these force `δ₁ = δ₂`, the primary source's (68.13) `Z₁ = Z₂`.

The proof compares the two closed forms
(`QED.TwoLoop.Ward.chargeZ_eq_one_add_onShellδ₂`). Neither the Pauli–Villars conditions on the
regulator fermions nor `Λ > m_γ` is used; the regulator-fermion data enter only to state (L₄).

## Main statements

* `QED.TwoLoop.Ward.isElectronOnShell_iff`: (Z₅) holds exactly when `δ₂ = onShellδ₂ P` and
  `δ_m = onShellδm P`.
* `QED.TwoLoop.Ward.δ₁_eq_δ₂_of_isChargeNormalized`: (Z₅) and (K₀) on `Z₁ = 1 + δ₁` give
  `δ₁ = δ₂`, for `e ≠ 0`.
* `QED.TwoLoop.Ward.δ₁_eq_δ₂_of_isLSZChargeNormalized`: the same with the LSZ form (L₄).
* `QED.TwoLoop.Ward.isChargeNormalized_iff_δ₁_eq_δ₂`: on shell and for `e ≠ 0`, (K₀) is
  equivalent to `δ₁ = δ₂`.
* `QED.TwoLoop.Ward.exists_counterexample_e_eq_zero`: the hypothesis `e ≠ 0` cannot be dropped.
-/

@[expose] public section

open Matrix Complex
open QED.WickModel QED.OneLoop QED.OneLoop.VertexLimit

namespace QED.TwoLoop.Ward

/-- **The on-shell conditions in closed form.** For `m, m_γ, Λ > 0`, the electron is on shell
(Z₅) exactly when `δ₂ = onShellδ₂ P` and `δ_m = onShellδm P`. -/
theorem isElectronOnShell_iff (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    IsElectronOnShell P hm hmγ hΛ ↔ P.δ₂ = onShellδ₂ P ∧ P.δm = onShellδm P := by
  have hμ := lt_min hmγ hΛ
  have hab : -P.m - min P.mγ P.Λ / 2 ≤ -P.m + min P.mγ P.Λ / 2 := by linarith
  have hx : -P.m ∈ Set.Ioo (-P.m - min P.mγ P.Λ / 2) (-P.m + min P.mγ P.Λ / 2) := by
    constructor <;> linarith
  have hAB : selfEnergyAB P hm hmγ hΛ =
      fun s => (selfEnergyLoopA P s.1 - P.δ₂, selfEnergyLoopB P s.1 - P.δm) :=
    eq_selfEnergyLoop_of_tendsto P hm hmγ hΛ (selfEnergyAB_spec P hm hmγ hΛ).1
  have hslash : ∀ z hz, selfEnergySlash P hm hmγ hΛ z hz =
      (selfEnergyLoopA P (-z ^ 2) - P.δ₂) * z + (selfEnergyLoopB P (-z ^ 2) - P.δm) * P.m := by
    intro z hz
    rw [selfEnergySlash, hAB]
  refine Iff.trans ?_ (selfEnergyLoop_onShell_iff P hm hmγ hΛ P.δ₂ P.δm)
  unfold IsElectronOnShell
  simp only [hslash]
  exact and_congr Iff.rfl (hasDerivAt_comp_projIcc_iff
    (f := fun z : ℝ => (selfEnergyLoopA P (-z ^ 2) - P.δ₂) * z
      + (selfEnergyLoopB P (-z ^ 2) - P.δm) * P.m) hab hx)

/-- On shell, `δ₂` is the closed-form counterterm `onShellδ₂ P`. -/
theorem δ₂_eq_onShellδ₂ {P : Params} {hm : 0 < P.m} {hmγ : 0 < P.mγ} {hΛ : 0 < P.Λ}
    (hon : IsElectronOnShell P hm hmγ hΛ) : P.δ₂ = onShellδ₂ P :=
  ((isElectronOnShell_iff P hm hmγ hΛ).1 hon).1

/-- **The one-loop Ward identity `δ₁ = δ₂` (O2-15), packet-3 form of the charge condition.**
For `e ≠ 0` and `m, m_γ, Λ > 0`: if the electron is on shell (Z₅) and `Z₁ = 1 + δ₁` satisfies
the charge condition (K₀), then `δ₁ = δ₂`. -/
theorem δ₁_eq_δ₂_of_isChargeNormalized (P : Params) (he : P.e ≠ 0) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hon : IsElectronOnShell P hm hmγ hΛ)
    (hK : IsChargeNormalized P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ) : P.δ₁ = P.δ₂ := by
  have hZ := eq_chargeZ_of_isChargeNormalized he hm hmγ hΛ hK
  rw [chargeZ_eq_one_add_onShellδ₂ P hm hmγ hΛ] at hZ
  rw [δ₂_eq_onShellδ₂ hon]
  linarith

/-- **The one-loop Ward identity `δ₁ = δ₂` (O2-15), LSZ form of the charge condition.** For
`e ≠ 0`, `m, m_γ, Λ > 0` and Pauli–Villars regulator fermions as in (L₄): if the electron is on
shell (Z₅) and the LSZ charge condition (L₄) holds, then `δ₁ = δ₂`. -/
theorem δ₁_eq_δ₂_of_isLSZChargeNormalized (P : Params) (he : P.e ≠ 0) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
    (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
    (hon : IsElectronOnShell P hm hmγ hΛ)
    (hL : IsLSZChargeNormalized P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon) : P.δ₁ = P.δ₂ :=
  δ₁_eq_δ₂_of_isChargeNormalized P he hm hmγ hΛ hon
    ((isLSZChargeNormalized_iff_isChargeNormalized P hm hmγ hΛ hM₁ hM₂ hPV₁ hPV₂ hon).1 hL)

/-- **On shell, the charge condition is the Ward identity.** For `e ≠ 0`, `m, m_γ, Λ > 0` and
the electron on shell (Z₅), `Z₁ = 1 + δ₁` satisfies the charge condition (K₀) exactly when
`δ₁ = δ₂`. The direction `δ₁ = δ₂ → (K₀)` does not need `e ≠ 0`. -/
theorem isChargeNormalized_iff_δ₁_eq_δ₂ (P : Params) (he : P.e ≠ 0) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hon : IsElectronOnShell P hm hmγ hΛ) :
    IsChargeNormalized P.e (1 + P.δ₁) P.m P.mγ P.Λ hm hmγ hΛ ↔ P.δ₁ = P.δ₂ := by
  refine ⟨δ₁_eq_δ₂_of_isChargeNormalized P he hm hmγ hΛ hon, fun h => ?_⟩
  have hZ : 1 + P.δ₁ = chargeZ P.e P.m P.mγ P.Λ := by
    rw [chargeZ_eq_one_add_onShellδ₂ P hm hmγ hΛ, h, δ₂_eq_onShellδ₂ hon]
  rw [hZ]
  exact isChargeNormalized_chargeZ hm hmγ hΛ

/-- At `e = 0` the closed-form counterterm `onShellδ₂` vanishes. -/
theorem onShellδ₂_eq_zero_of_e_eq_zero (P : Params) (he : P.e = 0) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) : onShellδ₂ P = 0 := by
  rw [onShellδ₂_eq P hm hmγ hΛ, he]
  ring

/-- At `e = 0` every `Z₁` satisfies the charge condition (K₀). -/
theorem isChargeNormalized_zero (Z₁ m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ) (hΛ : 0 < Λ) :
    IsChargeNormalized 0 Z₁ m mγ Λ hm hmγ hΛ := by
  intro p hp hp0 μ u w hu hw
  rw [sandwich_vertexFunction_self hm hmγ hΛ hp hp0 μ hu hw]
  simp

/-- **The hypothesis `e ≠ 0` is needed.** At `e = 0`, for any `m, m_γ, Λ > 0`, there are
parameters with the electron on shell (Z₅) and `Z₁ = 1 + δ₁` satisfying the charge condition
(K₀), but `δ₁ ≠ δ₂`. -/
theorem exists_counterexample_e_eq_zero (m mγ Λ : ℝ) (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) :
    ∃ P : Params, ∃ (h₁ : 0 < P.m) (h₂ : 0 < P.mγ) (h₃ : 0 < P.Λ),
      P.e = 0 ∧ P.m = m ∧ P.mγ = mγ ∧ P.Λ = Λ ∧ IsElectronOnShell P h₁ h₂ h₃ ∧
        IsChargeNormalized P.e (1 + P.δ₁) P.m P.mγ P.Λ h₁ h₂ h₃ ∧ P.δ₁ ≠ P.δ₂ := by
  let P₀ : Params := ⟨0, 1, 0, 0, 0, m, mγ, Λ, 0, 0, 0, 0, 0⟩
  let P : Params := { P₀ with δm := onShellδm P₀ }
  have hδ₂ : onShellδ₂ P = 0 := onShellδ₂_eq_zero_of_e_eq_zero P rfl hm hmγ hΛ
  refine ⟨P, hm, hmγ, hΛ, rfl, rfl, rfl, rfl, ?_, isChargeNormalized_zero _ _ _ _ hm hmγ hΛ, ?_⟩
  · rw [isElectronOnShell_iff P hm hmγ hΛ, hδ₂]
    exact ⟨rfl, rfl⟩
  · show (1 : ℝ) ≠ 0
    exact one_ne_zero

end QED.TwoLoop.Ward

end
