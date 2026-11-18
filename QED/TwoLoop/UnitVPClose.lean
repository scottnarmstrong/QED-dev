/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.VPHalfAtAssemblyMatch
public import QED.TwoLoop.UnitVPLink

/-!
# The VP unit: the regulator limit without the nested-form hypothesis

The VP unit link of `QED/TwoLoop/UnitVPLink.lean` assumed the nested form `VPUnitNested` of the
model's VP unit. It is now proved (`QED.TwoLoop.VPHalfAtAssembly.vpUnitNested_of_assembly`,
through the fixed-momentum identity `QED.TwoLoop.VPHalf.VPHalfSubAt` along the boost curve), so
the D-37.4 iterated regulator limit of the model's VP unit holds with no remaining hypothesis
beyond the regulator conditions and the photon on-shell counterterm condition (Z₈).

* `vpUnitNested_atUnitCharge`: `VPUnitNested (atUnitCharge P d₁ d₂ d_m d₃)` at `m = 1`, for
  `0 < m_γ < Λ`, `m_γ < 2`, `M₁, M₂ > 1` and the Pauli–Villars conditions, for every choice of the
  counterterm coefficients.
* **`unitF2_VP_iterated_limit_closed`**: for every `η > 0` there is `R` such that for all
  `M₁, M₂ > R` there are `δ > 0` and `Λ₀` such that for every parameter set with `m = 1`, regulator
  masses `M₁, M₂`, Pauli–Villars coefficients, `m_γ ∈ (0, δ)`, `Λ > Λ₀`, and every `d₃` fixed by
  (Z₈) at charge `1`, `|16π⁴ unitF2 .VP (atUnitCharge P d₁ d₂ d_m d₃) - (119/36 - π²/3)| < η`.
-/

@[expose] public section

open Complex
open scoped Real

namespace QED.TwoLoop.UnitVPClose

open QED.WickModel QED.TwoLoop.UnitVPLink QED.TwoLoop.VPHalfAtAssembly QED.TwoLoop.UnitsRegulated
open QED.TwoLoop.VPUnit

/-- **The nested form of the VP unit at unit charge**, unconditionally under the regulator
conditions. -/
theorem vpUnitNested_atUnitCharge (P : Params) (hm : P.m = 1) (hM₁ : 1 < P.M₁) (hM₂ : 1 < P.M₂)
    (hmγ : 0 < P.mγ) (hmΛ : P.mγ < P.Λ) (hm2 : P.mγ < 2) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
    (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0) (d₁ d₂ dm d₃ : ℝ) :
    VPUnitNested (atUnitCharge P d₁ d₂ dm d₃) :=
  vpUnitNested_of_assembly (atUnitCharge P d₁ d₂ dm d₃) hm rfl hM₁ hM₂ hmγ hmΛ hm2 hc₁ hc₂

/-- **The D-37.4 iterated limit of the model's VP unit**, with no nested-form hypothesis: for
every `η > 0` there is `R` such that for all `M₁, M₂ > R` there are `δ > 0` and `Λ₀` such that for
every parameter set with `m = 1`, regulator masses `M₁, M₂`, Pauli–Villars coefficients,
`m_γ ∈ (0, δ)`, `Λ > Λ₀`, and every `d₃` fixed by (Z₈) at charge `1`,
`|16π⁴ unitF2 .VP (atUnitCharge P d₁ d₂ d_m d₃) - (119/36 - π²/3)| < η`. -/
theorem unitF2_VP_iterated_limit_closed :
    ∀ η > 0, ∃ R : ℝ, ∀ M₁ M₂ : ℝ, R < M₁ → R < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
        (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0),
        P.m = 1 → P.M₁ = M₁ → P.M₂ = M₂ → 0 < P.mγ → P.mγ < δ → Λ₀ < P.Λ →
        ∀ d₁ d₂ dm d₃ : ℝ, IsPhotonOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hM₁ hM₂ hPV₁ hPV₂ →
          ‖(16 * (π : ℂ) ^ 4) * unitF2 .VP (atUnitCharge P d₁ d₂ dm d₃) -
            ((119 / 36 - π ^ 2 / 3 : ℝ) : ℂ)‖ < η := by
  intro η hη
  obtain ⟨R, hR⟩ := unitF2_VP_iterated_limit η hη
  refine ⟨R, fun M₁ M₂ h1 h2 => ?_⟩
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hR M₁ M₂ h1 h2
  refine ⟨min δ 1, lt_min hδ one_pos, max Λ₀ 2, ?_⟩
  intro P hm hM₁ hM₂ hPV₁ hPV₂ hm1 e1 e2 hmγ hmδ hΛ d₁ d₂ dm d₃ hph
  have hmδ1 : P.mγ < 1 := hmδ.trans_le (min_le_right _ _)
  have hmΛ : P.mγ < P.Λ := by linarith [le_max_right Λ₀ 2]
  have hN := vpUnitNested_atUnitCharge P hm1 (hm1 ▸ hM₁) (hm1 ▸ hM₂) hmγ hmΛ (by linarith) hPV₁
    hPV₂ d₁ d₂ dm d₃
  exact hΛ₀ P hm hM₁ hM₂ hPV₁ hPV₂ hm1 e1 e2 hmγ (hmδ.trans_le (min_le_left _ _))
    (lt_of_le_of_lt (le_max_left _ _) hΛ) d₁ d₂ dm d₃ hph hN

end QED.TwoLoop.UnitVPClose

end
