/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.MassScalingUnits
public import QED.TwoLoop.UnitLClose
public import QED.TwoLoop.UnitVPClose
import Mathlib.Tactic.LinearCombination

/-!
# The unit links at arbitrary electron mass

The ladder and vacuum-polarization unit links were proved at `m = 1`
(`QED.TwoLoop.UnitLLink.unitF2_L_limit`, `QED.TwoLoop.UnitVPClose.unitF2_VP_iterated_limit_closed`).
The units are dimensionless (`QED.TwoLoop.MassScaling.unitF2_massScale`) and the frozen counterterm
conditions scale with the masses (`isChargeNormalized_mul_iff`, `isPhotonOnShell_massScale_iff`),
so the links hold at every `m > 0`, with the regulator thresholds measured in units of `m`:

* `unitF2_L_limit_scaled`: for every `η > 0` there are `δ > 0` and `R` such that for every
  parameter set with `m > 0`, `0 < m_γ < δ m`, `Λ > R m` and every `d₁` fixed by (K₀) at charge
  `1`, `‖16π⁴ unitF2 L - (11/48 + π²/18)‖ < η`;
* `unitF2_L_limit_mass`: the same at a fixed mass `m₀ > 0`, thresholds in absolute units;
* `unitF2_VP_iterated_limit_scaled`, `unitF2_VP_iterated_limit_mass`: the D-37.4 iterated limit of
  the VP unit, `‖16π⁴ unitF2 VP - (119/36 - π²/3)‖ < η`, with `M_f = M̂_f m` and the thresholds in
  units of `m` (respectively at a fixed mass `m₀`).
-/

@[expose] public section

open Complex
open scoped Real

namespace QED.TwoLoop.MassScaling

open QED.WickModel QED.TwoLoop.UnitsRegulated

/-! ### The ladder unit -/

/-- **The L unit link at every mass**, thresholds in units of `m`: for every `η > 0` there are
`δ > 0` and `R` such that for every parameter set with `m > 0`, `0 < m_γ < δ m`, `Λ > R m` and
every `d₁` satisfying the frozen charge condition (K₀) at charge `1`,
`‖16π⁴ unitF2 L (atUnitCharge P d₁ d₂ d_m d₃) - (11/48 + π²/18)‖ < η`. -/
theorem unitF2_L_limit_scaled {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ),
      P.mγ < δ * P.m → R * P.m < P.Λ → ∀ d₁ d₂ dm d₃ : ℝ,
        QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ →
        ‖16 * (π : ℂ) ^ 4 * unitF2 .L (atUnitCharge P d₁ d₂ dm d₃) -
          ((11 / 48 + π ^ 2 / 18 : ℝ) : ℂ)‖ < η := by
  obtain ⟨δ, hδ, R, hR⟩ := QED.TwoLoop.UnitLLink.unitF2_L_limit hη
  refine ⟨δ, hδ, R, fun P hm hmγ hΛ hmδ hRΛ d₁ d₂ dm d₃ hch => ?_⟩
  have hs : 0 < P.m⁻¹ := inv_pos.mpr hm
  have hm' : 0 < (unitMass P).m := mul_pos hs hm
  have hmγ' : 0 < (unitMass P).mγ := mul_pos hs hmγ
  have hΛ' : 0 < (unitMass P).Λ := mul_pos hs hΛ
  have hch' : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) (unitMass P).m (unitMass P).mγ
      (unitMass P).Λ hm' hmγ' hΛ' :=
    (isChargeNormalized_mul_iff hm hmγ hΛ hs hm' hmγ' hΛ').2 hch
  have h1 : (unitMass P).m = 1 := unitMass_m hm.ne'
  have h2 : (unitMass P).mγ < δ := by
    rw [unitMass_mγ, div_lt_iff₀ hm]
    exact hmδ
  have h3 : R < (unitMass P).Λ := by
    rw [unitMass_Λ, lt_div_iff₀ hm]
    exact hRΛ
  have key := hR (unitMass P) hm' hmγ' hΛ' h1 h2 h3 d₁ d₂ dm d₃ hch'
  have e : unitF2 .L (atUnitCharge (unitMass P) d₁ d₂ dm d₃) =
      unitF2 .L (atUnitCharge P d₁ d₂ dm d₃) :=
    unitF2_massScale_of_ne_VP (by decide) (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hs
  rwa [e] at key

/-- **The L unit link at a fixed mass `m₀ > 0`**, in the form of
`QED.TwoLoop.UnitLLink.unitF2_L_limit`: for every `η > 0` there are `δ > 0` and `R` such that for
every parameter set with `m = m₀`, `0 < m_γ < δ`, `Λ > R` and every `d₁` fixed by (K₀) at charge
`1`, `‖16π⁴ unitF2 L (atUnitCharge P d₁ d₂ d_m d₃) - (11/48 + π²/18)‖ < η`. -/
theorem unitF2_L_limit_mass {m₀ : ℝ} (hm₀ : 0 < m₀) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ R : ℝ, ∀ (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ),
      P.m = m₀ → P.mγ < δ → R < P.Λ → ∀ d₁ d₂ dm d₃ : ℝ,
        QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ →
        ‖16 * (π : ℂ) ^ 4 * unitF2 .L (atUnitCharge P d₁ d₂ dm d₃) -
          ((11 / 48 + π ^ 2 / 18 : ℝ) : ℂ)‖ < η := by
  obtain ⟨δ, hδ, R, hR⟩ := unitF2_L_limit_scaled hη
  refine ⟨δ * m₀, mul_pos hδ hm₀, R * m₀, fun P hm hmγ hΛ hm1 hmδ hRΛ => ?_⟩
  subst hm1
  exact hR P hm hmγ hΛ hmδ hRΛ

/-! ### The vacuum-polarization unit -/

/-- **The D-37.4 iterated limit of the VP unit at every mass**, regulators in units of `m`: for
every `η > 0` there is `R` such that for all `M̂₁, M̂₂ > R` there are `δ > 0` and `Λ₀` such that
for every parameter set with `m > 0`, regulator masses `M_f = M̂_f m`, Pauli–Villars
coefficients, `0 < m_γ < δ m`, `Λ > Λ₀ m`, and every `d₃` fixed by (Z₈) at charge `1`,
`‖16π⁴ unitF2 VP (atUnitCharge P d₁ d₂ d_m d₃) - (119/36 - π²/3)‖ < η`. -/
theorem unitF2_VP_iterated_limit_scaled :
    ∀ η > 0, ∃ R : ℝ, ∀ M₁ M₂ : ℝ, R < M₁ → R < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
        (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0),
        P.M₁ = M₁ * P.m → P.M₂ = M₂ * P.m → 0 < P.mγ → P.mγ < δ * P.m → Λ₀ * P.m < P.Λ →
        ∀ d₁ d₂ dm d₃ : ℝ, IsPhotonOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hM₁ hM₂ hPV₁ hPV₂ →
          ‖(16 * (π : ℂ) ^ 4) * unitF2 .VP (atUnitCharge P d₁ d₂ dm d₃) -
            ((119 / 36 - π ^ 2 / 3 : ℝ) : ℂ)‖ < η := by
  intro η hη
  obtain ⟨R, hR⟩ := QED.TwoLoop.UnitVPClose.unitF2_VP_iterated_limit_closed η hη
  refine ⟨R, fun M₁ M₂ h1 h2 => ?_⟩
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hR M₁ M₂ h1 h2
  refine ⟨δ, hδ, max Λ₀ 1, ?_⟩
  intro P hm hM₁ hM₂ hPV₁ hPV₂ e1 e2 hmγ hmδ hΛ d₁ d₂ dm d₃ hph
  have hΛa : Λ₀ * P.m < P.Λ :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left Λ₀ 1) hm.le) hΛ
  have hΛpos : 0 < P.Λ := by
    have := mul_le_mul_of_nonneg_right (le_max_right Λ₀ 1) hm.le
    linarith
  have hs : 0 < P.m⁻¹ := inv_pos.mpr hm
  set Q := atUnitCharge P d₁ d₂ dm d₃ with hQ
  have hm' : 0 < (massScale P.m⁻¹ Q).m := mul_pos hs hm
  have hM₁' : (massScale P.m⁻¹ Q).m < (massScale P.m⁻¹ Q).M₁ := mul_lt_mul_of_pos_left hM₁ hs
  have hM₂' : (massScale P.m⁻¹ Q).m < (massScale P.m⁻¹ Q).M₂ := mul_lt_mul_of_pos_left hM₂ hs
  have hPV₂' : (massScale P.m⁻¹ Q).m ^ 2 + (massScale P.m⁻¹ Q).c₁ * (massScale P.m⁻¹ Q).M₁ ^ 2 +
      (massScale P.m⁻¹ Q).c₂ * (massScale P.m⁻¹ Q).M₂ ^ 2 = 0 := by
    have hQm : Q.m = P.m := rfl
    have hQ1 : Q.M₁ = P.M₁ := rfl
    have hQ2 : Q.M₂ = P.M₂ := rfl
    have hQc1 : Q.c₁ = P.c₁ := rfl
    have hQc2 : Q.c₂ = P.c₂ := rfl
    simp only [massScale_m, massScale_c₁, massScale_c₂, massScale_M₁, massScale_M₂, hQm, hQ1, hQ2,
      hQc1, hQc2]
    linear_combination P.m⁻¹ ^ 2 * hPV₂
  have hph' : IsPhotonOnShell (massScale P.m⁻¹ Q) hm' hM₁' hM₂' hPV₁ hPV₂' :=
    (isPhotonOnShell_massScale_iff Q hm hM₁ hM₂ hPV₁ hPV₂ hs hm' hM₁' hM₂' hPV₁ hPV₂').2 hph
  have hm1 : (unitMass P).m = 1 := unitMass_m hm.ne'
  have hM1 : (unitMass P).M₁ = M₁ := by
    rw [unitMass_M₁, e1]
    field_simp
  have hM2 : (unitMass P).M₂ = M₂ := by
    rw [unitMass_M₂, e2]
    field_simp
  have hmγ' : 0 < (unitMass P).mγ := mul_pos hs hmγ
  have hmγδ : (unitMass P).mγ < δ := by
    rw [unitMass_mγ, div_lt_iff₀ hm]
    exact hmδ
  have hΛ' : Λ₀ < (unitMass P).Λ := by
    rw [unitMass_Λ, lt_div_iff₀ hm]
    exact hΛa
  have key := hΛ₀ (unitMass P) hm' hM₁' hM₂' hPV₁ hPV₂' hm1 hM1 hM2 hmγ' hmγδ hΛ' d₁ d₂ dm d₃ hph'
  have e : unitF2 .VP (atUnitCharge (unitMass P) d₁ d₂ dm d₃) = unitF2 .VP Q :=
    unitF2_massScale .VP Q hm hmγ hΛpos hM₁.le hM₂.le hs
  rwa [e] at key

/-- **The D-37.4 iterated limit of the VP unit at a fixed mass `m₀ > 0`**, in the form of
`QED.TwoLoop.UnitVPClose.unitF2_VP_iterated_limit_closed`: for every `η > 0` there is `R` such
that for all `M₁, M₂ > R` there are `δ > 0` and `Λ₀` such that for every parameter set with
`m = m₀`, regulator masses `M₁, M₂`, Pauli–Villars coefficients, `m_γ ∈ (0, δ)`, `Λ > Λ₀`, and
every `d₃` fixed by (Z₈) at charge `1`,
`‖16π⁴ unitF2 VP (atUnitCharge P d₁ d₂ d_m d₃) - (119/36 - π²/3)‖ < η`. -/
theorem unitF2_VP_iterated_limit_mass {m₀ : ℝ} (hm₀ : 0 < m₀) :
    ∀ η > 0, ∃ R : ℝ, ∀ M₁ M₂ : ℝ, R < M₁ → R < M₂ → ∃ δ > 0, ∃ Λ₀ : ℝ,
      ∀ (P : Params) (hm : 0 < P.m) (hM₁ : P.m < P.M₁) (hM₂ : P.m < P.M₂)
        (hPV₁ : 1 + P.c₁ + P.c₂ = 0) (hPV₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0),
        P.m = m₀ → P.M₁ = M₁ → P.M₂ = M₂ → 0 < P.mγ → P.mγ < δ → Λ₀ < P.Λ →
        ∀ d₁ d₂ dm d₃ : ℝ, IsPhotonOnShell (atUnitCharge P d₁ d₂ dm d₃) hm hM₁ hM₂ hPV₁ hPV₂ →
          ‖(16 * (π : ℂ) ^ 4) * unitF2 .VP (atUnitCharge P d₁ d₂ dm d₃) -
            ((119 / 36 - π ^ 2 / 3 : ℝ) : ℂ)‖ < η := by
  intro η hη
  obtain ⟨R, hR⟩ := unitF2_VP_iterated_limit_scaled η hη
  refine ⟨R * m₀, fun M₁ M₂ h1 h2 => ?_⟩
  have h1' : R < M₁ / m₀ := by rw [lt_div_iff₀ hm₀]; exact h1
  have h2' : R < M₂ / m₀ := by rw [lt_div_iff₀ hm₀]; exact h2
  obtain ⟨δ, hδ, Λ₀, hΛ₀⟩ := hR (M₁ / m₀) (M₂ / m₀) h1' h2'
  refine ⟨δ * m₀, mul_pos hδ hm₀, Λ₀ * m₀, ?_⟩
  intro P hm hM₁ hM₂ hPV₁ hPV₂ hm1 e1 e2 hmγ hmδ hΛ
  subst hm1
  refine hΛ₀ P hm hM₁ hM₂ hPV₁ hPV₂ ?_ ?_ hmγ hmδ hΛ
  · rw [e1]
    field_simp
  · rw [e2]
    field_simp

end QED.TwoLoop.MassScaling

end
