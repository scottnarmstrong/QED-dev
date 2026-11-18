/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.MassScalingVP
public import QED.TwoLoop.MassScalingCt
public import QED.TwoLoop.MassScalingCounterterm
public import QED.TwoLoop.UnitsRegulated
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The regulated `F₂⁽⁴⁾(0)` is dimensionless

Multiplying all five masses `m, m_γ, Λ, M₁, M₂` by `s > 0` (`massScale s P`), with the charge
and the counterterms unchanged, multiplies each of the fourteen explicit class values by `s⁵`
(`QED/TwoLoop/MassScalingOpen.lean`, `…VP.lean`, `…Ct.lean`), so

* `unitZero_massScale`: `unitZero U (massScale s P) = s⁵ unitZero U P`;
* `unitF2_massScale`: each unit's Pauli coefficient `unitF2 U = (1/(64 m⁵)) (1/i) unitZero U` is
  invariant (for `U ≠ VP` without the regulator-fermion hypotheses: `unitF2_massScale_of_ne_VP`);
* `pauliZeroFour_massScale`, `pauliZeroLimit_massScale`: the regulated coefficient
  `F₂⁽⁴⁾(0)` and the `q² → 0⁺` limit are invariant.

With `s = 1/m` (`unitMass P`, of mass `1` and regulators `m_γ/m, Λ/m, M₁/m, M₂/m`):

* `unitF2_eq_unitMass`, `pauliZeroFour_eq_unitMass`: the value at mass `m` equals the value at
  mass `1` with the regulators divided by `m`, counterterms unchanged.

The frozen counterterm conditions scale in the same way
(`QED/TwoLoop/MassScalingCounterterm.lean`).
-/

@[expose] public section

open Complex
open scoped Real

namespace QED.TwoLoop.MassScaling

open QED.WickModel QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitsRegulated
open QED.TwoLoop.Enumeration QED.TwoLoop.PauliZeroLimit

/-- **The parameters at unit mass**: all masses divided by `m`, so that the electron mass is `1`
and the regulators are `m_γ/m, Λ/m, M₁/m, M₂/m`. -/
noncomputable def unitMass (P : Params) : Params := massScale P.m⁻¹ P

theorem unitMass_m {P : Params} (hm : P.m ≠ 0) : (unitMass P).m = 1 := inv_mul_cancel₀ hm
theorem unitMass_mγ (P : Params) : (unitMass P).mγ = P.mγ / P.m := inv_mul_eq_div _ _
theorem unitMass_Λ (P : Params) : (unitMass P).Λ = P.Λ / P.m := inv_mul_eq_div _ _
theorem unitMass_M₁ (P : Params) : (unitMass P).M₁ = P.M₁ / P.m := inv_mul_eq_div _ _
theorem unitMass_M₂ (P : Params) : (unitMass P).M₂ = P.M₂ / P.m := inv_mul_eq_div _ _

theorem atUnitCharge_massScale (s : ℝ) (P : Params) (d₁ d₂ dm d₃ : ℝ) :
    atUnitCharge (massScale s P) d₁ d₂ dm d₃ = massScale s (atUnitCharge P d₁ d₂ dm d₃) := rfl

theorem atUnitCharge_unitMass (P : Params) (d₁ d₂ dm d₃ : ℝ) :
    atUnitCharge (unitMass P) d₁ d₂ dm d₃ = unitMass (atUnitCharge P d₁ d₂ dm d₃) := rfl

/-! ### The units -/

theorem mem_openClasses_Sp : Class5.Sp ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide
theorem mem_openClasses_Sm : Class5.Sm ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide
theorem mem_openClasses_Cp : Class5.Cp ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide
theorem mem_openClasses_Cm : Class5.Cm ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide
theorem mem_openClasses_L : Class5.L ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide
theorem mem_openClasses_X : Class5.X ∈ QED.TwoLoop.ClassIntegrable.openClasses := by decide

/-- **Mass scaling of the units other than `VP`**: `unitZero U (massScale s P) = s⁵ unitZero U P`
for `s > 0`. -/
theorem unitZero_massScale_of_ne_VP {U : TwoLoopUnit} (hU : U ≠ .VP) (P : Params)
    (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {s : ℝ} (hs : 0 < s) :
    unitZero U (massScale s P) = (s : ℂ) ^ 5 * unitZero U P := by
  cases U
  · exact absurd rfl hU
  · simp only [unitZero, openZero_massScale mem_openClasses_Sp P hm hmγ hΛ hs,
      openZero_massScale mem_openClasses_Sm P hm hmγ hΛ hs, d2InZero_massScale P hm hmγ hΛ hs,
      d2OutZero_massScale P hm hmγ hΛ hs]
    ring
  · simp only [unitZero, openZero_massScale mem_openClasses_Cp P hm hmγ hΛ hs,
      openZero_massScale mem_openClasses_Cm P hm hmγ hΛ hs, d1Zero_massScale P hs]
    ring
  · simp only [unitZero, openZero_massScale mem_openClasses_L P hm hmγ hΛ hs,
      d1Zero_massScale P hs]
    ring
  · simp only [unitZero, openZero_massScale mem_openClasses_X P hm hmγ hΛ hs]

/-- **Mass scaling of the `VP` unit**: `unitZero VP (massScale s P) = s⁵ unitZero VP P`. -/
theorem unitZero_VP_massScale (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ)
    (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) {s : ℝ} (hs : 0 < s) :
    unitZero .VP (massScale s P) = (s : ℂ) ^ 5 * unitZero .VP P := by
  simp only [unitZero, vpZero_massScale P hm hmγ hΛ hM₁ hM₂ hs, d3Zero_massScale P hm hmγ hΛ hs]
  ring

theorem unitZero_massScale (U : TwoLoopUnit) (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) {s : ℝ} (hs : 0 < s) :
    unitZero U (massScale s P) = (s : ℂ) ^ 5 * unitZero U P := by
  by_cases hU : U = .VP
  · subst hU
    exact unitZero_VP_massScale P hm hmγ hΛ hM₁ hM₂ hs
  · exact unitZero_massScale_of_ne_VP hU P hm hmγ hΛ hs

theorem unitF2_massScale_of_unitZero {U : TwoLoopUnit} {P : Params} (hm : 0 < P.m) {s : ℝ}
    (hs : 0 < s) (h : unitZero U (massScale s P) = (s : ℂ) ^ 5 * unitZero U P) :
    unitF2 U (massScale s P) = unitF2 U P := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hm0 : (P.m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  simp only [unitF2, h, massScale_m]
  push_cast
  field_simp

/-- **Each unit other than `VP` is dimensionless**: `unitF2 U (massScale s P) = unitF2 U P`. -/
theorem unitF2_massScale_of_ne_VP {U : TwoLoopUnit} (hU : U ≠ .VP) (P : Params) (hm : 0 < P.m)
    (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) {s : ℝ} (hs : 0 < s) :
    unitF2 U (massScale s P) = unitF2 U P :=
  unitF2_massScale_of_unitZero hm hs (unitZero_massScale_of_ne_VP hU P hm hmγ hΛ hs)

/-- **Each unit is dimensionless**: `unitF2 U (massScale s P) = unitF2 U P` for `s > 0`. -/
theorem unitF2_massScale (U : TwoLoopUnit) (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) {s : ℝ} (hs : 0 < s) :
    unitF2 U (massScale s P) = unitF2 U P :=
  unitF2_massScale_of_unitZero hm hs (unitZero_massScale U P hm hmγ hΛ hM₁ hM₂ hs)

/-- **A unit at mass `m` equals the unit at mass `1`** with the regulators divided by `m`. -/
theorem unitF2_eq_unitMass (U : TwoLoopUnit) (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁) (hM₂ : P.m ≤ P.M₂) :
    unitF2 U P = unitF2 U (unitMass P) :=
  (unitF2_massScale U P hm hmγ hΛ hM₁ hM₂ (inv_pos.mpr hm)).symm

/-! ### The regulated coefficient -/

section Coefficient

variable (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) (hM₁ : P.m ≤ P.M₁)
  (hM₂ : P.m ≤ P.M₂) (hc₁ : 1 + P.c₁ + P.c₂ = 0)
  (hc₂ : P.m ^ 2 + P.c₁ * P.M₁ ^ 2 + P.c₂ * P.M₂ ^ 2 = 0)
include hm hmγ hΛ hM₁ hM₂ hc₁ hc₂

/-- **`F₂⁽⁴⁾(0)` is dimensionless**: `pauliZeroFour (massScale s P) d = pauliZeroFour P d` for
`s > 0`, counterterms `dᵢ` unchanged. -/
theorem pauliZeroFour_massScale {s : ℝ} (hs : 0 < s) (d₁ d₂ dm d₃ : ℝ) :
    pauliZeroFour (massScale s P) d₁ d₂ dm d₃ = pauliZeroFour P d₁ d₂ dm d₃ := by
  have hc₂' : (massScale s P).m ^ 2 + (massScale s P).c₁ * (massScale s P).M₁ ^ 2 +
      (massScale s P).c₂ * (massScale s P).M₂ ^ 2 = 0 := by
    simp only [massScale_m, massScale_c₁, massScale_c₂, massScale_M₁, massScale_M₂]
    linear_combination s ^ 2 * hc₂
  rw [pauliZeroFour_eq_sum_units (massScale s P) (mul_pos hs hm) (mul_pos hs hmγ)
      (mul_pos hs hΛ) (mul_le_mul_of_nonneg_left hM₁ hs.le)
      (mul_le_mul_of_nonneg_left hM₂ hs.le) hc₁ hc₂',
    pauliZeroFour_eq_sum_units P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [atUnitCharge_massScale]
  exact unitF2_massScale U (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ hM₁ hM₂ hs

/-- **`F₂⁽⁴⁾(0)` at mass `m` is its value at mass `1`** with the regulators divided by `m`. -/
theorem pauliZeroFour_eq_unitMass (d₁ d₂ dm d₃ : ℝ) :
    pauliZeroFour P d₁ d₂ dm d₃ = pauliZeroFour (unitMass P) d₁ d₂ dm d₃ :=
  (pauliZeroFour_massScale P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ (inv_pos.mpr hm) d₁ d₂ dm d₃).symm

/-- **The `q² → 0⁺` limit of the Pauli projection is invariant** under the mass scaling, at every
charge `e` (with the counterterms of `P` unchanged). -/
theorem pauliZeroLimit_massScale {s : ℝ} (hs : 0 < s) (e : ℝ) :
    pauliZeroLimit (massScale s P) e = pauliZeroLimit P e := by
  have hc₂' : (massScale s P).m ^ 2 + (massScale s P).c₁ * (massScale s P).M₁ ^ 2 +
      (massScale s P).c₂ * (massScale s P).M₂ ^ 2 = 0 := by
    simp only [massScale_m, massScale_c₁, massScale_c₂, massScale_M₁, massScale_M₂]
    linear_combination s ^ 2 * hc₂
  rw [pauliZeroLimit_eq_units (massScale s P) (mul_pos hs hm) (mul_pos hs hmγ) (mul_pos hs hΛ)
      (mul_le_mul_of_nonneg_left hM₁ hs.le) (mul_le_mul_of_nonneg_left hM₂ hs.le) hc₁ hc₂' e,
    pauliZeroLimit_eq_units P hm hmγ hΛ hM₁ hM₂ hc₁ hc₂ e]
  congr 1
  exact Finset.sum_congr rfl fun U _ => unitF2_massScale U P hm hmγ hΛ hM₁ hM₂ hs

end Coefficient

end QED.TwoLoop.MassScaling

end
