/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitsRegulated
public import QED.TwoLoop.WardIdentityParametric
public import QED.OneLoop.ChargeCondition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The ladder unit L: its counterterm half in the variables of `docs/TWO-LOOP-UNITS.md`

Section 8 of `docs/TWO-LOOP-UNITS.md`, stage (1) of the L link, counterterm half. The model's
L unit is `unitF2 .L P = (1/(64 m⁵)) (1/i) (openZero .L P + d1Zero P)`
(`QED.TwoLoop.UnitsRegulated.unitF2`); it splits into the ladder graph and the `δ₁` insertion at
the external vertex (`unitF2_L_eq`). This file rewrites the `δ₁` half exactly in the variables of
sections 3.2 and 3.3 of the document: with the inner mass function
`M_μ(Y) = Y² m² + (1 - Y) μ²` (`ladderInnerMass`, the doc's `M_μ` at `m = 1`),

* `F₂⁽²⁾(μ) = ∫₀¹ Y² (1 - Y) m² / M_μ(Y) dY` (`oneLoopF2`), and the one-loop Pauli integral at
  `q² = 0` is `B(0) = 2 (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))` (`oneLoopPauliZero_eq`);
* `δ₁ = -∫₀¹ [Y(Y² + 2Y - 2)/2 · m² (1/M_{m_γ} - 1/M_Λ) - (Y/2) log(M_{m_γ}/M_Λ)] dY`
  (`ladderDeltaOne`, eq. of section 3.2), and the counterterm `d₁` fixed by the frozen charge
  condition (K₀) at charge `1` satisfies `4π² d₁ = δ₁` (`four_pi_sq_mul_eq_ladderDeltaOne`);
* **the counterterm half of the L unit**, normalized to the coefficient of `r² = (α/π)²`
  (the factor `16π⁴`, since `r² = e⁴/(16π⁴)`):
  `16π⁴ · (1/(64 m⁵)) (1/i) d1Zero P₁ = δ₁ · (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))`
  (`sixteen_pi_pow_four_mul_ctHalf`), with `P₁ = atUnitCharge P d₁ d₂ d_m d₃`.

This is the term `δ₁ F₂⁽²⁾` of the unit table of the document (at finite `Λ`, with the outer
Pauli–Villars subtraction `- δ₁ F₂⁽²⁾(Λ)` still present). The ladder-graph half
`openZero .L` is not rewritten here: it needs the Dirac algebra of the class numerator
(`QED.TwoLoop.PauliZeroExplicit.openNum`), see `QED/TwoLoop/UnitLLinkLimit.lean` for the status
of the remaining stages.
-/

@[expose] public section

open Complex MeasureTheory Set
open scoped Real

namespace QED.TwoLoop.UnitLLink

open QED.WickModel QED.TwoLoop.PauliZeroExplicit QED.TwoLoop.UnitsRegulated
open QED.OneLoop.VertexLimit QED.Integration

/-! ### The variables of section 3 -/

/-- The inner mass function `M_μ(Y) = Y² m² + (1 - Y) μ²` of the document (eq. (2.1), with the
mass `m` restored); `M_{m_γ}` is the on-shell `V` of the inner vertex subgraph. -/
def ladderInnerMass (m μ Y : ℝ) : ℝ := Y ^ 2 * m ^ 2 + (1 - Y) * μ ^ 2

/-- **The one-loop Pauli coefficient** `F₂⁽²⁾(μ) = ∫₀¹ Y² (1 - Y) m² / M_μ(Y) dY` (coefficient of
`r`, photon mass `μ`; the document's `F₂⁽²⁾(λ)` at `m = 1`). -/
noncomputable def oneLoopF2 (m μ : ℝ) : ℝ :=
  ∫ Y in (0 : ℝ)..1, Y ^ 2 * (1 - Y) * m ^ 2 / ladderInnerMass m μ Y

/-- **The on-shell vertex counterterm in the inner parameter** (section 3.2 of the document,
coefficient of `r`):
`δ₁ = -∫₀¹ [Y(Y² + 2Y - 2)/2 · m² (1/M_{m_γ} - 1/M_Λ) - (Y/2) log(M_{m_γ}/M_Λ)] dY`. -/
noncomputable def ladderDeltaOne (m mγ Λ : ℝ) : ℝ :=
  -∫ Y in (0 : ℝ)..1, (Y * (Y ^ 2 + 2 * Y - 2) / 2 *
      (m ^ 2 / ladderInnerMass m mγ Y - m ^ 2 / ladderInnerMass m Λ Y) -
    Y / 2 * Real.log (ladderInnerMass m mγ Y / ladderInnerMass m Λ Y))

theorem ladderInnerMass_pos {m μ Y : ℝ} (hm : 0 < m) (hμ : 0 < μ) (hY : Y ∈ Icc (0 : ℝ) 1) :
    0 < ladderInnerMass m μ Y := by
  unfold ladderInnerMass
  rcases eq_or_lt_of_le hY.2 with h1 | h1
  · subst h1; simp; positivity
  · have : 0 < 1 - Y := by linarith
    have : 0 ≤ Y ^ 2 * m ^ 2 := by positivity
    have : 0 < (1 - Y) * μ ^ 2 := by positivity
    linarith

theorem continuousOn_oneLoopF2_integrand {m μ : ℝ} (hm : 0 < m) (hμ : 0 < μ) :
    ContinuousOn (fun Y => Y ^ 2 * (1 - Y) * m ^ 2 / ladderInnerMass m μ Y) (Icc 0 1) := by
  refine ContinuousOn.div (by fun_prop) (by unfold ladderInnerMass; fun_prop) fun Y hY => ?_
  exact (ladderInnerMass_pos hm hμ hY).ne'

theorem intervalIntegrable_oneLoopF2_integrand {m μ : ℝ} (hm : 0 < m) (hμ : 0 < μ) :
    IntervalIntegrable (fun Y => Y ^ 2 * (1 - Y) * m ^ 2 / ladderInnerMass m μ Y) volume 0 1 :=
  (continuousOn_oneLoopF2_integrand hm hμ).intervalIntegrable_of_Icc zero_le_one

/-! ### The one-loop Pauli integral at `q² = 0` -/

/-- **`B(0) = 2 (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))`**: the one-loop Pauli integral of the `δ₁` class value in
the variables of the document. -/
theorem oneLoopPauliZero_eq (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ) (hΛ : 0 < P.Λ) :
    oneLoopPauliZero P = 2 * (oneLoopF2 P.m P.mγ - oneLoopF2 P.m P.Λ) := by
  set g : ℝ → ℝ := fun y => 2 * y * ((1 - y) - (1 - y) ^ 2) * P.m ^ 2 *
    (((1 - y) * P.mγ ^ 2 + y ^ 2 * P.m ^ 2)⁻¹ - ((1 - y) * P.Λ ^ 2 + y ^ 2 * P.m ^ 2)⁻¹) with hg
  have h : (fun z => pauliIntegrand P.m (P.mγ, P.Λ, 0) z) = fun z : ℝ × ℝ => g z.2 := by
    funext z
    simp only [hg, pauliIntegrand, mul_zero, add_zero]
  have h1 : oneLoopPauliZero P = ∫ y in (0 : ℝ)..1, g y := by
    rw [oneLoopPauliZero, h, feynmanMeasure, integral_fun_snd g,
      intervalIntegral.integral_of_le zero_le_one]
    simp [Measure.real]
  rw [h1, oneLoopF2, oneLoopF2, ← intervalIntegral.integral_sub
    (intervalIntegrable_oneLoopF2_integrand hm hmγ) (intervalIntegrable_oneLoopF2_integrand hm hΛ),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [uIcc_of_le zero_le_one] at hy
  have h1 := ladderInnerMass_pos hm hmγ hy
  have h2 := ladderInnerMass_pos hm hΛ hy
  simp only [ladderInnerMass] at h1 h2
  have h1' : (1 - y) * P.mγ ^ 2 + y ^ 2 * P.m ^ 2 ≠ 0 := by linarith
  have h2' : (1 - y) * P.Λ ^ 2 + y ^ 2 * P.m ^ 2 ≠ 0 := by linarith
  simp only [hg, ladderInnerMass]
  field_simp
  ring

/-! ### The counterterm from the charge condition -/

/-- **The counterterm fixed by the charge condition, in the inner parameter**: if `d₁` satisfies
the frozen charge condition (K₀) at charge `1`, then `4π² d₁ = δ₁` of section 3.2. -/
theorem four_pi_sq_mul_eq_ladderDeltaOne {d₁ m mγ Λ : ℝ} (hm : 0 < m) (hmγ : 0 < mγ)
    (hΛ : 0 < Λ) (hch : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) m mγ Λ hm hmγ hΛ) :
    4 * π ^ 2 * d₁ = ladderDeltaOne m mγ Λ := by
  have hZ := eq_chargeZ_of_isChargeNormalized one_ne_zero hm hmγ hΛ hch
  have hd : d₁ = -chargeA0 1 m mγ Λ := by rw [chargeZ] at hZ; linarith
  have hS : ∀ M y, QED.WickModel.selfEnergyFeynmanMass m M (-m ^ 2) y =
      ladderInnerMass m M y := fun M y => by
    unfold QED.WickModel.selfEnergyFeynmanMass ladderInnerMass; ring
  rw [hd, chargeA0, QED.TwoLoop.Ward.integral_formIntegrandAq_zero, ladderDeltaOne]
  simp only [hS]
  have e : ∀ y : ℝ, 2 * y * (Real.log (ladderInnerMass m Λ y / ladderInnerMass m mγ y) +
      1 / 2 * ((ladderInnerMass m mγ y)⁻¹ - (ladderInnerMass m Λ y)⁻¹) *
        (2 * ((1 - 4 * (1 - y) + (1 - y) ^ 2) * m ^ 2))) =
      4 * (y * (y ^ 2 + 2 * y - 2) / 2 *
        (m ^ 2 / ladderInnerMass m mγ y - m ^ 2 / ladderInnerMass m Λ y) -
        y / 2 * Real.log (ladderInnerMass m mγ y / ladderInnerMass m Λ y)) := fun y => by
    have hl : Real.log (ladderInnerMass m Λ y / ladderInnerMass m mγ y) =
        -Real.log (ladderInnerMass m mγ y / ladderInnerMass m Λ y) := by
      rw [← Real.log_inv, inv_div]
    rw [hl]
    simp only [div_eq_mul_inv]
    ring
  simp only [e]
  rw [intervalIntegral.integral_const_mul]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have key : ∀ I : ℝ, 4 * π ^ 2 * -((1 : ℝ) ^ 2 / (16 * π ^ 2) * (4 * I)) = -I := fun I => by
    field_simp
    ring
  exact key _

/-! ### The L unit and its counterterm half -/

/-- The ladder-graph half of the L unit: `(1/(64 m⁵)) (1/i) openZero .L P`. -/
noncomputable def graphHalf (P : Params) : ℂ :=
  1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * openZero .L P)

/-- The counterterm half of the L unit: `(1/(64 m⁵)) (1/i) d1Zero P`. -/
noncomputable def ctHalf (P : Params) : ℂ :=
  1 / (64 * (P.m : ℂ) ^ 5) * ((1 / I) * d1Zero P)

/-- **The L unit is the ladder graph plus the `δ₁` insertion at the external vertex.** -/
theorem unitF2_L_eq (P : Params) : unitF2 .L P = graphHalf P + ctHalf P := by
  simp only [unitF2, unitZero, graphHalf, ctHalf]
  ring

/-- The counterterm half is real: `δ₁ e³ B(0) / (8π²)`. -/
theorem ctHalf_eq (P : Params) (hm : 0 < P.m) :
    ctHalf P = ((P.δ₁ * P.e ^ 3 / (8 * π ^ 2) * oneLoopPauliZero P : ℝ) : ℂ) := by
  have hm' : (P.m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [ctHalf, d1Zero]
  push_cast
  field_simp
  ring

/-- **The counterterm half of the L unit in the variables of the document**, normalized to the
coefficient of `r² = (α/π)²`: at charge `1` with the counterterm `d₁` fixed by the frozen charge
condition, `16π⁴ · (1/(64 m⁵)) (1/i) d1Zero P₁ = δ₁ · (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))`. -/
theorem sixteen_pi_pow_four_mul_ctHalf (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {d₁ d₂ dm d₃ : ℝ}
    (hch : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ) :
    16 * (π : ℂ) ^ 4 * ctHalf (atUnitCharge P d₁ d₂ dm d₃) =
      ((ladderDeltaOne P.m P.mγ P.Λ * (oneLoopF2 P.m P.mγ - oneLoopF2 P.m P.Λ) : ℝ) : ℂ) := by
  have hB := oneLoopPauliZero_eq (atUnitCharge P d₁ d₂ dm d₃) hm hmγ hΛ
  rw [ctHalf_eq (atUnitCharge P d₁ d₂ dm d₃) hm, hB,
    ← four_pi_sq_mul_eq_ladderDeltaOne hm hmγ hΛ hch]
  simp only [atUnitCharge]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- **Stage (1), counterterm half, assembled**: the model's L unit at charge `1`, normalized to the
coefficient of `r²`, is `16π⁴` times the ladder-graph half plus `δ₁ (F₂⁽²⁾(m_γ) - F₂⁽²⁾(Λ))`. -/
theorem sixteen_pi_pow_four_mul_unitF2_L (P : Params) (hm : 0 < P.m) (hmγ : 0 < P.mγ)
    (hΛ : 0 < P.Λ) {d₁ d₂ dm d₃ : ℝ}
    (hch : QED.OneLoop.IsChargeNormalized 1 (1 + d₁) P.m P.mγ P.Λ hm hmγ hΛ) :
    16 * (π : ℂ) ^ 4 * unitF2 .L (atUnitCharge P d₁ d₂ dm d₃) =
      16 * (π : ℂ) ^ 4 * graphHalf (atUnitCharge P d₁ d₂ dm d₃) +
        ((ladderDeltaOne P.m P.mγ P.Λ * (oneLoopF2 P.m P.mγ - oneLoopF2 P.m P.Λ) : ℝ) : ℂ) := by
  rw [unitF2_L_eq, mul_add, sixteen_pi_pow_four_mul_ctHalf P hm hmγ hΛ hch]

end QED.TwoLoop.UnitLLink

end
