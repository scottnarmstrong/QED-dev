/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXKernelDeriv
public import QED.TwoLoop.UnitXKernelLimits
public import QED.TwoLoop.UnitC
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ExtendFrom

/-!
# The one-dimensional integral of the crossed-ladder unit (helper level, O2-25)

Section 4.5 of `docs/TWO-LOOP-UNITS.md` reduces the crossed-ladder unit X to the one-dimensional
integral `X = ∫₀¹ K_X` (eq. (4.7)) with an explicit kernel `K_X` (`crossedKernel`) in the
functions `Li₂ Y`, `D(Y) = Li₂ (1 - 2Y) - Li₂ (2Y - 1)` (`crossedD`), `log Y` and `log (1 - Y)`.
This file evaluates that integral.

## Main statements

* `QED.TwoLoop.Units.intervalIntegrable_crossedKernel`: `K_X` is integrable on `[0, 1]`.
* `QED.TwoLoop.Units.intervalIntegrable_and_integral_crossedKernel`:
  `∫₀¹ K_X = 1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)`.
* `QED.TwoLoop.Units.crossedUnit_value`: the same value of `∫₀¹ K_X`, BMR-I's value of the
  crossed-ladder unit (row e) on p. 852), as stated in eq. (4.12).

Here `ζ(2) = π²/6` and `ζ(3) = zeta3`.

## Proof

By eq. (4.8), `K_X = G' + p + K_m` on `(0, 1) \ {1/2}` (`hasDerivAt_crossedBoundary`), with the
boundary values `G(0⁺) = 17/24 + ζ(2)/4`, `G(1⁻) = 1/3 + ζ(2)/12` of eq. (4.10)
(`tendsto_crossedBoundary_zero`, `tendsto_crossedBoundary_one`). The fundamental theorem of
calculus on `[0, 1/2]` and `[1/2, 1]` gives
`∫₀¹ K_X = G(1⁻) - G(0⁺) + ∫₀¹ p + ∫₀¹ K_m`, with `∫₀¹ p = 13/24 + 7 ζ(2)/4`
(`intervalIntegrable_and_integral_crossedPoly`) and `∫₀¹ K_m` from the eight master integrals of
`QED.TwoLoop.UnitX` (`intervalIntegrable_and_integral_crossedMasterKernel`).

Integrability: `K_X` equals `crossedKernelReg - log² Y/4 - (7/8) log Y - log (1 - Y)/8` minus
`1/8` times the integrand of `M₈` (`crossedKernel_eq_reg`). The function `crossedKernelReg` is
continuous on `(0, 1)` with finite limits at both ends (`QED.TwoLoop.UnitXKernelLimits`), hence
integrable; the other terms are integrable.

**Scope.** Helper level: this file evaluates the explicit one-dimensional integral `∫₀¹ K_X`. Not
proved here: the representation (4.4) of X and its link to the model (section 8 of the document),
and the `ξ`-integration giving `K_X` (eq. (4.7)) with the identities (4.6). Those steps are derived
in exact rational arithmetic and checked numerically (mode `crossedexact` of
`scripts/numerics/two_loop_unit_integrals.py`), not proved.
-/

public section

open Real MeasureTheory Set Filter Topology QED.Polylog

namespace QED.TwoLoop.Units

/-! ### Integrability of `K_X` -/

/-- `K_X` differs from its regular part by multiples of `log² Y`, `log Y`, `log (1 - Y)` and the
integrand of `M₈`. -/
theorem crossedKernel_eq_reg {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hh : Y ≠ 1 / 2) :
    crossedKernel Y = crossedKernelReg Y - log Y ^ 2 / 4 - 7 / 8 * log Y - log (1 - Y) / 8 -
      1 / 8 * ((log Y - log (1 - Y)) / (2 * Y - 1)) := by
  have h0 : Y ≠ 0 := hY.1.ne'
  have h1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have h2 : 2 * Y - 1 ≠ 0 := fun h => hh (by linarith)
  unfold crossedKernel crossedKernelReg
  field_simp
  ring

theorem continuousOn_crossedKernelReg : ContinuousOn crossedKernelReg (Ioo 0 1) := by
  intro Y hY
  refine ContinuousAt.continuousWithinAt ?_
  have h0 : Y ≠ 0 := hY.1.ne'
  have h1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have hL : ContinuousAt Li₂ Y :=
    continuousOn_Li₂.continuousAt (Icc_mem_nhds (by linarith [hY.1]) hY.2)
  have hD : ContinuousAt crossedD Y := continuousOn_crossedD.continuousAt (Icc_mem_nhds hY.1 hY.2)
  have ha : ContinuousAt log Y := continuousAt_log h0
  have hb : ContinuousAt (fun Y : ℝ => log (1 - Y)) Y :=
    (by fun_prop : ContinuousAt (fun y : ℝ => 1 - y) Y).log (by linarith [hY.2])
  unfold crossedKernelReg crossedRho
  fun_prop (disch := simp [h0, h1])

theorem intervalIntegrable_crossedKernelReg : IntervalIntegrable crossedKernelReg volume 0 1 := by
  have hc := continuousOn_crossedKernelReg
  have hG := continuousOn_Icc_extendFrom_Ioo hc tendsto_crossedKernelReg_zero
    tendsto_crossedKernelReg_one
  refine (hG.intervalIntegrable_of_Icc zero_le_one).congr_uIoo fun Y hY => ?_
  rw [uIoo_of_le zero_le_one] at hY
  exact extendFrom_extends hc Y hY

theorem intervalIntegrable_log_sq_unit :
    IntervalIntegrable (fun Y : ℝ => log Y ^ 2) volume 0 1 := by
  refine (intervalIntegrable_mul_unit intervalIntegrable_and_integral_log_sq_div_sub_one.1
    (g := fun Y => Y - 1) (by fun_prop)).congr_uIoo fun Y hY => ?_
  rw [uIoo_of_le zero_le_one] at hY
  have : Y - 1 ≠ 0 := by linarith [hY.2]
  field_simp

theorem intervalIntegrable_log_one_sub_unit :
    IntervalIntegrable (fun Y : ℝ => log (1 - Y)) volume 0 1 := by
  refine (intervalIntegrable_mul_unit intervalIntegrable_and_integral_log_one_sub_div.1
    (g := fun Y => Y) (by fun_prop)).congr_uIoo fun Y hY => ?_
  rw [uIoo_of_le zero_le_one] at hY
  have : Y ≠ 0 := hY.1.ne'
  field_simp

/-- **`K_X` is integrable on `[0, 1]`.** -/
theorem intervalIntegrable_crossedKernel : IntervalIntegrable crossedKernel volume 0 1 := by
  have hg : IntervalIntegrable (fun Y => crossedKernelReg Y - log Y ^ 2 / 4 - 7 / 8 * log Y -
      log (1 - Y) / 8 - 1 / 8 * ((log Y - log (1 - Y)) / (2 * Y - 1))) volume 0 1 :=
    (((intervalIntegrable_crossedKernelReg.sub (intervalIntegrable_log_sq_unit.div_const 4)).sub
      ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).const_mul (7 / 8))).sub
      (intervalIntegrable_log_one_sub_unit.div_const 8)).sub
      (intervalIntegrable_and_integral_log_sub_log_div.1.const_mul (1 / 8))
  have h₁ : IntervalIntegrable crossedKernel volume 0 (1 / 2) := by
    refine (hg.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le zero_le_one]; norm_num)
      (by rw [uIcc_of_le zero_le_one]; norm_num))).congr_uIoo fun Y hY => ?_
    rw [uIoo_of_le (by norm_num)] at hY
    exact (crossedKernel_eq_reg ⟨hY.1, by linarith [hY.2]⟩ hY.2.ne).symm
  have h₂ : IntervalIntegrable crossedKernel volume (1 / 2) 1 := by
    refine (hg.mono_set (uIcc_subset_uIcc (by rw [uIcc_of_le zero_le_one]; norm_num)
      (by rw [uIcc_of_le zero_le_one]; norm_num))).congr_uIoo
      fun Y hY => ?_
    rw [uIoo_of_le (by norm_num)] at hY
    exact (crossedKernel_eq_reg ⟨by linarith [hY.1], hY.2⟩ hY.1.ne').symm
  exact h₁.trans h₂

/-! ### `∫₀¹ p` and `∫₀¹ K_m` -/

/-- `∫₀¹ p = 13/24 + 7 ζ(2)/4`. -/
theorem intervalIntegrable_and_integral_crossedPoly :
    IntervalIntegrable crossedPoly volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, crossedPoly Y = 13 / 24 + 7 * π ^ 2 / 24 := by
  have hc : Continuous crossedPoly := by
    unfold crossedPoly
    fun_prop
  refine ⟨hc.intervalIntegrable 0 1, ?_⟩
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun Y => (30 + 19 * (π ^ 2 / 6)) / 24 * Y + (46 * (π ^ 2 / 6) - 34) / 48 * Y ^ 2)
      (crossedPoly x) x := by
    intro x _
    have := ((hasDerivAt_id' x).const_mul ((30 + 19 * (π ^ 2 / 6)) / 24)).add
      ((hasDerivAt_pow 2 x).const_mul ((46 * (π ^ 2 / 6) - 34) / 48))
    refine this.congr_deriv ?_
    unfold crossedPoly
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)]
  ring

/-- `∫₀¹ K_m`, from the eight masters of `QED.TwoLoop.UnitX`. -/
theorem intervalIntegrable_and_integral_crossedMasterKernel :
    IntervalIntegrable crossedMasterKernel volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, crossedMasterKernel Y =
        5 / 6 * (zeta3 + zeta3 + (-(π ^ 2 / 2) * log 2 - 7 / 4 * zeta3) + 2 * (2 * zeta3) +
            (-(π ^ 2 / 2) * log 2 - 7 / 4 * zeta3)) +
          5 / 12 * (-2 * zeta3) + 5 / 12 * (π ^ 2 / 6) + 11 / 6 * (-(π ^ 2 / 6)) +
          4 / 3 * (π ^ 2 / 4) := by
  have m1 := intervalIntegrable_and_integral_Li₂_div
  have m2 := intervalIntegrable_and_integral_log_mul_log_one_sub_div
  have m3 := intervalIntegrable_and_integral_crossedD_sub_div
  have m4 := unitIntegral_const_mul intervalIntegrable_and_integral_Li₂_sub_div_sub_one 2
  have m3' := intervalIntegrable_and_integral_crossedD_add_div_sub_one
  have m5 := unitIntegral_const_mul intervalIntegrable_and_integral_log_sq_div_sub_one (5 / 12)
  have m6 := unitIntegral_const_mul intervalIntegrable_and_integral_log_div_sub_one (5 / 12)
  have m7 := unitIntegral_const_mul intervalIntegrable_and_integral_log_one_sub_div (11 / 6)
  have m8 := unitIntegral_const_mul intervalIntegrable_and_integral_log_sub_log_div (4 / 3)
  exact unitIntegral_congr (unitIntegral_add (unitIntegral_add (unitIntegral_add (unitIntegral_add
    (unitIntegral_const_mul (unitIntegral_add (unitIntegral_add (unitIntegral_add
      (unitIntegral_add m1 m2) m3) m4) m3') (5 / 6)) m5) m6) m7) m8) (fun Y _ => rfl) rfl

/-! ### The value -/

theorem continuousAt_crossedBoundary_half : ContinuousAt crossedBoundary (1 / 2) := by
  have hL : ContinuousAt Li₂ (1 / 2) :=
    continuousOn_Li₂.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have hD : ContinuousAt crossedD (1 / 2) :=
    continuousOn_crossedD.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have ha : ContinuousAt log (1 / 2) := continuousAt_log (by norm_num)
  have hb : ContinuousAt (fun Y : ℝ => log (1 - Y)) (1 / 2) :=
    (continuousAt_log (by norm_num)).comp (by fun_prop)
  unfold crossedBoundary
  fun_prop (disch := norm_num)

/-- **`∫₀¹ K_X = 1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)`**, with integrability. -/
theorem intervalIntegrable_and_integral_crossedKernel :
    IntervalIntegrable crossedKernel volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, crossedKernel Y =
        1 / 6 - 5 * (π ^ 2 / 6) * log 2 + 13 / 6 * (π ^ 2 / 6) + 5 / 4 * zeta3 := by
  have hp := intervalIntegrable_and_integral_crossedPoly
  have hKm := intervalIntegrable_and_integral_crossedMasterKernel
  have hdiff : IntervalIntegrable
      (fun Y => crossedKernel Y - crossedPoly Y - crossedMasterKernel Y) volume 0 1 :=
    (intervalIntegrable_crossedKernel.sub hp.1).sub hKm.1
  have hsub : ∀ c d : ℝ, c ∈ Icc (0 : ℝ) 1 → d ∈ Icc (0 : ℝ) 1 → IntervalIntegrable
      (fun Y => crossedKernel Y - crossedPoly Y - crossedMasterKernel Y) volume c d :=
    fun c d hc hd => hdiff.mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le zero_le_one])
      (by rwa [uIcc_of_le zero_le_one]))
  have hhalf := continuousAt_crossedBoundary_half
  have e₁ := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0 : ℝ) < 1 / 2)
    (fun Y hY => hasDerivAt_crossedBoundary ⟨hY.1, by linarith [hY.2]⟩ hY.2.ne)
    (hsub 0 (1 / 2) (by norm_num) (by norm_num)) tendsto_crossedBoundary_zero
    (hhalf.tendsto.mono_left nhdsWithin_le_nhds)
  have e₂ := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (1 / 2 : ℝ) < 1)
    (fun Y hY => hasDerivAt_crossedBoundary ⟨by linarith [hY.1], hY.2⟩ hY.1.ne')
    (hsub (1 / 2) 1 (by norm_num) (by norm_num)) (hhalf.tendsto.mono_left nhdsWithin_le_nhds)
    tendsto_crossedBoundary_one
  have hD : IntervalIntegrable
      (fun Y => crossedKernel Y - crossedPoly Y - crossedMasterKernel Y) volume 0 1 ∧
      ∫ Y in (0 : ℝ)..1, crossedKernel Y - crossedPoly Y - crossedMasterKernel Y =
        (1 / 3 + π ^ 2 / 72) - (17 / 24 + π ^ 2 / 24) := by
    refine ⟨hdiff, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hsub 0 (1 / 2) (by norm_num)
      (by norm_num)) (hsub (1 / 2) 1 (by norm_num) (by norm_num)), e₁, e₂]
    ring
  exact unitIntegral_congr (unitIntegral_add (unitIntegral_add hD hp) hKm) (fun Y _ => by ring)
    (by ring)

/-- **The crossed-ladder unit.** `X = ∫₀¹ K_X = 1/6 - 5 ζ(2) log 2 + (13/6) ζ(2) + (5/4) ζ(3)`,
BMR-I p. 852 row e) (eqs. (4.7) and (4.12) of the document). -/
theorem crossedUnit_value :
    ∫ Y in (0 : ℝ)..1, crossedKernel Y =
      1 / 6 - 5 * (π ^ 2 / 6) * log 2 + 13 / 6 * (π ^ 2 / 6) + 5 / 4 * zeta3 :=
  intervalIntegrable_and_integral_crossedKernel.2

end QED.TwoLoop.Units
