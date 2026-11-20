/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitLLinkDominated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K: the infrared logarithm of the vertex counterterm bracket

Helper level (no frozen statement), for the regulator links of the set (c) kernel. With
`M = M_λ(Y) = Y² + (1-Y) λ²` and the counterterm bracket `CT(λ; Y) = Y(Y² + 2Y - 2)/(2M) -
(Y/2) log M` of eq. (3.4) (`QED.TwoLoop.UnitLLink.ladderCtBracket`), the `-Y/M` part carries the
infrared logarithm: `-Y/M = -M'/(2M) - λ²/(2M)` with `∫₀¹ M'/(2M) = -log λ`. Hence

* `integral_ladderCtBracket_eq`: `∫₀¹ CT(λ) = ∫₀¹ ctReg(λ) + log λ` for `λ > 0`, with
  `ctReg = Y²(Y + 2)/(2M) - λ²/(2M) - (Y/2) log M` (`ctReg`), bounded by `4` for `λ ≤ 1`;
* **`tendsto_integral_ladderCtBracket_sub_log`**: `∫₀¹ CT(λ) - log λ → 3/2` as `λ → 0⁺`.

With the Phase 4 limit `J(λ) + ∫₀¹ CT(λ) → -1/3`
(`QED.TwoLoop.UnitLLink.tendsto_outerSoftJ_add_integral_ladderCtBracket`) this gives
**`tendsto_outerSoftJ_add_log`**: `J(λ) + log λ → -11/6`. The constants `3/2` and `11/6` are those
of the outer and inner ladder placements (`QED.ChainProof.SetCK.lOuter`,
`QED.ChainProof.SetCK.lInner`).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink

/-- The infrared-regular part of the counterterm bracket. -/
noncomputable def ctReg (lam Y : ℝ) : ℝ :=
  Y ^ 2 * (Y + 2) / (2 * ladderInnerMass 1 lam Y) - lam ^ 2 / (2 * ladderInnerMass 1 lam Y) -
    Y / 2 * log (ladderInnerMass 1 lam Y)

theorem ladderInnerMass_pos_of_pos {lam Y : ℝ} (hY : 0 < Y) (hY1 : Y ≤ 1) :
    0 < ladderInnerMass 1 lam Y := by
  unfold ladderInnerMass
  have : 0 ≤ (1 - Y) * lam ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  positivity

theorem continuous_ctReg_lam {Y : ℝ} (hY : 0 < Y) (hY1 : Y ≤ 1) :
    Continuous fun lam => ctReg lam Y := by
  have hM : ∀ lam, ladderInnerMass 1 lam Y ≠ 0 := fun lam =>
    (ladderInnerMass_pos_of_pos hY hY1).ne'
  unfold ctReg
  refine ((Continuous.div (by fun_prop) ?_ fun lam => ?_).sub
    (Continuous.div (by fun_prop) ?_ fun lam => ?_)).sub
    (continuous_const.mul (Continuous.log ?_ hM))
  · unfold ladderInnerMass; fun_prop
  · exact mul_ne_zero two_ne_zero (hM lam)
  · unfold ladderInnerMass; fun_prop
  · exact mul_ne_zero two_ne_zero (hM lam)
  · unfold ladderInnerMass; fun_prop

theorem ctReg_zero {Y : ℝ} (hY : 0 < Y) : ctReg 0 Y = (Y + 2) / 2 - Y * log Y := by
  unfold ctReg ladderInnerMass
  have hY0 := hY.ne'
  rw [show Y ^ 2 * 1 ^ 2 + (1 - Y) * 0 ^ 2 = Y ^ 2 by ring, log_pow]
  field_simp
  push_cast
  ring

theorem abs_ctReg_le {lam Y : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) 1) (hY : Y ∈ Ioc (0 : ℝ) 1) :
    |ctReg lam Y| ≤ 4 := by
  obtain ⟨hY0, hY1⟩ := hY
  obtain ⟨hl0, hl1⟩ := hlam
  set M := ladderInnerMass 1 lam Y with hM_def
  have hMY : Y ^ 2 ≤ M := by
    rw [hM_def]; unfold ladderInnerMass
    nlinarith [mul_nonneg (sub_nonneg.2 hY1) (sq_nonneg lam)]
  have hM1 : M ≤ 1 := by
    rw [hM_def]; unfold ladderInnerMass
    have : lam ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (sub_nonneg.2 hY1)]
  have hMl : 3 / 4 * lam ^ 2 ≤ M := by
    rw [hM_def]; unfold ladderInnerMass
    have : lam ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (Y - 1 / 2), mul_le_mul_of_nonneg_left this (sq_nonneg Y)]
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hMY
  have t1 : |Y ^ 2 * (Y + 2) / (2 * M)| ≤ 3 / 2 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have t2 : |lam ^ 2 / (2 * M)| ≤ 2 / 3 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have t3 : |Y / 2 * log M| ≤ 1 := by
    have hlo : 2 * log Y ≤ log M := by
      have := log_le_log (by positivity) hMY
      rw [log_pow] at this
      push_cast at this
      exact this
    have hhi : log M ≤ 0 := log_nonpos hM0.le hM1
    have hYl : |log Y * Y| < 1 := abs_log_mul_self_lt Y hY0 hY1
    rw [abs_mul, abs_of_pos (by positivity : 0 < Y / 2), abs_of_nonpos hhi]
    have : -log M ≤ -2 * log Y := by linarith
    have hneg : log Y * Y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (log_nonpos hY0.le hY1) hY0.le
    rw [abs_of_nonpos hneg] at hYl
    nlinarith
  unfold ctReg
  rw [← hM_def]
  have := abs_sub (Y ^ 2 * (Y + 2) / (2 * M) - lam ^ 2 / (2 * M)) (Y / 2 * log M)
  have := abs_sub (Y ^ 2 * (Y + 2) / (2 * M)) (lam ^ 2 / (2 * M))
  linarith

/-- `∫₀¹ (2Y - λ²)/(2 M_λ) = -log λ` for `λ > 0`. -/
theorem integral_ladderInnerMass_log_deriv {lam : ℝ} (hlam : 0 < lam) :
    ∫ Y in (0 : ℝ)..1, (2 * Y - lam ^ 2) / (2 * ladderInnerMass 1 lam Y) = -log lam := by
  have hpos : ∀ Y ∈ uIcc (0 : ℝ) 1, 0 < ladderInnerMass 1 lam Y := by
    intro Y hY
    rw [uIcc_of_le zero_le_one] at hY
    exact ladderInnerMass_pos one_pos hlam hY
  have hd : ∀ Y ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun Y => log (ladderInnerMass 1 lam Y) / 2)
      ((2 * Y - lam ^ 2) / (2 * ladderInnerMass 1 lam Y)) Y := by
    intro Y hY
    have hM := hpos Y hY
    have h1 : HasDerivAt (fun Y => ladderInnerMass 1 lam Y) (2 * Y - lam ^ 2) Y := by
      have := ((hasDerivAt_pow 2 Y).mul_const ((1 : ℝ) ^ 2)).add
        (((hasDerivAt_id' Y).const_sub 1).mul_const (lam ^ 2))
      exact this.congr_deriv (by simp; ring)
    convert (h1.log hM.ne').div_const 2 using 1
    field_simp
  have hc : ContinuousOn (fun Y => (2 * Y - lam ^ 2) / (2 * ladderInnerMass 1 lam Y))
      (uIcc 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by unfold ladderInnerMass; fun_prop) fun Y hY => ?_
    exact mul_ne_zero two_ne_zero (hpos Y hY).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)]
  unfold ladderInnerMass
  simp only [one_pow, mul_one, sub_self, zero_mul, add_zero, one_pow, sub_zero, one_mul]
  rw [show (0 : ℝ) ^ 2 + lam ^ 2 = lam ^ 2 by ring, log_pow]
  norm_num

theorem intervalIntegrable_ctReg {lam : ℝ} (hlam : 0 < lam) :
    IntervalIntegrable (ctReg lam) volume 0 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  have hpos : ∀ Y ∈ uIcc (0 : ℝ) 1, ladderInnerMass 1 lam Y ≠ 0 := by
    intro Y hY
    rw [uIcc_of_le zero_le_one] at hY
    exact (ladderInnerMass_pos one_pos hlam hY).ne'
  unfold ctReg
  refine ((ContinuousOn.div (by fun_prop) (by unfold ladderInnerMass; fun_prop)
    fun Y hY => mul_ne_zero two_ne_zero (hpos Y hY)).sub
    (ContinuousOn.div (by fun_prop) (by unfold ladderInnerMass; fun_prop)
      fun Y hY => mul_ne_zero two_ne_zero (hpos Y hY))).sub
    ((continuousOn_id.div_const 2).mul
      (ContinuousOn.log (by unfold ladderInnerMass; fun_prop) hpos))

/-- `∫₀¹ CT(λ) = ∫₀¹ ctReg(λ) + log λ` for `λ > 0`. -/
theorem integral_ladderCtBracket_eq {lam : ℝ} (hlam : 0 < lam) :
    ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y = (∫ Y in (0 : ℝ)..1, ctReg lam Y) + log lam := by
  have hpos : ∀ Y ∈ uIcc (0 : ℝ) 1, ladderInnerMass 1 lam Y ≠ 0 := by
    intro Y hY
    rw [uIcc_of_le zero_le_one] at hY
    exact (ladderInnerMass_pos one_pos hlam hY).ne'
  have hi : IntervalIntegrable (fun Y => (2 * Y - lam ^ 2) / (2 * ladderInnerMass 1 lam Y))
      volume 0 1 :=
    (ContinuousOn.div (by fun_prop) (by unfold ladderInnerMass; fun_prop)
      fun Y hY => mul_ne_zero two_ne_zero (hpos Y hY)).intervalIntegrable
  have e : ∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y =
      ∫ Y in (0 : ℝ)..1, (ctReg lam Y - (2 * Y - lam ^ 2) / (2 * ladderInnerMass 1 lam Y)) := by
    refine intervalIntegral.integral_congr fun Y hY => ?_
    have hM := hpos Y hY
    simp only [ladderCtBracket, ctReg]
    field_simp
    ring
  rw [e, intervalIntegral.integral_sub (intervalIntegrable_ctReg hlam) hi,
    integral_ladderInnerMass_log_deriv hlam]
  ring

theorem integral_ctReg_zero : ∫ Y in (0 : ℝ)..1, ctReg 0 Y = 3 / 2 := by
  have hp : IntervalIntegrable (fun Y : ℝ => (Y + 2) / 2) volume 0 1 :=
    (by fun_prop : Continuous fun Y : ℝ => (Y + 2) / 2).intervalIntegrable 0 1
  have e : ∫ Y in (0 : ℝ)..1, ctReg 0 Y = ∫ Y in (0 : ℝ)..1, ((Y + 2) / 2 - Y * log Y) := by
    refine intervalIntegral.integral_congr_ae ?_
    refine Eventually.of_forall fun Y hY => ?_
    rw [uIoc_of_le zero_le_one] at hY
    exact ctReg_zero hY.1
  rw [e, intervalIntegral.integral_sub hp intervalIntegrable_and_integral_mul_log.1,
    intervalIntegrable_and_integral_mul_log.2]
  have : ∫ Y in (0 : ℝ)..1, (Y + 2) / 2 = 5 / 4 := by
    simp only [intervalIntegral.integral_div, intervalIntegral.integral_add
      intervalIntegral.intervalIntegrable_id intervalIntegrable_const, integral_id,
      intervalIntegral.integral_const]
    norm_num
  rw [this]
  norm_num

theorem tendsto_integral_ctReg :
    Tendsto (fun lam => ∫ Y in (0 : ℝ)..1, ctReg lam Y) (𝓝[>] 0) (𝓝 (3 / 2)) := by
  rw [← integral_ctReg_zero]
  have hev : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 4) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [hev] with lam hl
    exact (intervalIntegrable_ctReg hl.1).def'.aestronglyMeasurable
  · filter_upwards [hev] with lam hl
    refine Eventually.of_forall fun Y hY => ?_
    rw [uIoc_of_le zero_le_one] at hY
    rw [Real.norm_eq_abs]; exact abs_ctReg_le hl hY
  · refine Eventually.of_forall fun Y hY => ?_
    rw [uIoc_of_le zero_le_one] at hY
    exact ((continuous_ctReg_lam hY.1 hY.2).tendsto 0).mono_left nhdsWithin_le_nhds

/-- **`∫₀¹ CT(λ) - log λ → 3/2` as `λ → 0⁺`.** -/
theorem tendsto_integral_ladderCtBracket_sub_log :
    Tendsto (fun lam => (∫ Y in (0 : ℝ)..1, ladderCtBracket lam Y) - log lam) (𝓝[>] 0)
      (𝓝 (3 / 2)) := by
  refine tendsto_integral_ctReg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with lam (hl : 0 < lam)
  rw [integral_ladderCtBracket_eq hl]
  ring

/-- **`J(λ) + log λ → -11/6` as `λ → 0⁺`.** -/
theorem tendsto_outerSoftJ_add_log :
    Tendsto (fun lam => outerSoftJ lam + log lam) (𝓝[>] 0) (𝓝 (-11 / 6)) := by
  have := tendsto_outerSoftJ_add_integral_ladderCtBracket.sub
    tendsto_integral_ladderCtBracket_sub_log
  refine (this.congr fun lam => ?_).trans (by norm_num)
  ring

end QED.ChainProof.SetCK
