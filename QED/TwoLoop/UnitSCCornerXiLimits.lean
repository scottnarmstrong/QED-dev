/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitSCCornerXiEnds
public import QED.TwoLoop.UnitSCCornerXiDeriv
public import QED.TwoLoop.UnitXXiLimits
import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The endpoint limits of the corner `ξ`-antiderivative

For `Y ∈ (0, 1)`, `Y ≠ 1/2`, as in `QED.TwoLoop.UnitXXiLimits`: `tendsto_cxiF_zero`,
`tendsto_cxiF_one` and `continuousAt_cxiF` (including the removable point `ξ = 1/2`).
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.TwoLoop.UnitSCCornerXi

open QED.TwoLoop.UnitXClose QED.TwoLoop.UnitXXi QED.TwoLoop.UnitSCCorner

theorem continuousOn_cxiDil {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) : ContinuousOn (cxiDil Y)
    (Icc 0 1) := by
  obtain ⟨hY0, hY1⟩ := hY
  have hY1' : 0 < 1 - Y := by linarith
  have hL : ∀ {g : ℝ → ℝ}, ContinuousOn g (Icc 0 1) → MapsTo g (Icc 0 1) (Icc (-1) 1) →
      ContinuousOn (fun ξ => Li₂ (g ξ)) (Icc 0 1) := fun hg hm => continuousOn_Li₂.comp hg hm
  have hD : ∀ {g : ℝ → ℝ}, ContinuousOn g (Icc 0 1) → MapsTo g (Icc 0 1) (Iio 1) →
      ContinuousOn (fun ξ => dilogI (g ξ)) (Icc 0 1) := fun hg hm => continuousOn_dilogI.comp hg hm
  have h1 := hL (g := fun ξ => Y * ξ) (by fun_prop) (fun ξ hξ => ⟨by nlinarith [hξ.1], by
    nlinarith [hξ.2]⟩)
  have h2 := hL (g := fun ξ => 1 - ξ) (by fun_prop) (fun ξ hξ => ⟨by linarith [hξ.2], by
    linarith [hξ.1]⟩)
  have h3 := hD (g := fun ξ => -(Y * (1 - ξ) / (1 - Y))) (by fun_prop (disch := exact hY1'.ne'))
    (fun ξ hξ => by
      have : 0 ≤ Y * (1 - ξ) / (1 - Y) := div_nonneg (mul_nonneg hY0.le (by linarith [hξ.2]))
        hY1'.le
      show -(Y * (1 - ξ) / (1 - Y)) < 1
      linarith)
  have h4 := hD (g := fun ξ => (1 - 2 * Y) * (1 - ξ) / (1 - Y))
    (by fun_prop (disch := exact hY1'.ne')) (fun ξ hξ => by
      show (1 - 2 * Y) * (1 - ξ) / (1 - Y) < 1
      rw [div_lt_one hY1']
      rcases eq_or_lt_of_le hξ.2 with h | h
      · rw [h]; linarith
      · nlinarith [mul_pos hY0 (sub_pos.2 h), mul_nonneg hξ.1 hY1'.le])
  have h5 := hL (g := fun ξ => 1 - 2 * ξ) (by fun_prop) (fun ξ hξ => ⟨by linarith [hξ.2], by
    linarith [hξ.1]⟩)
  have h6 := hL (g := fun ξ => (1 - 2 * Y) * (1 - 2 * ξ)) (by fun_prop) (fun ξ hξ => by
    obtain ⟨hξ0, hξ1⟩ := hξ
    constructor <;> nlinarith)
  have h7 := hD (g := fun ξ => (2 * Y - 1) * ξ / Y) (by fun_prop (disch := exact hY0.ne'))
    (fun ξ hξ => by
      show (2 * Y - 1) * ξ / Y < 1
      rw [div_lt_one hY0]
      rcases eq_or_lt_of_le hξ.2 with h | h
      · rw [h]; linarith
      · nlinarith [mul_pos hY0 (sub_pos.2 h), mul_nonneg hξ.1 hY1'.le])
  unfold cxiDil
  exact ((((h1.const_smul (cxiCL Y)).add (((h2.add h3).sub h4).const_smul (cxiCq Y))).add
    ((h6.sub h5).div_const (2 * Y ^ 2))).add (h7.const_smul (cxiCD Y)))

/-- The limit of `cxiF` at `ξ → 0⁺`. -/
noncomputable def cxiL0 (Y : ℝ) : ℝ := cxiU0 Y 0 + cxiW0 Y 0 * log Y + cxiDil Y 0

/-- The limit of `cxiF` at `ξ → 1⁻`. -/
noncomputable def cxiL1 (Y : ℝ) : ℝ :=
  cxiU1 Y 1 + cxiW1Y Y 1 * log Y + cxiW1 Y 1 * log (1 - Y) + cxiDil Y 1

/-- **`cxiF → cxiL0` as `ξ → 0⁺`.** -/
theorem tendsto_cxiF_zero {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) :
    Tendsto (cxiF Y) (𝓝[>] 0) (𝓝 (cxiL0 Y)) := by
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have hY2' : 2 * Y - 1 ≠ 0 := fun h => hY2 (by linarith)
  have cU : ContinuousAt (cxiU0 Y) 0 := by
    unfold cxiU0; fun_prop (disch := simp [hY0])
  have cW : ContinuousAt (cxiW0 Y) 0 := by
    unfold cxiW0; fun_prop (disch := simp [hY0, hY1])
  have cV : ContinuousAt (cxiV0 Y) 0 := by
    unfold cxiV0; fun_prop (disch := simp [hY0])
  have cA : ContinuousAt (cxiA0 Y) 0 := by
    unfold cxiA0; fun_prop (disch := simp [hY0, hY1])
  have cB : ContinuousAt (cxiB0 Y) 0 := by
    unfold cxiB0; fun_prop (disch := simp [hY0, hY1])
  have h := (((((tendsto_cont_nhdsGT cU).add ((tendsto_cont_nhdsGT cW).mul_const (log Y))).add
    ((tendsto_cont_nhdsGT cV).mul tendsto_mul_log_zero)).add
    ((tendsto_cont_nhdsGT cA).mul (tendsto_lr2_div Y))).add
    ((tendsto_cont_nhdsGT cB).mul (tendsto_lr2_div ((2 * Y - 1) / Y)))).add
    (tendsto_nhdsGT_of_continuousOn_Icc (continuousOn_cxiDil hY))
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ξ hξ
  exact (cxiF_eq_zero_form hY hY2 hξ).symm

/-- **`cxiF → cxiL1` as `ξ → 1⁻`.** -/
theorem tendsto_cxiF_one {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) :
    Tendsto (cxiF Y) (𝓝[<] 1) (𝓝 (cxiL1 Y)) := by
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have hY2' : 2 * Y - 1 ≠ 0 := fun h => hY2 (by linarith)
  have cU : ContinuousAt (cxiU1 Y) 1 := by
    unfold cxiU1; fun_prop (disch := simp [hY0, hY1])
  have cWY : ContinuousAt (cxiW1Y Y) 1 := by
    unfold cxiW1Y; fun_prop (disch := simp [hY1])
  have cW : ContinuousAt (cxiW1 Y) 1 := by
    unfold cxiW1; fun_prop (disch := simp [hY0])
  have cX : ContinuousAt (cxiX1 Y) 1 := by
    unfold cxiX1; fun_prop (disch := simp [hY0])
  have cA : ContinuousAt (cxiA1 Y) 1 := by
    unfold cxiA1; fun_prop (disch := simp [hY0, hY1])
  have cB : ContinuousAt (cxiB1 Y) 1 := by
    unfold cxiB1; fun_prop (disch := simp [hY0, hY1])
  have hX : Tendsto (fun ξ : ℝ => lr3 (1 - ξ) / (1 - ξ) ^ 3) (𝓝[<] 1) (𝓝 0) := by
    simpa only [one_mul] using tendsto_lr3_div_one_sub 1
  have h := ((((((tendsto_cont_nhdsLT cU).add ((tendsto_cont_nhdsLT cWY).mul_const (log Y))).add
    ((tendsto_cont_nhdsLT cW).mul_const (log (1 - Y)))).add
    ((tendsto_cont_nhdsLT cX).mul hX)).add
    ((tendsto_cont_nhdsLT cA).mul (tendsto_lr3_div_one_sub (-(Y / (1 - Y)))))).add
    ((tendsto_cont_nhdsLT cB).mul (tendsto_lr3_div_one_sub ((1 - 2 * Y) / (1 - Y))))).add
    (tendsto_nhdsLT_of_continuousOn_Icc (continuousOn_cxiDil hY))
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with ξ hξ
  exact (cxiF_eq_one_form hY hY2 hξ).symm

/-! ### Continuity on `(0, 1)` -/

/-- **`cxiF(Y, ·)` is continuous on `(0, 1)`**, including the removable point `ξ = 1/2`. -/
theorem continuousAt_cxiF {Y ξ : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (cxiF Y) ξ := by
  obtain ⟨hξ0, hξ1⟩ := hξ
  have h0 : ξ ≠ 0 := hξ0.ne'
  have h1 : ξ - 1 ≠ 0 := by linarith
  have hA : 0 < 1 - Y * ξ := by nlinarith [hY.1, hY.2]
  have hB : 0 < ξ + Y - 2 * Y * ξ := by nlinarith [hY.1, hY.2]
  have hD : ContinuousAt (cxiDil Y) ξ :=
    (continuousOn_cxiDil hY).continuousAt (Icc_mem_nhds hξ0 hξ1)
  have hlA : ContinuousAt (fun ξ => log (1 - Y * ξ)) ξ :=
    (by fun_prop : ContinuousAt (fun ξ : ℝ => 1 - Y * ξ) ξ).log hA.ne'
  have hlB : ContinuousAt (fun ξ => log (ξ + Y - 2 * Y * ξ)) ξ :=
    (by fun_prop : ContinuousAt (fun ξ : ℝ => ξ + Y - 2 * Y * ξ) ξ).log hB.ne'
  have h := (((((hasDerivAt_cxiR0 Y h0 h1).continuousAt.add
    ((hasDerivAt_cxiPx Y h0 h1).continuousAt.mul (continuousAt_log h0))).add
    ((hasDerivAt_cxiPA Y h0 h1).continuousAt.mul hlA)).add
    ((hasDerivAt_cxiPB Y h0 h1).continuousAt.mul hlB)).add
    ((hasDerivAt_cxiPY Y h0 h1).continuousAt.mul
      (continuousAt_const : ContinuousAt (fun _ : ℝ => log Y) ξ))).add hD
  have e : cxiF Y = fun ξ => cxiR0 Y ξ + cxiPx Y ξ * log ξ + cxiPA Y ξ * log (1 - Y * ξ) +
      cxiPB Y ξ * log (ξ + Y - 2 * Y * ξ) + cxiPY Y ξ * log Y + cxiDil Y ξ := by
    funext ξ
    unfold cxiF cxiDil
    ring
  rw [e]
  exact h

end QED.TwoLoop.UnitSCCornerXi

end
