/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.TwoLoop.UnitXXiEnds
public import QED.TwoLoop.UnitXXiDeriv
import QED.Polylog.ExtraIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The endpoint limits of the `ξ`-antiderivative

For `Y ∈ (0, 1)`, `Y ≠ 1/2`:

* `tendsto_xiF_zero`: `xiF(Y, ξ) → U₀(Y, 0) + W₀(Y, 0) log Y + xiDil(Y, 0)` as `ξ → 0⁺`;
* `tendsto_xiF_one`: `xiF(Y, ξ) → U₁(Y, 1) + W₁'(Y, 1) log Y + W₁(Y, 1) log (1 - Y) + xiDil(Y, 1)`
  as `ξ → 1⁻`;
* `continuousAt_xiF`: `xiF(Y, ·)` is continuous on `(0, 1)`, including the removable point
  `ξ = 1/2`.

By the endpoint forms of `QED.TwoLoop.UnitXXiEnds`, the divergent parts of `xiF` cancel exactly;
what remains are coefficients continuous at the endpoint times `ξ log ξ` or the Taylor remainders
`lr2 (a ξ)/ξ²`, `lr3 (a s)/s³`, which tend to `0` by the bound
`|log (1 - z) + z + … + zⁿ/n| ≤ |z|ⁿ⁺¹/(1 - |z|)` (`Real.abs_log_sub_add_sum_range_le`), and the
dilogarithm terms `xiDil`, continuous on `[0, 1]` (`continuousOn_xiDil`).
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.TwoLoop.UnitXXi

open QED.TwoLoop.UnitXClose

/-! ### Taylor remainders of `log (1 - z)` -/

/-- `(∑_{i<n} (a s)^{i+1}/(i+1) + log (1 - a s))/sⁿ → 0` as `s → 0⁺`. -/
theorem tendsto_logTaylor_div (a : ℝ) (n : ℕ) :
    Tendsto (fun s : ℝ => ((∑ i ∈ Finset.range n, (a * s) ^ (i + 1) / (i + 1)) +
      log (1 - a * s)) / s ^ n) (𝓝[>] 0) (𝓝 0) := by
  have hlin : Tendsto (fun s : ℝ => |a| * s) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => |a| * s) (𝓝 0) (𝓝 (|a| * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), |a| * s < 1 / 2 :=
    hlin.eventually (gt_mem_nhds (by norm_num))
  have hbound : Tendsto (fun s : ℝ => 2 * |a| ^ (n + 1) * s) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => 2 * |a| ^ (n + 1) * s) (𝓝 0) (𝓝 (2 * |a| ^ (n + 1) * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [hsmall, self_mem_nhdsWithin] with s hs hs0
  have hs0' : 0 < s := hs0
  have habs : |a * s| = |a| * s := by rw [abs_mul, abs_of_pos hs0']
  have h1 : |a * s| < 1 := by rw [habs]; linarith
  have hT := Real.abs_log_sub_add_sum_range_le h1 n
  have hsn : 0 < s ^ n := pow_pos hs0' n
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hsn, div_le_iff₀ hsn]
  calc _ ≤ |a * s| ^ (n + 1) / (1 - |a * s|) := hT
    _ ≤ |a * s| ^ (n + 1) / (1 / 2) := by
        gcongr
        rw [habs]; linarith
    _ = 2 * |a| ^ (n + 1) * s * s ^ n := by rw [habs, mul_pow]; ring

theorem lr2_eq (z : ℝ) :
    lr2 z = (∑ i ∈ Finset.range 2, z ^ (i + 1) / (i + 1)) + log (1 - z) := by
  simp only [lr2, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

theorem lr3_eq (z : ℝ) :
    lr3 z = (∑ i ∈ Finset.range 3, z ^ (i + 1) / (i + 1)) + log (1 - z) := by
  simp only [lr3, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

theorem tendsto_lr2_div (a : ℝ) :
    Tendsto (fun s : ℝ => lr2 (a * s) / s ^ 2) (𝓝[>] 0) (𝓝 0) := by
  simpa only [lr2_eq] using tendsto_logTaylor_div a 2

theorem tendsto_lr3_div (a : ℝ) :
    Tendsto (fun s : ℝ => lr3 (a * s) / s ^ 3) (𝓝[>] 0) (𝓝 0) := by
  simpa only [lr3_eq] using tendsto_logTaylor_div a 3

theorem tendsto_lr3_div_one_sub (a : ℝ) :
    Tendsto (fun ξ : ℝ => lr3 (a * (1 - ξ)) / (1 - ξ) ^ 3) (𝓝[<] 1) (𝓝 0) :=
  (tendsto_lr3_div a).comp tendsto_one_sub_nhdsLT_one

/-! ### The dilogarithm terms are continuous on `[0, 1]` -/

theorem continuousOn_dilogI : ContinuousOn dilogI (Iio 1) :=
  fun _ hx => (hasDerivAt_dilogI hx).continuousAt.continuousWithinAt

theorem continuousOn_xiDil {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) : ContinuousOn (xiDil Y) (Icc 0 1) := by
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
  unfold xiDil
  exact ((((h1.const_smul (xiCL Y)).add (((h2.add h3).sub h4).const_smul (xiCq Y))).add
    ((h5.sub h6).div_const (2 * Y ^ 2))).add (h7.const_smul (xiCD Y)))

theorem tendsto_nhdsGT_of_continuousOn_Icc {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) :
    Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := by
  have h := (hg 0 ⟨le_rfl, zero_le_one⟩).tendsto
  rw [← nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
  exact h.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)

theorem tendsto_nhdsLT_of_continuousOn_Icc {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) :
    Tendsto g (𝓝[<] 1) (𝓝 (g 1)) := by
  have h := (hg 1 ⟨zero_le_one, le_rfl⟩).tendsto
  rw [← nhdsWithin_Ioo_eq_nhdsLT zero_lt_one]
  exact h.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)

/-! ### The limits -/

/-- The limit of `xiF` at `ξ → 0⁺`. -/
noncomputable def xiL0 (Y : ℝ) : ℝ := xiU0 Y 0 + xiW0 Y 0 * log Y + xiDil Y 0

/-- The limit of `xiF` at `ξ → 1⁻`. -/
noncomputable def xiL1 (Y : ℝ) : ℝ :=
  xiU1 Y 1 + xiW1Y Y 1 * log Y + xiW1 Y 1 * log (1 - Y) + xiDil Y 1

theorem tendsto_cont_nhdsGT {g : ℝ → ℝ} (hg : ContinuousAt g 0) :
    Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
  hg.tendsto.mono_left nhdsWithin_le_nhds

theorem tendsto_cont_nhdsLT {g : ℝ → ℝ} (hg : ContinuousAt g 1) :
    Tendsto g (𝓝[<] 1) (𝓝 (g 1)) :=
  hg.tendsto.mono_left nhdsWithin_le_nhds

/-- **`xiF → xiL0` as `ξ → 0⁺`.** -/
theorem tendsto_xiF_zero {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) :
    Tendsto (xiF Y) (𝓝[>] 0) (𝓝 (xiL0 Y)) := by
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have hY2' : 2 * Y - 1 ≠ 0 := fun h => hY2 (by linarith)
  have cU : ContinuousAt (xiU0 Y) 0 := by
    unfold xiU0; fun_prop (disch := simp [hY0, hY1])
  have cW : ContinuousAt (xiW0 Y) 0 := by
    unfold xiW0; fun_prop (disch := simp [hY0, hY1, hY2'])
  have cV : ContinuousAt (xiV0 Y) 0 := by
    unfold xiV0; fun_prop (disch := simp [hY0])
  have cA : ContinuousAt (xiA0 Y) 0 := by
    unfold xiA0; fun_prop (disch := simp [hY0, hY1])
  have cB : ContinuousAt (xiB0 Y) 0 := by
    unfold xiB0; fun_prop (disch := simp [hY0, hY1, hY2'])
  have h := (((((tendsto_cont_nhdsGT cU).add ((tendsto_cont_nhdsGT cW).mul_const (log Y))).add
    ((tendsto_cont_nhdsGT cV).mul tendsto_mul_log_zero)).add
    ((tendsto_cont_nhdsGT cA).mul (tendsto_lr2_div Y))).add
    ((tendsto_cont_nhdsGT cB).mul (tendsto_lr2_div ((2 * Y - 1) / Y)))).add
    (tendsto_nhdsGT_of_continuousOn_Icc (continuousOn_xiDil hY))
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ξ hξ
  exact (xiF_eq_zero_form hY hY2 hξ).symm

/-- **`xiF → xiL1` as `ξ → 1⁻`.** -/
theorem tendsto_xiF_one {Y : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hY2 : Y ≠ 1 / 2) :
    Tendsto (xiF Y) (𝓝[<] 1) (𝓝 (xiL1 Y)) := by
  have hY0 : Y ≠ 0 := hY.1.ne'
  have hY1 : Y - 1 ≠ 0 := by linarith [hY.2]
  have hY2' : 2 * Y - 1 ≠ 0 := fun h => hY2 (by linarith)
  have cU : ContinuousAt (xiU1 Y) 1 := by
    unfold xiU1; fun_prop (disch := simp [hY0, hY1])
  have cWY : ContinuousAt (xiW1Y Y) 1 := by
    unfold xiW1Y; fun_prop (disch := simp [hY1])
  have cW : ContinuousAt (xiW1 Y) 1 := by
    unfold xiW1; fun_prop (disch := simp [hY0, hY1, hY2'])
  have cX : ContinuousAt (xiX1 Y) 1 := by
    unfold xiX1; fun_prop (disch := simp [hY0])
  have cA : ContinuousAt (xiA1 Y) 1 := by
    unfold xiA1; fun_prop (disch := simp [hY0, hY1])
  have cB : ContinuousAt (xiB1 Y) 1 := by
    unfold xiB1; fun_prop (disch := simp [hY0, hY1, hY2'])
  have hX : Tendsto (fun ξ : ℝ => lr3 (1 - ξ) / (1 - ξ) ^ 3) (𝓝[<] 1) (𝓝 0) := by
    simpa only [one_mul] using tendsto_lr3_div_one_sub 1
  have h := ((((((tendsto_cont_nhdsLT cU).add ((tendsto_cont_nhdsLT cWY).mul_const (log Y))).add
    ((tendsto_cont_nhdsLT cW).mul_const (log (1 - Y)))).add
    ((tendsto_cont_nhdsLT cX).mul hX)).add
    ((tendsto_cont_nhdsLT cA).mul (tendsto_lr3_div_one_sub (-(Y / (1 - Y)))))).add
    ((tendsto_cont_nhdsLT cB).mul (tendsto_lr3_div_one_sub ((1 - 2 * Y) / (1 - Y))))).add
    (tendsto_nhdsLT_of_continuousOn_Icc (continuousOn_xiDil hY))
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with ξ hξ
  exact (xiF_eq_one_form hY hY2 hξ).symm

/-! ### Continuity on `(0, 1)` -/

/-- **`xiF(Y, ·)` is continuous on `(0, 1)`**, including the removable point `ξ = 1/2`. -/
theorem continuousAt_xiF {Y ξ : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hξ : ξ ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (xiF Y) ξ := by
  obtain ⟨hξ0, hξ1⟩ := hξ
  have h0 : ξ ≠ 0 := hξ0.ne'
  have h1 : ξ - 1 ≠ 0 := by linarith
  have hA : 0 < 1 - Y * ξ := by nlinarith [hY.1, hY.2]
  have hB : 0 < ξ + Y - 2 * Y * ξ := by nlinarith [hY.1, hY.2]
  have hD : ContinuousAt (xiDil Y) ξ :=
    (continuousOn_xiDil hY).continuousAt (Icc_mem_nhds hξ0 hξ1)
  have hlA : ContinuousAt (fun ξ => log (1 - Y * ξ)) ξ :=
    (by fun_prop : ContinuousAt (fun ξ : ℝ => 1 - Y * ξ) ξ).log hA.ne'
  have hlB : ContinuousAt (fun ξ => log (ξ + Y - 2 * Y * ξ)) ξ :=
    (by fun_prop : ContinuousAt (fun ξ : ℝ => ξ + Y - 2 * Y * ξ) ξ).log hB.ne'
  have h := (((((hasDerivAt_xiR0 Y h0 h1).continuousAt.add
    ((hasDerivAt_xiPx Y h0 h1).continuousAt.mul (continuousAt_log h0))).add
    ((hasDerivAt_xiPA Y h0 h1).continuousAt.mul hlA)).add
    ((hasDerivAt_xiPB Y h0 h1).continuousAt.mul hlB)).add
    ((hasDerivAt_xiPY Y h0 h1).continuousAt.mul
      (continuousAt_const : ContinuousAt (fun _ : ℝ => log Y) ξ))).add hD
  have e : xiF Y = fun ξ => xiR0 Y ξ + xiPx Y ξ * log ξ + xiPA Y ξ * log (1 - Y * ξ) +
      xiPB Y ξ * log (ξ + Y - 2 * Y * ξ) + xiPY Y ξ * log Y + xiDil Y ξ := by
    funext ξ
    unfold xiF xiDil
    ring
  rw [e]
  exact h

end QED.TwoLoop.UnitXXi

end
