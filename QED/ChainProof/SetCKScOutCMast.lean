/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCrossTW
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G4: the `b`-masters of the corner at a mass of either sign

Helper level (no frozen statement). In the corner with the outer photon of mass² `t` the mass
function `M = Y² - t y₃ y₄` is negative for `t > 4` on a set of positive measure, while
`M + β h > 0` always. The masters `∫_c^∞ dz/(zᵏ (M + z)ʲ)` of `SetCKCornInW` and `SetCKCrossTW`
assume `M > 0`; here they are proved for `M ≠ 0` and `M + c > 0` (`c > 0`):

* `∫_c^∞ dz/(M + z)² = 1/(M + c)` (`scOutCI0`),
* `∫_c^∞ dz/(z (M + z)²) = L/M² - 1/(M (M + c))` (`scOutCI1`),
* `∫_c^∞ dz/(z² (M + z)²) = 1/(M² c) - 2L/M³ + 1/(M² (M + c))` (`scOutCI2`),
* `∫_c^∞ dz/(z (M + z)) = L/M` (`scOutCJ1`),
* `∫_c^∞ dz/(z² (M + z)) = 1/(M c) - L/M²` (`scOutCJ2`),
* `∫_c^∞ dz/(z³ (M + z)) = 1/(2 M c²) - 1/(M² c) + L/M³` (`scOutCJ3`),

with `L = log(1 + M/c)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

section

variable {M c : ℝ}

theorem scOutC_tendsto_logw (M : ℝ) :
    Tendsto (fun w : ℝ => log w - log (M + w)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun w : ℝ => 1 + M / w) atTop (𝓝 1) := by
    have := (tendsto_const_nhds : Tendsto (fun _ : ℝ => M) atTop (𝓝 M)).div_atTop tendsto_id
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add this
  have h2 : Tendsto (fun w : ℝ => log (1 + M / w)) atTop (𝓝 0) := by
    have := ((continuousAt_log one_ne_zero).tendsto).comp h1
    simpa [Function.comp_def] using this
  have h3 := h2.neg
  rw [neg_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 (-M))] with w hw
  have hw0 : 0 < w := lt_of_le_of_lt (le_max_left _ _) hw
  have hMw : 0 < M + w := by linarith [lt_of_le_of_lt (le_max_right _ _) hw]
  have e : 1 + M / w = (M + w) / w := by field_simp; ring
  rw [e, log_div hMw.ne' hw0.ne']
  ring

theorem scOutC_hasDerivAt_logw {w : ℝ} (hw : 0 < w) (hMw : 0 < M + w) :
    HasDerivAt (fun w => log w - log (M + w)) (1 / w - 1 / (M + w)) w := by
  have h1 : HasDerivAt (fun w => M + w) 1 w := (hasDerivAt_id w).const_add M
  have := (Real.hasDerivAt_log hw.ne').sub (h1.log hMw.ne')
  exact this.congr_deriv (by simp [one_div])

theorem scOutC_log_eq (hc : 0 < c) (hMc : 0 < M + c) :
    log (1 + M / c) = log (M + c) - log c := by
  have e : 1 + M / c = (M + c) / c := by field_simp; ring
  rw [e, log_div hMc.ne' hc.ne']

/-- `∫_c^∞ dz/(M + z)² = 1/(M + c)`. -/
theorem scOutCI0 (hMc : 0 < M + c) :
    IntegrableOn (fun v => 1 / (M + v) ^ 2) (Ioi c) ∧
      ∫ v in Ioi c, 1 / (M + v) ^ 2 = 1 / (M + c) := by
  have hd : ∀ v ∈ Ici c, HasDerivAt (fun v => -(1 / (M + v))) (1 / (M + v) ^ 2) v :=
    fun v hv => by
      have hMv : 0 < M + v := by linarith [mem_Ici.1 hv]
      exact (crossT_hasDerivAt_inv hMv).neg.congr_deriv (neg_neg _)
  have hf : ∀ v ∈ Ioi c, 0 ≤ 1 / (M + v) ^ 2 := fun v _ => by positivity
  have hl : Tendsto (fun v => -(1 / (M + v))) atTop (𝓝 0) := by
    simpa using (crossT_tendsto_inv_add M).neg
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  exact ⟨hi, by rw [hv]; ring⟩

/-- `∫_c^∞ dz/(z (M + z)²) = L/M² - 1/(M (M + c))`. -/
theorem scOutCI1 (hM : M ≠ 0) (hc : 0 < c) (hMc : 0 < M + c) :
    IntegrableOn (fun v => 1 / (v * (M + v) ^ 2)) (Ioi c) ∧
      ∫ v in Ioi c, 1 / (v * (M + v) ^ 2) = log (1 + M / c) / M ^ 2 - 1 / (M * (M + c)) := by
  have hd : ∀ v ∈ Ici c, HasDerivAt
      (fun v => (log v - log (M + v)) / M ^ 2 + 1 / M * (1 / (M + v)))
      (1 / (v * (M + v) ^ 2)) v := fun v hv => by
    have hv0 : 0 < v := lt_of_lt_of_le hc hv
    have hMv : 0 < M + v := by linarith [mem_Ici.1 hv]
    refine (((scOutC_hasDerivAt_logw hv0 hMv).div_const (M ^ 2)).add
      ((crossT_hasDerivAt_inv hMv).const_mul (1 / M))).congr_deriv ?_
    have := hMv.ne'
    field_simp
    ring
  have hf : ∀ v ∈ Ioi c, 0 ≤ 1 / (v * (M + v) ^ 2) := fun v hv => by
    have hv0 : 0 < v := hc.trans hv
    positivity
  have hl : Tendsto (fun v => (log v - log (M + v)) / M ^ 2 + 1 / M * (1 / (M + v))) atTop
      (𝓝 0) := by
    have h := ((scOutC_tendsto_logw M).div_const (M ^ 2)).add
      ((crossT_tendsto_inv_add M).const_mul (1 / M))
    simp only [zero_div, mul_zero, add_zero] at h
    exact h
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  refine ⟨hi, hv.trans ?_⟩
  rw [scOutC_log_eq hc hMc]
  have := hMc.ne'
  field_simp
  ring

/-- `∫_c^∞ dz/(z² (M + z)²) = 1/(M² c) - 2L/M³ + 1/(M² (M + c))`. -/
theorem scOutCI2 (hM : M ≠ 0) (hc : 0 < c) (hMc : 0 < M + c) :
    IntegrableOn (fun v => 1 / (v ^ 2 * (M + v) ^ 2)) (Ioi c) ∧
      ∫ v in Ioi c, 1 / (v ^ 2 * (M + v) ^ 2) =
        1 / (M ^ 2 * c) - 2 * log (1 + M / c) / M ^ 3 + 1 / (M ^ 2 * (M + c)) := by
  have hd : ∀ v ∈ Ici c, HasDerivAt
      (fun v => -(1 / M ^ 2 * (1 / v)) - 2 * (log v - log (M + v)) / M ^ 3 -
        1 / M ^ 2 * (1 / (M + v)))
      (1 / (v ^ 2 * (M + v) ^ 2)) v := fun v hv => by
    have hv0 : 0 < v := lt_of_lt_of_le hc hv
    have hMv : 0 < M + v := by linarith [mem_Ici.1 hv]
    have h1 := crossT_hasDerivAt_one_div hv0
    refine (((h1.const_mul (1 / M ^ 2)).neg.sub
      (((scOutC_hasDerivAt_logw hv0 hMv).const_mul 2).div_const (M ^ 3))).sub
      ((crossT_hasDerivAt_inv hMv).const_mul (1 / M ^ 2))).congr_deriv ?_
    have := hMv.ne'
    field_simp
    ring
  have hf : ∀ v ∈ Ioi c, 0 ≤ 1 / (v ^ 2 * (M + v) ^ 2) := fun v _ => by positivity
  have hl : Tendsto (fun v => -(1 / M ^ 2 * (1 / v)) - 2 * (log v - log (M + v)) / M ^ 3 -
      1 / M ^ 2 * (1 / (M + v))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun v : ℝ => 1 / v) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h := ((h0.const_mul (1 / M ^ 2)).neg.sub
      (((scOutC_tendsto_logw M).const_mul 2).div_const (M ^ 3))).sub
      ((crossT_tendsto_inv_add M).const_mul (1 / M ^ 2))
    simp only [zero_div, mul_zero, neg_zero, sub_zero] at h
    exact h
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  refine ⟨hi, hv.trans ?_⟩
  rw [scOutC_log_eq hc hMc]
  have := hMc.ne'
  field_simp
  ring

/-- `∫_c^∞ dz/(z (M + z)) = L/M`. -/
theorem scOutCJ1 (hM : M ≠ 0) (hc : 0 < c) (hMc : 0 < M + c) :
    IntegrableOn (fun w => 1 / (w * (M + w))) (Ioi c) ∧
      ∫ w in Ioi c, 1 / (w * (M + w)) = log (1 + M / c) / M := by
  have hd : ∀ w ∈ Ici c, HasDerivAt (fun w => (log w - log (M + w)) / M)
      (1 / (w * (M + w))) w := fun w hw => by
    have hw0 : 0 < w := lt_of_lt_of_le hc hw
    have hMw : 0 < M + w := by linarith [mem_Ici.1 hw]
    refine ((scOutC_hasDerivAt_logw hw0 hMw).div_const M).congr_deriv ?_
    have := hMw.ne'
    field_simp
    ring
  have hf : ∀ w ∈ Ioi c, 0 ≤ 1 / (w * (M + w)) := fun w hw => by
    have hw0 : 0 < w := hc.trans hw
    have hMw : 0 < M + w := by linarith [mem_Ioi.1 hw]
    positivity
  have hl : Tendsto (fun w => (log w - log (M + w)) / M) atTop (𝓝 0) := by
    simpa using (scOutC_tendsto_logw M).div_const M
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  refine ⟨hi, hv.trans ?_⟩
  rw [scOutC_log_eq hc hMc]
  ring

/-- `∫_c^∞ dz/(z² (M + z)) = 1/(M c) - L/M²`. -/
theorem scOutCJ2 (hM : M ≠ 0) (hc : 0 < c) (hMc : 0 < M + c) :
    IntegrableOn (fun w => 1 / (w ^ 2 * (M + w))) (Ioi c) ∧
      ∫ w in Ioi c, 1 / (w ^ 2 * (M + w)) = 1 / (M * c) - log (1 + M / c) / M ^ 2 := by
  have hd : ∀ w ∈ Ici c, HasDerivAt (fun w => -(1 / M * (1 / w)) - (log w - log (M + w)) / M ^ 2)
      (1 / (w ^ 2 * (M + w))) w := fun w hw => by
    have hw0 : 0 < w := lt_of_lt_of_le hc hw
    have hMw : 0 < M + w := by linarith [mem_Ici.1 hw]
    refine (((crossT_hasDerivAt_one_div hw0).const_mul (1 / M)).neg.sub
      ((scOutC_hasDerivAt_logw hw0 hMw).div_const (M ^ 2))).congr_deriv ?_
    have := hMw.ne'
    field_simp
    ring
  have hf : ∀ w ∈ Ioi c, 0 ≤ 1 / (w ^ 2 * (M + w)) := fun w hw => by
    have hw0 : 0 < w := hc.trans hw
    have hMw : 0 < M + w := by linarith [mem_Ioi.1 hw]
    positivity
  have hl : Tendsto (fun w => -(1 / M * (1 / w)) - (log w - log (M + w)) / M ^ 2) atTop
      (𝓝 0) := by
    have h0 : Tendsto (fun v : ℝ => 1 / v) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h := (h0.const_mul (1 / M)).neg.sub ((scOutC_tendsto_logw M).div_const (M ^ 2))
    simp only [zero_div, mul_zero, neg_zero, sub_zero] at h
    exact h
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  refine ⟨hi, hv.trans ?_⟩
  rw [scOutC_log_eq hc hMc]
  field_simp
  ring

/-- `∫_c^∞ dz/(z³ (M + z)) = 1/(2 M c²) - 1/(M² c) + L/M³`. -/
theorem scOutCJ3 (hM : M ≠ 0) (hc : 0 < c) (hMc : 0 < M + c) :
    IntegrableOn (fun w => 1 / (w ^ 3 * (M + w))) (Ioi c) ∧
      ∫ w in Ioi c, 1 / (w ^ 3 * (M + w)) =
        1 / (2 * M * c ^ 2) - 1 / (M ^ 2 * c) + log (1 + M / c) / M ^ 3 := by
  have hd : ∀ w ∈ Ici c, HasDerivAt
      (fun w => -(1 / (2 * M) * ((1 / w) * (1 / w))) + 1 / M ^ 2 * (1 / w) +
        (log w - log (M + w)) / M ^ 3)
      (1 / (w ^ 3 * (M + w))) w := fun w hw => by
    have hw0 : 0 < w := lt_of_lt_of_le hc hw
    have hMw : 0 < M + w := by linarith [mem_Ici.1 hw]
    have h1 := crossT_hasDerivAt_one_div hw0
    refine ((((h1.mul h1).const_mul (1 / (2 * M))).neg.add (h1.const_mul (1 / M ^ 2))).add
      ((scOutC_hasDerivAt_logw hw0 hMw).div_const (M ^ 3))).congr_deriv ?_
    have := hMw.ne'
    field_simp
    ring
  have hf : ∀ w ∈ Ioi c, 0 ≤ 1 / (w ^ 3 * (M + w)) := fun w hw => by
    have hw0 : 0 < w := hc.trans hw
    have hMw : 0 < M + w := by linarith [mem_Ioi.1 hw]
    positivity
  have hl : Tendsto (fun w => -(1 / (2 * M) * ((1 / w) * (1 / w))) + 1 / M ^ 2 * (1 / w) +
      (log w - log (M + w)) / M ^ 3) atTop (𝓝 0) := by
    have h0 : Tendsto (fun v : ℝ => 1 / v) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h := ((((h0.mul h0).const_mul (1 / (2 * M))).neg.add (h0.const_mul (1 / M ^ 2))).add
      ((scOutC_tendsto_logw M).div_const (M ^ 3)))
    simp only [zero_div, mul_zero, neg_zero, add_zero] at h
    exact h
  obtain ⟨hi, hv⟩ := cornIn_ioi_of_deriv hd hf hl
  refine ⟨hi, hv.trans ?_⟩
  rw [scOutC_log_eq hc hMc]
  field_simp
  ring

end

end QED.ChainProof.SetCK

end
