/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ParamHPL
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Log moments on `(0, 1)`: domination, integrability and boundary limits

Companion to `QED.Polylog.ParamHPL`: the elementary estimates needed to apply the
differential-equation method to integrands with logarithmic end-point singularities. A function
`f` on `(0, 1)` with a log-power bound `|f v| ≤ D (C + |log v| + |log (1 - v)|)ⁿ`

* is integrable on `(0, 1)` (`integrableOn_Ioo_of_abs_le_logs`);
* satisfies `(1 - v) f v → 0` as `v → 1⁻` and `v f v → 0` as `v → 0⁺`
  (`tendsto_one_sub_mul_of_abs_le_logs`, `tendsto_mul_of_abs_le_logs`), the boundary terms of
  an integration by parts against `v` or `v - 1`.

All of these follow from `logs_pow_le`: `(C + |log v| + |log (1 - v)|)ⁿ ≤ K (v^{-1/2} +
(1 - v)^{-1/2})` on `(0, 1)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.Polylog.ParamHPL

open QED.Polylog.HPL

/-- `|log t| ≤ A t^{-δ}` on `(0, 1)`. -/
theorem abs_log_le_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∃ A, 0 ≤ A ∧ ∀ t ∈ Ioo (0 : ℝ) 1, |log t| ≤ A * t ^ (-δ) := by
  obtain ⟨A, hA, h⟩ := abs_log_pow_le 1 hδ
  exact ⟨A, hA, fun t ht => by simpa using h t ⟨ht.1, ht.2.le⟩⟩

/-- The log-power bound: `(C + |log v| + |log (1 - v)|)ⁿ ≤ K (v^{-1/2} + (1 - v)^{-1/2})` on
`(0, 1)`. -/
theorem logs_pow_le {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ v ∈ Ioo (0 : ℝ) 1, (C + |log v| + |log (1 - v)|) ^ n ≤
      K * (v ^ (-(1 / 2) : ℝ) + (1 - v) ^ (-(1 / 2) : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, zero_le_one, fun v hv => ?_⟩
    have h1 : 1 ≤ v ^ (-(1 / 2) : ℝ) :=
      one_le_rpow_of_pos_of_le_one_of_nonpos hv.1 hv.2.le (by norm_num)
    have h2 : 0 ≤ (1 - v) ^ (-(1 / 2) : ℝ) := rpow_nonneg (by linarith [hv.2]) _
    simp only [pow_zero, one_mul]
    linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set δ : ℝ := 1 / (4 * n) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨A, hA, hlog⟩ := abs_log_le_rpow hδ0
  refine ⟨(C + 2 * A) ^ n, by positivity, fun v hv => ?_⟩
  have hv0 := hv.1
  have hv1 : 0 < 1 - v := by linarith [hv.2]
  have hg1 : 1 ≤ v ^ (-δ) := one_le_rpow_of_pos_of_le_one_of_nonpos hv0 hv.2.le (by linarith)
  have hg2 : 1 ≤ (1 - v) ^ (-δ) :=
    one_le_rpow_of_pos_of_le_one_of_nonpos hv1 (by linarith) (by linarith)
  set g := v ^ (-δ) * (1 - v) ^ (-δ) with hg
  have hg1' : 1 ≤ g := by nlinarith
  have hl1 : |log v| ≤ A * g := by
    refine (hlog v hv).trans (mul_le_mul_of_nonneg_left ?_ hA)
    nlinarith
  have hl2 : |log (1 - v)| ≤ A * g := by
    refine (hlog (1 - v) ⟨hv1, by linarith [hv.1]⟩).trans (mul_le_mul_of_nonneg_left ?_ hA)
    nlinarith
  have hsum : C + |log v| + |log (1 - v)| ≤ (C + 2 * A) * g := by nlinarith
  have hpow : (C + |log v| + |log (1 - v)|) ^ n ≤ (C + 2 * A) ^ n * g ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hsum n
  refine hpow.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  -- `g ^ n = v^{-1/4} (1 - v)^{-1/4} ≤ v^{-1/2} + (1 - v)^{-1/2}`
  have hgn : g ^ n = v ^ (-(1 / 4) : ℝ) * (1 - v) ^ (-(1 / 4) : ℝ) := by
    rw [hg, mul_pow, ← rpow_natCast, ← rpow_natCast ((1 - v) ^ (-δ)), ← rpow_mul hv0.le,
      ← rpow_mul hv1.le]
    have : -δ * (n : ℝ) = -(1 / 4) := by rw [hδ]; field_simp
    rw [this]
  have ha : (v ^ (-(1 / 4) : ℝ)) ^ 2 = v ^ (-(1 / 2) : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hv0.le]; norm_num
  have hb : ((1 - v) ^ (-(1 / 4) : ℝ)) ^ 2 = (1 - v) ^ (-(1 / 2) : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hv1.le]; norm_num
  rw [hgn, ← ha, ← hb]
  have h0 : 0 ≤ v ^ (-(1 / 4) : ℝ) := rpow_nonneg hv0.le _
  have h0' : 0 ≤ (1 - v) ^ (-(1 / 4) : ℝ) := rpow_nonneg hv1.le _
  nlinarith [sq_nonneg (v ^ (-(1 / 4) : ℝ) - (1 - v) ^ (-(1 / 4) : ℝ)), mul_nonneg h0 h0']

/-- `v^{-1/2} + (1 - v)^{-1/2}` is integrable on `(0, 1)`. -/
theorem integrableOn_rpow_add_one_sub_rpow :
    IntegrableOn (fun v : ℝ => v ^ (-(1 / 2) : ℝ) + (1 - v) ^ (-(1 / 2) : ℝ)) (Ioo 0 1) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  have h1 : IntervalIntegrable (fun v : ℝ => v ^ (-(1 / 2) : ℝ)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 : IntervalIntegrable (fun v : ℝ => (1 - v) ^ (-(1 / 2) : ℝ)) volume 0 1 := by
    simpa using (h1.comp_sub_left 1).symm
  exact h1.add h2

/-- A function with a log-power bound `|f v| ≤ D (C + |log v| + |log (1 - v)|)ⁿ` on `(0, 1)` is
integrable there. -/
theorem integrableOn_Ioo_of_abs_le_logs {f : ℝ → ℝ} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (n : ℕ)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo 0 1)))
    (hb : ∀ v ∈ Ioo (0 : ℝ) 1, |f v| ≤ D * (C + |log v| + |log (1 - v)|) ^ n) :
    IntegrableOn f (Ioo 0 1) := by
  obtain ⟨K, -, hK⟩ := logs_pow_le hC n
  refine ((integrableOn_rpow_add_one_sub_rpow.const_mul K).const_mul D).mono' hf
    ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun v hv => ?_))
  rw [Real.norm_eq_abs]
  exact (hb v hv).trans (mul_le_mul_of_nonneg_left (hK v hv) hD)

/-- The boundary term at `1`: `(1 - v) f v → 0` as `v → 1⁻` under a log-power bound. -/
theorem tendsto_one_sub_mul_of_abs_le_logs {f : ℝ → ℝ} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (n : ℕ) (hb : ∀ v ∈ Ioo (0 : ℝ) 1, |f v| ≤ D * (C + |log v| + |log (1 - v)|) ^ n) :
    Tendsto (fun v => (1 - v) * f v) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨K₀, hK0', hK₀⟩ := logs_pow_le hC n
  set K := D * K₀ with hKdef
  have hK0 : 0 ≤ K := mul_nonneg hD hK0'
  have hK : ∀ v ∈ Ioo (0 : ℝ) 1, D * (C + |log v| + |log (1 - v)|) ^ n ≤
      K * (v ^ (-(1 / 2) : ℝ) + (1 - v) ^ (-(1 / 2) : ℝ)) := fun v hv => by
    rw [hKdef, mul_assoc]; exact mul_le_mul_of_nonneg_left (hK₀ v hv) hD
  have hlim : Tendsto (fun v : ℝ => K * ((1 - v) * v ^ (-(1 / 2) : ℝ) + (1 - v) ^ (1 / 2 : ℝ)))
      (𝓝[<] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun v : ℝ => K * ((1 - v) * v ^ (-(1 / 2) : ℝ) +
        (1 - v) ^ (1 / 2 : ℝ))) 1 := by
      refine continuousAt_const.mul (ContinuousAt.add ?_ ?_)
      · exact (continuousAt_const.sub continuousAt_id).mul
          (continuousAt_id.rpow_const (Or.inl one_ne_zero))
      · exact (continuousAt_const.sub continuousAt_id).rpow_const (Or.inr (by norm_num))
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with v hv
  have hv1 : 0 < 1 - v := by linarith [hv.2]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hv1]
  have hsq : (1 - v) * (1 - v) ^ (-(1 / 2) : ℝ) = (1 - v) ^ (1 / 2 : ℝ) := by
    rw [← rpow_one_add' hv1.le (by norm_num)]; norm_num
  calc (1 - v) * |f v| ≤ (1 - v) * (K * (v ^ (-(1 / 2) : ℝ) + (1 - v) ^ (-(1 / 2) : ℝ))) :=
        mul_le_mul_of_nonneg_left ((hb v hv).trans (hK v hv)) hv1.le
    _ = K * ((1 - v) * v ^ (-(1 / 2) : ℝ) + (1 - v) * (1 - v) ^ (-(1 / 2) : ℝ)) := by ring
    _ = _ := by rw [hsq]

/-- The boundary term at `0`: `v f v → 0` as `v → 0⁺` under a log-power bound. -/
theorem tendsto_mul_of_abs_le_logs {f : ℝ → ℝ} {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (n : ℕ)
    (hb : ∀ v ∈ Ioo (0 : ℝ) 1, |f v| ≤ D * (C + |log v| + |log (1 - v)|) ^ n) :
    Tendsto (fun v => v * f v) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_one_sub_mul_of_abs_le_logs (f := fun v => f (1 - v)) hC hD n fun v hv => by
    have := hb (1 - v) ⟨by linarith [hv.2], by linarith [hv.1]⟩
    simpa [add_right_comm] using this
  have hm : Tendsto (fun v : ℝ => 1 - v) (𝓝[>] 0) (𝓝[<] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun v : ℝ => 1 - v) (𝓝 0) (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with v hv
      simp only [mem_Iio, mem_Ioi] at hv ⊢
      linarith
  refine (h.comp hm).congr fun v => ?_
  simp

end QED.Polylog.ParamHPL
