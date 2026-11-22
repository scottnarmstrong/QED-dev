/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKDDisp
public import QED.ChainProof.SetAKSKUElem
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (a), stage D: the dispersion of a squared logarithmic node

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. Next to
the dispersion of one logarithmic node (`ksD_log_eq_integral`), the finite parts of the vertex
classes contain squared logarithms `log² A`, `A = 1 + s/t₀`, of the one-loop denominators. Their
once-subtracted dispersive form has the spectral density `2 log(t/t₀ - 1)` on `t > t₀`:

  `log²(1 + s/t₀) = ∫_{t > t₀} 2 log((t - t₀)/t₀) · s/(t(s + t)) dt`   (`t₀ > 0`, `s > -t₀`).

The antiderivative in `t` is
`G(t) = 2 log((t-t₀)/t₀) (log(t/t₀) - log((t+s)/(t₀+s))) - 2K((t-t₀)/t₀) + 2K((t-t₀)/(t₀+s))`,
with `K(z) = ∫₀^z log(1+u)/u du` (`ksUK`); `G(t₀) = 0`, and `G(t) → log²(1 + s/t₀)` at infinity
by the inversion `K(z) + K(1/z) = log² z/2 + 2K(1)` (`ksU_ksUK_inv`).

Main results:

* `ksW_tendsto_ksUK_zero`: `K(z) → 0` as `z → 0⁺`;
* `ksW_hasDerivAt_logSqG`: the derivative of the antiderivative;
* **`ksW_logSq_eq_integral`**: the dispersion of `log²(1 + s/t₀)`;
* **`ksW_ksUK_node`**: the dispersion of `K(B/(1 + s/t₀))`, a finite-interval density
  `log((t - t₀)/t₀) - log B` on `(t₀, t₀(1 + B))`, from the same antiderivative.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

theorem ksW_tendsto_ksUK_zero : Tendsto ksUK (𝓝[≥] 0) (𝓝 0) := by
  have h : Tendsto (fun z : ℝ => z) (𝓝[≥] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz using ksU_ksUK_nonneg hz
  · filter_upwards [self_mem_nhdsWithin] with z hz using ksU_ksUK_le hz

theorem ksW_ksUK_zero : ksUK 0 = 0 := by simp [ksUK]

/-- The antiderivative of `2 log((t-t₀)/t₀) · s/(t(s+t))` on `t > t₀`. -/
noncomputable def ksWLogSqG (t₀ s t : ℝ) : ℝ :=
  2 * (log ((t - t₀) / t₀) * (log (t / t₀) - log ((t + s) / (t₀ + s)))) -
    2 * ksUK ((t - t₀) / t₀) + 2 * ksUK ((t - t₀) / (t₀ + s))

section LogSq

variable {s t₀ : ℝ} (ht₀ : 0 < t₀) (hs : -t₀ < s)
include ht₀ hs

theorem ksW_hasDerivAt_logSqG {t : ℝ} (ht : t₀ < t) :
    HasDerivAt (ksWLogSqG t₀ s) (2 * log ((t - t₀) / t₀) * (s / (t * (s + t)))) t := by
  have hp : 0 < t₀ + s := by linarith
  have htp : 0 < t := by linarith
  have hts : 0 < t + s := by linarith
  have hd : 0 < t - t₀ := by linarith
  have hz₁ : 0 < (t - t₀) / t₀ := div_pos hd ht₀
  have hz₂ : 0 < (t - t₀) / (t₀ + s) := div_pos hd hp
  have hI := hasDerivAt_id t
  have hl : HasDerivAt (fun t => log ((t - t₀) / t₀)) (1 / (t - t₀)) t := by
    have := ((hI.sub_const t₀).div_const t₀).log hz₁.ne'
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  have hl₁ : HasDerivAt (fun t => log (t / t₀)) (1 / t) t := by
    have := (hI.div_const t₀).log (div_pos htp ht₀).ne'
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  have hl₂ : HasDerivAt (fun t => log ((t + s) / (t₀ + s))) (1 / (t + s)) t := by
    have := ((hI.add_const s).div_const (t₀ + s)).log (div_pos hts hp).ne'
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  have hK₁ : HasDerivAt (fun t => ksUK ((t - t₀) / t₀)) (log (t / t₀) / (t - t₀)) t := by
    have := (ksU_hasDerivAt_ksUK hz₁).comp t ((hI.sub_const t₀).div_const t₀)
    refine this.congr_deriv ?_
    simp only [ksUKer]
    rw [show 1 + (t - t₀) / t₀ = t / t₀ by field_simp; ring]
    field_simp
  have hK₂ : HasDerivAt (fun t => ksUK ((t - t₀) / (t₀ + s)))
      (log ((t + s) / (t₀ + s)) / (t - t₀)) t := by
    have := (ksU_hasDerivAt_ksUK hz₂).comp t ((hI.sub_const t₀).div_const (t₀ + s))
    refine this.congr_deriv ?_
    simp only [ksUKer]
    rw [show 1 + (t - t₀) / (t₀ + s) = (t + s) / (t₀ + s) by field_simp; ring]
    field_simp
  have hD : HasDerivAt (fun t => log (t / t₀) - log ((t + s) / (t₀ + s))) (1 / t - 1 / (t + s))
      t := hl₁.sub hl₂
  have h := (((hl.mul hD).const_mul 2).sub (hK₁.const_mul 2)).add (hK₂.const_mul 2)
  refine h.congr_deriv ?_
  have := hts.ne'
  have : s + t ≠ 0 := by linarith
  have := htp.ne'
  have := hd.ne'
  generalize log ((t - t₀) / t₀) = ℓ
  generalize log (t / t₀) = L₁
  generalize log ((t + s) / (t₀ + s)) = L₂
  field_simp
  ring

theorem ksW_continuousWithinAt_logSqG : ContinuousWithinAt (ksWLogSqG t₀ s) (Ici t₀) t₀ := by
  have hp : 0 < t₀ + s := by linarith
  have hG0 : ksWLogSqG t₀ s t₀ = 0 := by simp [ksWLogSqG, ksW_ksUK_zero]
  rw [ContinuousWithinAt, hG0]
  -- the two `K` terms
  have hK : ∀ c : ℝ, 0 < c →
      Tendsto (fun t => ksUK ((t - t₀) / c)) (𝓝[≥] t₀) (𝓝 0) := fun c hc => by
    refine ksW_tendsto_ksUK_zero.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      _ ?_ ?_)
    · have : Tendsto (fun t : ℝ => (t - t₀) / c) (𝓝 t₀) (𝓝 ((t₀ - t₀) / c)) :=
        (by fun_prop : Continuous fun t : ℝ => (t - t₀) / c).tendsto t₀
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_nonneg (sub_nonneg.2 ht) hc.le
  -- the product term, dominated by `c |z log z|`
  set c : ℝ := 1 + t₀ / (t₀ + s) with hc
  have hz : Tendsto (fun t : ℝ => (t - t₀) / t₀ * log ((t - t₀) / t₀)) (𝓝[≥] t₀) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (t - t₀) / t₀) (𝓝 t₀) (𝓝 0) := by
      have := (by fun_prop : Continuous fun t : ℝ => (t - t₀) / t₀).tendsto t₀
      simpa using this
    have := (continuous_mul_log.tendsto 0).comp h1
    simpa [Function.comp_def] using this.mono_left nhdsWithin_le_nhds
  have hP : Tendsto (fun t => 2 * (log ((t - t₀) / t₀) *
      (log (t / t₀) - log ((t + s) / (t₀ + s))))) (𝓝[≥] t₀) (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => 2 * c * |(t - t₀) / t₀ * log ((t - t₀) / t₀)|)
        (𝓝[≥] t₀) (𝓝 0) := by
      simpa using (hz.abs.const_mul (2 * c))
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : t₀ ≤ t := ht
    have hz0 : 0 ≤ (t - t₀) / t₀ := div_nonneg (by linarith) ht₀.le
    have hA1 : 0 ≤ log (t / t₀) := log_nonneg ((one_le_div ht₀).2 ht)
    have hA2 : log (t / t₀) ≤ (t - t₀) / t₀ := by
      have := log_le_sub_one_of_pos (x := t / t₀) (div_pos (by linarith) ht₀)
      rw [show t / t₀ - 1 = (t - t₀) / t₀ by field_simp] at this
      exact this
    have hB1 : 0 ≤ log ((t + s) / (t₀ + s)) := log_nonneg ((one_le_div hp).2 (by linarith))
    have hB2 : log ((t + s) / (t₀ + s)) ≤ (t - t₀) / t₀ * (t₀ / (t₀ + s)) := by
      have := log_le_sub_one_of_pos (x := (t + s) / (t₀ + s)) (div_pos (by linarith) hp)
      rw [show (t + s) / (t₀ + s) - 1 = (t - t₀) / t₀ * (t₀ / (t₀ + s)) by
        field_simp; ring] at this
      exact this
    have hq : 0 ≤ t₀ / (t₀ + s) := div_nonneg ht₀.le hp.le
    have hD : |log (t / t₀) - log ((t + s) / (t₀ + s))| ≤ (t - t₀) / t₀ * c := by
      rw [abs_le, hc]
      constructor <;> nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg hz0]
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    calc 2 * (|log ((t - t₀) / t₀)| * |log (t / t₀) - log ((t + s) / (t₀ + s))|)
        ≤ 2 * (|log ((t - t₀) / t₀)| * ((t - t₀) / t₀ * c)) := by gcongr
      _ = 2 * c * ((t - t₀) / t₀ * |log ((t - t₀) / t₀)|) := by ring
  have := (hP.sub ((hK t₀ ht₀).const_mul 2)).add ((hK (t₀ + s) hp).const_mul 2)
  simp only [mul_zero, sub_zero, add_zero] at this
  exact this

theorem ksW_tendsto_logSqG :
    Tendsto (ksWLogSqG t₀ s) atTop (𝓝 (log (1 + s / t₀) ^ 2)) := by
  have hp : 0 < t₀ + s := by linarith
  -- `K(1/z) → 0` along `z = (t - t₀)/c → ∞`
  have hKi : ∀ c : ℝ, 0 < c → Tendsto (fun t => ksUK ((t - t₀) / c)⁻¹) atTop (𝓝 0) :=
    fun c hc => by
      have h0 : Tendsto (fun t : ℝ => t - t₀) atTop atTop :=
        (tendsto_atTop_add_const_right atTop (-t₀) tendsto_id).congr
          fun t => (sub_eq_add_neg t t₀).symm
      have h1 : Tendsto (fun t : ℝ => (t - t₀) / c) atTop atTop := h0.atTop_div_const hc
      exact ksW_tendsto_ksUK_zero.comp
        ((tendsto_inv_atTop_nhdsGT_zero.comp h1).mono_right (nhdsWithin_mono _ Ioi_subset_Ici_self))
  -- `(log(t - t₀) - log t₀)/t → 0`
  have hm : Tendsto (fun t : ℝ => (log (t - t₀) - log t₀) / t) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t - t₀) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (-t₀) tendsto_id).congr
        fun t => (sub_eq_add_neg t t₀).symm
    have h2 := (Real.tendsto_pow_log_div_mul_add_atTop 1 t₀ 1 one_ne_zero).comp h1
    have h3 : Tendsto (fun t : ℝ => log t₀ / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h4 := h2.sub h3
    rw [sub_zero] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp_def, pow_one, one_mul, sub_add_cancel]
    ring
  have hL := Real.tendsto_mul_log_one_add_div_atTop s
  have hmain := ((((hm.mul hL).const_mul (-2)).add (((hKi t₀ ht₀).const_mul 2).sub
    ((hKi (t₀ + s) hp).const_mul 2)))).const_add (log (1 + s / t₀) ^ 2)
  simp only [zero_mul, mul_zero, sub_zero, add_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (t₀ + |s| + 1)] with t ht
  have hs' : -|s| ≤ s := neg_abs_le s
  have htp : 0 < t := by linarith [abs_nonneg s]
  have hts : 0 < t + s := by linarith
  have hd : 0 < t - t₀ := by linarith [abs_nonneg s]
  have hz₁ : 0 < (t - t₀) / t₀ := div_pos hd ht₀
  have hz₂ : 0 < (t - t₀) / (t₀ + s) := div_pos hd hp
  have i₁ := ksU_ksUK_inv hz₁
  have i₂ := ksU_ksUK_inv hz₂
  have e1 : log (1 + s / t) = log (t + s) - log t := by
    rw [show 1 + s / t = (t + s) / t by field_simp, log_div hts.ne' htp.ne']
  have e2 : log (1 + s / t₀) = log (t₀ + s) - log t₀ := by
    rw [show 1 + s / t₀ = (t₀ + s) / t₀ by field_simp, log_div hp.ne' ht₀.ne']
  rw [e1, e2]
  have ht' : ∀ X : ℝ, (log (t - t₀) - log t₀) / t * (t * X) = (log (t - t₀) - log t₀) * X :=
    fun X => by field_simp
  rw [ht']
  simp only [ksWLogSqG]
  simp only [log_div hd.ne' ht₀.ne', log_div hd.ne' hp.ne', log_div htp.ne' ht₀.ne',
    log_div hts.ne' hp.ne'] at i₁ i₂ ⊢
  linear_combination 2 * i₁ - 2 * i₂

theorem ksW_integrableOn_logSq :
    IntegrableOn (fun t => 2 * log ((t - t₀) / t₀) * (s / (t * (s + t)))) (Ioi t₀) := by
  have hp : 0 < t₀ + s := by linarith
  have h2 : t₀ < 2 * t₀ := by linarith
  rw [← Ioc_union_Ioi_eq_Ioi h2.le]
  refine IntegrableOn.union ?_ ?_
  · -- a logarithm times a continuous kernel on the compact interval
    have hk : ContinuousOn (fun t : ℝ => s / (t * (s + t))) (Icc t₀ (2 * t₀)) := by
      refine continuousOn_const.div (by fun_prop) fun t ht => ?_
      have := ht.1
      exact (mul_pos (by linarith) (by linarith)).ne'
    have hlog : IntegrableOn (fun t => log (t - t₀)) (Ioc t₀ (2 * t₀)) := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := t₀)).comp_sub_right t₀
      rw [zero_add, show t₀ + t₀ = 2 * t₀ by ring,
        intervalIntegrable_iff_integrableOn_Ioc_of_le h2.le] at this
      exact this
    have hf0 : IntegrableOn (fun t => 2 * (log (t - t₀) - log t₀)) (Ioc t₀ (2 * t₀)) :=
      (hlog.sub ((continuousOn_const.integrableOn_compact isCompact_Icc).mono_set
        Ioc_subset_Icc_self)).const_mul 2
    have hf := hf0.mul_continuousOn_of_subset hk measurableSet_Ioc isCompact_Icc
      Ioc_subset_Icc_self
    refine hf.congr_fun (fun t ht => ?_) measurableSet_Ioc
    have : 0 < t - t₀ := by linarith [ht.1]
    simp only [log_div this.ne' ht₀.ne']
  · have hcont : ContinuousWithinAt (ksWLogSqG t₀ s) (Ici (2 * t₀)) (2 * t₀) :=
      (ksW_hasDerivAt_logSqG ht₀ hs h2).continuousAt.continuousWithinAt
    have hder : ∀ t ∈ Ioi (2 * t₀), HasDerivAt (ksWLogSqG t₀ s)
        (2 * log ((t - t₀) / t₀) * (s / (t * (s + t)))) t := fun t ht =>
      ksW_hasDerivAt_logSqG ht₀ hs (h2.trans ht)
    have hl : ∀ t ∈ Ioi (2 * t₀), 0 ≤ log ((t - t₀) / t₀) := fun t ht => by
      have ht : 2 * t₀ < t := ht
      exact log_nonneg ((one_le_div ht₀).2 (by linarith))
    have hk : ∀ t ∈ Ioi (2 * t₀), 0 < t * (s + t) := fun t ht => by
      have ht : 2 * t₀ < t := ht
      exact mul_pos (by linarith) (by linarith)
    rcases le_or_gt 0 s with h0 | h0
    · exact integrableOn_Ioi_deriv_of_nonneg hcont hder (fun t ht =>
        mul_nonneg (mul_nonneg zero_le_two (hl t ht)) (div_nonneg h0 (hk t ht).le))
        (ksW_tendsto_logSqG ht₀ hs)
    · exact integrableOn_Ioi_deriv_of_nonpos hcont hder (fun t ht =>
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg zero_le_two (hl t ht))
          (div_nonpos_of_nonpos_of_nonneg h0.le (hk t ht).le)) (ksW_tendsto_logSqG ht₀ hs)

/-- **The dispersion of a squared logarithmic node**:
`log²(1 + s/t₀) = ∫_{t > t₀} 2 log((t - t₀)/t₀) · s/(t(s + t)) dt`. -/
theorem ksW_logSq_eq_integral :
    log (1 + s / t₀) ^ 2 = ∫ t in Ioi t₀, 2 * log ((t - t₀) / t₀) * (s / (t * (s + t))) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (ksW_continuousWithinAt_logSqG ht₀ hs)
    (fun t ht => ksW_hasDerivAt_logSqG ht₀ hs ht) (ksW_integrableOn_logSq ht₀ hs)
    (ksW_tendsto_logSqG ht₀ hs)
  rw [h]
  simp [ksWLogSqG, ksW_ksUK_zero]

/-! ### The `K` node -/

/-- **The dispersion of the `K` node** `K(B/A)`, `A = 1 + s/t₀`: its spectral density is
`-log(B/a)` on `0 < a = t/t₀ - 1 < B`, so
`K(B/(1 + s/t₀)) - K(B) = ∫_{t₀}^{t₀(1+B)} (log((t - t₀)/t₀) - log B) · s/(t(s + t)) dt`. -/
theorem ksW_ksUK_node {B : ℝ} (hB : 0 < B) :
    ksUK (B / (1 + s / t₀)) - ksUK B =
      ∫ t in t₀..t₀ * (1 + B), (log ((t - t₀) / t₀) - log B) * (s / (t * (s + t))) := by
  have hp : 0 < t₀ + s := by linarith
  have hle : t₀ ≤ t₀ * (1 + B) := by nlinarith
  set H : ℝ → ℝ := fun t => log (t / t₀) - log ((t + s) / (t₀ + s)) with hH
  have hHd : ∀ t, t₀ < t → HasDerivAt H (s / (t * (s + t))) t := fun t ht => by
    have htp : 0 < t := by linarith
    have hts : 0 < t + s := by linarith
    have h1 := ((hasDerivAt_id t).div_const t₀).log (div_pos htp ht₀).ne'
    have h2 := (((hasDerivAt_id t).add_const s).div_const (t₀ + s)).log (div_pos hts hp).ne'
    refine (h1.sub h2).congr_deriv ?_
    simp only [id]
    have : s + t ≠ 0 := by linarith
    field_simp
    ring
  set G : ℝ → ℝ := fun t => ksWLogSqG t₀ s t / 2 - log B * H t with hG
  have hGd : ∀ t ∈ Ioo t₀ (t₀ * (1 + B)), HasDerivAt G
      ((log ((t - t₀) / t₀) - log B) * (s / (t * (s + t)))) t := fun t ht => by
    have := ((ksW_hasDerivAt_logSqG ht₀ hs ht.1).div_const 2).sub ((hHd t ht.1).const_mul (log B))
    refine this.congr_deriv ?_
    ring
  have hGc : ContinuousOn G (Icc t₀ (t₀ * (1 + B))) := by
    intro t ht
    rcases ht.1.eq_or_lt with h | h
    · subst h
      have hc := (ksW_continuousWithinAt_logSqG ht₀ hs).div_const 2
      have hHc : ContinuousWithinAt H (Ici t₀) t₀ := by
        have htp : (0 : ℝ) < t₀ / t₀ := div_pos ht₀ ht₀
        have hts : (0 : ℝ) < (t₀ + s) / (t₀ + s) := div_pos hp hp
        refine (ContinuousAt.sub ?_ ?_).continuousWithinAt
        · exact ((continuousAt_id.div_const t₀).log htp.ne')
        · exact (((continuousAt_id.add continuousAt_const).div_const (t₀ + s)).log hts.ne')
      exact (hc.sub (hHc.const_mul (log B))).mono Icc_subset_Ici_self
    · have h' := (ksW_hasDerivAt_logSqG ht₀ hs h).continuousAt.div_const 2
      exact (h'.sub ((hHd t h).continuousAt.const_mul (log B))).continuousWithinAt
  have hint : IntervalIntegrable (fun t => (log ((t - t₀) / t₀) - log B) * (s / (t * (s + t))))
      volume t₀ (t₀ * (1 + B)) := by
    have hk : ContinuousOn (fun t : ℝ => s / (t * (s + t))) (Icc t₀ (t₀ * (1 + B))) := by
      refine continuousOn_const.div (by fun_prop) fun t ht => ?_
      have := ht.1
      exact (mul_pos (by linarith) (by linarith)).ne'
    have hlog : IntegrableOn (fun t => log (t - t₀)) (Ioc t₀ (t₀ * (1 + B))) := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := t₀ * B)).comp_sub_right t₀
      rw [zero_add, show t₀ * B + t₀ = t₀ * (1 + B) by ring,
        intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at this
      exact this
    have hc : IntegrableOn (fun _ : ℝ => log t₀ + log B) (Ioc t₀ (t₀ * (1 + B))) :=
      (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hf := (hlog.sub hc).mul_continuousOn_of_subset hk measurableSet_Ioc isCompact_Icc
      Ioc_subset_Icc_self
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
    refine hf.congr_fun (fun t ht => ?_) measurableSet_Ioc
    have : 0 < t - t₀ := by linarith [ht.1]
    simp only [Pi.sub_apply, log_div this.ne' ht₀.ne']
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle hGc hGd hint]
  have e1 : (t₀ * (1 + B) - t₀) / t₀ = B := by field_simp; ring
  have e2 : (t₀ * (1 + B) - t₀) / (t₀ + s) = B / (1 + s / t₀) := by field_simp; ring
  simp only [hG, hH, ksWLogSqG, e1, e2, sub_self, ksW_ksUK_zero, div_self ht₀.ne',
    div_self hp.ne', log_one, mul_zero, zero_div, sub_zero]
  ring

end LogSq

end QED.ChainProof.SetAKS

end
