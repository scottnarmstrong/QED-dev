/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKDDisp

/-!
# Set (a), stage D: the dispersion of two rational-logarithmic nodes

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. Next to
`log A`, `log² A` and `K(B/A)` (`A = 1 + s/t₀`, `B > 0`), the finite part of the `VA` class has
two more nodes, whose once-subtracted dispersive densities (in `a = t/t₀ - 1`) are elementary:

* `A log(1 + B/A) - log(1 + B)`: density `a` on `0 < a < B`;
* `(log(A + B) - log B)/A - (log(1 + B) - log B)`: density `-1/a` on `a > B`.

Both are proved from explicit antiderivatives in `t`.

Main results:

* **`ksW_mulLog_node`**;
* **`ksW_logRatio_node`**.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

section Nodes

variable {s t₀ : ℝ} (ht₀ : 0 < t₀) (hs : -t₀ < s)
include ht₀ hs

/-- **The dispersion of the node `A log(1 + B/A)`**, `A = 1 + s/t₀`: its density is `a` on
`0 < a = t/t₀ - 1 < B`. -/
theorem ksW_mulLog_node {B : ℝ} (hB : 0 ≤ B) :
    (1 + s / t₀) * log (1 + B / (1 + s / t₀)) - log (1 + B) =
      ∫ t in t₀..t₀ * (1 + B), (t - t₀) / t₀ * (s / (t * (s + t))) := by
  have hp : 0 < t₀ + s := by linarith
  have hA : 0 < 1 + s / t₀ := by
    rw [show 1 + s / t₀ = (t₀ + s) / t₀ by field_simp]
    exact div_pos hp ht₀
  have hle : t₀ ≤ t₀ * (1 + B) := by nlinarith
  set G : ℝ → ℝ := fun t => (1 + s / t₀) * log (s + t) - log t with hG
  have hGd : ∀ t, t₀ ≤ t → HasDerivAt G ((t - t₀) / t₀ * (s / (t * (s + t)))) t := fun t ht => by
    have htp : 0 < t := by linarith
    have hts : 0 < s + t := by linarith
    have h1 := (((hasDerivAt_id t).const_add s).log hts.ne').const_mul (1 + s / t₀)
    have h2 := (hasDerivAt_id t).log htp.ne'
    refine (h1.sub h2).congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have hint : IntervalIntegrable (fun t => (t - t₀) / t₀ * (s / (t * (s + t)))) volume t₀
      (t₀ * (1 + B)) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hle]
    refine ContinuousOn.mul (by fun_prop) (continuousOn_const.div (by fun_prop) fun t ht => ?_)
    exact (mul_pos (by linarith [ht.1]) (by linarith [ht.1])).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hGd t (by
    rw [uIcc_of_le hle] at ht; exact ht.1)) hint]
  have hB1 : 0 < 1 + B := by linarith
  have e1 : s + t₀ * (1 + B) = (s + t₀) * (1 + B / (1 + s / t₀)) := by field_simp; ring
  have hq : 0 < 1 + B / (1 + s / t₀) := by positivity
  simp only [hG]
  rw [e1, log_mul (by linarith) hq.ne', log_mul ht₀.ne' hB1.ne']
  ring

/-- The antiderivative of `-(t₀/(t - t₀)) · s/(t(s + t))` on `t > t₀`, vanishing at infinity. -/
noncomputable def ksWLogRatioG (t₀ s t : ℝ) : ℝ :=
  -((1 - (1 + s / t₀)⁻¹) * log ((t - t₀) / t) + (1 + s / t₀)⁻¹ * log ((s + t) / t))

theorem ksW_hasDerivAt_logRatioG {t : ℝ} (ht : t₀ < t) :
    HasDerivAt (ksWLogRatioG t₀ s) (-(t₀ / (t - t₀)) * (s / (t * (s + t)))) t := by
  have hp : 0 < t₀ + s := by linarith
  have htp : 0 < t := by linarith
  have hts : 0 < s + t := by linarith
  have hd : 0 < t - t₀ := by linarith
  have hI := hasDerivAt_id t
  have h1 := ((hI.sub_const t₀).div hI htp.ne').log (div_pos hd htp).ne'
  have h2 := ((hI.const_add s).div hI htp.ne').log (div_pos hts htp).ne'
  refine ((h1.const_mul (1 - (1 + s / t₀)⁻¹)).add (h2.const_mul (1 + s / t₀)⁻¹)).neg
    |>.congr_deriv ?_
  simp only [id, Pi.div_apply]
  field_simp
  ring

omit ht₀ hs in
theorem ksW_tendsto_logRatioG : Tendsto (ksWLogRatioG t₀ s) atTop (𝓝 0) := by
  have hq : ∀ c : ℝ, Tendsto (fun t : ℝ => log ((c + t) / t)) atTop (𝓝 0) := fun c => by
    have h0 : Tendsto (fun t : ℝ => c / t + 1) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.div_atTop tendsto_id).add_const (1 : ℝ)
    have h1 : Tendsto (fun t : ℝ => (c + t) / t) atTop (𝓝 1) := by
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      field_simp
    simpa [Function.comp_def] using (continuousAt_log one_ne_zero).tendsto.comp h1
  have h := (((hq (-t₀)).const_mul (1 - (1 + s / t₀)⁻¹)).add
    ((hq s).const_mul (1 + s / t₀)⁻¹)).neg
  simp only [mul_zero, add_zero, neg_zero] at h
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp only [ksWLogRatioG, neg_add_eq_sub]

theorem ksW_logRatio_sign {c : ℝ} (hc : t₀ < c) :
    (∀ t ∈ Ioi c, 0 ≤ -(t₀ / (t - t₀)) * (s / (t * (s + t)))) ∨
      ∀ t ∈ Ioi c, -(t₀ / (t - t₀)) * (s / (t * (s + t))) ≤ 0 := by
  have hpos : ∀ t ∈ Ioi c, 0 < t ∧ 0 < s + t ∧ 0 < t - t₀ := fun t ht => by
    have : c < t := ht
    exact ⟨by linarith, by linarith, by linarith⟩
  rcases le_or_gt 0 s with h0 | h0
  · refine Or.inr fun t ht => ?_
    obtain ⟨htp, hts, hd⟩ := hpos t ht
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (div_pos ht₀ hd).le)
      (div_nonneg h0 (mul_pos htp hts).le)
  · refine Or.inl fun t ht => ?_
    obtain ⟨htp, hts, hd⟩ := hpos t ht
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 (div_pos ht₀ hd).le)
      (div_nonpos_of_nonpos_of_nonneg h0.le (mul_pos htp hts).le)

theorem ksW_integrableOn_logRatio {c : ℝ} (hc : t₀ < c) :
    IntegrableOn (fun t => -(t₀ / (t - t₀)) * (s / (t * (s + t)))) (Ioi c) := by
  have hcont : ContinuousWithinAt (ksWLogRatioG t₀ s) (Ici c) c :=
    (ksW_hasDerivAt_logRatioG ht₀ hs hc).continuousAt.continuousWithinAt
  have hder : ∀ t ∈ Ioi c, HasDerivAt (ksWLogRatioG t₀ s)
      (-(t₀ / (t - t₀)) * (s / (t * (s + t)))) t := fun t ht =>
    ksW_hasDerivAt_logRatioG ht₀ hs (hc.trans ht)
  rcases ksW_logRatio_sign ht₀ hs hc with h | h
  · exact integrableOn_Ioi_deriv_of_nonneg hcont hder h ksW_tendsto_logRatioG
  · exact integrableOn_Ioi_deriv_of_nonpos hcont hder h ksW_tendsto_logRatioG

/-- **The dispersion of the node `(log(A + B) - log B)/A`**, `A = 1 + s/t₀`: its density is
`-1/a` on `a = t/t₀ - 1 > B`. -/
theorem ksW_logRatio_node {B : ℝ} (hB : 0 < B) :
    (log (1 + s / t₀ + B) - log B) / (1 + s / t₀) - (log (1 + B) - log B) =
      ∫ t in Ioi (t₀ * (1 + B)), -(t₀ / (t - t₀)) * (s / (t * (s + t))) := by
  have hp : 0 < t₀ + s := by linarith
  have hA : 0 < 1 + s / t₀ := by
    rw [show 1 + s / t₀ = (t₀ + s) / t₀ by field_simp]
    exact div_pos hp ht₀
  have h₁ : t₀ < t₀ * (1 + B) := by nlinarith
  have hcont : ContinuousWithinAt (ksWLogRatioG t₀ s) (Ici (t₀ * (1 + B))) (t₀ * (1 + B)) :=
    (ksW_hasDerivAt_logRatioG ht₀ hs h₁).continuousAt.continuousWithinAt
  have hder : ∀ t ∈ Ioi (t₀ * (1 + B)), HasDerivAt (ksWLogRatioG t₀ s)
      (-(t₀ / (t - t₀)) * (s / (t * (s + t)))) t := fun t ht =>
    ksW_hasDerivAt_logRatioG ht₀ hs (h₁.trans ht)
  have hval : 0 - ksWLogRatioG t₀ s (t₀ * (1 + B)) =
      (log (1 + s / t₀ + B) - log B) / (1 + s / t₀) - (log (1 + B) - log B) := by
    have hB1 : 0 < 1 + B := by linarith
    have hAB : 0 < 1 + s / t₀ + B := by linarith
    have e1 : (t₀ * (1 + B) - t₀) / (t₀ * (1 + B)) = B / (1 + B) := by field_simp; ring
    have e2 : (s + t₀ * (1 + B)) / (t₀ * (1 + B)) = (1 + s / t₀ + B) / (1 + B) := by
      field_simp; ring
    simp only [ksWLogRatioG, e1, e2]
    rw [log_div hB.ne' hB1.ne', log_div hAB.ne' hB1.ne']
    field_simp
    ring
  rcases ksW_logRatio_sign ht₀ hs h₁ with h | h
  · rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hder h ksW_tendsto_logRatioG, hval]
  · rw [integral_Ioi_of_hasDerivAt_of_nonpos hcont hder h ksW_tendsto_logRatioG, hval]
end Nodes

end QED.ChainProof.SetAKS

end
