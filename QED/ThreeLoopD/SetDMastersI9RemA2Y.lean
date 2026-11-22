/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ExtraIntegrals

/-!
# Set (d), master `I₉`: the `y`-integral of `S₂` in the second Taylor coefficient of `Rem`

For `a, w > 0`, `b = a + w`, `P = a + w y` and `f(t) = t log² t`, the `y`-subtraction
`S₂(y) = f(P) - f(w y) - (1 - y) f(a) - y f(b) + y f(w)` (the function `i9RemS 2` of
`QED.ThreeLoopD.SetDMastersI9RemTaylor` at `a = P₀`) has, with `q = w / b`,

  `∫₀¹ S₂ / (y (1 - y)) dy = (a + b) F(q) + a/3 · log³ (b/a) + 2 a log a · Li₂ q
      + a log a · log² (b/a) + 4 a ζ(3) - 2 b log b · Li₂ q + π²/3 · w log w`,

where `F(v) = log v log² (1 - v) + 2 log (1 - v) Li₂ (1 - v) - 2 Li₃ (1 - v)` is
`QED.Polylog.logOneSubSqPrim`, the antiderivative of `log² (1 - v) / v`. The proof is one
antiderivative in `y`, from the pointwise splitting

  `S₂ / (y (1 - y)) = a (log² P - log² a) / y + b (log² P - log² b) / (1 - y)
      - w (log² (w y) - log² w) / (1 - y)`,

with every polylogarithm argument in `[0, 1]`. Integrability is a hypothesis, as in
`QED.ThreeLoopD.integral_i9RemS1_div`.

## Main results

* `QED.ThreeLoopD.integral_i9A2S2_div`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- The `y`-subtraction `S₂` of `t log² t`, for general `a, w` (`P = a + w y`, `b = a + w`). -/
noncomputable def i9A2S2 (a w y : ℝ) : ℝ :=
  (a + w * y) * Real.log (a + w * y) ^ 2 - w * y * Real.log (w * y) ^ 2 -
    (1 - y) * a * Real.log a ^ 2 - y * (a + w) * Real.log (a + w) ^ 2 + y * w * Real.log w ^ 2

/-- The closed form of `∫₀¹ S₂ / (y (1 - y)) dy`. -/
noncomputable def i9A2Y2 (a w : ℝ) : ℝ :=
  (a + (a + w)) * logOneSubSqPrim (w / (a + w)) + a / 3 * Real.log ((a + w) / a) ^ 3 +
    2 * a * Real.log a * Li₂ (w / (a + w)) + a * Real.log a * Real.log ((a + w) / a) ^ 2 +
    4 * a * zeta3 - 2 * (a + w) * Real.log (a + w) * Li₂ (w / (a + w)) +
    π ^ 2 / 3 * w * Real.log w

/-- The `y`-antiderivative of `S₂ / (y (1 - y))`. -/
noncomputable def i9A2H2 (a w y : ℝ) : ℝ :=
  a * (logOneSubSqPrim (w * y / (a + w * y)) + Real.log ((a + w * y) / a) ^ 3 / 3 +
      2 * Real.log a * (Li₂ (w * y / (a + w * y)) + Real.log ((a + w * y) / a) ^ 2 / 2)) -
    (a + w) * logOneSubSqPrim (w / (a + w) * (1 - y)) +
    2 * (a + w) * Real.log (a + w) * Li₂ (w / (a + w) * (1 - y)) +
    w * (logOneSubSqPrim (1 - y) - 2 * Real.log w * Li₂ (1 - y))

theorem hasDerivAt_i9A2H2 {a w y : ℝ} (ha : 0 < a) (hw : 0 < w) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => i9A2H2 a w y) (i9A2S2 a w y / (y * (1 - y))) y := by
  obtain ⟨hy0, hy1⟩ := hy
  have hy1' : 0 < 1 - y := by linarith
  have hP : 0 < a + w * y := by positivity
  have hb : 0 < a + w := by positivity
  -- `v = w y / P`
  have hv : HasDerivAt (fun y => w * y / (a + w * y)) (w * a / (a + w * y) ^ 2) y := by
    have h1 : HasDerivAt (fun y => w * y) w y := by simpa using (hasDerivAt_id y).const_mul w
    convert h1.div (h1.const_add a) hP.ne' using 1
    field_simp
    ring
  have hv0 : 0 < w * y / (a + w * y) := by positivity
  have hv1 : w * y / (a + w * y) < 1 := by rw [div_lt_one hP]; linarith
  have hFv := (hasDerivAt_logOneSubSqPrim ⟨hv0, hv1⟩).comp y hv
  have hLv := (hasDerivAt_Li₂' ⟨hv0, hv1⟩).comp y hv
  -- `ℓ = log (P / a)`
  have hl : HasDerivAt (fun y => Real.log ((a + w * y) / a)) (w / (a + w * y)) y := by
    have h2 : HasDerivAt (fun y => (a + w * y) / a) (w / a) y := by
      simpa using (((hasDerivAt_id y).const_mul w).const_add a).div_const a
    convert h2.log (by positivity) using 1
    field_simp
  -- `r = q (1 - y)`
  have hr : HasDerivAt (fun y => w / (a + w) * (1 - y)) (-(w / (a + w))) y := by
    simpa using ((hasDerivAt_id y).const_sub 1).const_mul (w / (a + w))
  have hr0 : 0 < w / (a + w) * (1 - y) := by positivity
  have hr1 : w / (a + w) * (1 - y) < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one hb]; nlinarith
  have hFr := (hasDerivAt_logOneSubSqPrim ⟨hr0, hr1⟩).comp y hr
  have hLr := (hasDerivAt_Li₂' ⟨hr0, hr1⟩).comp y hr
  -- `1 - y`
  have hs : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have hFs := (hasDerivAt_logOneSubSqPrim ⟨hy1', by linarith⟩).comp y hs
  have hLs := (hasDerivAt_Li₂' ⟨hy1', by linarith⟩).comp y hs
  have h := ((((hFv.add ((hl.pow 3).div_const 3)).add ((hLv.add ((hl.pow 2).div_const 2)).const_mul
    (2 * Real.log a))).const_mul a).sub (hFr.const_mul (a + w))).add
    (hLr.const_mul (2 * (a + w) * Real.log (a + w)))
  have h' := h.add ((hFs.sub (hLs.const_mul (2 * Real.log w))).const_mul w)
  refine h'.congr_deriv ?_
  -- the derivative identity
  have e1 : 1 - w * y / (a + w * y) = a / (a + w * y) := by field_simp; ring
  have e2 : 1 - w / (a + w) * (1 - y) = (a + w * y) / (a + w) := by field_simp; ring
  have e3 : (1 : ℝ) - (1 - y) = y := by ring
  rw [e1, e2, e3, Real.log_div ha.ne' hP.ne', Real.log_div hP.ne' hb.ne',
    Real.log_div hP.ne' ha.ne']
  unfold i9A2S2
  rw [Real.log_mul hw.ne' hy0.ne']
  field_simp
  ring

/-- `v = w y / (a + w y) → 0⁺` as `y → 0⁺`. -/
theorem tendsto_i9A2_v_zero {a w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    Tendsto (fun y => w * y / (a + w * y)) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : ContinuousAt (fun y => w * y / (a + w * y)) 0 :=
      ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [ha.ne'])
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
    have := hy.1
    exact div_pos (by positivity) (by positivity)

/-- `q (1 - y) → 0⁺` as `y → 1⁻`. -/
theorem tendsto_i9A2_r_one {q : ℝ} (hq : 0 < q) :
    Tendsto (fun y => q * (1 - y)) (𝓝[<] 1) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : ContinuousAt (fun y : ℝ => q * (1 - y)) 1 := by fun_prop
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y (hy : y < 1)
    exact mul_pos hq (by linarith)

/-- `Li₂ ∘ g` is continuous at a point where `g` is continuous with value in `(-1, 1)`. -/
theorem tendsto_i9A2_Li₂ {g : ℝ → ℝ} {y₀ : ℝ} {l : Filter ℝ} (hl : l ≤ 𝓝 y₀)
    (hg : ContinuousAt g y₀) (h0 : -1 < g y₀) (h1 : g y₀ < 1) :
    Tendsto (fun y => Li₂ (g y)) l (𝓝 (Li₂ (g y₀))) :=
  ((continuousOn_Li₂.continuousAt (Icc_mem_nhds h0 h1)).tendsto.comp hg.tendsto).mono_left hl

/-- `logOneSubSqPrim ∘ g` likewise, at a value in `(0, 1)`. -/
theorem tendsto_i9A2_F {g : ℝ → ℝ} {y₀ : ℝ} {l : Filter ℝ} (hl : l ≤ 𝓝 y₀)
    (hg : ContinuousAt g y₀) (h0 : 0 < g y₀) (h1 : g y₀ < 1) :
    Tendsto (fun y => logOneSubSqPrim (g y)) l (𝓝 (logOneSubSqPrim (g y₀))) :=
  (((hasDerivAt_logOneSubSqPrim ⟨h0, h1⟩).continuousAt.tendsto).comp hg.tendsto).mono_left hl

theorem tendsto_i9A2H2_zero {a w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    Tendsto (fun y => i9A2H2 a w y) (𝓝[>] 0)
      (𝓝 (a * (-2 * zeta3 + 0 / 3 + 2 * Real.log a * (Li₂ 0 + 0 / 2)) -
        (a + w) * logOneSubSqPrim (w / (a + w)) +
        2 * (a + w) * Real.log (a + w) * Li₂ (w / (a + w)) +
        w * (0 - 2 * Real.log w * (π ^ 2 / 6)))) := by
  have hb : 0 < a + w := by positivity
  have hq0 : 0 < w / (a + w) := by positivity
  have hq1 : w / (a + w) < 1 := by rw [div_lt_one hb]; linarith
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have hvc : ContinuousAt (fun y => w * y / (a + w * y)) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by simp [ha.ne'])
  have hlc : ContinuousAt (fun y => Real.log ((a + w * y) / a)) 0 :=
    ContinuousAt.log (by fun_prop) (by simp [ha.ne'])
  have hl0 : Real.log ((a + w * 0) / a) = 0 := by simp [ha.ne']
  have hl := hlc.tendsto.mono_left hle
  rw [hl0] at hl
  have hFv := tendsto_logOneSubSqPrim_zero.comp (tendsto_i9A2_v_zero ha hw)
  have hLv := tendsto_i9A2_Li₂ hle hvc (by simp) (by simp)
  simp only [mul_zero, zero_div] at hLv
  have hrc : ContinuousAt (fun y : ℝ => w / (a + w) * (1 - y)) 0 := by fun_prop
  have hFr := tendsto_i9A2_F hle hrc (by simpa using hq0) (by simpa using hq1)
  have hLr := tendsto_i9A2_Li₂ hle hrc (by simp; linarith) (by simpa using hq1)
  have hFs := tendsto_logOneSubSqPrim_one.comp tendsto_one_sub_nhdsGT_zero
  have hLs := tendsto_Li₂_one_left.comp tendsto_one_sub_nhdsGT_zero
  simp only [sub_zero, mul_one] at hFr hLr
  have h := ((((hFv.add ((hl.pow 3).div_const 3)).add
    ((hLv.add ((hl.pow 2).div_const 2)).const_mul (2 * Real.log a))).const_mul a).sub
    (hFr.const_mul (a + w))).add (hLr.const_mul (2 * (a + w) * Real.log (a + w)))
  have h' := h.add ((hFs.sub (hLs.const_mul (2 * Real.log w))).const_mul w)
  convert h' using 2
  · simp [i9A2H2]
  · simp

theorem tendsto_i9A2H2_one {a w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    Tendsto (fun y => i9A2H2 a w y) (𝓝[<] 1)
      (𝓝 (a * (logOneSubSqPrim (w / (a + w)) + Real.log ((a + w) / a) ^ 3 / 3 +
          2 * Real.log a * (Li₂ (w / (a + w)) + Real.log ((a + w) / a) ^ 2 / 2)) -
        (a + w) * (-2 * zeta3) + 2 * (a + w) * Real.log (a + w) * Li₂ 0 +
        w * (-2 * zeta3 - 2 * Real.log w * Li₂ 0))) := by
  have hb : 0 < a + w := by positivity
  have hq0 : 0 < w / (a + w) := by positivity
  have hq1 : w / (a + w) < 1 := by rw [div_lt_one hb]; linarith
  have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have hvc : ContinuousAt (fun y => w * y / (a + w * y)) 1 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by simp; linarith)
  have hlc : ContinuousAt (fun y => Real.log ((a + w * y) / a)) 1 :=
    ContinuousAt.log (by fun_prop) (by simp; exact ⟨hb.ne', ha.ne'⟩)
  have hl := hlc.tendsto.mono_left hle
  simp only [mul_one] at hl
  have hFv := tendsto_i9A2_F hle hvc (by simpa using hq0) (by simpa using hq1)
  have hLv := tendsto_i9A2_Li₂ hle hvc (by simp; linarith) (by simpa using hq1)
  simp only [mul_one] at hFv hLv
  have hFr := tendsto_logOneSubSqPrim_zero.comp (tendsto_i9A2_r_one hq0)
  have hrc : ContinuousAt (fun y : ℝ => w / (a + w) * (1 - y)) 1 := by fun_prop
  have hLr := tendsto_i9A2_Li₂ hle hrc (by simp) (by simp)
  have hFs := tendsto_logOneSubSqPrim_zero.comp tendsto_one_sub_nhdsLT_one
  have hsc : ContinuousAt (fun y : ℝ => 1 - y) 1 := by fun_prop
  have hLs := tendsto_i9A2_Li₂ hle hsc (by simp) (by simp)
  simp only [sub_self, mul_zero] at hLr hLs
  have h := ((((hFv.add ((hl.pow 3).div_const 3)).add
    ((hLv.add ((hl.pow 2).div_const 2)).const_mul (2 * Real.log a))).const_mul a).sub
    (hFr.const_mul (a + w))).add (hLr.const_mul (2 * (a + w) * Real.log (a + w)))
  have h' := h.add ((hFs.sub (hLs.const_mul (2 * Real.log w))).const_mul w)
  convert h' using 2
  simp [i9A2H2]

/-- **The `y`-integral of `S₂ / (y (1 - y))`.** -/
theorem integral_i9A2S2_div {a w : ℝ} (ha : 0 < a) (hw : 0 < w)
    (hint : IntegrableOn (fun y => i9A2S2 a w y / (y * (1 - y))) (Ioo 0 1)) :
    ∫ y in Ioo (0 : ℝ) 1, i9A2S2 a w y / (y * (1 - y)) = i9A2Y2 a w := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun y hy => hasDerivAt_i9A2H2 ha hw hy)
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hint)
    (tendsto_i9A2H2_zero ha hw) (tendsto_i9A2H2_one ha hw)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hFTC
  rw [hFTC, i9A2Y2, Li₂_zero]
  ring

end QED.ThreeLoopD
