/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Deriv
public import QED.Polylog.ExtraIntegrals
import QED.Polylog.LiLimits
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₁₅`: primitives of products of logarithms

The weight-two primitives behind the inner integrals of `∫ F₂`
(`QED.ThreeLoopD.SetDMastersI15KValTwo`). For `a, b > 0`, `0 < v ≤ 1`, `0 < u < 1`:

* `i15VLL a b`: a primitive of `log x · log (a + b x)`, built from `Li₂ (b x / (a + b x))`;
* `i15VLM v`: a primitive of `log x · log (1 - v x)`, built from `Li₂ (v x)`;
* `i15VL p q`, `i15VL2 p q`: primitives of `log (p + q x)` and `log² (p + q x)`;
* `i15VAB u`: a primitive of `log (u + v x) · log (1 - v x)`, `v = 1 - u`, built from
  `Li₂ ((1 - v x) / (1 + u))`;
* `i15VCR a b`: for `0 < a < b`, `a + b = 1`, a primitive of `log (a + b u) · log (b + a u)`,
  built from `Li₂ ((b - a) / (b (b + a u)))`.

All dilogarithm arguments stay in `(0, 1)`. The file also records the one-sided limits at `0`
that need more than continuity.
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-! ### A limit -/

/-- `log x · g x → 0` at `0⁺` when `|g x| ≤ C x` eventually. -/
theorem i15V_tendsto_log_mul_of_abs_le {g : ℝ → ℝ} {C : ℝ}
    (hb : ∀ᶠ x in 𝓝[>] (0 : ℝ), |g x| ≤ C * x) :
    Tendsto (fun x => log x * g x) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_mul_log_zero.abs).const_mul |C|
  rw [abs_zero, mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [hb, self_mem_nhdsWithin] with x hx (hx0 : 0 < x)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hx0]
  calc |log x| * |g x| ≤ |log x| * (C * x) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = C * (x * |log x|) := by ring
    _ ≤ |C| * (x * |log x|) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hx0.le (abs_nonneg _))

/-! ### `log x · log (a + b x)` -/

/-- A primitive of `log x · log (a + b x)` (`a, b > 0`). -/
noncomputable def i15VLL (a b x : ℝ) : ℝ :=
  (x * log x - x) * log (a + b * x) - x * log x + 2 * x +
    a / b * (log x * (log (a + b * x) - log a) - Li₂ (b * x / (a + b * x)) -
      (log (a + b * x) - log a) ^ 2 / 2 - log (a + b * x))

theorem hasDerivAt_i15VLL {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    HasDerivAt (i15VLL a b) (log x * log (a + b * x)) x := by
  have hD : 0 < a + b * x := by positivity
  have hw0 : 0 < b * x / (a + b * x) := by positivity
  have hw1 : b * x / (a + b * x) < 1 := by rw [div_lt_one hD]; linarith
  have hlin : HasDerivAt (fun x => a + b * x) b x := by
    simpa using ((hasDerivAt_id x).const_mul b).const_add a
  have hA := hlin.log hD.ne'
  have hl := Real.hasDerivAt_log hx.ne'
  have hxl : HasDerivAt (fun x => x * log x) (log x + 1) x := Real.hasDerivAt_mul_log hx.ne'
  have hwd : HasDerivAt (fun x => b * x / (a + b * x))
      ((b * 1 * (a + b * x) - b * x * (b * 1)) / (a + b * x) ^ 2) x :=
    ((hasDerivAt_id x).const_mul b).div (((hasDerivAt_id x).const_mul b).const_add a) hD.ne'
  have hLi := (hasDerivAt_Li₂ (by rw [abs_of_pos hw0]; exact hw1) hw0.ne').comp x hwd
  have hA' := hA.sub_const (log a)
  have h1 := ((hxl.sub (hasDerivAt_id x)).mul hA).sub hxl
  have h2 := (h1.add ((hasDerivAt_id x).const_mul 2))
  have h3 := (((hl.mul hA').sub hLi).sub ((hA'.pow 2).div_const 2)).sub hA
  have h := h2.add (h3.const_mul (a / b))
  convert h using 1
  · funext y
    simp only [i15VLL, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply,
      Function.comp_apply, id]
  have e1 : 1 - b * x / (a + b * x) = a / (a + b * x) := by field_simp; ring
  simp only [Pi.sub_apply, id, e1, Real.log_div ha.ne' hD.ne']
  field_simp
  ring

theorem continuousAt_i15VLL {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    ContinuousAt (i15VLL a b) x :=
  (hasDerivAt_i15VLL ha hb hx).continuousAt

/-- `i15VLL a b → -(a/b) log a` at `0⁺`. -/
theorem tendsto_i15VLL_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (i15VLL a b) (𝓝[>] 0) (𝓝 (-(a / b * log a))) := by
  have hc : ContinuousAt (fun x : ℝ => log (a + b * x)) 0 := by
    have : a + b * 0 ≠ 0 := by simp; exact ha.ne'
    exact (continuous_const.add (continuous_const.mul continuous_id)).continuousAt.log this
  have hA : Tendsto (fun x : ℝ => log (a + b * x)) (𝓝[>] 0) (𝓝 (log a)) := by
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hw : Tendsto (fun x : ℝ => b * x / (a + b * x)) (𝓝[>] 0) (𝓝 0) := by
    have hD : ContinuousAt (fun x : ℝ => b * x / (a + b * x)) 0 := by
      have : a + b * 0 ≠ 0 := by simp; exact ha.ne'
      exact ((continuous_const.mul continuous_id).continuousAt).div
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt this
    have := hD.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hLi : Tendsto (fun x : ℝ => Li₂ (b * x / (a + b * x))) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_Li₂_comp (a := 0) (by norm_num) hw (by
      filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
      have hD : 0 < a + b * x := by positivity
      exact ⟨by linarith [(by positivity : 0 ≤ b * x / (a + b * x))],
        by rw [div_le_one hD]; linarith⟩)
    simpa [Li₂_zero] using this
  have hlog : Tendsto (fun x : ℝ => log x * (log (a + b * x) - log a)) (𝓝[>] 0) (𝓝 0) := by
    refine i15V_tendsto_log_mul_of_abs_le (C := b / a) ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    rw [show a + b * x = a * (1 + b / a * x) by field_simp, Real.log_mul ha.ne' (by positivity),
      add_sub_cancel_left]
    calc |log (1 + b / a * x)| ≤ b / a * x := abs_log_one_add_le (by positivity)
      _ = b / a * x := rfl
  have h := (((((tendsto_mul_log_zero.sub hx0).mul hA).sub tendsto_mul_log_zero).add
    (hx0.const_mul 2)).add ((((hlog.sub hLi).sub
      (((hA.sub_const (log a)).pow 2).div_const 2)).sub hA).const_mul (a / b)))
  have e : -(a / b * log a) = (0 - 0) * log a - 0 + 2 * 0 +
      a / b * (0 - 0 - (log a - log a) ^ 2 / 2 - log a) := by ring
  rw [e]
  exact h

/-! ### `log x · log (1 - v x)` -/

/-- A primitive of `log x · log (1 - v x)` (`0 < v ≤ 1`). -/
noncomputable def i15VLM (v x : ℝ) : ℝ :=
  log (1 - v * x) * ((x - 1 / v) * (log x - 1)) - x * log x + 2 * x - Li₂ (v * x) / v

theorem hasDerivAt_i15VLM {v x : ℝ} (hv : 0 < v) (hx : 0 < x) (hvx : v * x < 1) :
    HasDerivAt (i15VLM v) (log x * log (1 - v * x)) x := by
  have hB : 0 < 1 - v * x := by linarith
  have hvx0 : 0 < v * x := mul_pos hv hx
  have hlin : HasDerivAt (fun x => 1 - v * x) (-v) x := by
    simpa using ((hasDerivAt_id x).const_mul v).const_sub 1
  have hBd := hlin.log hB.ne'
  have hl := Real.hasDerivAt_log hx.ne'
  have hxl : HasDerivAt (fun x => x * log x) (log x + 1) x := Real.hasDerivAt_mul_log hx.ne'
  have hLi := (hasDerivAt_Li₂ (by rw [abs_of_pos hvx0]; exact hvx) hvx0.ne').comp x
    ((hasDerivAt_id x).const_mul v)
  have h := (((hBd.mul (((hasDerivAt_id x).sub_const (1 / v)).mul (hl.sub_const 1))).sub hxl).add
    ((hasDerivAt_id x).const_mul 2)).sub (hLi.div_const v)
  convert h using 1
  · funext y
    simp only [i15VLM, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Function.comp_apply, id]
  simp only [Pi.mul_apply, id]
  field_simp
  ring

/-- `i15VLM v → 0` at `0⁺`. -/
theorem tendsto_i15VLM_zero {v : ℝ} (hv : 0 < v) :
    Tendsto (i15VLM v) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous fun x : ℝ => 1 - v * x := by fun_prop
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hB : Tendsto (fun x : ℝ => log (1 - v * x)) (𝓝[>] 0) (𝓝 0) := by
    have := ((hc.continuousAt (x := 0)).log (by simp)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hLB : Tendsto (fun x : ℝ => log x * log (1 - v * x)) (𝓝[>] 0) (𝓝 0) := by
    refine i15V_tendsto_log_mul_of_abs_le (C := 2 * v) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / (2 * v) by positivity)] with x hx
    have h1 : v * x ≤ 1 / 2 := by
      have := hx.2; rw [lt_div_iff₀ (by positivity)] at this; nlinarith
    have := abs_log_one_sub_le (x := v * x) (by nlinarith [hx.1]) h1
    linarith
  have hLi : Tendsto (fun x : ℝ => Li₂ (v * x)) (𝓝[>] 0) (𝓝 0) := by
    have hw : Tendsto (fun x : ℝ => v * x) (𝓝[>] 0) (𝓝 0) := by simpa using hx0.const_mul v
    have := tendsto_Li₂_comp (a := 0) (by norm_num) hw (by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / v by positivity)] with x hx
      have := hx.2; rw [lt_div_iff₀ hv] at this
      exact ⟨by nlinarith [hx.1], by nlinarith⟩)
    simpa [Li₂_zero] using this
  have h1 : Tendsto (fun x : ℝ => log (1 - v * x) * ((x - 1 / v) * (log x - 1)))
      (𝓝[>] 0) (𝓝 0) := by
    have := ((hLB.mul (hx0.sub_const (1 / v))).sub (hB.mul (hx0.sub_const (1 / v))))
    simp only [zero_mul, sub_zero] at this
    refine this.congr fun x => ?_
    ring
  have h := ((h1.sub tendsto_mul_log_zero).add (hx0.const_mul 2)).sub (hLi.div_const v)
  have e : (0 : ℝ) - 0 + 2 * 0 - 0 / v = 0 := by simp
  rw [e] at h
  exact h

/-- `i15VLM 1 → 2 - π²/6` at `1⁻`. -/
theorem tendsto_i15VLM_one_one :
    Tendsto (i15VLM 1) (𝓝[<] 1) (𝓝 (2 - π ^ 2 / 6)) := by
  have hc1 : ContinuousAt (fun x : ℝ => x * log x) 1 :=
    Real.continuous_mul_log.continuousAt
  have hxl : Tendsto (fun x : ℝ => x * log x) (𝓝[<] 1) (𝓝 0) := by
    have := hc1.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio 1))
    simpa using this
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun x : ℝ => (x - 1) * (log x - 1) * log (1 - x)) (𝓝[<] 1) (𝓝 0) := by
    refine tendsto_mul_log_one_sub_of_abs_le (C := 2) ?_
    filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hl : |log x| ≤ 1 := by
      rw [abs_le]
      constructor
      · have h2 := Real.log_le_log (by norm_num) hx.1.le
        rw [one_div, Real.log_inv] at h2
        linarith [Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)]
      · have := Real.log_le_sub_one_of_pos hx0
        linarith [hx.2]
    rw [abs_mul, abs_of_neg (by linarith [hx.2] : x - 1 < 0)]
    have : |log x - 1| ≤ 2 := by
      calc |log x - 1| ≤ |log x| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ 2 := by norm_num; linarith
    nlinarith [abs_nonneg (log x - 1), hx.2]
  have hLi : Tendsto (fun x : ℝ => Li₂ x / 1) (𝓝[<] 1) (𝓝 (π ^ 2 / 6 / 1)) :=
    tendsto_Li₂_one_left.div_const 1
  have h := ((h1.sub hxl).add (hx1.const_mul 2)).sub hLi
  have e : (0 : ℝ) - 0 + 2 * 1 - π ^ 2 / 6 / 1 = 2 - π ^ 2 / 6 := by ring
  rw [e] at h
  refine h.congr fun x => ?_
  simp only [i15VLM, one_mul, div_one]
  ring

/-! ### `log (p + q x)` and `log² (p + q x)` -/

/-- A primitive of `log (p + q x)`. -/
noncomputable def i15VL (p q x : ℝ) : ℝ :=
  ((p + q * x) * log (p + q * x) - (p + q * x)) / q

/-- A primitive of `log² (p + q x)`. -/
noncomputable def i15VL2 (p q x : ℝ) : ℝ :=
  ((p + q * x) * log (p + q * x) ^ 2 - 2 * ((p + q * x) * log (p + q * x)) +
    2 * (p + q * x)) / q

theorem hasDerivAt_i15VL {p q x : ℝ} (hq : q ≠ 0) (h : 0 < p + q * x) :
    HasDerivAt (i15VL p q) (log (p + q * x)) x := by
  have hlin : HasDerivAt (fun x => p + q * x) q x := by
    simpa using ((hasDerivAt_id x).const_mul q).const_add p
  have h1 := (hlin.mul (hlin.log h.ne')).sub hlin
  have hne := h.ne'
  convert h1.div_const q using 1
  · funext y; simp only [i15VL, Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

theorem hasDerivAt_i15VL2 {p q x : ℝ} (hq : q ≠ 0) (h : 0 < p + q * x) :
    HasDerivAt (i15VL2 p q) (log (p + q * x) ^ 2) x := by
  have hlin : HasDerivAt (fun x => p + q * x) q x := by
    simpa using ((hasDerivAt_id x).const_mul q).const_add p
  have hL := hlin.log h.ne'
  have h1 := (((hlin.mul (hL.pow 2)).sub ((hlin.mul hL).const_mul 2)).add
    (hlin.const_mul 2))
  have hne := h.ne'
  convert h1.div_const q using 1
  · funext y; simp only [i15VL2, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem continuousOn_i15VL {p q : ℝ} {s : Set ℝ} (h : ∀ x ∈ s, 0 < p + q * x) :
    ContinuousOn (i15VL p q) s := by
  have hc : ContinuousOn (fun x : ℝ => p + q * x) s := by fun_prop
  have hl : ContinuousOn (fun x : ℝ => log (p + q * x)) s := hc.log fun x hx => (h x hx).ne'
  exact ((hc.mul hl).sub hc).div_const q

theorem continuousOn_i15VL2 {p q : ℝ} {s : Set ℝ} (h : ∀ x ∈ s, 0 < p + q * x) :
    ContinuousOn (i15VL2 p q) s := by
  have hc : ContinuousOn (fun x : ℝ => p + q * x) s := by fun_prop
  have hl : ContinuousOn (fun x : ℝ => log (p + q * x)) s := hc.log fun x hx => (h x hx).ne'
  exact (((hc.mul (hl.pow 2)).sub ((hc.mul hl).const_mul 2)).add (hc.const_mul 2)).div_const q

/-! ### `log (u + v x) · log (1 - v x)` -/

/-- A primitive of `log (u + v x) · log (1 - v x)`, `v = 1 - u`. -/
noncomputable def i15VAB (u x : ℝ) : ℝ :=
  i15VL u (1 - u) x * log (1 - (1 - u) * x) - (i15VL u (1 - u) x - x) +
    (1 + u) * (-(log (1 + u) * log (1 - (1 - u) * x) -
      Li₂ ((1 - (1 - u) * x) / (1 + u))) / (1 - u) + log (1 - (1 - u) * x) / (1 - u))

theorem hasDerivAt_i15VAB {u x : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (i15VAB u) (log (u + (1 - u) * x) * log (1 - (1 - u) * x)) x := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hx0, hx1⟩ := hx
  have hv : 0 < 1 - u := by linarith
  have hA : 0 < u + (1 - u) * x := by nlinarith
  have hB : 0 < 1 - (1 - u) * x := by nlinarith
  have hs : 0 < 1 + u := by linarith
  have hw0 : 0 < (1 - (1 - u) * x) / (1 + u) := by positivity
  have hw1 : (1 - (1 - u) * x) / (1 + u) < 1 := by
    rw [div_lt_one hs]; nlinarith
  have hlinB : HasDerivAt (fun x => 1 - (1 - u) * x) (-(1 - u)) x := by
    simpa using ((hasDerivAt_id x).const_mul (1 - u)).const_sub 1
  have hBd := hlinB.log hB.ne'
  have hPA := hasDerivAt_i15VL (p := u) (q := 1 - u) (x := x) hv.ne' hA
  have hLi := (hasDerivAt_Li₂ (by rw [abs_of_pos hw0]; exact hw1) hw0.ne').comp x
    (hlinB.div_const (1 + u))
  have h := ((hPA.mul hBd).sub (hPA.sub (hasDerivAt_id x))).add
    (((((hBd.const_mul (log (1 + u))).sub hLi).neg.div_const (1 - u)).add
      (hBd.div_const (1 - u))).const_mul (1 + u))
  convert h using 1
  · funext y; simp [i15VAB, Function.comp_def]
  have e1 : 1 - (1 - (1 - u) * x) / (1 + u) = (u + (1 - u) * x) / (1 + u) := by
    field_simp; ring
  simp only [e1, Real.log_div hA.ne' hs.ne']
  unfold i15VL
  field_simp
  ring

theorem continuousOn_i15VAB {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (i15VAB u) (Icc 0 1) := by
  obtain ⟨hu0, hu1⟩ := hu
  have hA : ∀ x ∈ Icc (0 : ℝ) 1, 0 < u + (1 - u) * x := fun x hx => by nlinarith [hx.1]
  have hB : ∀ x ∈ Icc (0 : ℝ) 1, 0 < 1 - (1 - u) * x := fun x hx => by nlinarith [hx.2]
  have hPA : ContinuousOn (i15VL u (1 - u)) (Icc 0 1) := continuousOn_i15VL hA
  have hLB : ContinuousOn (fun x : ℝ => log (1 - (1 - u) * x)) (Icc 0 1) :=
    (by fun_prop : Continuous fun x : ℝ => 1 - (1 - u) * x).continuousOn.log
      fun x hx => (hB x hx).ne'
  have hLi : ContinuousOn (fun x : ℝ => Li₂ ((1 - (1 - u) * x) / (1 + u))) (Icc 0 1) :=
    continuousOn_Li₂.comp (by fun_prop) fun x hx => by
      have := hB x hx
      have hs : 0 < 1 + u := by linarith
      exact ⟨by linarith [(by positivity : 0 ≤ (1 - (1 - u) * x) / (1 + u))],
        by rw [div_le_one hs]; nlinarith [hx.1]⟩
  unfold i15VAB
  exact ((hPA.mul hLB).sub (hPA.sub continuousOn_id)).add (continuousOn_const.mul
    ((((continuousOn_const.mul hLB).sub hLi).neg.div_const _).add (hLB.div_const _)))

/-! ### `log (a + b u) · log (b + a u)` -/

/-- For `0 < a < b`, `a + b = 1`: a primitive of `log (a + b u) · log (b + a u)`. -/
noncomputable def i15VCR (a b u : ℝ) : ℝ :=
  i15VL a b u * log (b + a * u) - (i15VL a b u - u) -
    (a - b) / (a * b) * (log (b / a) * log (b + a * u) + log (b + a * u) ^ 2 / 2 +
      Li₂ ((b - a) / (b * (b + a * u))) - log (b + a * u))

theorem i15VCR_arg_pos {a b u : ℝ} (ha : 0 < a) (hab : a < b) (hu : 0 ≤ u) :
    0 < (b - a) / (b * (b + a * u)) := by
  have hb : 0 < b := by linarith
  have : 0 < b + a * u := by positivity
  apply div_pos (by linarith) (by positivity)

theorem i15VCR_arg_lt {a b u : ℝ} (ha : 0 < a) (hab : a < b) (h1 : a + b = 1) (hu : 0 ≤ u) :
    (b - a) / (b * (b + a * u)) < 1 := by
  have hb : 0 < b := by linarith
  have : 0 < b * (b + a * u) := by positivity
  rw [div_lt_one this]
  have : b - a < b * b := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hb.le ha.le) hu]

theorem hasDerivAt_i15VCR {a b u : ℝ} (ha : 0 < a) (hab : a < b) (h1 : a + b = 1)
    (hu : 0 ≤ u) :
    HasDerivAt (i15VCR a b) (log (a + b * u) * log (b + a * u)) u := by
  have hb : 0 < b := by linarith
  have hA : 0 < a + b * u := by positivity
  have hB : 0 < b + a * u := by positivity
  have hw0 := i15VCR_arg_pos ha hab hu
  have hw1 := i15VCR_arg_lt ha hab h1 hu
  have hlinB : HasDerivAt (fun u => b + a * u) a u := by
    simpa using ((hasDerivAt_id u).const_mul a).const_add b
  have hBd := hlinB.log hB.ne'
  have hPA := hasDerivAt_i15VL (p := a) (q := b) (x := u) hb.ne' hA
  have hwd : HasDerivAt (fun u => (b - a) / (b * (b + a * u)))
      (-((b - a) * (b * a)) / (b * (b + a * u)) ^ 2) u := by
    have := (hlinB.const_mul b).inv (by positivity)
    have h2 := this.const_mul (b - a)
    convert h2 using 1
    · funext y; simp [div_eq_mul_inv]
    · field_simp
  have hLi := (hasDerivAt_Li₂ (by rw [abs_of_pos hw0]; exact hw1) hw0.ne').comp u hwd
  have h := ((hPA.mul hBd).sub (hPA.sub (hasDerivAt_id u))).sub
    (((((hBd.const_mul (log (b / a))).add ((hBd.pow 2).div_const 2)).add hLi).sub
      hBd).const_mul ((a - b) / (a * b)))
  convert h using 1
  · funext y; simp [i15VCR, Function.comp_def]
  have e1 : 1 - (b - a) / (b * (b + a * u)) = a * (a + b * u) / (b * (b + a * u)) := by
    field_simp
    have : b = 1 - a := by linarith
    subst this
    ring
  simp only [e1]
  rw [Real.log_div hb.ne' ha.ne', Real.log_div (x := a * (a + b * u)) (y := b * (b + a * u))
    (by positivity) (by positivity), Real.log_mul ha.ne' hA.ne', Real.log_mul hb.ne' hB.ne']
  unfold i15VL
  have hb' : b = 1 - a := by linarith
  subst hb'
  field_simp
  ring

theorem continuousOn_i15VCR {a b : ℝ} (ha : 0 < a) (hab : a < b) (h1 : a + b = 1) :
    ContinuousOn (i15VCR a b) (Icc 0 1) := by
  have hb : 0 < b := by linarith
  have hA : ∀ u ∈ Icc (0 : ℝ) 1, 0 < a + b * u := fun u hu => by nlinarith [hu.1]
  have hB : ∀ u ∈ Icc (0 : ℝ) 1, 0 < b + a * u := fun u hu => by nlinarith [hu.1]
  have hPA : ContinuousOn (i15VL a b) (Icc 0 1) := continuousOn_i15VL hA
  have hLB : ContinuousOn (fun u : ℝ => log (b + a * u)) (Icc 0 1) :=
    (by fun_prop : Continuous fun u : ℝ => b + a * u).continuousOn.log
      fun u hu => (hB u hu).ne'
  have hLi : ContinuousOn (fun u : ℝ => Li₂ ((b - a) / (b * (b + a * u)))) (Icc 0 1) :=
    continuousOn_Li₂.comp
      ((continuousOn_const).div (by fun_prop) fun u hu => (mul_pos hb (hB u hu)).ne')
      fun u hu => ⟨by linarith [i15VCR_arg_pos ha hab hu.1],
        (i15VCR_arg_lt ha hab h1 hu.1).le⟩
  unfold i15VCR
  exact ((hPA.mul hLB).sub (hPA.sub continuousOn_id)).sub (continuousOn_const.mul
    ((((continuousOn_const.mul hLB).add ((hLB.pow 2).div_const 2)).add hLi).sub hLB))

end QED.ThreeLoopD
