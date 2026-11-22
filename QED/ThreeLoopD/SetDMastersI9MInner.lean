/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.Polylog.ExtraIntegrals
import QED.ThreeLoopD.SetDMastersI9KValB
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Set (d), master `I₉`: the `x`-integrals behind `M₂`

Fix `w ∈ (0, 1)` and write `u = 1 - w`, `A = w + u x`, `B = 1 - u x` (so `P = c u² + w = A B`
with `c = x (1 - x)`). The `x`-integrand of the Taylor coefficient `M₂` of
`QED.ThreeLoopD.i9M` is, up to the factor `-(3/2)(1 - w²)/w`, the sum `s(x) + s(1 - x)` of

  `s = 4 log w (log A - log x) - 3 log² A - 3 log A log B + 4 log x log A + 4 log x log B
      - log² (x (1 - x)) / 2`.

This file computes `∫₀¹ s` from the closed forms

* `∫₀¹ log A = -1 - w log w / u`, `∫₀¹ log² A = 2 + (2 w log w - w log² w)/u`;
* `∫₀¹ log x log A = 2 + w log w / u - w (Li₂ u + log² w / 2)/u`;
* `∫₀¹ log x log B = 2 + w log w / u - Li₂ u / u`;
* `u ∫₀¹ log A log B = 2 - 2w - (1 - w) log w + (1 + w) (log w - log (1 + w) log w
    + Li₂ (w/(1 + w)) - Li₂ (1/(1 + w)))`,

each by an explicit antiderivative (all dilogarithm arguments in `(0, 1)`).

## Main results

* `QED.ThreeLoopD.i9M2S_integral`: integrability of `s` on `[0, 1]` and `∫₀¹ s = i9M2Sig w`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The half-integrand `s` of `M₂` at fixed `w` (see the module docstring). -/
noncomputable def i9M2S (w x : ℝ) : ℝ :=
  4 * Real.log w * (Real.log (w + (1 - w) * x) - Real.log x) -
    3 * Real.log (w + (1 - w) * x) ^ 2 -
    3 * (Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x)) +
    4 * (Real.log x * Real.log (w + (1 - w) * x)) +
    4 * (Real.log x * Real.log (1 - (1 - w) * x)) - Real.log (x * (1 - x)) ^ 2 / 2

/-- `∫₀¹ log A log B`, in closed form. -/
noncomputable def i9M2JAB (w : ℝ) : ℝ :=
  (2 - 2 * w - (1 - w) * Real.log w + (1 + w) * (Real.log w -
    Real.log (1 + w) * Real.log w + Li₂ (w / (1 + w)) - Li₂ (1 / (1 + w)))) / (1 - w)

/-- The value of `∫₀¹ s`. -/
noncomputable def i9M2Sig (w : ℝ) : ℝ :=
  4 * Real.log w * (-1 - w * Real.log w / (1 - w) + 1) -
    3 * (2 + (2 * w * Real.log w - w * Real.log w ^ 2) / (1 - w)) - 3 * i9M2JAB w +
    4 * (2 + w * Real.log w / (1 - w) - w * (Li₂ (1 - w) + Real.log w ^ 2 / 2) / (1 - w)) +
    4 * (2 + w * Real.log w / (1 - w) - Li₂ (1 - w) / (1 - w)) - (8 - π ^ 2 / 3) / 2

/-! ### Tools -/

/-- One step of a linear combination of integrals over `[0, 1]`. -/
theorem i9M2_step {F g : ℝ → ℝ} {V W : ℝ}
    (hF : IntervalIntegrable F volume 0 1 ∧ ∫ x in (0 : ℝ)..1, F x = V)
    (hg : IntervalIntegrable g volume 0 1 ∧ ∫ x in (0 : ℝ)..1, g x = W) (c : ℝ) :
    IntervalIntegrable (fun x => F x + c * g x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (F x + c * g x) = V + c * W :=
  ⟨hF.1.add (hg.1.const_mul c), by
    rw [intervalIntegral.integral_add hF.1 (hg.1.const_mul c),
      intervalIntegral.integral_const_mul, hF.2, hg.2]⟩

theorem i9M2_hasDerivAt_A (w x : ℝ) : HasDerivAt (fun x => w + (1 - w) * x) (1 - w) x := by
  simpa using ((hasDerivAt_id x).const_mul (1 - w)).const_add w

theorem i9M2_hasDerivAt_B (w x : ℝ) : HasDerivAt (fun x => 1 - (1 - w) * x) (-(1 - w)) x := by
  simpa using ((hasDerivAt_id x).const_mul (1 - w)).const_sub 1

theorem i9M2_A_pos {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : 0 ≤ x) : 0 < w + (1 - w) * x := by
  have : 0 ≤ (1 - w) * x := mul_nonneg (by linarith [hw.2]) hx
  linarith [hw.1]

theorem i9M2_B_pos {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ≤ 1) : 0 < 1 - (1 - w) * x := by
  have : (1 - w) * x ≤ 1 - w := mul_le_of_le_one_right (by linarith [hw.2]) hx
  linarith [hw.1]

theorem i9M2_A_le {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ≤ 1) : w + (1 - w) * x ≤ 1 := by
  have : (1 - w) * x ≤ 1 - w := mul_le_of_le_one_right (by linarith [hw.2]) hx
  linarith

theorem i9M2_B_le {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : 0 ≤ x) : 1 - (1 - w) * x ≤ 1 := by
  have : 0 ≤ (1 - w) * x := mul_nonneg (by linarith [hw.2]) hx
  linarith

/-- A function continuous at `a` tends to its value at `a` along any punctured side. -/
theorem i9M2_tendsto_of_continuousAt {f : ℝ → ℝ} {a : ℝ} {s : Set ℝ} (hf : ContinuousAt f a) :
    Tendsto f (𝓝[s] a) (𝓝 (f a)) :=
  hf.tendsto.mono_left nhdsWithin_le_nhds

/-! ### The single and squared logarithm of `A` -/

theorem i9M2_logA {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) = -1 - w * Real.log w / (1 - w) := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hA : ∀ x ∈ uIcc (0 : ℝ) 1, 0 < w + (1 - w) * x := fun x hx => by
    rw [uIcc_of_le zero_le_one] at hx; exact i9M2_A_pos hw hx.1
  have hint : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x)) volume 0 1 :=
    (ContinuousOn.log (by fun_prop) fun x hx => (hA x hx).ne').intervalIntegrable
  refine ⟨hint, ?_⟩
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x => ((w + (1 - w) * x) *
      Real.log (w + (1 - w) * x) - (w + (1 - w) * x)) / (1 - w))
      (Real.log (w + (1 - w) * x)) x := by
    intro x hx
    have hAx := (hA x hx).ne'
    have h1 := i9M2_hasDerivAt_A w x
    have h2 := ((h1.mul (h1.log hAx)).sub h1).div_const (1 - w)
    refine h2.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  norm_num
  field_simp
  ring

theorem i9M2_logA_sq {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) ^ 2 =
        2 + (2 * w * Real.log w - w * Real.log w ^ 2) / (1 - w) := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hA : ∀ x ∈ uIcc (0 : ℝ) 1, 0 < w + (1 - w) * x := fun x hx => by
    rw [uIcc_of_le zero_le_one] at hx; exact i9M2_A_pos hw hx.1
  have hint : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) ^ 2) volume 0 1 :=
    ((ContinuousOn.log (by fun_prop) fun x hx => (hA x hx).ne').pow 2).intervalIntegrable
  refine ⟨hint, ?_⟩
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x => ((w + (1 - w) * x) *
      (Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x)) -
      2 * ((w + (1 - w) * x) * Real.log (w + (1 - w) * x)) + 2 * (w + (1 - w) * x)) / (1 - w))
      (Real.log (w + (1 - w) * x) ^ 2) x := by
    intro x hx
    have hAx := (hA x hx).ne'
    have h1 := i9M2_hasDerivAt_A w x
    have hl := h1.log hAx
    have h2 := (((h1.mul (hl.mul hl)).sub ((h1.mul hl).const_mul 2)).add
      (h1.const_mul 2)).div_const (1 - w)
    refine h2.congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  norm_num
  field_simp
  ring

/-! ### `log A log B` -/

/-- The antiderivative of `log A log B`. -/
noncomputable def i9M2FAB (w x : ℝ) : ℝ :=
  ((w + (1 - w) * x) * Real.log (w + (1 - w) * x) - (w + (1 - w) * x)) *
      Real.log (1 - (1 - w) * x) / (1 - w) +
    (1 + w) * (-(Real.log (1 + w) * Real.log (1 - (1 - w) * x)) / (1 - w) +
      Li₂ ((1 - (1 - w) * x) / (1 + w)) / (1 - w) + Real.log (1 - (1 - w) * x) / (1 - w)) -
    ((w + (1 - w) * x) * Real.log (w + (1 - w) * x) - 2 * (w + (1 - w) * x)) / (1 - w)

theorem i9M2_logA_logB {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x))
      volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) =
        i9M2JAB w := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hA : ∀ x ∈ uIcc (0 : ℝ) 1, 0 < w + (1 - w) * x := fun x hx => by
    rw [uIcc_of_le zero_le_one] at hx; exact i9M2_A_pos hw hx.1
  have hB : ∀ x ∈ uIcc (0 : ℝ) 1, 0 < 1 - (1 - w) * x := fun x hx => by
    rw [uIcc_of_le zero_le_one] at hx; exact i9M2_B_pos hw hx.2
  have hint : IntervalIntegrable
      (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x)) volume 0 1 :=
    ((ContinuousOn.log (by fun_prop) fun x hx => (hA x hx).ne').mul
      (ContinuousOn.log (by fun_prop) fun x hx => (hB x hx).ne')).intervalIntegrable
  refine ⟨hint, ?_⟩
  have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (i9M2FAB w)
      (Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x)) x := by
    intro x hx
    have hAx := hA x hx
    have hBx := hB x hx
    have ha : 0 < 1 + w := by linarith
    have hBa : (1 - (1 - w) * x) / (1 + w) ∈ Ioo (0 : ℝ) 1 :=
      ⟨by positivity, by rw [div_lt_one ha]; linarith⟩
    have h1 := i9M2_hasDerivAt_A w x
    have h2 := i9M2_hasDerivAt_B w x
    have hlA := h1.log hAx.ne'
    have hlB := h2.log hBx.ne'
    have hLi := (hasDerivAt_Li₂' hBa).comp x (h2.div_const (1 + w))
    have hG1 := (((h1.mul hlA).sub h1).mul hlB).div_const (1 - w)
    have hG2 := ((((hlB.const_mul (Real.log (1 + w))).neg.div_const (1 - w)).add
        (hLi.div_const (1 - w))).add (hlB.div_const (1 - w))).const_mul (1 + w)
    have hG3 := ((h1.mul hlA).sub (h1.const_mul 2)).div_const (1 - w)
    refine ((hG1.add hG2).sub hG3).congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply]
    have e1 : 1 - (1 - (1 - w) * x) / (1 + w) = (w + (1 - w) * x) / (1 + w) := by
      field_simp; ring
    rw [e1, Real.log_div hAx.ne' ha.ne']
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  unfold i9M2FAB i9M2JAB
  norm_num
  field_simp
  ring

/-! ### `log x log A` -/

/-- The antiderivative of `log x log A`. -/
noncomputable def i9M2FXA (w x : ℝ) : ℝ :=
  (x * Real.log x - x) * Real.log (w + (1 - w) * x) - x * Real.log x + 2 * x +
    w / (1 - w) * (Real.log x * Real.log ((w + (1 - w) * x) / w) -
      Li₂ ((1 - w) * x / (w + (1 - w) * x)) -
      Real.log ((w + (1 - w) * x) / w) * Real.log ((w + (1 - w) * x) / w) / 2 -
      Real.log (w + (1 - w) * x))

/-- `|log x log (1 + t x)| ≤ t |x log x|` for `x, t > 0`, so it tends to `0` at `0⁺`. -/
theorem i9M2_tendsto_log_mul_log_one_add {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun x => Real.log x * Real.log (1 + t * x)) (𝓝[>] 0) (𝓝 0) := by
  have hb : Tendsto (fun x => t * ‖x * Real.log x‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_mul_log_zero.norm).const_mul t
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  have h0 : 0 ≤ Real.log (1 + t * x) := Real.log_nonneg (by nlinarith)
  have h1 : Real.log (1 + t * x) ≤ t * x := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + t * x)
    linarith
  simp only [norm_mul, Real.norm_eq_abs]
  rw [abs_of_nonneg h0, abs_of_pos hx]
  calc |Real.log x| * Real.log (1 + t * x) ≤ |Real.log x| * (t * x) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = t * (x * |Real.log x|) := by ring

theorem i9M2_tendsto_log_mul_log_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Tendsto (fun x => Real.log x * Real.log (1 - t * x)) (𝓝[>] 0) (𝓝 0) := by
  have hb : Tendsto (fun x => t / (1 - t) * ‖x * Real.log x‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_mul_log_zero.norm).const_mul (t / (1 - t))
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx0 := hx.1
  have hx1 : 0 ≤ 1 - x := by linarith [hx.2]
  have htx : t * x ≤ t := mul_le_of_le_one_right ht0 hx.2.le
  have h1t : 0 < 1 - t * x := by linarith
  have h0 : Real.log (1 - t * x) ≤ 0 :=
    Real.log_nonpos h1t.le (by nlinarith [mul_nonneg ht0 hx0.le])
  have h1 : -Real.log (1 - t * x) ≤ t / (1 - t) * x := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 h1t)
    rw [Real.log_inv] at this
    have e : (1 - t * x)⁻¹ - 1 = t * x / (1 - t * x) := by field_simp; ring
    have e2 : t * x / (1 - t * x) ≤ t / (1 - t) * x := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ h1t (by linarith)]
      nlinarith [mul_nonneg (sq_nonneg t) (mul_nonneg hx0.le hx1)]
    linarith
  simp only [norm_mul, Real.norm_eq_abs]
  rw [abs_of_nonpos h0, abs_of_pos hx0]
  calc |Real.log x| * -Real.log (1 - t * x) ≤ |Real.log x| * (t / (1 - t) * x) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = t / (1 - t) * (x * |Real.log x|) := by ring

theorem i9M2_logX_logA {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log x * Real.log (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log (w + (1 - w) * x) =
        2 + w * Real.log w / (1 - w) -
          w * (Li₂ (1 - w) + Real.log w ^ 2 / 2) / (1 - w) := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (i9M2FXA w)
      (Real.log x * Real.log (w + (1 - w) * x)) x := by
    intro x hx
    have hx0 := hx.1
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx0.le
    have h1 := i9M2_hasDerivAt_A w x
    have hlA := h1.log hAx.ne'
    have hlx := Real.hasDerivAt_log hx0.ne'
    have hid := hasDerivAt_id x
    have hlq := (h1.div_const w).log (div_pos hAx hw0).ne'
    have hz := ((hasDerivAt_id x).const_mul (1 - w)).div h1 hAx.ne'
    have hz1 : (1 - w) * id x / (w + (1 - w) * x) ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos (mul_pos hu hx0) hAx, by rw [div_lt_one hAx]; simp only [id]; linarith⟩
    have hLi := (hasDerivAt_Li₂' hz1).comp x hz
    have hG1 := ((((hid.mul hlx).sub hid).mul hlA).sub (hid.mul hlx)).add (hid.const_mul 2)
    have hG2 := ((((hlx.mul hlq).sub hLi).sub ((hlq.mul hlq).div_const 2)).sub hlA).const_mul
        (w / (1 - w))
    refine (hG1.add hG2).congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply, id]
    have e1 : 1 - (1 - w) * x / (w + (1 - w) * x) = w / (w + (1 - w) * x) := by
      field_simp; ring
    rw [e1, Real.log_div hw0.ne' hAx.ne', Real.log_div hAx.ne' hw0.ne']
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ Real.log x * Real.log (w + (1 - w) * x) := fun x hx =>
    mul_nonneg_of_nonpos_of_nonpos (Real.log_nonpos hx.1.le hx.2.le)
      (Real.log_nonpos (i9M2_A_pos hw hx.1.le).le (i9M2_A_le hw hx.2.le))
  -- limits at `0⁺`
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hlA0 : Tendsto (fun x => Real.log (w + (1 - w) * x)) (𝓝[>] 0)
      (𝓝 (Real.log (w + (1 - w) * 0))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log (w + (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => w + (1 - w) * x) 0).log (by simp; exact hw0.ne'))
  have hq : ∀ x, (w + (1 - w) * x) / w = 1 + (1 - w) / w * x := fun x => by
    field_simp
  have hlq0 : Tendsto (fun x => Real.log ((w + (1 - w) * x) / w)) (𝓝[>] 0)
      (𝓝 (Real.log ((w + (1 - w) * 0) / w))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log ((w + (1 - w) * x) / w))
      ((by fun_prop : ContinuousAt (fun x : ℝ => (w + (1 - w) * x) / w) 0).log
        (by simp; exact hw0.ne'))
  have hxq0 : Tendsto (fun x => Real.log x * Real.log ((w + (1 - w) * x) / w)) (𝓝[>] 0)
      (𝓝 0) := by
    simpa only [hq] using i9M2_tendsto_log_mul_log_one_add (t := (1 - w) / w) (by positivity)
  have hz0 : Tendsto (fun x => (1 - w) * x / (w + (1 - w) * x)) (𝓝[>] 0)
      (𝓝 ((1 - w) * 0 / (w + (1 - w) * 0))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => (1 - w) * x / (w + (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => (1 - w) * x) 0).div (by fun_prop)
        (by simp; exact hw0.ne'))
  have hLi0 : Tendsto (fun x => Li₂ ((1 - w) * x / (w + (1 - w) * x))) (𝓝[>] 0)
      (𝓝 (Li₂ ((1 - w) * 0 / (w + (1 - w) * 0)))) := by
    refine tendsto_Li₂_comp (by simp) hz0 ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
    exact ⟨by have : 0 ≤ (1 - w) * x / (w + (1 - w) * x) :=
                div_nonneg (mul_nonneg hu.le hx.1.le) hAx.le
              linarith,
      by rw [div_le_one hAx]; linarith⟩
  have hA1 := (((tendsto_mul_log_zero.sub hx0).mul hlA0).sub tendsto_mul_log_zero).add
    (hx0.const_mul 2)
  have hA2 := (((hxq0.sub hLi0).sub ((hlq0.mul hlq0).div_const 2)).sub hlA0).const_mul
    (w / (1 - w))
  have hA := hA1.add hA2
  -- limits at `1⁻`
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hl1 : Tendsto Real.log (𝓝[<] 1) (𝓝 (Real.log 1)) :=
    i9M2_tendsto_of_continuousAt (Real.continuousAt_log one_ne_zero)
  have hxl1 : Tendsto (fun x => x * Real.log x) (𝓝[<] 1) (𝓝 (1 * Real.log 1)) :=
    hx1.mul hl1
  have hlA1 : Tendsto (fun x => Real.log (w + (1 - w) * x)) (𝓝[<] 1)
      (𝓝 (Real.log (w + (1 - w) * 1))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log (w + (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => w + (1 - w) * x) 1).log (by simp))
  have hlq1 : Tendsto (fun x => Real.log ((w + (1 - w) * x) / w)) (𝓝[<] 1)
      (𝓝 (Real.log ((w + (1 - w) * 1) / w))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log ((w + (1 - w) * x) / w))
      ((by fun_prop : ContinuousAt (fun x : ℝ => (w + (1 - w) * x) / w) 1).log
        (by simp; exact hw0.ne'))
  have hz1 : Tendsto (fun x => (1 - w) * x / (w + (1 - w) * x)) (𝓝[<] 1)
      (𝓝 ((1 - w) * 1 / (w + (1 - w) * 1))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => (1 - w) * x / (w + (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => (1 - w) * x) 1).div (by fun_prop)
        (by simp))
  have hLi1 : Tendsto (fun x => Li₂ ((1 - w) * x / (w + (1 - w) * x))) (𝓝[<] 1)
      (𝓝 (Li₂ ((1 - w) * 1 / (w + (1 - w) * 1)))) := by
    refine tendsto_Li₂_comp ⟨by simp; linarith, by simp; linarith⟩ hz1 ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
    exact ⟨by have : 0 ≤ (1 - w) * x / (w + (1 - w) * x) :=
                div_nonneg (mul_nonneg hu.le hx.1.le) hAx.le
              linarith,
      by rw [div_le_one hAx]; linarith⟩
  have hB1 := (((hxl1.sub hx1).mul hlA1).sub hxl1).add (hx1.const_mul 2)
  have hB2 := (((hl1.mul hlq1).sub hLi1).sub ((hlq1.mul hlq1).div_const 2)).sub hlA1
  have hB := hB1.add (hB2.const_mul (w / (1 - w)))
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hf hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [mul_one, mul_zero, add_zero, zero_div, Li₂_zero, Real.log_one,
    div_one, add_sub_cancel]
  field_simp
  simp only [one_div, Real.log_inv, Real.log_one, neg_sq]
  ring

/-! ### `log x log B` -/

/-- The antiderivative of `log x log B`. -/
noncomputable def i9M2FXB (w x : ℝ) : ℝ :=
  (x * Real.log x - x) * Real.log (1 - (1 - w) * x) -
    (Real.log x * Real.log (1 - (1 - w) * x) + Li₂ ((1 - w) * x)) / (1 - w) +
    Real.log (1 - (1 - w) * x) / (1 - w) - x * Real.log x + 2 * x

theorem i9M2_logX_logB {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log x * Real.log (1 - (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log (1 - (1 - w) * x) =
        2 + w * Real.log w / (1 - w) - Li₂ (1 - w) / (1 - w) := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (i9M2FXB w)
      (Real.log x * Real.log (1 - (1 - w) * x)) x := by
    intro x hx
    have hx0 := hx.1
    have hBx : 0 < 1 - (1 - w) * x := i9M2_B_pos hw hx.2.le
    have h2 := i9M2_hasDerivAt_B w x
    have hlB := h2.log hBx.ne'
    have hlx := Real.hasDerivAt_log hx0.ne'
    have hid := hasDerivAt_id x
    have hz1 : (1 - w) * id x ∈ Ioo (0 : ℝ) 1 :=
      ⟨by simp only [id]; positivity, by simp only [id]; linarith⟩
    have hLi := (hasDerivAt_Li₂' hz1).comp x ((hasDerivAt_id x).const_mul (1 - w))
    have hG := ((((((hid.mul hlx).sub hid).mul hlB).sub (((hlx.mul hlB).add hLi).div_const
      (1 - w))).add (hlB.div_const (1 - w))).sub (hid.mul hlx)).add (hid.const_mul 2)
    refine hG.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.sub_apply, id]
    set B := 1 - (1 - w) * x with hBd
    have hB0 : B ≠ 0 := hBx.ne'
    field_simp
    rw [hBd]
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ Real.log x * Real.log (1 - (1 - w) * x) := fun x hx =>
    mul_nonneg_of_nonpos_of_nonpos (Real.log_nonpos hx.1.le hx.2.le)
      (Real.log_nonpos (i9M2_B_pos hw hx.2.le).le (i9M2_B_le hw hx.1.le))
  -- limits at `0⁺`
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hlB0 : Tendsto (fun x => Real.log (1 - (1 - w) * x)) (𝓝[>] 0)
      (𝓝 (Real.log (1 - (1 - w) * 0))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log (1 - (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => 1 - (1 - w) * x) 0).log (by simp))
  have hxB0 : Tendsto (fun x => Real.log x * Real.log (1 - (1 - w) * x)) (𝓝[>] 0) (𝓝 0) :=
    i9M2_tendsto_log_mul_log_one_sub (by linarith [hw.2]) (by linarith [hw.1])
  have hz0 : Tendsto (fun x => (1 - w) * x) (𝓝[>] 0) (𝓝 ((1 - w) * 0)) :=
    i9M2_tendsto_of_continuousAt (by fun_prop)
  have hLi0 : Tendsto (fun x => Li₂ ((1 - w) * x)) (𝓝[>] 0) (𝓝 (Li₂ ((1 - w) * 0))) := by
    refine tendsto_Li₂_comp (by simp) hz0 ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ⟨by nlinarith [hx.1], by nlinarith [hx.2, hx.1]⟩
  have hA := (((((tendsto_mul_log_zero.sub hx0).mul hlB0).sub ((hxB0.add hLi0).div_const
    (1 - w))).add (hlB0.div_const (1 - w))).sub tendsto_mul_log_zero).add (hx0.const_mul 2)
  -- limits at `1⁻`
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hl1 : Tendsto Real.log (𝓝[<] 1) (𝓝 (Real.log 1)) :=
    i9M2_tendsto_of_continuousAt (Real.continuousAt_log one_ne_zero)
  have hxl1 : Tendsto (fun x => x * Real.log x) (𝓝[<] 1) (𝓝 (1 * Real.log 1)) :=
    hx1.mul hl1
  have hlB1 : Tendsto (fun x => Real.log (1 - (1 - w) * x)) (𝓝[<] 1)
      (𝓝 (Real.log (1 - (1 - w) * 1))) :=
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log (1 - (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => 1 - (1 - w) * x) 1).log
        (by simp; exact hw0.ne'))
  have hz1 : Tendsto (fun x => (1 - w) * x) (𝓝[<] 1) (𝓝 ((1 - w) * 1)) :=
    i9M2_tendsto_of_continuousAt (by fun_prop)
  have hLi1 : Tendsto (fun x => Li₂ ((1 - w) * x)) (𝓝[<] 1) (𝓝 (Li₂ ((1 - w) * 1))) := by
    refine tendsto_Li₂_comp ⟨by simp; linarith, by simp; linarith⟩ hz1 ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    exact ⟨by nlinarith [hx.1], by nlinarith [hx.2, hx.1]⟩
  have hB := (((((hxl1.sub hx1).mul hlB1).sub (((hl1.mul hlB1).add hLi1).div_const
    (1 - w))).add (hlB1.div_const (1 - w))).sub hxl1).add (hx1.const_mul 2)
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hf hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [mul_one, mul_zero, sub_zero, Li₂_zero, Real.log_one, sub_sub_cancel]
  field_simp
  ring

/-! ### The constant pieces and the assembly -/

theorem i9M2_log :
    IntervalIntegrable (fun x => Real.log x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x = -1 := by
  refine ⟨intervalIntegral.intervalIntegrable_log', ?_⟩
  rw [integral_log]
  simp

theorem i9M2_logc_sq :
    IntervalIntegrable (fun x => Real.log (x * (1 - x)) ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (x * (1 - x)) ^ 2 = 8 - π ^ 2 / 3 := by
  have h : ∫ x in (0 : ℝ)..1, Real.log (x * (1 - x)) ^ 2 = 8 - π ^ 2 / 3 := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      integral_log_mul_one_sub_sq]
  refine ⟨intervalIntegral.intervalIntegrable_of_integral_ne_zero ?_, h⟩
  rw [h]
  have := Real.pi_le_four
  have := Real.pi_pos
  exact ne_of_gt (by nlinarith)

/-- **`∫₀¹ s = i9M2Sig w`**, with `s` integrable on `[0, 1]`. -/
theorem i9M2S_integral {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (i9M2S w) volume 0 1 ∧ ∫ x in (0 : ℝ)..1, i9M2S w x = i9M2Sig w := by
  have h0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 1 ∧
      ∫ _ in (0 : ℝ)..1, (0 : ℝ) = 0 := ⟨intervalIntegrable_const, by simp⟩
  have h := i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step h0
    (i9M2_logA hw) (4 * Real.log w)) i9M2_log (-(4 * Real.log w))) (i9M2_logA_sq hw) (-3))
    (i9M2_logA_logB hw) (-3)) (i9M2_logX_logA hw) 4) (i9M2_logX_logB hw) 4) i9M2_logc_sq
    (-(1 / 2))
  have e : i9M2S w = fun x => 0 + 4 * Real.log w * Real.log (w + (1 - w) * x) +
      -(4 * Real.log w) * Real.log x + -3 * Real.log (w + (1 - w) * x) ^ 2 +
      -3 * (Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x)) +
      4 * (Real.log x * Real.log (w + (1 - w) * x)) +
      4 * (Real.log x * Real.log (1 - (1 - w) * x)) + -(1 / 2) * Real.log (x * (1 - x)) ^ 2 := by
    funext x
    unfold i9M2S
    ring
  rw [e]
  exact ⟨h.1, h.2.trans (by unfold i9M2Sig; ring)⟩

end QED.ThreeLoopD
