/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemKuIBP
public import QED.ThreeLoopD.SetDMastersI9MInner
public import QED.Polylog.HPLLowWeight
import QED.Polylog.DilogPM

/-!
# Set (d), master `I₉`: the inner integral `T(w) = ∫₀¹ log² p dx` of `K_u`

`QED.ThreeLoopD.integral_log_one_sub_mul_i9A1Dens_eq` writes `K_u` as the `w`-integral of
`F(w) · 3 (1 - w²)/(2 w²) · T(w)` with `T(w) = ∫₀¹ log² p(x, w) dx`. With `A = w + (1 - w) x`,
`B = 1 - (1 - w) x` (so `x (1 - x)(1 - w)² + w = A B`),

  `log p = log (x (1 - x)) + 2 log (1 - w) - log A - log B`,

and `B(x) = A(1 - x)`. Expanding the square, `T(w)` is a combination of the `x`-integrals of
`QED.ThreeLoopD.i9M2S_integral` (`∫ log A`, `∫ log² A`, `∫ log x log A`, `∫ log x log B`,
`∫ log A log B`, `∫ log² (x (1 - x))`) and their mirror images under `x ↦ 1 - x`. In harmonic
polylogarithms of `w` over `{0, 1, -1}`, with `r = (1 + w)/(1 - w)`,

  `T = 4 H₁² + 4 r (ζ₂ + H₀ H₁ - H₀₁) + 2 r (2 H₀,₋₁ - ζ₂ - H₋₁ H₀)
      + H₀ (-8 w/(1 - w) · H₁ - 2 r H₋₁) - 2 ζ₂`.

## Main results

* `QED.ThreeLoopD.integral_log_i9KuP_sq`: `∫₀¹ log² p(x, w) dx = i9KuT w` for `w ∈ (0, 1)`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The closed form of `T(w) = ∫₀¹ log² p(x, w) dx`, in harmonic polylogarithms of `w`. -/
noncomputable def i9KuT (w : ℝ) : ℝ :=
  4 * hpl [one] w ^ 2 +
    4 * ((1 + w) / (1 - w)) * (π ^ 2 / 6 + hpl [zero] w * hpl [one] w - hpl [zero, one] w) +
    2 * ((1 + w) / (1 - w)) *
      (2 * hpl [zero, negOne] w - π ^ 2 / 6 - hpl [negOne] w * hpl [zero] w) +
    hpl [zero] w * (-8 * w / (1 - w) * hpl [one] w - 2 * ((1 + w) / (1 - w)) * hpl [negOne] w) -
    2 * (π ^ 2 / 6)

/-- The mirror `x ↦ 1 - x` of an integral over `[0, 1]`. -/
theorem i9KuT_mirror {f : ℝ → ℝ} {V : ℝ}
    (h : IntervalIntegrable f volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f x = V) :
    IntervalIntegrable (fun x => f (1 - x)) volume 0 1 ∧ ∫ x in (0 : ℝ)..1, f (1 - x) = V := by
  refine ⟨?_, ?_⟩
  · have := h.1.comp_sub_left 1
    simp only [sub_zero, sub_self] at this
    exact this.symm
  · rw [intervalIntegral.integral_comp_sub_left]
    simpa using h.2

theorem log_i9KuP_eq {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    Real.log (i9KuP x w) = Real.log x + Real.log (1 - x) + 2 * Real.log (1 - w) -
      Real.log (w + (1 - w) * x) - Real.log (1 - (1 - w) * x) := by
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hA := i9M2_A_pos hw hx.1.le
  have hB := i9M2_B_pos hw hx.2.le
  have e : i9A1P (x, w) = (w + (1 - w) * x) * (1 - (1 - w) * x) := by
    simp only [i9A1P]; ring
  have hx0 := hx.1
  rw [i9KuP, e, Real.log_div (by positivity) (by positivity),
    Real.log_mul (x := x * (1 - x)) (by positivity) (by positivity),
    Real.log_mul (x := w + (1 - w) * x) (by positivity) (by positivity),
    Real.log_mul hx0.ne' hx1.ne', Real.log_pow]
  push_cast
  ring

/-- **`∫₀¹ log² p(x, w) dx = T(w)`.** -/
theorem integral_log_i9KuP_sq {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∫ x in Ioo (0 : ℝ) 1, Real.log (i9KuP x w) ^ 2 = i9KuT w := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have h0 : IntervalIntegrable (fun _ : ℝ => 4 * Real.log (1 - w) ^ 2) volume 0 1 ∧
      ∫ _ in (0 : ℝ)..1, 4 * Real.log (1 - w) ^ 2 = 4 * Real.log (1 - w) ^ 2 :=
    ⟨intervalIntegrable_const, by simp⟩
  have s1 := i9M2_step h0 i9M2_logc_sq 1
  have s2 := i9M2_step s1 (i9M2_logA_sq hw) 1
  have s3 := i9M2_step s2 (i9KuT_mirror (i9M2_logA_sq hw)) 1
  have s4 := i9M2_step s3 (i9M2_logA_logB hw) 2
  have s5 := i9M2_step s4 (i9M2_logX_logA hw) (-2)
  have s6 := i9M2_step s5 (i9KuT_mirror (i9M2_logX_logB hw)) (-2)
  have s7 := i9M2_step s6 (i9M2_logX_logB hw) (-2)
  have s8 := i9M2_step s7 (i9KuT_mirror (i9M2_logX_logA hw)) (-2)
  have s9 := i9M2_step s8 i9M2_log (4 * Real.log (1 - w))
  have s10 := i9M2_step s9 (i9KuT_mirror i9M2_log) (4 * Real.log (1 - w))
  have s11 := i9M2_step s10 (i9M2_logA hw) (-(4 * Real.log (1 - w)))
  have h := i9M2_step s11 (i9KuT_mirror (i9M2_logA hw)) (-(4 * Real.log (1 - w)))
  have h2 := h.2
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h2
  refine (setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_).trans (h2.trans ?_)
  · have hx1 : 0 < 1 - x := by linarith [hx.2]
    have e1 : w + (1 - w) * (1 - x) = 1 - (1 - w) * x := by ring
    have e2 : 1 - (1 - w) * (1 - x) = w + (1 - w) * x := by ring
    simp only [e1, e2]
    rw [log_i9KuP_eq hx hw, Real.log_mul hx.1.ne' hx1.ne']
    ring
  · have hA := hpl_zero_one hw
    have hB := hpl_zero_negOne hw
    have hC := hpl_one hw
    have hD := hpl_negOne hw
    have r1 := Li_two_one_sub' hw
    have r2 := Li_two_div_one_add hw
    have r3 := Li_two_inv_one_add hw
    rw [Li_two] at hA hB r1 r2 r3
    have hp : (0 : ℝ) < 1 + w := by linarith
    unfold i9KuT i9M2JAB
    rw [hA, hB, hC, hD, hpl_zero, r1, r2, r3]
    field_simp
    ring

end QED.ThreeLoopD
