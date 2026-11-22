/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ExtraIntegrals
public import QED.Polylog.Reflection
public import QED.Polylog.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₉`: the one-dimensional integral behind `∫ F₁`

In the variables `p = P₀ / P₁` and `s = x (1 - w)` (see
`QED.ThreeLoopD.SetDMastersI9RemA1`), the first Taylor coefficient of `Rem` becomes
`-3 k(s, p) g(p)` with

  `k(s, p) = 1 + p (1 - p) (1 - s)² / (s + p (1 - s))²`,
  `g(p) = (π²/6 - Li₂ (1 - p)) / p + log² p / (2 (1 - p))`.

This file proves `∫₀¹ k(s, p) ds = K(p) = 2/(1 - p) + 2 p log p / (1 - p)²` and

  `∫₀¹ g(p) K(p) dp = π²/6 + 3 ζ(3)`,

with the explicit antiderivative `i9A1Prim` (dilogarithms of `p` and `1 - p`, `Li₃ p`).

## Main results

* `QED.ThreeLoopD.integral_i9A1k`: the `s`-integral of `k`.
* `QED.ThreeLoopD.intervalIntegrable_and_integral_i9A1gK`: the `p`-integral.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-- The `s`-kernel `k(s, p) = 1 + p (1 - p) (1 - s)² / (s + p (1 - s))²`. -/
noncomputable def i9A1k (s p : ℝ) : ℝ := 1 + p * (1 - p) * (1 - s) ^ 2 / (s + p * (1 - s)) ^ 2

/-- `K(p) = 2/(1 - p) + 2 p log p / (1 - p)²`, the `s`-integral of `k`. -/
noncomputable def i9A1K (p : ℝ) : ℝ := 2 / (1 - p) + 2 * p * Real.log p / (1 - p) ^ 2

/-- `g(p) = (π²/6 - Li₂ (1 - p)) / p + log² p / (2 (1 - p))`. -/
noncomputable def i9A1g (p : ℝ) : ℝ :=
  (π ^ 2 / 6 - Li₂ (1 - p)) / p + Real.log p ^ 2 / (2 * (1 - p))

/-- An antiderivative of `g K` on `(0, 1)`. -/
noncomputable def i9A1Prim (p : ℝ) : ℝ :=
  2 * (π ^ 2 / 6 - Li₂ (1 - p)) * Real.log p / (1 - p) +
    3 / 2 * p * Real.log p ^ 2 / (1 - p) - 3 * Li₂ (1 - p) -
    3 / 2 * Real.log (1 - p) * Real.log p ^ 2 - 3 * Li₂ p * Real.log p + 3 * Li₃ p +
    p ^ 2 * Real.log p ^ 3 / (2 * (1 - p) ^ 2)

/-! ### The `s`-integral -/

/-- The `s`-antiderivative of `k`. -/
noncomputable def i9A1kPrim (p s : ℝ) : ℝ :=
  s + p / (1 - p) ^ 2 * ((s + p * (1 - s)) - 1 / (s + p * (1 - s)) -
    2 * Real.log (s + p * (1 - s)))

theorem i9A1_E_pos {p s : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < s + p * (1 - s) := by
  nlinarith [hp.1, hp.2, hs.1, hs.2]

theorem hasDerivAt_i9A1kPrim {p s : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => i9A1kPrim p s) (i9A1k s p) s := by
  have hE := i9A1_E_pos hp hs
  have hp1 : (1 - p) ≠ 0 := by linarith [hp.2]
  have hEd : HasDerivAt (fun s => s + p * (1 - s)) (1 - p) s := by
    have := (hasDerivAt_id' s).add (((hasDerivAt_id' s).const_sub 1).const_mul p)
    convert this using 1; ring
  have h := (hasDerivAt_id' s).add ((((hEd.sub ((hasDerivAt_const s (1 : ℝ)).div hEd hE.ne')).sub
    ((hEd.log hE.ne').const_mul 2))).const_mul (p / (1 - p) ^ 2))
  convert h using 1
  · funext t
    simp only [i9A1kPrim, Pi.add_apply, Pi.sub_apply, Pi.div_apply]
  · unfold i9A1k
    field_simp
    ring

theorem continuousOn_i9A1kPrim {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun s => i9A1kPrim p s) (Icc 0 1) := fun _ hs =>
  (hasDerivAt_i9A1kPrim hp hs).continuousAt.continuousWithinAt

theorem continuousOn_i9A1k {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun s => i9A1k s p) (Icc 0 1) := by
  unfold i9A1k
  refine continuousOn_const.add (ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs => ?_)
  exact (pow_pos (i9A1_E_pos hp hs) 2).ne'

/-- **The `s`-integral of `k`.** -/
theorem integral_i9A1k {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∫ s in (0 : ℝ)..1, i9A1k s p = i9A1K p := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_i9A1kPrim hp) (fun s hs => hasDerivAt_i9A1kPrim hp (Ioo_subset_Icc_self hs))
    ((continuousOn_i9A1k hp).intervalIntegrable_of_Icc zero_le_one)]
  have hp0 : p ≠ 0 := hp.1.ne'
  have hp1 : (1 - p) ≠ 0 := by linarith [hp.2]
  unfold i9A1kPrim i9A1K
  simp only [sub_self, mul_zero, add_zero, zero_add, sub_zero, mul_one, div_one, Real.log_one]
  field_simp
  ring

theorem i9A1k_nonneg {p s : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : 0 ≤ i9A1k s p := by
  unfold i9A1k
  have : 0 ≤ p * (1 - p) * (1 - s) ^ 2 / (s + p * (1 - s)) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg hp.1.le (by linarith [hp.2])) (sq_nonneg _))
      (sq_nonneg _)
  linarith

/-! ### Signs -/

theorem i9A1K_nonneg {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : 0 ≤ i9A1K p := by
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  have hl : 1 - p⁻¹ ≤ Real.log p := Real.one_sub_inv_le_log_of_pos hp.1
  have h : 0 ≤ (1 - p) + p * Real.log p := by
    have : p * (1 - p⁻¹) = p - 1 := by rw [mul_sub, mul_inv_cancel₀ hp.1.ne', mul_one]
    nlinarith [mul_le_mul_of_nonneg_left hl hp.1.le]
  have e : i9A1K p = 2 * ((1 - p) + p * Real.log p) / (1 - p) ^ 2 := by
    unfold i9A1K; field_simp
  rw [e]; positivity

theorem i9A1g_nonneg {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : 0 ≤ i9A1g p := by
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  have hL : Li₂ (1 - p) ≤ π ^ 2 / 6 :=
    Li₂_le_pi_sq_div_six ⟨by linarith [hp.2], by linarith [hp.1]⟩
  unfold i9A1g
  have h1 : 0 ≤ (π ^ 2 / 6 - Li₂ (1 - p)) / p := div_nonneg (by linarith) hp.1.le
  have h2 : 0 ≤ Real.log p ^ 2 / (2 * (1 - p)) := by positivity
  linarith

/-! ### The antiderivative -/

theorem hasDerivAt_i9A1Prim {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i9A1Prim (i9A1g p * i9A1K p) p := by
  have hp0 : p ≠ 0 := hp.1.ne'
  have hp1' : 0 < 1 - p := by linarith [hp.2]
  have hp1 : (1 - p) ≠ 0 := hp1'.ne'
  have hq : 1 - p ∈ Ioo (0 : ℝ) 1 := ⟨hp1', by linarith [hp.1]⟩
  have hA : HasDerivAt (fun p => Li₂ (1 - p)) (Real.log p / (1 - p)) p := by
    refine ((hasDerivAt_Li₂' hq).comp p ((hasDerivAt_id' p).const_sub 1)).congr_deriv ?_
    rw [sub_sub_cancel]
    ring
  have hB := hasDerivAt_Li₂' hp
  have hC := hasDerivAt_Li₃' hp
  have hl := Real.hasDerivAt_log hp0
  have hm : HasDerivAt (fun p => Real.log (1 - p)) (-1 / (1 - p)) p := by
    have := ((hasDerivAt_id' p).const_sub 1).log hp1
    convert this using 1
  have hd : HasDerivAt (fun p : ℝ => 1 - p) (-1) p := by
    simpa using (hasDerivAt_id' p).const_sub 1
  have h1 := ((((hasDerivAt_const p (π ^ 2 / 6)).sub hA).const_mul 2).mul hl).div hd hp1
  have h2 := ((((hasDerivAt_id' p).const_mul (3 / 2)).mul (hl.pow 2))).div hd hp1
  have h3 := hA.const_mul 3
  have h4 := (hm.const_mul (3 / 2)).mul (hl.pow 2)
  have h5 := (hB.const_mul 3).mul hl
  have h6 := hC.const_mul 3
  have h7 := ((hasDerivAt_id' p).pow 2).mul (hl.pow 3) |>.div ((hd.pow 2).const_mul 2)
    (mul_ne_zero two_ne_zero (pow_ne_zero 2 hp1))
  have h := (((((h1.add h2).sub h3).sub h4).sub h5).add h6).add h7
  convert h using 1
  · funext t
    simp only [i9A1Prim, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply]
  · unfold i9A1g i9A1K
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat]
    norm_num
    field_simp
    ring

/-! ### Limits -/

theorem i9A1_tendsto_log_div_one_sub :
    Tendsto (fun p : ℝ => Real.log p / (1 - p)) (𝓝[<] 1) (𝓝 (-1)) := by
  have h := tendsto_log_one_sub_div_zero'.comp tendsto_one_sub_nhdsLT_one
  refine h.congr fun p => ?_
  simp only [Function.comp_apply, sub_sub_cancel]

theorem i9A1_tendsto_log_one : Tendsto (fun p : ℝ => Real.log p) (𝓝[<] 1) (𝓝 0) := by
  have h := (Real.continuousAt_log one_ne_zero).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Iio 1))
  rwa [Real.log_one] at h

theorem tendsto_i9A1Prim_one :
    Tendsto i9A1Prim (𝓝[<] 1) (𝓝 (-(π ^ 2 / 3) + 3 * zeta3)) := by
  have hr := i9A1_tendsto_log_div_one_sub
  have hl := i9A1_tendsto_log_one
  have hA : Tendsto (fun p : ℝ => Li₂ (1 - p)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_Li₂_zero_right.comp tendsto_one_sub_nhdsLT_one
  have hid : Tendsto (fun p : ℝ => p) (𝓝[<] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds
    tendsto_id
  have h := ((((((((tendsto_const_nhds (x := π ^ 2 / 6)).sub hA).const_mul 2).mul hr).add
    (((hid.const_mul (3 / 2)).mul hl).mul hr)).sub (hA.const_mul 3)).sub
    ((tendsto_log_mul_log_one_sub_one.const_mul (3 / 2)).mul hl)).sub
    ((tendsto_Li₂_one_left.const_mul 3).mul hl)).add (tendsto_Li₃_one_left.const_mul 3) |>.add
    (((hid.pow 2).mul hl).mul (hr.pow 2) |>.div_const 2)
  refine (h.congr' ?_).trans (le_of_eq (by congr 1; ring))
  filter_upwards [self_mem_nhdsWithin] with p (hp : p < 1)
  have hp1 : (1 - p) ≠ 0 := by linarith
  simp only [i9A1Prim]
  field_simp

theorem tendsto_i9A1Prim_zero : Tendsto i9A1Prim (𝓝[>] 0) (𝓝 (-(π ^ 2 / 2))) := by
  have hm := tendsto_log_one_sub_div_zero'
  have h2 := tendsto_mul_log_sq_zero
  have h1 := tendsto_mul_log_zero
  have hL := tendsto_log_mul_Li₂_zero
  have hA : Tendsto (fun p : ℝ => Li₂ (1 - p)) (𝓝[>] 0) (𝓝 (π ^ 2 / 6)) :=
    tendsto_Li₂_one_left.comp tendsto_one_sub_nhdsGT_zero
  have hd : Tendsto (fun p : ℝ => 1 - p) (𝓝[>] 0) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds
    ((continuous_sub_left (1 : ℝ)).tendsto' 0 1 (by norm_num))
  have hlm := h2.mul hm
  have h := ((((((((hL.add hlm).const_mul 2).div hd one_ne_zero).add
    ((h2.const_mul (3 / 2)).div hd one_ne_zero)).sub (hA.const_mul 3)).sub
    (hlm.const_mul (3 / 2))).sub (hL.const_mul 3)).add
    (tendsto_Li₃_zero_right.const_mul 3)).add
    ((h1.mul h2).div ((hd.pow 2).const_mul 2) (by norm_num))
  refine (h.congr' ?_).trans (le_of_eq (by congr 1; ring))
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with p hp
  have hp0 : p ≠ 0 := hp.1.ne'
  have hp1 : (1 - p) ≠ 0 := by linarith [hp.2]
  have hR := Li₂_add_Li₂_one_sub hp.1.le hp.2.le
  have e : π ^ 2 / 6 - Li₂ (1 - p) = Li₂ p + Real.log p * Real.log (1 - p) := by linarith
  simp only [i9A1Prim, Pi.div_apply]
  rw [e]
  field_simp

/-- **`∫₀¹ g(p) K(p) dp = π²/6 + 3 ζ(3)`.** -/
theorem intervalIntegrable_and_integral_i9A1gK :
    IntervalIntegrable (fun p => i9A1g p * i9A1K p) volume 0 1 ∧
      ∫ p in (0 : ℝ)..1, i9A1g p * i9A1K p = π ^ 2 / 6 + 3 * zeta3 := by
  obtain ⟨hi, hv⟩ := intervalIntegrable_and_integral_eq_of_nonneg
    (fun p hp => hasDerivAt_i9A1Prim hp)
    (fun p hp => mul_nonneg (i9A1g_nonneg hp) (i9A1K_nonneg hp))
    tendsto_i9A1Prim_zero tendsto_i9A1Prim_one
  refine ⟨hi, ?_⟩
  rw [hv]
  ring

end QED.ThreeLoopD
