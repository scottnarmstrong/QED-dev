/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI2P1USig
public import QED.Polylog.LogLiDiv
import QED.Polylog.ExtraIntegralsC
import QED.Polylog.LiLimits

/-!
# Set (d), master `I₂`: the last integral of the `ℱ`-part of `P'(0)`

The `ℱ`-part `∫ (1 - w) log (ℱ / 𝒰) / 𝒰²` of `P'(0)` reduces, after the integrations over the
five Feynman parameters except one, to the single integral

  `∫₀¹ (1 + t) / (t (1 - t)) · log² t · I(t) dt = 2 π⁴ / 45 - 4 ζ(3) + π² / 3`,
  `I(t) = 3 (1 - t) / 2 - t log t / 2 + (t - 1)(t - 3) / (2 t) · log (1 - t)`,

proved here. Expanding,

  `(1 + t) / (t (1 - t)) log² t I(t) = 3/2 log² t - log³ t / (1 - t) + 1/2 log³ t
    - 1/2 log² t log (1 - t) + log² t log (1 - t) / t + 3/2 log² t (log (1 - t) + t) / t²`,

and the six integrals are `2`, `-π⁴/15`, `-6`, `-6 + π²/3 + 2ζ(3)`, `-π⁴/45` and
`π²/3 - 2ζ(3) - 2`; the fourth and the sixth have the primitives `QED.ThreeLoopD.i2P1FEndF3` and
`QED.ThreeLoopD.i2P1FEndF5` (in `Li₂`, `Li₃`).

## Main results

* `QED.ThreeLoopD.i2P1FEnd_log_sq`, `QED.ThreeLoopD.i2P1FEnd_log_cube`.
* `QED.ThreeLoopD.i2P1FEnd_P3`, `QED.ThreeLoopD.i2P1FEnd_P5`.
* `QED.ThreeLoopD.i2P1FEnd_value`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- The inner integral `I(t) = 3 (1 - t) / 2 - t log t / 2 + (t - 1)(t - 3) / (2 t) log (1 - t)`
of the `ℱ`-part of `P'(0)`. -/
noncomputable def i2P1FI (t : ℝ) : ℝ :=
  3 * (1 - t) / 2 - t * log t / 2 + (t - 1) * (t - 3) / (2 * t) * log (1 - t)

theorem i2P1FEnd_tendsto_log_one : Tendsto (fun t : ℝ => log t) (𝓝[<] 1) (𝓝 0) := by
  have := ((continuousAt_log one_ne_zero).tendsto).mono_left (nhdsWithin_le_nhds (s := Iio 1))
  rwa [log_one] at this

theorem i2P1FEnd_tendsto_one_sub_mul_log :
    Tendsto (fun t : ℝ => (1 - t) * log (1 - t)) (𝓝[<] 1) (𝓝 0) :=
  tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one

theorem i2P1FEnd_tendsto_log_mul_Li₂ :
    Tendsto (fun t : ℝ => log t * Li₂ t) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_mul_log_zero.mul tendsto_Li₂_div_zero
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  field_simp

theorem i2P1FEnd_tendsto_mul_log_cube :
    Tendsto (fun t : ℝ => t * log t ^ 3) (𝓝[>] 0) (𝓝 0) := by
  have h2 := (tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 3) (by norm_num)).pow 3
  rw [zero_pow (by norm_num)] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
  have hc : (u ^ (1 / 3 : ℝ)) ^ 3 = u := by
    rw [← rpow_natCast, ← rpow_mul hu.le]
    norm_num
  rw [mul_pow, hc]
  ring

/-- **`∫₀¹ log² t = 2`**. -/
theorem i2P1FEnd_log_sq :
    IntervalIntegrable (fun t => log t ^ 2) volume 0 1 ∧
      ∫ t in (0 : ℝ)..1, log t ^ 2 = 2 := by
  have h := intervalIntegrable_and_integral_eq_of_nonneg
    (F := fun t => t * log t ^ 2 - 2 * (t * log t) + 2 * t) (f := fun t => log t ^ 2)
    (fun x hx => by
      have hl := hasDerivAt_log hx.1.ne'
      have hd := (((hasDerivAt_id x).mul (hl.pow 2)).sub (((hasDerivAt_id x).mul hl).const_mul
        2)).add ((hasDerivAt_id x).const_mul 2)
      refine hd.congr_deriv ?_
      have h0 : x ≠ 0 := hx.1.ne'
      simp only [id, Pi.pow_apply]
      field_simp
      ring)
    (fun x _ => sq_nonneg _)
    ((tendsto_mul_log_sq_zero.sub (tendsto_mul_log_zero.const_mul 2)).add
      ((tendsto_id.mono_left nhdsWithin_le_nhds).const_mul 2))
    (((tendsto_id.mono_left nhdsWithin_le_nhds).mul (i2P1FEnd_tendsto_log_one.pow 2)).sub
      (((tendsto_id.mono_left nhdsWithin_le_nhds).mul i2P1FEnd_tendsto_log_one).const_mul 2)
      |>.add ((tendsto_id.mono_left nhdsWithin_le_nhds).const_mul 2))
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp

/-- **`∫₀¹ log³ t = -6`**. -/
theorem i2P1FEnd_log_cube :
    IntervalIntegrable (fun t => log t ^ 3) volume 0 1 ∧
      ∫ t in (0 : ℝ)..1, log t ^ 3 = -6 := by
  have hi : Tendsto (fun t : ℝ => t) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h := intervalIntegrable_and_integral_eq_of_nonpos
    (F := fun t => t * log t ^ 3 - 3 * (t * log t ^ 2) + 6 * (t * log t) - 6 * t)
    (f := fun t => log t ^ 3)
    (fun x hx => by
      have hl := hasDerivAt_log hx.1.ne'
      have hd := ((((hasDerivAt_id x).mul (hl.pow 3)).sub (((hasDerivAt_id x).mul
        (hl.pow 2)).const_mul 3)).add (((hasDerivAt_id x).mul hl).const_mul 6)).sub
        ((hasDerivAt_id x).const_mul 6)
      refine hd.congr_deriv ?_
      have h0 : x ≠ 0 := hx.1.ne'
      simp only [id, Pi.pow_apply]
      field_simp
      ring)
    (fun x hx => Odd.pow_nonpos (by decide) (log_nonpos hx.1.le hx.2.le))
    (((i2P1FEnd_tendsto_mul_log_cube.sub (tendsto_mul_log_sq_zero.const_mul 3)).add
      (tendsto_mul_log_zero.const_mul 6)).sub
      ((tendsto_id.mono_left nhdsWithin_le_nhds).const_mul 6))
    ((((hi.mul (i2P1FEnd_tendsto_log_one.pow 3)).sub
      ((hi.mul (i2P1FEnd_tendsto_log_one.pow 2)).const_mul 3)).add
      ((hi.mul i2P1FEnd_tendsto_log_one).const_mul 6)).sub (hi.const_mul 6))
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp

/-- The primitive of `log² t log (1 - t)`. -/
noncomputable def i2P1FEndF3 (t : ℝ) : ℝ :=
  (t - 1) * (log (1 - t) * log t ^ 2) - 2 * ((t - 1) * (log t * log (1 - t))) -
    2 * ((1 - t) * log (1 - t)) + 4 * (t * log t) - t * log t ^ 2 - 6 * t + 2 * Li₂ t -
    2 * (log t * Li₂ t) + 2 * Li₃ t

theorem i2P1FEnd_hasDerivAt_F3 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i2P1FEndF3 (log x ^ 2 * log (1 - x)) x := by
  have hl := hasDerivAt_log hx.1.ne'
  have hl1 := hasDerivAt_log_one_sub hx.2
  have h2 := hasDerivAt_Li₂' hx
  have h3 := hasDerivAt_Li₃' hx
  have hm := (hasDerivAt_id x).sub_const 1
  have hm' := (hasDerivAt_id x).const_sub 1
  have hd := ((((((((hm.mul (hl1.mul (hl.pow 2))).sub ((hm.mul (hl.mul hl1)).const_mul 2)).sub
    ((hm'.mul hl1).const_mul 2)).add (((hasDerivAt_id x).mul hl).const_mul 4)).sub
    ((hasDerivAt_id x).mul (hl.pow 2))).sub ((hasDerivAt_id x).const_mul 6)).add
    (h2.const_mul 2)).sub ((hl.mul h2).const_mul 2)).add (h3.const_mul 2)
  refine hd.congr_deriv ?_
  have h1 : (1 - x) ≠ 0 := by linarith [hx.2]
  have h0 : x ≠ 0 := hx.1.ne'
  simp only [id, Pi.mul_apply, Pi.pow_apply]
  field_simp
  ring

/-- **`∫₀¹ log² t log (1 - t) = -6 + π² / 3 + 2 ζ(3)`**. -/
theorem i2P1FEnd_P3 :
    IntervalIntegrable (fun t => log t ^ 2 * log (1 - t)) volume 0 1 ∧
      ∫ t in (0 : ℝ)..1, log t ^ 2 * log (1 - t) = -6 + π ^ 2 / 3 + 2 * zeta3 := by
  have hi0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hi1 : Tendsto (fun t : ℝ => t) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hl1 := i2P1FEnd_tendsto_log_one
  have hll1 : Tendsto (fun t : ℝ => log (1 - t) * log t ^ 2) (𝓝[<] 1) (𝓝 0) := by
    have := tendsto_log_mul_log_one_sub_one.mul hl1
    rw [zero_mul] at this
    exact this.congr fun t => by ring
  have hA := (((((((((hi0.sub_const 1).mul tendsto_log_one_sub_mul_log_sq).sub
    (((hi0.sub_const 1).mul tendsto_log_mul_log_one_sub_zero).const_mul 2)).sub
    (((hi0.const_sub 1).mul tendsto_log_one_sub_zero).const_mul 2)).add
    (tendsto_mul_log_zero.const_mul 4)).sub tendsto_mul_log_sq_zero).sub (hi0.const_mul 6)).add
    (tendsto_Li₂_zero_right.const_mul 2)).sub (i2P1FEnd_tendsto_log_mul_Li₂.const_mul 2)).add
    (tendsto_Li₃_zero_right.const_mul 2)
  have hB := (((((((((hi1.sub_const 1).mul hll1).sub
    (((hi1.sub_const 1).mul tendsto_log_mul_log_one_sub_one).const_mul 2)).sub
    (i2P1FEnd_tendsto_one_sub_mul_log.const_mul 2)).add
    ((hi1.mul hl1).const_mul 4)).sub (hi1.mul (hl1.pow 2))).sub (hi1.const_mul 6)).add
    (tendsto_Li₂_one_left.const_mul 2)).sub ((hl1.mul tendsto_Li₂_one_left).const_mul 2)).add
    (tendsto_Li₃_one_left.const_mul 2)
  have h := intervalIntegrable_and_integral_eq_of_nonpos (F := i2P1FEndF3)
    (f := fun t => log t ^ 2 * log (1 - t)) (fun x hx => i2P1FEnd_hasDerivAt_F3 hx)
    (fun x hx => mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
      (log_nonpos (by linarith [hx.2]) (by linarith [hx.1]))) hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2]
  ring

/-- The primitive of `log² t (log (1 - t) + t) / t²`. -/
noncomputable def i2P1FEndF5 (t : ℝ) : ℝ :=
  -((1 - t) * ((log (1 - t) + t) / t) * log t ^ 2) -
    2 * ((1 - t) * (log t * (log (1 - t) + t) / t)) - 2 * ((1 - t) * (log (1 - t) / t)) +
    2 * Li₂ t + 2 * (log t * Li₂ t) - 2 * Li₃ t - 2 * (t * log t) - t * log t ^ 2

theorem i2P1FEnd_hasDerivAt_F5 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i2P1FEndF5 (log x ^ 2 * (log (1 - x) + x) / x ^ 2) x := by
  have hl := hasDerivAt_log hx.1.ne'
  have hl1 := hasDerivAt_log_one_sub hx.2
  have h2 := hasDerivAt_Li₂' hx
  have h3 := hasDerivAt_Li₃' hx
  have hm' := (hasDerivAt_id x).const_sub 1
  have h0 : x ≠ 0 := hx.1.ne'
  have hg := (hl1.add (hasDerivAt_id x)).div (hasDerivAt_id x) h0
  have hd := (((((((((hm'.mul hg).mul (hl.pow 2)).neg.sub
    ((hm'.mul ((hl.mul (hl1.add (hasDerivAt_id x))).div (hasDerivAt_id x) h0)).const_mul 2)).sub
    ((hm'.mul (hl1.div (hasDerivAt_id x) h0)).const_mul 2)).add (h2.const_mul 2)).add
    ((hl.mul h2).const_mul 2)).sub (h3.const_mul 2)).sub
    (((hasDerivAt_id x).mul hl).const_mul 2)).sub ((hasDerivAt_id x).mul (hl.pow 2)))
  refine hd.congr_deriv ?_
  have h1 : (1 - x) ≠ 0 := by linarith [hx.2]
  simp only [id, Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Pi.div_apply]
  field_simp
  ring

/-- **`∫₀¹ log² t (log (1 - t) + t) / t² = π² / 3 - 2 ζ(3) - 2`**. -/
theorem i2P1FEnd_P5 :
    IntervalIntegrable (fun t => log t ^ 2 * (log (1 - t) + t) / t ^ 2) volume 0 1 ∧
      ∫ t in (0 : ℝ)..1, log t ^ 2 * (log (1 - t) + t) / t ^ 2 = π ^ 2 / 3 - 2 * zeta3 - 2 := by
  have hi0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hi1 : Tendsto (fun t : ℝ => t) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hl1 := i2P1FEnd_tendsto_log_one
  -- at `0⁺`
  have hg0 : Tendsto (fun t : ℝ => (1 - t) * ((log (1 - t) + t) / t) * log t ^ 2) (𝓝[>] 0)
      (𝓝 0) := by
    refine tendsto_mul_log_sq_of_abs_le (C := 1) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have h1 : 0 < 1 - t := by linarith [ht.2]
    have hb := abs_log_one_sub_add_le ht.1.le ht.2
    rw [abs_mul, abs_div, abs_of_pos h1, abs_of_pos ht.1]
    calc (1 - t) * (|log (1 - t) + t| / t) ≤ (1 - t) * (t ^ 2 / (1 - t) / t) := by
          gcongr; exact ht.1.le
      _ = 1 * t := by field_simp
  have hk0 : Tendsto (fun t : ℝ => (1 - t) * (log t * (log (1 - t) + t) / t)) (𝓝[>] 0)
      (𝓝 0) := by
    have := (hi0.const_sub 1).mul tendsto_log_mul_log_one_sub_add_div_zero
    rwa [mul_zero] at this
  have hA := (((((((hg0.neg.sub (hk0.const_mul 2)).sub
    (((hi0.const_sub 1).mul tendsto_log_one_sub_div_zero').const_mul 2)).add
    (tendsto_Li₂_zero_right.const_mul 2)).add (i2P1FEnd_tendsto_log_mul_Li₂.const_mul 2)).sub
    (tendsto_Li₃_zero_right.const_mul 2)).sub (tendsto_mul_log_zero.const_mul 2)).sub
    tendsto_mul_log_sq_zero)
  -- at `1⁻`
  have hg1 : Tendsto (fun t : ℝ => (1 - t) * ((log (1 - t) + t) / t) * log t ^ 2) (𝓝[<] 1)
      (𝓝 0) := by
    have h := ((((i2P1FEnd_tendsto_one_sub_mul_log.mul hl1).add
      (((hi1.const_sub 1).mul hi1).mul hl1)).div hi1 one_ne_zero).mul hl1)
    simp only [mul_zero, add_zero, zero_div] at h
    refine h.congr fun t => ?_
    simp only [Pi.div_apply]
    ring
  have hk1 : Tendsto (fun t : ℝ => (1 - t) * (log t * (log (1 - t) + t) / t)) (𝓝[<] 1)
      (𝓝 0) := by
    have h := (((i2P1FEnd_tendsto_one_sub_mul_log.mul hl1).add
      (((hi1.const_sub 1).mul hi1).mul hl1)).div hi1 one_ne_zero)
    simp only [mul_zero, add_zero, zero_div] at h
    refine h.congr fun t => ?_
    simp only [Pi.div_apply]
    ring
  have hq1 : Tendsto (fun t : ℝ => (1 - t) * (log (1 - t) / t)) (𝓝[<] 1) (𝓝 0) := by
    have h := i2P1FEnd_tendsto_one_sub_mul_log.div hi1 one_ne_zero
    rw [zero_div] at h
    refine h.congr fun t => ?_
    simp only [Pi.div_apply]
    ring
  have hB := (((((((hg1.neg.sub (hk1.const_mul 2)).sub
    (hq1.const_mul 2)).add
    (tendsto_Li₂_one_left.const_mul 2)).add ((hl1.mul tendsto_Li₂_one_left).const_mul 2)).sub
    (tendsto_Li₃_one_left.const_mul 2)).sub ((hi1.mul hl1).const_mul 2)).sub
    (hi1.mul (hl1.pow 2)))
  have h := intervalIntegrable_and_integral_eq_of_nonpos (F := i2P1FEndF5)
    (f := fun t => log t ^ 2 * (log (1 - t) + t) / t ^ 2)
    (fun x hx => i2P1FEnd_hasDerivAt_F5 hx)
    (fun x hx => by
      have hb : log (1 - x) + x ≤ 0 := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 - x by linarith [hx.2])
        linarith
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hb)
        (sq_nonneg _))
    hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2]
  ring

/-- **The last integral of the `ℱ`-part**:
`∫₀¹ (1 + t) / (t (1 - t)) log² t I(t) dt = 2 π⁴ / 45 - 4 ζ(3) + π² / 3`. -/
theorem i2P1FEnd_value :
    IntervalIntegrable (fun t => (1 + t) / (t * (1 - t)) * log t ^ 2 * i2P1FI t) volume 0 1 ∧
      ∫ t in (0 : ℝ)..1, (1 + t) / (t * (1 - t)) * log t ^ 2 * i2P1FI t =
        2 * π ^ 4 / 45 - 4 * zeta3 + π ^ 2 / 3 := by
  obtain ⟨i1, v1⟩ := i2P1FEnd_log_sq
  obtain ⟨i2, v2⟩ := i2P1USig_log_cube
  obtain ⟨i3, v3⟩ := i2P1FEnd_log_cube
  obtain ⟨i4, v4⟩ := i2P1FEnd_P3
  obtain ⟨i5, v5⟩ := intervalIntegrable_and_integral_log_sq_mul_log_one_sub_div
  obtain ⟨i6, v6⟩ := i2P1FEnd_P5
  have hi := ((((i1.const_mul (3 / 2)).sub i2).add (i3.const_mul (1 / 2))).sub
    (i4.const_mul (1 / 2))).add i5 |>.add (i6.const_mul (3 / 2))
  have heq : EqOn (fun t => 3 / 2 * log t ^ 2 - log t ^ 3 / (1 - t) + 1 / 2 * log t ^ 3 -
      1 / 2 * (log t ^ 2 * log (1 - t)) + log t ^ 2 * log (1 - t) / t +
      3 / 2 * (log t ^ 2 * (log (1 - t) + t) / t ^ 2))
      (fun t => (1 + t) / (t * (1 - t)) * log t ^ 2 * i2P1FI t) (uIoo 0 1) := by
    intro t ht
    rw [uIoo_of_le zero_le_one] at ht
    have h0 : t ≠ 0 := ht.1.ne'
    have h1 : 1 - t ≠ 0 := by linarith [ht.2]
    simp only [i2P1FI]
    field_simp
    ring
  refine ⟨hi.congr_uIoo heq, ?_⟩
  rw [← intervalIntegral.integral_congr_uIoo heq]
  simp only [intervalIntegral.integral_add ((((i1.const_mul (3 / 2)).sub i2).add
      (i3.const_mul (1 / 2))).sub (i4.const_mul (1 / 2)) |>.add i5) (i6.const_mul (3 / 2)),
    intervalIntegral.integral_add ((((i1.const_mul (3 / 2)).sub i2).add
      (i3.const_mul (1 / 2))).sub (i4.const_mul (1 / 2))) i5,
    intervalIntegral.integral_sub (((i1.const_mul (3 / 2)).sub i2).add
      (i3.const_mul (1 / 2))) (i4.const_mul (1 / 2)),
    intervalIntegral.integral_add ((i1.const_mul (3 / 2)).sub i2) (i3.const_mul (1 / 2)),
    intervalIntegral.integral_sub (i1.const_mul (3 / 2)) i2,
    intervalIntegral.integral_const_mul, v1, v2, v3, v4, v5, v6]
  ring

end QED.ThreeLoopD
