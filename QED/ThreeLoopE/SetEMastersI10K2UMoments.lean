/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.ExtraIntegrals
import QED.Polylog.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Affine logarithmic moments of the inner parameter of `K₂`

The affine base is `1 - t + t * u`. The two pure moments have elementary
primitives. In the mixed moment with `log u`, the primitive of
`log (1 + t * u / (1 - t)) / u` is obtained by composing the dilogarithm
with `t * u / (1 - t + t * u)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ThreeLoopE

/-- Primitive of `x * log x`. -/
noncomputable def i10K2UPrimOne (x : ℝ) : ℝ := x ^ 2 * (log x / 2 - 1 / 4)

/-- Primitive of `x * log x ^ 2`. -/
noncomputable def i10K2UPrimTwo (x : ℝ) : ℝ :=
  x ^ 2 / 2 * (log x ^ 2 - log x + 1 / 2)

private theorem hasDerivAt_i10K2UPrimOne {x : ℝ} (hx : 0 < x) :
    HasDerivAt i10K2UPrimOne (x * log x) x := by
  refine ((hasDerivAt_pow 2 x).mul
    (((hasDerivAt_log hx.ne').div_const 2).sub_const (1 / 4))).congr_deriv ?_
  field_simp [hx.ne']
  ring

private theorem hasDerivAt_i10K2UPrimTwo {x : ℝ} (hx : 0 < x) :
    HasDerivAt i10K2UPrimTwo (x * log x ^ 2) x := by
  have h := hasDerivAt_log hx.ne'
  refine (((hasDerivAt_pow 2 x).div_const 2).mul
    (((h.pow 2).sub h).add_const (1 / 2))).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.pow_apply]
  field_simp [hx.ne']
  ring

private theorem i10K2U_base_pos {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) 1) : 0 < 1 - t + t * u :=
  add_pos_of_pos_of_nonneg (sub_pos.mpr ht.2) (mul_nonneg ht.1.le hu.1)

private theorem intervalIntegrable_i10K2U_base_pow {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
    IntervalIntegrable (fun u => (1 - t + t * u) * log (1 - t + t * u) ^ n) volume 0 1 := by
  have h : ContinuousOn (fun u : ℝ => 1 - t + t * u) (Icc 0 1) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  rw [← uIcc_of_le zero_le_one] at h
  apply (h.mul ((h.log ?_).pow n)).intervalIntegrable
  intro u hu
  rw [uIcc_of_le zero_le_one] at hu
  exact (i10K2U_base_pos ht hu).ne'

theorem integral_i10K2U_log {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫ u in (0 : ℝ)..1, (1 - t + t * u) * log (1 - t + t * u) =
      (i10K2UPrimOne 1 - i10K2UPrimOne (1 - t)) / t := by
  have hI := intervalIntegrable_i10K2U_base_pow ht 1
  simp only [pow_one] at hI
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => i10K2UPrimOne (1 - t + t * u) / t) ?_ hI]
  · norm_num [show 1 - t + t = 1 by ring]
    ring
  · intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    have hq := ((hasDerivAt_id' u).const_mul t).const_add (1 - t)
    refine (((hasDerivAt_i10K2UPrimOne (i10K2U_base_pos ht hu)).comp u hq).div_const t)
      |>.congr_deriv ?_
    field_simp [ht.1.ne']

theorem integral_i10K2U_log_sq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∫ u in (0 : ℝ)..1, (1 - t + t * u) * log (1 - t + t * u) ^ 2 =
      (i10K2UPrimTwo 1 - i10K2UPrimTwo (1 - t)) / t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => i10K2UPrimTwo (1 - t + t * u) / t) ?_
    (intervalIntegrable_i10K2U_base_pow ht 2)]
  · norm_num [show 1 - t + t = 1 by ring]
    ring
  · intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    have hq := ((hasDerivAt_id' u).const_mul t).const_add (1 - t)
    refine (((hasDerivAt_i10K2UPrimTwo (i10K2U_base_pos ht hu)).comp u hq).div_const t)
      |>.congr_deriv ?_
    field_simp [ht.1.ne']

private noncomputable def i10K2ULanden (y : ℝ) : ℝ :=
  Li₂ y + log (1 - y) ^ 2 / 2

private theorem hasDerivAt_i10K2ULanden {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt i10K2ULanden (-log (1 - y) / (y * (1 - y))) y := by
  have hc := (sub_pos.mpr hy.2).ne'
  have h := (((hasDerivAt_id' y).const_sub 1).log hc).pow 2
  refine ((hasDerivAt_Li₂' hy).add (h.div_const 2)).congr_deriv ?_
  field_simp [hy.1.ne', hc]
  ring

private theorem hasDerivAt_i10K2ULanden_comp {c t u : ℝ}
    (hc : 0 < c) (ht : 0 < t) (hu : 0 < u) :
    HasDerivAt (fun v => i10K2ULanden (t * v / (c + t * v)))
      ((log (c + t * u) - log c) / u) u := by
  have hp : 0 < c + t * u := add_pos hc (mul_pos ht hu)
  have hy : t * u / (c + t * u) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (mul_pos ht hu) hp, (div_lt_one hp).mpr (by linarith)⟩
  have hn := (hasDerivAt_id' u).const_mul t
  have hd := (hasDerivAt_i10K2ULanden hy).comp u (hn.div (hn.const_add c) hp.ne')
  refine hd.congr_deriv ?_
  rw [show 1 - t * u / (c + t * u) = c / (c + t * u) by field_simp; ring,
    log_div hc.ne' hp.ne']
  field_simp [hc.ne', ht.ne', hu.ne', hp.ne']
  ring

private noncomputable def i10K2UPrimAux (c q : ℝ) : ℝ :=
  i10K2UPrimOne q / 2 + c * (q * (log q - 1)) / 2 - q ^ 2 / 8 - c * q / 4

private theorem hasDerivAt_i10K2UPrimAux (c : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (i10K2UPrimAux c) ((q + c) * (log q / 2 - 1 / 4)) q := by
  have hl := ((hasDerivAt_id' q).mul ((hasDerivAt_log hq.ne').sub_const 1)).const_mul c
  refine (((((hasDerivAt_i10K2UPrimOne hq).div_const 2).add (hl.div_const 2)).sub
    ((hasDerivAt_pow 2 q).div_const 8)).sub
    (((hasDerivAt_id' q).const_mul c).div_const 4)).congr_deriv ?_
  field_simp [hq.ne']
  ring

private noncomputable def i10K2UPrimMixed (c t u : ℝ) : ℝ :=
  let q := c + t * u
  ((i10K2UPrimOne q - i10K2UPrimOne c) * log u -
    c ^ 2 / 2 * i10K2ULanden (t * u / q) - i10K2UPrimAux c q) / t

private theorem hasDerivAt_i10K2UPrimMixed {c t u : ℝ}
    (hc : 0 < c) (ht : 0 < t) (hu : 0 < u) :
    HasDerivAt (i10K2UPrimMixed c t) ((c + t * u) * log (c + t * u) * log u) u := by
  have hp : 0 < c + t * u := add_pos hc (mul_pos ht hu)
  have hq := ((hasDerivAt_id' u).const_mul t).const_add c
  have h := ((((hasDerivAt_i10K2UPrimOne hp).comp u hq).sub_const
    (i10K2UPrimOne c)).mul (hasDerivAt_log hu.ne')).sub
    ((hasDerivAt_i10K2ULanden_comp hc ht hu).const_mul (c ^ 2 / 2))
  refine ((h.sub ((hasDerivAt_i10K2UPrimAux c hp).comp u hq)).div_const t).congr_deriv ?_
  simp only [Function.comp_apply, i10K2UPrimOne]
  field_simp [ht.ne', hu.ne']
  ring

private theorem tendsto_i10K2UPrimMixed_zero {c t : ℝ} (hc : 0 < c) :
    Tendsto (i10K2UPrimMixed c t) (𝓝[>] 0) (𝓝 (-i10K2UPrimAux c c / t)) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hq : Tendsto (fun u => c + t * u) (𝓝[>] 0) (𝓝 c) := by
    simpa only [mul_zero, add_zero] using (hu.const_mul t).const_add c
  have hf : HasDerivAt (fun u : ℝ => c + t * u) t 0 := by
    simpa only [mul_one] using ((hasDerivAt_id' (0 : ℝ)).const_mul t).const_add c
  have hc0 : c + t * 0 = c := by ring
  have hd' : HasDerivAt (fun u => i10K2UPrimOne (c + t * u)) ((c * log c) * t) 0 :=
    ((hasDerivAt_i10K2UPrimOne hc).comp_of_eq 0 hf hc0.symm)
  have hs := hd'.tendsto_slope_zero_right
  simp only [zero_add, mul_zero, add_zero, smul_eq_mul] at hs
  have hl := hs.mul tendsto_mul_log_zero
  simp only [mul_zero] at hl
  have hlog : Tendsto (fun u => (i10K2UPrimOne (c + t * u) - i10K2UPrimOne c) * log u)
      (𝓝[>] 0) (𝓝 0) := by
    refine hl.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u (hu' : 0 < u)
    field_simp [hu'.ne']
  have hy : Tendsto (fun u => t * u / (c + t * u)) (𝓝[>] 0) (𝓝 0) := by
    have h := (hu.const_mul t).div hq hc.ne'
    rw [mul_zero, zero_div] at h
    exact h.congr (fun _ => rfl)
  have hL : ContinuousAt i10K2ULanden 0 := by
    unfold i10K2ULanden
    refine hasDerivAt_Li₂_zero.continuousAt.add
      (((continuous_const.sub continuous_id).continuousAt.log ?_).pow 2 |>.div_const 2)
    norm_num
  have h := ((hlog.sub ((hL.tendsto.comp hy).const_mul (c ^ 2 / 2))).sub
    ((hasDerivAt_i10K2UPrimAux c hc).continuousAt.tendsto.comp hq)).div_const t
  unfold i10K2UPrimMixed
  simpa [i10K2ULanden, Li₂_zero] using h

theorem integral_i10K2U_log_mul_log {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    let c := 1 - t
    IntervalIntegrable (fun u => (c + t * u) * log (c + t * u) * log u) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, (c + t * u) * log (c + t * u) * log u =
      -(c ^ 2 / 2 * (Li₂ t + log c ^ 2 / 2) +
        (i10K2UPrimOne 1 - i10K2UPrimOne c + c * (-1 - c * (log c - 1))) / 2 -
        (1 - c ^ 2) / 8 - c * t / 4) / t := by
  dsimp only
  set c := 1 - t
  have hc : 0 < c := sub_pos.mpr ht.2
  have he : c + t * 1 = 1 := by dsimp [c]; ring
  have hq : ContinuousAt (fun u => c + t * u) 1 :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
  have hqNe : c + t * 1 ≠ 0 := by rw [he]; exact one_ne_zero
  have hy : ContinuousAt (fun u => t * u / (c + t * u)) 1 :=
    (continuous_const.mul continuous_id).continuousAt.div hq hqNe
  have hy1 : t * 1 / (c + t * 1) = t := by rw [he, mul_one, div_one]
  have hL := (hasDerivAt_i10K2ULanden ht).continuousAt
  have hLc : ContinuousAt (fun u => i10K2ULanden (t * u / (c + t * u))) 1 := by
    exact hL.comp_of_eq hy hy1
  have hq0 : 0 < c + t * 1 := by rw [he]; exact zero_lt_one
  have h1 : ContinuousAt (fun u => i10K2UPrimOne (c + t * u)) 1 :=
    (hasDerivAt_i10K2UPrimOne hq0).continuousAt.comp'
      (f := fun u : ℝ => c + t * u) hq
  have h2 : ContinuousAt (fun u => i10K2UPrimAux c (c + t * u)) 1 :=
    (hasDerivAt_i10K2UPrimAux c hq0).continuousAt.comp'
      (f := fun u : ℝ => c + t * u) hq
  have hC : ContinuousAt (i10K2UPrimMixed c t) 1 :=
    ((((h1.sub_const (i10K2UPrimOne c)).mul (continuousAt_log one_ne_zero)).sub
      (hLc.const_mul (c ^ 2 / 2))).sub h2).div_const t
  have h := intervalIntegrable_and_integral_eq_of_nonneg
    (fun u hu => hasDerivAt_i10K2UPrimMixed hc ht.1 hu.1)
    (fun u hu => ?_) (tendsto_i10K2UPrimMixed_zero hc)
    (hC.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ))))
  · refine ⟨h.1, ?_⟩
    rw [h.2]
    unfold i10K2UPrimMixed i10K2UPrimAux i10K2ULanden
    dsimp only
    rw [hy1, he]
    simp only [log_one, mul_zero, zero_sub, one_pow, one_mul]
    have ht' : t = 1 - c := by dsimp [c]; ring
    linear_combination (-c / 4 / t) * ht'
  · have hp := i10K2U_base_pos ht (Ioo_subset_Icc_self hu)
    have hb : c + t * u ≤ 1 := by
      dsimp [c]
      nlinarith only [mul_nonneg ht.1.le (sub_nonneg.mpr hu.2.le)]
    exact mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hp.le (log_nonpos hp.le hb))
      (log_nonpos hu.1.le hu.2.le)

private theorem i10K2U_weight_log :
    IntervalIntegrable (fun u : ℝ => (1 - u) * log u) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, (1 - u) * log u = -(3 / 4) := by
  let F := fun u : ℝ => u * (log u - 1) - i10K2UPrimOne u
  have hd {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F ((1 - u) * log u) u := by
    have h := (hasDerivAt_id' u).mul ((hasDerivAt_log hu.1.ne').sub_const 1)
    refine (h.sub (hasDerivAt_i10K2UPrimOne hu.1)).congr_deriv ?_
    field_simp [hu.1.ne']
    ring
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlog := tendsto_mul_log_zero
  have h0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have h := (hlog.sub hu).sub (((hu.mul hlog).div_const 2).sub ((hu.pow 2).div_const 4))
    norm_num at h
    exact h.congr fun u => by dsimp [F, i10K2UPrimOne]; ring
  have h1 : Tendsto F (𝓝[<] 1) (𝓝 (-(3 / 4))) := by
    have hc : ContinuousAt F 1 :=
      (continuousAt_id.mul ((continuousAt_log one_ne_zero).sub_const 1)).sub
        (hasDerivAt_i10K2UPrimOne zero_lt_one).continuousAt
    have hv : F 1 = -(3 / 4) := by norm_num [F, i10K2UPrimOne]
    rw [← hv]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [sub_zero] using intervalIntegrable_and_integral_eq_of_nonpos
    (fun _ => hd) (fun u hu => mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu.2.le)
      (log_nonpos hu.1.le hu.2.le)) h0 h1

private theorem i10K2U_weight_log_sq :
    IntervalIntegrable (fun u : ℝ => (1 - u) * log u ^ 2) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, (1 - u) * log u ^ 2 = 7 / 4 := by
  let F := fun u : ℝ => u * (log u ^ 2 - 2 * log u + 2) - i10K2UPrimTwo u
  have hd {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F ((1 - u) * log u ^ 2) u := by
    have hl := hasDerivAt_log hu.1.ne'
    have h := (hasDerivAt_id' u).mul (((hl.pow 2).sub (hl.const_mul 2)).add_const 2)
    refine (h.sub (hasDerivAt_i10K2UPrimTwo hu.1)).congr_deriv ?_
    simp only [Pi.sub_apply, Pi.pow_apply]
    field_simp [hu.1.ne']
    ring
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hl := tendsto_mul_log_zero
  have hls := tendsto_mul_log_sq_zero
  have h0 : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have h := ((hls.sub (hl.const_mul 2)).add (hu.const_mul 2)).sub
      ((hu.mul ((hls.sub hl).add (hu.div_const 2))).div_const 2)
    norm_num at h
    exact h.congr fun u => by dsimp [F, i10K2UPrimTwo]; ring
  have h1 : Tendsto F (𝓝[<] 1) (𝓝 (7 / 4)) := by
    have hl := continuousAt_log (x := (1 : ℝ)) one_ne_zero
    have hc : ContinuousAt F 1 :=
      (continuousAt_id.mul (((hl.pow 2).sub (hl.const_mul 2)).add_const 2)).sub
        (hasDerivAt_i10K2UPrimTwo zero_lt_one).continuousAt
    have hv : F 1 = 7 / 4 := by norm_num [F, i10K2UPrimTwo]
    rw [← hv]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [sub_zero] using intervalIntegrable_and_integral_eq_of_nonneg
    (fun _ => hd) (fun u hu => mul_nonneg (sub_nonneg.mpr hu.2.le) (sq_nonneg _)) h0 h1

private theorem i10K2U_weight :
    IntervalIntegrable (fun u : ℝ => 1 - u) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, 1 - u = 1 / 2 := by
  have hI : IntervalIntegrable (fun u : ℝ => u) volume 0 1 :=
    continuous_id.intervalIntegrable _ _
  refine ⟨intervalIntegrable_const.sub hI, ?_⟩
  rw [intervalIntegral.integral_sub intervalIntegrable_const hI, integral_id]
  norm_num

theorem integral_i10K2U_weight_log_sub (L : ℝ) :
    IntervalIntegrable (fun u : ℝ => (1 - u) * (L - log u)) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, (1 - u) * (L - log u) = L / 2 + 3 / 4 := by
  have he : (fun u : ℝ => (1 - u) * (L - log u)) =
      (fun u => L * (1 - u) - (1 - u) * log u) := by
    funext u
    ring
  rw [he]
  have hI := (i10K2U_weight.1.const_mul L).sub i10K2U_weight_log.1
  refine ⟨hI, ?_⟩
  rw [intervalIntegral.integral_sub (i10K2U_weight.1.const_mul L) i10K2U_weight_log.1,
    intervalIntegral.integral_const_mul, i10K2U_weight.2, i10K2U_weight_log.2]
  ring

theorem integral_i10K2U_weight_log_sub_sq (L : ℝ) :
    IntervalIntegrable (fun u : ℝ => (1 - u) * (L - log u) ^ 2) volume 0 1 ∧
      ∫ u in (0 : ℝ)..1, (1 - u) * (L - log u) ^ 2 = L ^ 2 / 2 + 3 * L / 2 + 7 / 4 := by
  have he : (fun u : ℝ => (1 - u) * (L - log u) ^ 2) =
      (fun u => L ^ 2 * (1 - u) - (2 * L) * ((1 - u) * log u) + (1 - u) * log u ^ 2) := by
    funext u
    ring
  rw [he]
  have h := i10K2U_weight.1.const_mul (L ^ 2)
  have hL := i10K2U_weight_log.1.const_mul (2 * L)
  refine ⟨(h.sub hL).add i10K2U_weight_log_sq.1, ?_⟩
  rw [intervalIntegral.integral_add (h.sub hL) i10K2U_weight_log_sq.1,
    intervalIntegral.integral_sub h hL, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, i10K2U_weight.2, i10K2U_weight_log.2,
    i10K2U_weight_log_sq.2]
  ring

/-- The integrated coefficient of degree one in the inner integral of `K₂`. -/
theorem integral_i10K2U_coeff_one {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    let q := fun u : ℝ => 1 - (1 - u) * t
    ∫ u in (0 : ℝ)..1, (-(1 - u)) * (log t - log u) - 3 * q u * log (q u) / t =
      -log t / 2 - 3 / 2 + 3 / (2 * t) + 3 / 2 * ((1 - t) ^ 2 * log (1 - t)) / t ^ 2 := by
  have e (u : ℝ) : 1 - (1 - u) * t = 1 - t + t * u := by ring
  dsimp only
  simp only [e]
  have h := integral_i10K2U_weight_log_sub (log t)
  have hQ := intervalIntegrable_i10K2U_base_pow ht 1
  simp only [pow_one] at hQ
  have hc : (fun u : ℝ => (-(1 - u)) * (log t - log u) -
      3 * (1 - t + t * u) * log (1 - t + t * u) / t) =
      (fun u => -(1) * ((1 - u) * (log t - log u)) -
        (3 / t) * ((1 - t + t * u) * log (1 - t + t * u))) := by
    funext u
    ring
  rw [hc, intervalIntegral.integral_sub (h.1.const_mul (-1)) (hQ.const_mul (3 / t)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h.2,
    integral_i10K2U_log ht]
  unfold i10K2UPrimOne
  rw [log_one]
  field_simp [ht.1.ne']
  ring

/-- The integrated coefficient of degree two in the inner integral of `K₂`. -/
theorem integral_i10K2U_coeff_two {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    let c := 1 - t
    let q := fun u : ℝ => 1 - (1 - u) * t
    let L := log t
    let M₁ := (i10K2UPrimOne 1 - i10K2UPrimOne c) / t
    let M₂ := (i10K2UPrimTwo 1 - i10K2UPrimTwo c) / t
    let M₃ := -(c ^ 2 / 2 * (Li₂ t + log c ^ 2 / 2) +
      (i10K2UPrimOne 1 - i10K2UPrimOne c + c * (-1 - c * (log c - 1))) / 2 -
      (1 - c ^ 2) / 8 - c * t / 4) / t
    ∫ u in (0 : ℝ)..1, (-(1 - u)) * (L - log u) ^ 2 / 2 -
        3 * q u * log (q u) * (L - log u) / t + (9 / 2) * q u * log (q u) ^ 2 / t =
      -L ^ 2 / 4 - 3 * L / 4 - 7 / 8 - 3 / t * (L * M₁ - M₃) + 9 / (2 * t) * M₂ := by
  let c := 1 - t
  let q := fun u : ℝ => c + t * u
  let L := log t
  have e (u : ℝ) : 1 - (1 - u) * t = q u := by
    dsimp [c, q]
    ring
  dsimp only
  simp only [e]
  obtain ⟨hM, vM⟩ := integral_i10K2U_log_mul_log ht
  obtain ⟨hW, vW⟩ := integral_i10K2U_weight_log_sub_sq L
  have hQ := intervalIntegrable_i10K2U_base_pow ht 1
  simp only [pow_one] at hQ
  have hQ2 := intervalIntegrable_i10K2U_base_pow ht 2
  have hc : (fun u => (-(1 - u)) * (log t - log u) ^ 2 / 2 -
        3 * q u * log (q u) * (log t - log u) / t + (9 / 2) * q u * log (q u) ^ 2 / t) =
        (fun u => (-(1 / 2)) * ((1 - u) * (L - log u) ^ 2) -
          (3 / t) * (L * (q u * log (q u)) - q u * log (q u) * log u) +
          (9 / (2 * t)) * (q u * log (q u) ^ 2)) := by
    funext u
    dsimp only [L]
    ring
  rw [hc]
  have hMid : IntervalIntegrable (fun u => L * (q u * log (q u)) - q u * log (q u) * log u)
      volume 0 1 := (hQ.const_mul L).sub hM
  have h1 : IntervalIntegrable (fun u => -(1 / 2) * ((1 - u) * (L - log u) ^ 2)) volume 0 1 :=
    hW.const_mul _
  have h2 := hMid.const_mul (3 / t)
  have h3 : IntervalIntegrable (fun u => (9 / (2 * t)) * (q u * log (q u) ^ 2)) volume 0 1 :=
    hQ2.const_mul _
  rw [intervalIntegral.integral_add (h1.sub h2) h3, intervalIntegral.integral_sub h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, vW, intervalIntegral.integral_sub (hQ.const_mul L) hM,
    intervalIntegral.integral_const_mul, integral_i10K2U_log ht, integral_i10K2U_log_sq ht, vM]
  dsimp only [L]
  ring

end QED.ThreeLoopE
