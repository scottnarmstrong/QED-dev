/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemA2LDeriv
public import QED.Polylog.LiLimits
public import QED.Polylog.Integral

/-!
# Set (d), master `I₉`: the log-weighted `y`-integral of `S₁`

For `a, w > 0`, `b = a + w`, `q = w / b` and `K = log (b / a)`,

  `∫₀¹ (log y + log (1 - y)) S₁ / (y (1 - y)) dy
     = a (3/2 F(q) + 3 ζ(3) - 2 Li₃ q - 2 K Li₂ q - K³/6) + b (ζ(3) + 2 Li₃ q + F(q)/2)
       - 3 w ζ(3)`,

with `F = QED.Polylog.logOneSubSqPrim` and `S₁ = QED.ThreeLoopD.i9A2S1`. The antiderivative is
`QED.ThreeLoopD.i9A2HL` (`QED.ThreeLoopD.SetDMastersI9RemA2LDeriv`); here we compute its
one-sided limits at `0` and `1`. Each product that is singular at an endpoint is a logarithm
times a factor bounded by a multiple of the distance to that endpoint.

## Main results

* `QED.ThreeLoopD.integral_i9A2YL_div`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- The closed form of `∫₀¹ (log y + log (1 - y)) S₁ / (y (1 - y)) dy`. -/
noncomputable def i9A2YL (a w : ℝ) : ℝ :=
  a * (3 / 2 * logOneSubSqPrim (w / (a + w)) + 3 * zeta3 - 2 * Li₃ (w / (a + w)) -
      2 * Real.log ((a + w) / a) * Li₂ (w / (a + w)) - Real.log ((a + w) / a) ^ 3 / 6) +
    (a + w) * (zeta3 + 2 * Li₃ (w / (a + w)) + logOneSubSqPrim (w / (a + w)) / 2) -
    3 * w * zeta3

/-! ### Limit tools -/

/-- `log y · g y → 0` at `0⁺` when `|g y| ≤ C y` eventually. -/
theorem i9A2L_tendsto_log_mul {g : ℝ → ℝ} {C : ℝ}
    (hb : ∀ᶠ y in 𝓝[>] (0 : ℝ), |g y| ≤ C * y) :
    Tendsto (fun y => Real.log y * g y) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_mul_log_zero.abs).const_mul |C|
  rw [abs_zero, mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [hb, self_mem_nhdsWithin] with x hx (hx0 : 0 < x)
  rw [Real.norm_eq_abs, abs_mul]
  calc |Real.log x| * |g x| ≤ |Real.log x| * (C * x) :=
        mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = C * |x * Real.log x| := by rw [abs_mul, abs_of_pos hx0]; ring
    _ ≤ |C| * |x * Real.log x| := mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)

/-- `g y · log² (1 - y) → 0` at `1⁻` when `|g y| ≤ C (1 - y)` eventually. -/
theorem i9A2L_tendsto_mul_log_one_sub_sq {g : ℝ → ℝ} {C : ℝ}
    (hb : ∀ᶠ y in 𝓝[<] (1 : ℝ), |g y| ≤ C * (1 - y)) :
    Tendsto (fun y => g y * Real.log (1 - y) ^ 2) (𝓝[<] 1) (𝓝 0) := by
  have hb' : ∀ᶠ t in 𝓝[>] (0 : ℝ), |g (1 - t)| ≤ C * t :=
    (tendsto_one_sub_nhdsGT_zero.eventually hb).mono fun t ht => by
      simpa only [sub_sub_cancel] using ht
  have h := (tendsto_mul_log_sq_of_abs_le hb').comp tendsto_one_sub_nhdsLT_one
  refine h.congr' ?_
  filter_upwards with x
  simp only [Function.comp_apply, sub_sub_cancel]

/-- Continuity at an endpoint, as a one-sided limit. -/
theorem i9A2L_tendsto_of_hasDerivAt {f : ℝ → ℝ} {f' y₀ : ℝ} {l : Filter ℝ} (hl : l ≤ 𝓝 y₀)
    (hf : HasDerivAt f f' y₀) : Tendsto f l (𝓝 (f y₀)) :=
  hf.continuousAt.tendsto.mono_left hl

theorem i9A2L_eventually_mem_zero :
    ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)

theorem i9A2L_eventually_mem_one :
    ∀ᶠ y in 𝓝[<] (1 : ℝ), y ∈ Ioo (1 / 2 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)

/-! ### Endpoint bounds -/

section Bounds

variable {a w : ℝ} (ha : 0 < a) (hw : 0 < w)
include ha hw

theorem i9A2L_abs_Li₂_v_le :
    ∀ᶠ y in 𝓝[>] (0 : ℝ), |Li₂ (i9A2v a w y)| ≤ π ^ 2 / 6 * (w / a) * y := by
  filter_upwards [i9A2L_eventually_mem_zero] with y hy
  have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
  have hm := i9A2v_mem ha hw hy'
  have hP : 0 < a + w * y := by have := hy.1; positivity
  have hle : i9A2v a w y ≤ w / a * y := by
    unfold i9A2v
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by have := hy.1; positivity) ha (by nlinarith [hy.1])
  calc |Li₂ (i9A2v a w y)| ≤ π ^ 2 / 6 * |i9A2v a w y| :=
        abs_Li₂_le (by rw [abs_of_pos hm.1]; exact hm.2.le)
    _ ≤ π ^ 2 / 6 * (w / a * y) := by
        rw [abs_of_pos hm.1]; gcongr
    _ = _ := by ring

theorem i9A2L_abs_Li₂_z_le :
    ∀ᶠ y in 𝓝[>] (0 : ℝ), |Li₂ (i9A2z a w y)| ≤ π ^ 2 / 6 * ((a + w) / a) * y := by
  filter_upwards [i9A2L_eventually_mem_zero] with y hy
  have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
  have hm := i9A2z_mem ha hw hy'
  have hle : i9A2z a w y ≤ (a + w) / a * y := by
    unfold i9A2z
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (by have := hy.1; positivity) ha (by nlinarith [hy.1])
  calc |Li₂ (i9A2z a w y)| ≤ π ^ 2 / 6 * |i9A2z a w y| :=
        abs_Li₂_le (by rw [abs_of_pos hm.1]; exact hm.2.le)
    _ ≤ π ^ 2 / 6 * ((a + w) / a * y) := by
        rw [abs_of_pos hm.1]; gcongr
    _ = _ := by ring

theorem i9A2L_abs_l_sq_le :
    ∀ᶠ y in 𝓝[>] (0 : ℝ), |i9A2l a w y ^ 2| ≤ (w / a) ^ 2 * y := by
  filter_upwards [i9A2L_eventually_mem_zero] with y hy
  have hy0 := hy.1
  have hP : 0 < (a + w * y) / a := by positivity
  have h0 : 0 ≤ i9A2l a w y := Real.log_nonneg (by rw [le_div_iff₀ ha]; nlinarith)
  have h1 : i9A2l a w y ≤ w / a * y := by
    have := Real.log_le_sub_one_of_pos hP
    have e : (a + w * y) / a - 1 = w / a * y := by field_simp; ring
    unfold i9A2l; linarith
  have hwy : 0 ≤ w / a * y := by positivity
  rw [abs_of_nonneg (sq_nonneg _)]
  calc i9A2l a w y ^ 2 ≤ (w / a * y) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (w / a) ^ 2 * y * y := by ring
    _ ≤ (w / a) ^ 2 * y * 1 := by gcongr; linarith [hy.2]
    _ = _ := by ring

theorem i9A2L_abs_m_le {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    |i9A2m a w y| ≤ Real.log ((a + w) / a) := by
  have hP : 0 < a + w * y := by have := hy.1; positivity
  have hb : 0 < a + w := by positivity
  unfold i9A2m
  rw [Real.log_div hP.ne' hb.ne', Real.log_div hb.ne' ha.ne', abs_le]
  have h1 : Real.log a ≤ Real.log (a + w * y) := Real.log_le_log ha (by nlinarith [hy.1])
  have h2 : Real.log (a + w * y) ≤ Real.log (a + w) := Real.log_le_log hP (by nlinarith [hy.2])
  constructor <;> linarith

theorem i9A2L_abs_m_mul_le :
    ∀ᶠ y in 𝓝[>] (0 : ℝ), |i9A2m a w y * Real.log (1 - y)| ≤
      2 * Real.log ((a + w) / a) * y := by
  filter_upwards [i9A2L_eventually_mem_zero] with y hy
  have hm := i9A2L_abs_m_le ha hw ⟨hy.1.le, by linarith [hy.2]⟩
  have hl := abs_log_one_sub_le hy.1.le hy.2.le
  rw [abs_mul]
  calc |i9A2m a w y| * |Real.log (1 - y)| ≤ Real.log ((a + w) / a) * (2 * y) :=
        mul_le_mul hm hl (abs_nonneg _) ((abs_nonneg _).trans hm)
    _ = _ := by ring

theorem i9A2L_abs_m_le_one :
    ∀ᶠ y in 𝓝[<] (1 : ℝ), |i9A2m a w y| ≤ 2 * (1 - y) := by
  filter_upwards [i9A2L_eventually_mem_one] with y hy
  have hm := i9A2r_mem ha hw ⟨by linarith [hy.1], hy.2⟩
  have hb : 0 < a + w := by positivity
  have hq : w / (a + w) ≤ 1 := by rw [div_le_one hb]; linarith
  have hr : i9A2r a w y ≤ 1 - y := by
    unfold i9A2r
    calc w / (a + w) * (1 - y) ≤ 1 * (1 - y) := by gcongr; linarith [hy.2]
      _ = 1 - y := one_mul _
  have e : (a + w * y) / (a + w) = 1 - i9A2r a w y := by unfold i9A2r; field_simp; ring
  have hl := abs_log_one_sub_le hm.1.le (by linarith [hy.1])
  unfold i9A2m
  rw [e]
  linarith

theorem i9A2L_abs_Li₂_r_le :
    ∀ᶠ y in 𝓝[<] (1 : ℝ), |Li₂ (i9A2r a w y)| ≤ π ^ 2 / 6 * (1 - y) := by
  filter_upwards [i9A2L_eventually_mem_one] with y hy
  have hm := i9A2r_mem ha hw ⟨by linarith [hy.1], hy.2⟩
  have hb : 0 < a + w := by positivity
  have hr : i9A2r a w y ≤ 1 - y := by
    unfold i9A2r
    have hq : w / (a + w) ≤ 1 := by rw [div_le_one hb]; linarith
    calc w / (a + w) * (1 - y) ≤ 1 * (1 - y) := by gcongr; linarith [hy.2]
      _ = 1 - y := one_mul _
  calc |Li₂ (i9A2r a w y)| ≤ π ^ 2 / 6 * |i9A2r a w y| :=
        abs_Li₂_le (by rw [abs_of_pos hm.1]; exact hm.2.le)
    _ ≤ π ^ 2 / 6 * (1 - y) := by rw [abs_of_pos hm.1]; gcongr

end Bounds

theorem i9A2L_abs_log_le_one :
    ∀ᶠ y in 𝓝[<] (1 : ℝ), |Real.log y| ≤ 2 * (1 - y) := by
  filter_upwards [i9A2L_eventually_mem_one] with y hy
  have := abs_log_one_sub_le (x := 1 - y) (by linarith [hy.2]) (by linarith [hy.1])
  rwa [sub_sub_cancel] at this

theorem i9A2L_abs_Li₂_one_sub_le :
    ∀ᶠ y in 𝓝[<] (1 : ℝ), |Li₂ (1 - y)| ≤ π ^ 2 / 6 * (1 - y) := by
  filter_upwards [i9A2L_eventually_mem_one] with y hy
  have h : |1 - y| = 1 - y := abs_of_pos (by linarith [hy.2])
  calc |Li₂ (1 - y)| ≤ π ^ 2 / 6 * |1 - y| := abs_Li₂_le (by rw [h]; linarith [hy.1])
    _ = _ := by rw [h]

/-! ### The limits -/

theorem i9A2L_mem_Icc_zero {g : ℝ → ℝ} (hg : ∀ y ∈ Ioo (0 : ℝ) 1, g y ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ y in 𝓝[>] (0 : ℝ), g y ∈ Icc (-1 : ℝ) 1 := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
  exact ⟨by linarith [(hg y hy).1], (hg y hy).2.le⟩

theorem i9A2L_mem_Icc_one {g : ℝ → ℝ} (hg : ∀ y ∈ Ioo (0 : ℝ) 1, g y ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ y in 𝓝[<] (1 : ℝ), g y ∈ Icc (-1 : ℝ) 1 := by
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with y hy
  exact ⟨by linarith [(hg y hy).1], (hg y hy).2.le⟩

theorem tendsto_i9A2HL_zero {a w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    Tendsto (fun y => i9A2HL a w y) (𝓝[>] 0)
      (𝓝 (a * (-2 * zeta3 + (-logOneSubSqPrim (w / (a + w)) + 2 * Li₃ (w / (a + w)) +
          2 * Real.log ((a + w) / a) * Li₂ (w / (a + w))) / 2) +
        (a + w) * (-logOneSubSqPrim (w / (a + w)) / 2 - Li₃ (w / (a + w))) + w * zeta3)) := by
  have hb : 0 < a + w := by positivity
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have hq0 : 0 < w / (a + w) := by positivity
  have hq1 : w / (a + w) < 1 := by rw [div_lt_one hb]; linarith
  have hqm : w / (a + w) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hq1.le⟩
  set K := Real.log ((a + w) / a) with hK
  -- the arguments
  have tv : Tendsto (i9A2v a w) (𝓝[>] 0) (𝓝 0) := by
    simpa [i9A2v] using i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2v ha hw le_rfl)
  have tz : Tendsto (i9A2z a w) (𝓝[>] 0) (𝓝 0) := by
    simpa [i9A2z] using i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2z ha hw le_rfl)
  have tr : Tendsto (i9A2r a w) (𝓝[>] 0) (𝓝 (w / (a + w))) := by
    simpa [i9A2r] using i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2r a w 0)
  have tl : Tendsto (i9A2l a w) (𝓝[>] 0) (𝓝 0) := by
    simpa [i9A2l, ha.ne'] using i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2l ha hw le_rfl)
  have tm : Tendsto (i9A2m a w) (𝓝[>] 0) (𝓝 (i9A2m a w 0)) :=
    i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2m ha hw le_rfl)
  have tvp : Tendsto (i9A2v a w) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tv, by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
      exact (i9A2v_mem ha hw hy).1⟩
  have tzp : Tendsto (i9A2z a w) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tz, by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
      exact (i9A2z_mem ha hw hy).1⟩
  have hvI := i9A2L_mem_Icc_zero fun y hy => i9A2v_mem ha hw hy
  have hzI := i9A2L_mem_Icc_zero fun y hy => i9A2z_mem ha hw hy
  have hrI := i9A2L_mem_Icc_zero fun y hy => i9A2r_mem ha hw hy
  have tLv : Tendsto (fun y => Li₂ (i9A2v a w y)) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_Li₂_comp (by norm_num) tv hvI
  have tTv : Tendsto (fun y => Li₃ (i9A2v a w y)) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_Li₃_comp (by norm_num) tv hvI
  have tLz : Tendsto (fun y => Li₂ (i9A2z a w y)) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_Li₂_comp (by norm_num) tz hzI
  have tTz : Tendsto (fun y => Li₃ (i9A2z a w y)) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_Li₃_comp (by norm_num) tz hzI
  have tLr := tendsto_Li₂_comp hqm tr hrI
  have tTr := tendsto_Li₃_comp hqm tr hrI
  have tFv := tendsto_logOneSubSqPrim_zero.comp tvp
  have tFz := tendsto_logOneSubSqPrim_zero.comp tzp
  have tFy := tendsto_logOneSubSqPrim_zero
  have tFr : Tendsto (fun y => logOneSubSqPrim (i9A2r a w y)) (𝓝[>] 0)
      (𝓝 (logOneSubSqPrim (w / (a + w)))) :=
    ((hasDerivAt_logOneSubSqPrim ⟨hq0, hq1⟩).continuousAt.tendsto).comp tr
  have tFs := tendsto_logOneSubSqPrim_one.comp tendsto_one_sub_nhdsGT_zero
  have tY1 := tendsto_log_one_sub_zero
  have tLs := tendsto_Li₂_one_left.comp tendsto_one_sub_nhdsGT_zero
  have tTs := tendsto_Li₃_one_left.comp tendsto_one_sub_nhdsGT_zero
  -- the singular products
  have sYLv := i9A2L_tendsto_log_mul (i9A2L_abs_Li₂_v_le ha hw)
  have sYLz := i9A2L_tendsto_log_mul (i9A2L_abs_Li₂_z_le ha hw)
  have sYl := i9A2L_tendsto_log_mul (i9A2L_abs_l_sq_le ha hw)
  have sYmY1 := i9A2L_tendsto_log_mul (i9A2L_abs_m_mul_le ha hw)
  have sY2Y1 : Tendsto (fun y => Real.log y ^ 2 * Real.log (1 - y)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_one_sub_mul_log_sq.congr fun y => mul_comm _ _
  have sYLy := tendsto_log_mul_Li₂_zero
  have smYY1 : Tendsto (fun y => i9A2m a w y * Real.log y * Real.log (1 - y)) (𝓝[>] 0)
      (𝓝 0) := sYmY1.congr fun y => by ring
  -- assembling
  have hA := (((((sYLv.add (sYl.div_const 2)).sub tTv).sub (tl.mul tLv)).add tFv).sub
    ((tl.pow 3).div_const 6)).add ((((((((((tFy.sub tFz).sub tFr).sub (tm.mul (tY1.pow 2))).add
    ((tm.pow 2).mul tY1)).add ((tm.const_mul (2 * K)).mul tY1)).sub
    ((tLr.mul tY1).const_mul 2)).add (tTr.const_mul 2)).add (tLr.const_mul (2 * K))).div_const 2))
  have hB := ((((((((tFs.add tFr).sub ((sY2Y1.sub (smYY1.const_mul 2)).add
    ((tm.pow 2).mul tY1))).sub ((sYLz.sub (tm.mul tLz)).const_mul 2)).add
    (tTz.const_mul 2)).add ((sYLv.sub (tm.mul tLv)).const_mul 2)).sub
    (tTv.const_mul 2)).neg.div_const 2).add (tLr.mul tY1)).sub tTr
  have hW := ((((tLs.mul tY1).neg.add (sYLy.const_mul 2)).add tTs).sub
    (tendsto_Li₃_zero_right.const_mul 2)).add sY2Y1
  have h := ((hA.const_mul a).add (hB.const_mul (a + w))).add (hW.const_mul w)
  refine (h.congr' (Eventually.of_forall fun y => rfl)).trans (le_of_eq ?_)
  congr 1
  ring

theorem tendsto_i9A2HL_one {a w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    Tendsto (fun y => i9A2HL a w y) (𝓝[<] 1)
      (𝓝 (a * (-Li₃ (w / (a + w)) - Real.log ((a + w) / a) * Li₂ (w / (a + w)) +
          logOneSubSqPrim (w / (a + w)) - Real.log ((a + w) / a) ^ 3 / 6 + zeta3) +
        (a + w) * (zeta3 + Li₃ (w / (a + w))) - 2 * w * zeta3)) := by
  have hb : 0 < a + w := by positivity
  have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have hq0 : 0 < w / (a + w) := by positivity
  have hq1 : w / (a + w) < 1 := by rw [div_lt_one hb]; linarith
  have hqm : w / (a + w) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hq1.le⟩
  set K := Real.log ((a + w) / a) with hK
  -- the arguments
  have tY : Tendsto (fun y => Real.log y) (𝓝[<] 1) (𝓝 0) := by
    simpa using i9A2L_tendsto_of_hasDerivAt hle (Real.hasDerivAt_log one_ne_zero)
  have tv : Tendsto (i9A2v a w) (𝓝[<] 1) (𝓝 (w / (a + w))) := by
    simpa [i9A2v] using i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2v ha hw zero_le_one)
  have tz : Tendsto (i9A2z a w) (𝓝[<] 1) (𝓝 1) := by
    simpa [i9A2z, hb.ne'] using
      i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2z ha hw zero_le_one)
  have tr : Tendsto (i9A2r a w) (𝓝[<] 1) (𝓝 0) := by
    simpa [i9A2r] using i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2r a w 1)
  have tl : Tendsto (i9A2l a w) (𝓝[<] 1) (𝓝 K) := by
    simpa [i9A2l] using i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2l ha hw zero_le_one)
  have tm : Tendsto (i9A2m a w) (𝓝[<] 1) (𝓝 0) := by
    simpa [i9A2m, hb.ne'] using
      i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2m ha hw zero_le_one)
  have trp : Tendsto (i9A2r a w) (𝓝[<] 1) (𝓝[>] 0) := tendsto_i9A2_r_one hq0
  have tzm : Tendsto (i9A2z a w) (𝓝[<] 1) (𝓝[<] 1) :=
    tendsto_nhdsWithin_iff.2 ⟨tz, by
      filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with y hy
      exact (i9A2z_mem ha hw hy).2⟩
  have hvI := i9A2L_mem_Icc_one fun y hy => i9A2v_mem ha hw hy
  have hzI := i9A2L_mem_Icc_one fun y hy => i9A2z_mem ha hw hy
  have hrI := i9A2L_mem_Icc_one fun y hy => i9A2r_mem ha hw hy
  have tLv := tendsto_Li₂_comp hqm tv hvI
  have tTv := tendsto_Li₃_comp hqm tv hvI
  have tLz : Tendsto (fun y => Li₂ (i9A2z a w y)) (𝓝[<] 1) (𝓝 (π ^ 2 / 6)) := by
    simpa [Li₂_one] using tendsto_Li₂_comp (by norm_num) tz hzI
  have tTz : Tendsto (fun y => Li₃ (i9A2z a w y)) (𝓝[<] 1) (𝓝 zeta3) := by
    simpa [Li₃_one] using tendsto_Li₃_comp (by norm_num) tz hzI
  have tLr : Tendsto (fun y => Li₂ (i9A2r a w y)) (𝓝[<] 1) (𝓝 0) := by
    simpa using tendsto_Li₂_comp (by norm_num) tr hrI
  have tTr : Tendsto (fun y => Li₃ (i9A2r a w y)) (𝓝[<] 1) (𝓝 0) := by
    simpa using tendsto_Li₃_comp (by norm_num) tr hrI
  have tFv : Tendsto (fun y => logOneSubSqPrim (i9A2v a w y)) (𝓝[<] 1)
      (𝓝 (logOneSubSqPrim (w / (a + w)))) :=
    ((hasDerivAt_logOneSubSqPrim ⟨hq0, hq1⟩).continuousAt.tendsto).comp tv
  have tFz := tendsto_logOneSubSqPrim_one.comp tzm
  have tFr := tendsto_logOneSubSqPrim_zero.comp trp
  have tFy := tendsto_logOneSubSqPrim_one
  have tFs := tendsto_logOneSubSqPrim_zero.comp tendsto_one_sub_nhdsLT_one
  have tTs := tendsto_Li₃_zero_right.comp tendsto_one_sub_nhdsLT_one
  -- the singular products
  have bm := i9A2L_abs_m_le_one ha hw
  have bY := i9A2L_abs_log_le_one
  have b1 := i9A2L_eventually_mem_one
  have sY2Y1 : Tendsto (fun y => Real.log y ^ 2 * Real.log (1 - y)) (𝓝[<] 1) (𝓝 0) := by
    refine tendsto_mul_log_one_sub_of_abs_le (C := 2) ?_
    filter_upwards [bY, b1] with y h h1
    rw [abs_pow]
    nlinarith [abs_nonneg (Real.log y), h1.1, h1.2]
  have smY1 := i9A2L_tendsto_mul_log_one_sub_sq bm
  have sm2Y1 : Tendsto (fun y => i9A2m a w y ^ 2 * Real.log (1 - y)) (𝓝[<] 1) (𝓝 0) := by
    refine tendsto_mul_log_one_sub_of_abs_le (C := 2) ?_
    filter_upwards [bm, b1] with y h h1
    rw [abs_pow]
    nlinarith [abs_nonneg (i9A2m a w y), h1.1, h1.2]
  have sKmY1 : Tendsto (fun y => 2 * K * i9A2m a w y * Real.log (1 - y)) (𝓝[<] 1) (𝓝 0) := by
    refine tendsto_mul_log_one_sub_of_abs_le (C := 2 * |K| * 2) ?_
    filter_upwards [bm] with y h
    rw [abs_mul, abs_mul, abs_two, mul_assoc (2 * |K|) 2]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have sLrY1 := tendsto_mul_log_one_sub_of_abs_le (i9A2L_abs_Li₂_r_le ha hw)
  have smYY1 : Tendsto (fun y => i9A2m a w y * Real.log y * Real.log (1 - y)) (𝓝[<] 1)
      (𝓝 0) := by
    refine tendsto_mul_log_one_sub_of_abs_le (C := 2) ?_
    filter_upwards [bm, bY, b1] with y h h' h1
    rw [abs_mul]
    nlinarith [abs_nonneg (i9A2m a w y), abs_nonneg (Real.log y), h1.1, h1.2]
  have sLsY1 := tendsto_mul_log_one_sub_of_abs_le i9A2L_abs_Li₂_one_sub_le
  -- assembling
  have hA := (((((tY.mul tLv).add ((tY.mul (tl.pow 2)).div_const 2)).sub tTv).sub
    (tl.mul tLv)).add tFv).sub ((tl.pow 3).div_const 6) |>.add
    ((((((((((tFy.sub tFz).sub tFr).sub smY1).add sm2Y1).add sKmY1).sub
      (sLrY1.const_mul 2)).add (tTr.const_mul 2)).add (tLr.const_mul (2 * K))).div_const 2))
  have hB := ((((((((tFs.add tFr).sub ((sY2Y1.sub (smYY1.const_mul 2)).add sm2Y1)).sub
    (((tY.mul tLz).sub (tm.mul tLz)).const_mul 2)).add (tTz.const_mul 2)).add
    (((tY.mul tLv).sub (tm.mul tLv)).const_mul 2)).sub (tTv.const_mul 2)).neg.div_const 2).add
    sLrY1).sub tTr
  have hW := ((((sLsY1.neg.add ((tY.mul tendsto_Li₂_one_left).const_mul 2)).add tTs).sub
    (tendsto_Li₃_one_left.const_mul 2)).add sY2Y1)
  have h := ((hA.const_mul a).add (hB.const_mul (a + w))).add (hW.const_mul w)
  refine (h.congr' (Eventually.of_forall fun y => rfl)).trans (le_of_eq ?_)
  congr 1
  ring

/-! ### The integral -/

/-- **The log-weighted `y`-integral of `S₁ / (y (1 - y))`.** -/
theorem integral_i9A2YL_div {a w : ℝ} (ha : 0 < a) (hw : 0 < w)
    (hint : IntegrableOn (fun y => (Real.log y + Real.log (1 - y)) * i9A2S1 a w y /
      (y * (1 - y))) (Ioo 0 1)) :
    ∫ y in Ioo (0 : ℝ) 1, (Real.log y + Real.log (1 - y)) * i9A2S1 a w y / (y * (1 - y)) =
      i9A2YL a w := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun y hy => hasDerivAt_i9A2HL ha hw hy)
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hint)
    (tendsto_i9A2HL_zero ha hw) (tendsto_i9A2HL_one ha hw)
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hFTC
  rw [hFTC, i9A2YL]
  ring

end QED.ThreeLoopD
