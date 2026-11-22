/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9RemA1Kernel
public import QED.ThreeLoopD.SetDMastersI9RemA2L

/-!
# Set (d), master `I₉`: the `log b` moment of the kernel `k(s, p)`

In the variables `(p, s)` of `QED.ThreeLoopD.SetDMastersI9RemA1`, `P₁ = b = s (1 - s) / E` with
`E = s + p (1 - s)`, and the second Taylor coefficient of `Rem` carries a factor `log b`
against the kernel `k(s, p)` of `QED.ThreeLoopD.SetDMastersI9RemA1Kernel`. With `q = 1 - p`,

  `∫₀¹ k(s, p) log (s (1 - s) / E) ds = -2/q + (4 p Li₂ q + 2 p log p) / q²`.

Since `E ≥ s ≥ s (1 - s)`, the integrand is `≤ 0`, so it is integrable. The antiderivative is
the sum of three pieces: the `log s` piece (singular at `0`), the `log (1 - s)` piece
(singular at `1`) and the `log E` piece (smooth on `[0, 1]`), using
`k = (1 - 2p/E + p/E²)/q` and the dilogarithms `Li₂ (q s / E)`, `Li₂ (q (1 - s))`.

## Main results

* `QED.ThreeLoopD.intervalIntegrable_and_integral_i9A2kLogB`.
-/

@[expose] public section

open MeasureTheory Set Real Filter Topology QED.Polylog

namespace QED.ThreeLoopD

/-- `∫₀¹ k(s, p) log b ds = -2/q + (4 p Li₂ q + 2 p log p)/q²`. -/
noncomputable def i9A2Kb (p : ℝ) : ℝ :=
  -2 / (1 - p) + (4 * p * Li₂ (1 - p) + 2 * p * Real.log p) / (1 - p) ^ 2

/-- The `log s` piece of the antiderivative. -/
noncomputable def i9A2kbS (p s : ℝ) : ℝ :=
  (s * Real.log s - s - 2 * p / (1 - p) * (Real.log s * Real.log ((s + p * (1 - s)) / p) -
      Li₂ ((1 - p) * s / (s + p * (1 - s))) - Real.log ((s + p * (1 - s)) / p) ^ 2 / 2) +
    s * Real.log s / (s + p * (1 - s)) - Real.log (s + p * (1 - s)) / (1 - p)) / (1 - p)

/-- The `log (1 - s)` piece of the antiderivative. -/
noncomputable def i9A2kb1 (p s : ℝ) : ℝ :=
  (-((1 - s) * Real.log (1 - s)) - s - 2 * p / (1 - p) *
      (Real.log (s + p * (1 - s)) * Real.log (1 - s) + Li₂ ((1 - p) * (1 - s))) +
    p * (-((1 - s) * Real.log (1 - s)) / (s + p * (1 - s)) -
      Real.log (s + p * (1 - s)) / (1 - p))) / (1 - p)

/-- The `log E` piece of the antiderivative. -/
noncomputable def i9A2kbE (p s : ℝ) : ℝ :=
  ((s + p * (1 - s)) * Real.log (s + p * (1 - s)) - (s + p * (1 - s)) -
      p * Real.log (s + p * (1 - s)) ^ 2 -
      p * (Real.log (s + p * (1 - s)) + 1) / (s + p * (1 - s))) / (1 - p) ^ 2

/-! ### Derivatives -/

section Deriv

variable {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
include hp

theorem i9A2kb_E_pos' {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 < s + p * (1 - s) :=
  i9A1_E_pos hp ⟨hs0, hs1⟩

omit hp in
theorem hasDerivAt_i9A2kb_E (s : ℝ) :
    HasDerivAt (fun s => s + p * (1 - s)) (1 - p) s := by
  have := (hasDerivAt_id' s).add (((hasDerivAt_id' s).const_sub 1).const_mul p)
  convert this using 1; ring

theorem hasDerivAt_i9A2kbS {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    HasDerivAt (i9A2kbS p) ((1 - 2 * p / (s + p * (1 - s)) + p / (s + p * (1 - s)) ^ 2) /
      (1 - p) * Real.log s) s := by
  have hE := i9A2kb_E_pos' hp hs0.le hs1
  have hq : 0 < 1 - p := by linarith [hp.2]
  have hp0 := hp.1
  have hEd := hasDerivAt_i9A2kb_E (p := p) s
  have hY := Real.hasDerivAt_log hs0.ne'
  have hsl := (hasDerivAt_id' s).mul hY
  have hEp : HasDerivAt (fun s => (s + p * (1 - s)) / p) ((1 - p) / p) s := hEd.div_const p
  have hlEp := hEp.log (div_pos hE hp0).ne'
  have hlE := hEd.log hE.ne'
  have hζ : HasDerivAt (fun s => (1 - p) * s / (s + p * (1 - s)))
      ((1 - p) * p / (s + p * (1 - s)) ^ 2) s := by
    have h1 : HasDerivAt (fun s => (1 - p) * s) (1 - p) s := by
      simpa using (hasDerivAt_id' s).const_mul (1 - p)
    convert h1.div hEd hE.ne' using 1
    field_simp
    ring
  have hζm : (fun s => (1 - p) * s / (s + p * (1 - s))) s ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by simp only; positivity, ?_⟩
    simp only
    rw [div_lt_one hE]; nlinarith
  have hL := i9A2L_hasDerivAt_Li₂ hζ hζm
  have h := ((((hsl.sub (hasDerivAt_id' s)).sub (((hY.mul hlEp).sub hL).sub
    ((hlEp.pow 2).div_const 2) |>.const_mul (2 * p / (1 - p)))).add (hsl.div hEd hE.ne')).sub
    (hlE.div_const (1 - p))).div_const (1 - p)
  convert h using 1
  · funext t
    simp only [i9A2kbS, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  simp only [Pi.mul_apply]
  have e1 : 1 - (1 - p) * s / (s + p * (1 - s)) = p / (s + p * (1 - s)) := by
    field_simp; ring
  simp only [e1]
  rw [Real.log_div hp0.ne' hE.ne', Real.log_div hE.ne' hp0.ne']
  generalize Li₂ ((1 - p) * s / (s + p * (1 - s))) = L
  generalize Real.log (s + p * (1 - s)) = lE
  generalize Real.log s = Y
  generalize Real.log p = lp
  field_simp
  ring

theorem hasDerivAt_i9A2kb1 {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasDerivAt (i9A2kb1 p) ((1 - 2 * p / (s + p * (1 - s)) + p / (s + p * (1 - s)) ^ 2) /
      (1 - p) * Real.log (1 - s)) s := by
  have hE := i9A2kb_E_pos' hp hs0 hs1.le
  have hq : 0 < 1 - p := by linarith [hp.2]
  have hs1' : 0 < 1 - s := by linarith
  have hEd := hasDerivAt_i9A2kb_E (p := p) s
  have hd : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
    simpa using (hasDerivAt_id' s).const_sub 1
  have hY1 := hd.log hs1'.ne'
  have hsl := hd.mul hY1
  have hlE := hEd.log hE.ne'
  have hr : HasDerivAt (fun s => (1 - p) * (1 - s)) (-(1 - p)) s := by
    simpa using hd.const_mul (1 - p)
  have hrm : (fun s => (1 - p) * (1 - s)) s ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by simp only; positivity, ?_⟩
    simp only; nlinarith [hp.1]
  have hL := i9A2L_hasDerivAt_Li₂ hr hrm
  have h := ((((hsl.neg.sub (hasDerivAt_id' s)).sub ((hlE.mul hY1).add hL |>.const_mul
    (2 * p / (1 - p)))).add ((hsl.neg.div hEd hE.ne').sub (hlE.div_const (1 - p)) |>.const_mul
    p))).div_const (1 - p)
  convert h using 1
  · funext t
    simp only [i9A2kb1, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]
  simp only [Pi.mul_apply, Pi.neg_apply]
  have e1 : 1 - (1 - p) * (1 - s) = s + p * (1 - s) := by ring
  simp only [e1]
  generalize Li₂ ((1 - p) * (1 - s)) = L
  generalize Real.log (s + p * (1 - s)) = lE
  generalize Real.log (1 - s) = Y1
  field_simp
  ring

theorem hasDerivAt_i9A2kbE {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasDerivAt (i9A2kbE p) ((1 - 2 * p / (s + p * (1 - s)) + p / (s + p * (1 - s)) ^ 2) /
      (1 - p) * Real.log (s + p * (1 - s))) s := by
  have hE := i9A2kb_E_pos' hp hs0 hs1
  have hq : 0 < 1 - p := by linarith [hp.2]
  have hEd := hasDerivAt_i9A2kb_E (p := p) s
  have hlE := hEd.log hE.ne'
  have h := ((((hEd.mul hlE).sub hEd).sub ((hlE.pow 2).const_mul p)).sub
    (((hlE.add_const 1).const_mul p).div hEd hE.ne')).div_const ((1 - p) ^ 2)
  convert h using 1
  · funext t
    simp only [i9A2kbE, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
  generalize Real.log (s + p * (1 - s)) = lE
  field_simp
  ring

end Deriv

/-! ### The moment -/

/-- The antiderivative of `k(s, p) log b`. -/
noncomputable def i9A2kbPrim (p s : ℝ) : ℝ := i9A2kbS p s + i9A2kb1 p s - i9A2kbE p s

theorem i9A1k_eq {p s : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    i9A1k s p = (1 - 2 * p / (s + p * (1 - s)) + p / (s + p * (1 - s)) ^ 2) / (1 - p) := by
  have hE := i9A1_E_pos hp ⟨hs0, hs1⟩
  have hq : 0 < 1 - p := by linarith [hp.2]
  unfold i9A1k
  field_simp
  ring

theorem hasDerivAt_i9A2kbPrim {p s : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (i9A2kbPrim p)
      (i9A1k s p * Real.log (s * (1 - s) / (s + p * (1 - s)))) s := by
  have hE := i9A1_E_pos hp ⟨hs.1.le, hs.2.le⟩
  have h := ((hasDerivAt_i9A2kbS hp hs.1 hs.2.le).add (hasDerivAt_i9A2kb1 hp hs.1.le hs.2)).sub
    (hasDerivAt_i9A2kbE hp hs.1.le hs.2.le)
  refine h.congr_deriv ?_
  rw [i9A1k_eq hp hs.1.le hs.2.le, Real.log_div (by nlinarith [hs.1, hs.2]) hE.ne',
    Real.log_mul hs.1.ne' (by linarith [hs.2])]
  ring

theorem i9A2kbS_tendsto_zero {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i9A2kbS p) (𝓝[>] 0) (𝓝 (-Real.log p / (1 - p) ^ 2)) := by
  have hp0 := hp.1
  have hq : 0 < 1 - p := by linarith [hp.2]
  have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have tE : Tendsto (fun s => s + p * (1 - s)) (𝓝[>] 0) (𝓝 p) := by
    simpa using i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2kb_E (p := p) 0)
  have tlE : Tendsto (fun s => Real.log (s + p * (1 - s))) (𝓝[>] 0) (𝓝 (Real.log p)) :=
    tE.log hp0.ne'
  have tlEp : Tendsto (fun s => Real.log ((s + p * (1 - s)) / p)) (𝓝[>] 0) (𝓝 0) := by
    have := (tE.div_const p).log (by simp [hp0.ne'] : p / p ≠ 0)
    simpa [hp0.ne'] using this
  have tζ : Tendsto (fun s => (1 - p) * s / (s + p * (1 - s))) (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)).const_mul
      (1 - p)).div tE hp0.ne'
    simp only [id, mul_zero, zero_div] at this
    exact this
  have tL : Tendsto (fun s => Li₂ ((1 - p) * s / (s + p * (1 - s)))) (𝓝[>] 0) (𝓝 0) := by
    refine (tendsto_Li₂_comp (by norm_num) tζ ?_).trans (by rw [Li₂_zero])
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
    have hE := i9A1_E_pos hp ⟨hs.1.le, hs.2.le⟩
    refine ⟨by have := hs.1; nlinarith [div_nonneg (by positivity : 0 ≤ (1 - p) * s) hE.le],
      ?_⟩
    rw [div_le_one hE]; nlinarith [hs.1]
  have tsl := tendsto_mul_log_zero
  have ts : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
  have sYl : Tendsto (fun s => Real.log s * Real.log ((s + p * (1 - s)) / p)) (𝓝[>] 0)
      (𝓝 0) := by
    refine i9A2L_tendsto_log_mul (C := (1 - p) / p) ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
    have hE := i9A1_E_pos hp ⟨hs.1.le, hs.2.le⟩
    have e : (s + p * (1 - s)) / p = 1 + (1 - p) / p * s := by field_simp; ring
    rw [e]
    have := abs_log_one_add_le (by have := hs.1; positivity : 0 ≤ (1 - p) / p * s)
    linarith
  have h := (((((tsl.sub ts).sub ((sYl.sub tL).sub ((tlEp.pow 2).div_const 2) |>.const_mul
    (2 * p / (1 - p)))).add (tsl.div tE hp0.ne')).sub (tlE.div_const (1 - p))).div_const (1 - p))
  refine (h.congr' (Eventually.of_forall fun s => rfl)).trans (le_of_eq ?_)
  congr 1
  field_simp
  ring

theorem i9A2kb1_tendsto_one {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    Tendsto (i9A2kb1 p) (𝓝[<] 1) (𝓝 (-1 / (1 - p))) := by
  have hp0 := hp.1
  have hq : 0 < 1 - p := by linarith [hp.2]
  have hle : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have tE : Tendsto (fun s => s + p * (1 - s)) (𝓝[<] 1) (𝓝 1) := by
    simpa using i9A2L_tendsto_of_hasDerivAt hle (hasDerivAt_i9A2kb_E (p := p) 1)
  have tlE : Tendsto (fun s => Real.log (s + p * (1 - s))) (𝓝[<] 1) (𝓝 0) := by
    simpa using tE.log one_ne_zero
  have tr : Tendsto (fun s => (1 - p) * (1 - s)) (𝓝[<] 1) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => (1 - p) * (1 - s)) (𝓝 1) (𝓝 ((1 - p) * (1 - 1))) :=
      (continuous_const.mul (continuous_const.sub continuous_id)).tendsto 1
    simpa using this.mono_left hle
  have tL : Tendsto (fun s => Li₂ ((1 - p) * (1 - s))) (𝓝[<] 1) (𝓝 0) := by
    refine (tendsto_Li₂_comp (by norm_num) tr ?_).trans (by rw [Li₂_zero])
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with s hs
    exact ⟨by nlinarith [hs.2], by nlinarith [hs.1, hs.2]⟩
  have tsl : Tendsto (fun s : ℝ => (1 - s) * Real.log (1 - s)) (𝓝[<] 1) (𝓝 0) :=
    tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one
  have ts : Tendsto (fun s : ℝ => s) (𝓝[<] 1) (𝓝 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 1)
  have sEY1 : Tendsto (fun s => Real.log (s + p * (1 - s)) * Real.log (1 - s)) (𝓝[<] 1)
      (𝓝 0) := by
    refine tendsto_mul_log_one_sub_of_abs_le (C := 2) ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with s hs
    have e : s + p * (1 - s) = 1 - (1 - p) * (1 - s) := by ring
    rw [e]
    have := abs_log_one_sub_le (x := (1 - p) * (1 - s)) (by nlinarith [hs.2])
      (by nlinarith [hs.1, hs.2, hp.1])
    nlinarith [hs.2, hp.1]
  have h := ((((tsl.neg.sub ts).sub (sEY1.add tL |>.const_mul (2 * p / (1 - p)))).add
    ((tsl.neg.div tE one_ne_zero).sub (tlE.div_const (1 - p)) |>.const_mul p))).div_const
    (1 - p)
  refine (h.congr' (Eventually.of_forall fun s => rfl)).trans (le_of_eq ?_)
  congr 1
  ring

/-- **The `log b` moment of `k`**: `∫₀¹ k(s, p) log (s (1 - s)/E) ds = i9A2Kb p`. -/
theorem intervalIntegrable_and_integral_i9A2kLogB {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun s => i9A1k s p * Real.log (s * (1 - s) / (s + p * (1 - s))))
        volume 0 1 ∧
      ∫ s in (0 : ℝ)..1, i9A1k s p * Real.log (s * (1 - s) / (s + p * (1 - s))) =
        i9A2Kb p := by
  have hp0 := hp.1
  have hq : 0 < 1 - p := by linarith [hp.2]
  have hle0 : 𝓝[>] (0 : ℝ) ≤ 𝓝 0 := nhdsWithin_le_nhds
  have hle1 : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have h0 := ((i9A2kbS_tendsto_zero hp).add (i9A2L_tendsto_of_hasDerivAt hle0
    (hasDerivAt_i9A2kb1 hp le_rfl zero_lt_one))).sub
    (i9A2L_tendsto_of_hasDerivAt hle0 (hasDerivAt_i9A2kbE hp le_rfl zero_le_one))
  have h1 := ((i9A2L_tendsto_of_hasDerivAt hle1 (hasDerivAt_i9A2kbS hp zero_lt_one le_rfl)).add
    (i9A2kb1_tendsto_one hp)).sub
    (i9A2L_tendsto_of_hasDerivAt hle1 (hasDerivAt_i9A2kbE hp zero_le_one le_rfl))
  obtain ⟨hi, hv⟩ := intervalIntegrable_and_integral_eq_of_nonpos (F := i9A2kbPrim p)
    (fun s hs => hasDerivAt_i9A2kbPrim hp hs) (fun s hs => by
      have hE := i9A1_E_pos hp ⟨hs.1.le, hs.2.le⟩
      refine mul_nonpos_of_nonneg_of_nonpos (i9A1k_nonneg hp) (Real.log_nonpos
        (div_nonneg (mul_nonneg hs.1.le (by linarith [hs.2])) hE.le) ?_)
      rw [div_le_one hE]; nlinarith [hs.1, hs.2])
    h0 h1
  refine ⟨hi, hv.trans ?_⟩
  simp only [i9A2kbS, i9A2kb1, i9A2kbE, i9A2Kb]
  norm_num
  field_simp
  ring

end QED.ThreeLoopD
