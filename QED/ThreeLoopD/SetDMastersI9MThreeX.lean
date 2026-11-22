/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.Basic
public import QED.Polylog.HPLBasic
public import QED.Polylog.LiN
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import QED.ThreeLoopD.SetDMastersI9MInner
import QED.Polylog.ExtraIntegrals
import QED.Polylog.LiCalculus
import QED.Polylog.HPLCalculus
import QED.Polylog.HPLLowWeight
import QED.Polylog.DilogPM
import QED.Polylog.AlphabetPM
import QED.Polylog.Reflection

/-!
# Set (d), master `I₉`: five weight-three `x`-integrals behind `M₃`

Fix `w ∈ (0, 1)` and write `u = 1 - w`, `A = w + u x`, `B = 1 - u x`. The Taylor coefficient
`M₃` of `QED.ThreeLoopD.i9M` reduces, by integration by parts in `x`, to weight-two integrals and
nine sign-definite weight-three pieces. This file evaluates five of them,

  `P₁ = ∫₀¹ u log² A / B`, `P₃ = ∫₀¹ log² A / (1 - x)`, `P₅ = ∫₀¹ log A log (1 - x) / (1 - x)`,
  `R₁ = ∫₀¹ u log A log x / A`, `R₃ = ∫₀¹ u log² x / A`,

each by an explicit antiderivative with one-sided limits at `0` and `1`
(`QED.Polylog.intervalIntegrable_and_integral_eq_of_nonneg`). The polylogarithmic values

  `P₁ = 2 Li₃ (1/(1+w)) - 2 Li₃ (w/(1+w)) - log (1+w) log² w + 2 log w Li₂ (w/(1+w))`,
  `P₃ = 2ζ(3) - 2 Li₃ w + log u log² w + 2 log w Li₂ w`, `P₅ = Li₃ u`,
  `R₁ = Li₃ w - log³ w/3 - ζ(2) log w + log u log² w/2 - ζ(3)`,
  `R₃ = 2 Li₃ w + 2 Li₃ u - 2ζ(3) - log³ w/3 + log u log² w - 2ζ(2) log w`

are then rewritten as harmonic polylogarithms `H(·; w)` over the letters `0, 1, -1`. The one new
conversion is `Li₃ (w/(1+w)) = H(0,0,-1) - H(0,-1,-1) - H(-1,0,-1) + H(-1,-1,-1)`, proved by
differentiation (`QED.ThreeLoopD.i9M3X_hpl_zero_negOne_negOne`).
For `R₃` the antiderivative is taken after Euler's reflection, so that both limits exist termwise.

## Main results

* `QED.ThreeLoopD.i9M3X_Li₃_div_one_add`: `Li₃ (w/(1+w))` in harmonic polylogarithms.
* `QED.ThreeLoopD.i9M3X_P1`, `QED.ThreeLoopD.i9M3X_P3`, `QED.ThreeLoopD.i9M3X_P5`,
  `QED.ThreeLoopD.i9M3X_R1`, `QED.ThreeLoopD.i9M3X_R3`: integrability and the value of each
  piece in harmonic polylogarithms (the `_Li` versions give the polylogarithmic values).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-! ### `Li₃ (w/(1+w))` in harmonic polylogarithms -/

/-- `H(0, -1, -1; x)` through `Li₃ (x/(1+x))` and `Li₃ (-x)`. -/
theorem i9M3X_hpl_zero_negOne_negOne {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [zero, negOne, negOne] x = Li 3 (x / (1 + x)) + Li 3 (-x) -
      Real.log (1 + x) * Li 2 (-x) - Real.log (1 + x) ^ 3 / 6 := by
  refine eq_hpl_cons_of_hasDerivAt (a := zero) (w := [negOne, negOne]) (by simp)
    (F := fun y => Li 3 (y / (1 + y)) + Li 3 (-y) - Real.log (1 + y) * Li 2 (-y) -
      Real.log (1 + y) ^ 3 / 6) (fun y hy => ?_) ?_ x hx
  · obtain ⟨hf, h1, h0, hd, -, -⟩ := PM.data_divOneAdd hy.1 hy.2
    obtain ⟨gf, g1, g0, gd, -, gl1⟩ := PM.data_neg hy.1 hy.2
    have h3 := hasDerivAt_Li_three_of hf h1 h0 hd (Li_two_div_one_add hy)
    have g3 := hasDerivAt_Li_three_of gf g1 g0 gd rfl
    have g2 := hasDerivAt_Li_two_of gf g1 g0 gd gl1
    have h1y : (1 : ℝ) + y ≠ 0 := by linarith [hy.1]
    have hl := ((hasDerivAt_id y).const_add 1).log h1y
    refine (((h3.add g3).sub (hl.mul g2)).sub ((hl.pow 3).div_const 6)).congr_deriv ?_
    rw [kernel_zero, hpl_negOne_negOne hy]
    simp only [id]
    have hy0 : y ≠ 0 := hy.1.ne'
    field_simp
    ring
  · have hm1 : ∀ y ∈ Ioo (0 : ℝ) 1, y / (1 + y) ∈ Icc (-1 : ℝ) 1 := fun y hy =>
      ⟨by have : 0 < y / (1 + y) := by have := hy.1; positivity
          linarith,
        by rw [div_le_one (by linarith [hy.1])]; linarith [hy.1]⟩
    have hm2 : ∀ y ∈ Ioo (0 : ℝ) 1, -y ∈ Icc (-1 : ℝ) 1 :=
      fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hc : ContinuousAt (fun y : ℝ => y / (1 + y)) 0 := by fun_prop (disch := norm_num)
    have t3 := tendsto_Li_comp_zero (k := 3) (g := fun y => y / (1 + y)) (by norm_num) hc
      (by norm_num) hm1
    have s3 := tendsto_Li_comp_zero (k := 3) (g := fun y => -y) (by norm_num) continuousAt_neg
      (by norm_num) hm2
    have s2 := tendsto_Li_comp_zero (k := 2) (g := fun y => -y) le_rfl continuousAt_neg
      (by norm_num) hm2
    have tl := tendsto_nhdsGT_of_continuousAt (F := fun y => Real.log (1 + y))
      (c := 0) (by fun_prop (disch := norm_num)) (by simp)
    have h := ((t3.add s3).sub (tl.mul s2)).sub ((tl.pow 3).div_const 6)
    simpa using h

/-- **`Li₃ (w/(1+w))` in harmonic polylogarithms**:
`Li₃ (w/(1+w)) = H(0,0,-1) - H(0,-1,-1) - H(-1,0,-1) + H(-1,-1,-1)` on `(0, 1)`. -/
theorem i9M3X_Li₃_div_one_add {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    Li₃ (w / (1 + w)) = hpl [zero, zero, negOne] w - hpl [zero, negOne, negOne] w -
      hpl [negOne, zero, negOne] w + hpl [negOne, negOne, negOne] w := by
  rw [hpl_negOne_zero_negOne hw, hpl_zero_zero_negOne hw, hpl_negOne_negOne_negOne hw,
    i9M3X_hpl_zero_negOne_negOne hw]
  simp only [Li_two, Li_three]
  ring

/-! ### `P₃ = ∫₀¹ log² A / (1 - x)` -/

/-- The antiderivative of `log² A / (1 - x)`. -/
noncomputable def i9M3XFP3 (w x : ℝ) : ℝ :=
  2 * Li₃ (w + (1 - w) * x) - Real.log (1 - w) * Real.log (w + (1 - w) * x) ^ 2 -
    Real.log (1 - x) * Real.log (w + (1 - w) * x) ^ 2 -
    2 * Real.log (w + (1 - w) * x) * Li₂ (w + (1 - w) * x)

/-- `A ∈ [-1, 1]` for `x ∈ [0, 1]`. -/
theorem i9M3X_A_mem {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    w + (1 - w) * x ∈ Icc (-1 : ℝ) 1 :=
  ⟨by linarith [i9M2_A_pos hw hx.1], i9M2_A_le hw hx.2⟩

/-- `A` tends to its value at a point of `[0, 1]` along any punctured side. -/
theorem i9M3X_tendsto_A (w : ℝ) {a : ℝ} {s : Set ℝ} :
    Tendsto (fun x => w + (1 - w) * x) (𝓝[s] a) (𝓝 (w + (1 - w) * a)) :=
  i9M2_tendsto_of_continuousAt (f := fun x => w + (1 - w) * x) (by fun_prop)

/-- `log A` tends to its value at a point of `[0, 1]` along any punctured side. -/
theorem i9M3X_tendsto_logA {w a : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (ha : 0 ≤ a) {s : Set ℝ} :
    Tendsto (fun x => Real.log (w + (1 - w) * x)) (𝓝[s] a)
      (𝓝 (Real.log (w + (1 - w) * a))) :=
  i9M2_tendsto_of_continuousAt (f := fun x => Real.log (w + (1 - w) * x))
    ((by fun_prop : ContinuousAt (fun x : ℝ => w + (1 - w) * x) a).log
      (i9M2_A_pos hw ha).ne')

/-- `log (1 - x) log A → 0` as `x → 1⁻`. -/
theorem i9M3X_tendsto_logOneSub_mul_logA {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x => Real.log (1 - x) * Real.log (w + (1 - w) * x)) (𝓝[<] 1) (𝓝 0) := by
  have h := (i9M2_tendsto_log_mul_log_one_sub (t := 1 - w) (by linarith [hw.2])
    (by linarith [hw.1])).comp tendsto_one_sub_nhdsLT_one
  refine h.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [show 1 - (1 - w) * (1 - x) = w + (1 - w) * x by ring]

/-- `P₃` with its polylogarithmic value. -/
theorem i9M3X_P3_Li {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) ^ 2 / (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) ^ 2 / (1 - x) =
        2 * zeta3 - 2 * Li₃ w + Real.log (1 - w) * Real.log w ^ 2 +
          2 * Real.log w * Li₂ w := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (i9M3XFP3 w)
      (Real.log (w + (1 - w) * x) ^ 2 / (1 - x)) x := by
    intro x hx
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
    have hA1 : w + (1 - w) * x < 1 := by nlinarith [hx.2]
    have h1 := i9M2_hasDerivAt_A w x
    have hlA := h1.log hAx.ne'
    have h2 := (hasDerivAt_Li₂' ⟨hAx, hA1⟩).comp x h1
    have h3 := (hasDerivAt_Li₃' ⟨hAx, hA1⟩).comp x h1
    have hq := hasDerivAt_log_one_sub hx.2
    refine ((((h3.const_mul 2).sub ((hlA.pow 2).const_mul (Real.log (1 - w)))).sub
      (hq.mul (hlA.pow 2))).sub ((hlA.const_mul 2).mul h2)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.pow_apply]
    have h1x : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    rw [show 1 - (w + (1 - w) * x) = (1 - w) * (1 - x) by ring,
      Real.log_mul hu.ne' h1x]
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ Real.log (w + (1 - w) * x) ^ 2 / (1 - x) := fun x hx =>
    div_nonneg (sq_nonneg _) (by linarith [hx.2])
  -- limits at `0⁺`
  have h0 : ∀ᶠ x in 𝓝[>] (0 : ℝ), w + (1 - w) * x ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx using
      i9M3X_A_mem hw ⟨hx.1.le, hx.2.le⟩
  have hm0 := i9M3X_A_mem hw (x := 0) ⟨le_rfl, zero_le_one⟩
  have hlA0 := i9M3X_tendsto_logA hw le_rfl (s := Ioi 0)
  have hA := (((((tendsto_Li₃_comp hm0 (i9M3X_tendsto_A w) h0).const_mul 2).sub
    ((hlA0.pow 2).const_mul (Real.log (1 - w)))).sub (tendsto_log_one_sub_zero.mul
    (hlA0.pow 2))).sub ((hlA0.const_mul 2).mul (tendsto_Li₂_comp hm0 (i9M3X_tendsto_A w) h0)))
  -- limits at `1⁻`
  have h1 : ∀ᶠ x in 𝓝[<] (1 : ℝ), w + (1 - w) * x ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx using
      i9M3X_A_mem hw ⟨hx.1.le, hx.2.le⟩
  have hm1 := i9M3X_A_mem hw (x := 1) ⟨zero_le_one, le_rfl⟩
  have hlA1 := i9M3X_tendsto_logA hw zero_le_one (s := Iio 1)
  have hB := (((((tendsto_Li₃_comp hm1 (i9M3X_tendsto_A w) h1).const_mul 2).sub
    ((hlA1.pow 2).const_mul (Real.log (1 - w)))).sub
    ((i9M3X_tendsto_logOneSub_mul_logA hw).mul hlA1)).sub
    ((hlA1.const_mul 2).mul (tendsto_Li₂_comp hm1 (i9M3X_tendsto_A w) h1)))
  have hB' : Tendsto (i9M3XFP3 w) (𝓝[<] 1) (𝓝 (2 * zeta3)) := by
    simp only [mul_one, add_sub_cancel, Li₃_one, Real.log_one, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, sub_zero, zero_mul] at hB
    refine hB.congr fun x => ?_
    unfold i9M3XFP3
    ring
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hf hA hB'
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [mul_zero, add_zero, sub_zero, zero_mul]
  ring

/-- **`P₃`**: `∫₀¹ log² A / (1 - x) = 2ζ(3) - 2H(0,0,1) + 2 log w H(0,1) - log² w H(1)`
(all `H` at `w`). -/
theorem i9M3X_P3 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) ^ 2 / (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) ^ 2 / (1 - x) =
        2 * zeta3 - 2 * hpl [zero, zero, one] w + 2 * Real.log w * hpl [zero, one] w -
          Real.log w ^ 2 * hpl [one] w := by
  refine ⟨(i9M3X_P3_Li hw).1, (i9M3X_P3_Li hw).2.trans ?_⟩
  rw [hpl_zero_zero_one hw, hpl_zero_one hw, hpl_one hw]
  simp only [Li_two, Li_three]
  ring

/-! ### `P₁ = ∫₀¹ (1 - w) log² A / B` -/

/-- The antiderivative of `(1 - w) log² A / B`. -/
noncomputable def i9M3XFP1 (w x : ℝ) : ℝ :=
  2 * Li₃ ((w + (1 - w) * x) / (1 + w)) +
    Real.log (1 + w) * Real.log (w + (1 - w) * x) ^ 2 -
    Real.log (w + (1 - w) * x) ^ 2 * Real.log (1 - (1 - w) * x) -
    2 * Real.log (w + (1 - w) * x) * Li₂ ((w + (1 - w) * x) / (1 + w))

/-- `A/(1 + w) ∈ (0, 1)` for `x ∈ [0, 1]`. -/
theorem i9M3X_A_div_mem {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    (w + (1 - w) * x) / (1 + w) ∈ Ioo (0 : ℝ) 1 :=
  ⟨div_pos (i9M2_A_pos hw hx.1) (by linarith [hw.1]),
    by rw [div_lt_one (by linarith [hw.1])]; linarith [i9M2_A_le hw hx.2, hw.1]⟩

/-- `P₁` with its polylogarithmic value. -/
theorem i9M3X_P1_Li {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (1 - w) * Real.log (w + (1 - w) * x) ^ 2 /
        (1 - (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * Real.log (w + (1 - w) * x) ^ 2 / (1 - (1 - w) * x) =
        2 * Li₃ (1 / (1 + w)) - 2 * Li₃ (w / (1 + w)) - Real.log (1 + w) * Real.log w ^ 2 +
          2 * Real.log w * Li₂ (w / (1 + w)) := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hp : 0 < 1 + w := by linarith
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (i9M3XFP1 w)
      ((1 - w) * Real.log (w + (1 - w) * x) ^ 2 / (1 - (1 - w) * x)) x := by
    intro x hx
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
    have hBx : 0 < 1 - (1 - w) * x := i9M2_B_pos hw hx.2.le
    have hz := i9M3X_A_div_mem hw ⟨hx.1.le, hx.2.le⟩
    have h1 := i9M2_hasDerivAt_A w x
    have hlA := h1.log hAx.ne'
    have hlB := (i9M2_hasDerivAt_B w x).log hBx.ne'
    have hzd := h1.div_const (1 + w)
    have h2 := (hasDerivAt_Li₂' hz).comp x hzd
    have h3 := (hasDerivAt_Li₃' hz).comp x hzd
    refine ((((h3.const_mul 2).add ((hlA.pow 2).const_mul (Real.log (1 + w)))).sub
      ((hlA.pow 2).mul hlB)).sub ((hlA.const_mul 2).mul h2)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.pow_apply]
    rw [show 1 - (w + (1 - w) * x) / (1 + w) = (1 - (1 - w) * x) / (1 + w) by
      field_simp; ring, Real.log_div hBx.ne' hp.ne']
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1,
      0 ≤ (1 - w) * Real.log (w + (1 - w) * x) ^ 2 / (1 - (1 - w) * x) := fun x hx =>
    div_nonneg (mul_nonneg hu.le (sq_nonneg _)) (i9M2_B_pos hw hx.2.le).le
  have hzI : ∀ x ∈ Icc (0 : ℝ) 1, (w + (1 - w) * x) / (1 + w) ∈ Icc (-1 : ℝ) 1 :=
    fun x hx => ⟨by linarith [(i9M3X_A_div_mem hw hx).1], (i9M3X_A_div_mem hw hx).2.le⟩
  have hzt : ∀ (a : ℝ) (s : Set ℝ), Tendsto (fun x => (w + (1 - w) * x) / (1 + w)) (𝓝[s] a)
      (𝓝 ((w + (1 - w) * a) / (1 + w))) := fun a s => (i9M3X_tendsto_A w).div_const _
  have hlB : ∀ (a : ℝ) (s : Set ℝ), a ≤ 1 → Tendsto (fun x => Real.log (1 - (1 - w) * x))
      (𝓝[s] a) (𝓝 (Real.log (1 - (1 - w) * a))) := fun a s ha =>
    i9M2_tendsto_of_continuousAt (f := fun x => Real.log (1 - (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => 1 - (1 - w) * x) a).log
        (i9M2_B_pos hw ha).ne')
  -- limits at `0⁺`
  have h0 : ∀ᶠ x in 𝓝[>] (0 : ℝ), (w + (1 - w) * x) / (1 + w) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx using
      hzI x ⟨hx.1.le, hx.2.le⟩
  have hm0 := hzI 0 ⟨le_rfl, zero_le_one⟩
  have hlA0 := i9M3X_tendsto_logA hw le_rfl (s := Ioi 0)
  have hA := ((((tendsto_Li₃_comp hm0 (hzt 0 _) h0).const_mul 2).add
    ((hlA0.pow 2).const_mul (Real.log (1 + w)))).sub ((hlA0.pow 2).mul
    (hlB 0 (Ioi 0) zero_le_one))).sub ((hlA0.const_mul 2).mul
    (tendsto_Li₂_comp hm0 (hzt 0 _) h0))
  -- limits at `1⁻`
  have h1 : ∀ᶠ x in 𝓝[<] (1 : ℝ), (w + (1 - w) * x) / (1 + w) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx using
      hzI x ⟨hx.1.le, hx.2.le⟩
  have hm1 := hzI 1 ⟨zero_le_one, le_rfl⟩
  have hlA1 := i9M3X_tendsto_logA hw zero_le_one (s := Iio 1)
  have hB := ((((tendsto_Li₃_comp hm1 (hzt 1 _) h1).const_mul 2).add
    ((hlA1.pow 2).const_mul (Real.log (1 + w)))).sub ((hlA1.pow 2).mul
    (hlB 1 (Iio 1) le_rfl))).sub ((hlA1.const_mul 2).mul
    (tendsto_Li₂_comp hm1 (hzt 1 _) h1))
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hf hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [mul_one, mul_zero, add_zero, sub_zero, add_sub_cancel, sub_sub_cancel,
    Real.log_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
  ring

/-- **`P₁`**: `∫₀¹ (1 - w) log² A / B = 2ζ(3) - 2ζ(2) H(-1) - 2H(0,0,-1) + 4H(0,-1,-1)
+ 4H(-1,0,-1) + 2 log w H(0,-1) - 4 log w H(-1,-1) - log² w H(-1)` (all `H` at `w`). -/
theorem i9M3X_P1 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (1 - w) * Real.log (w + (1 - w) * x) ^ 2 /
        (1 - (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * Real.log (w + (1 - w) * x) ^ 2 / (1 - (1 - w) * x) =
        2 * zeta3 - 2 * (π ^ 2 / 6) * hpl [negOne] w - 2 * hpl [zero, zero, negOne] w +
          4 * hpl [zero, negOne, negOne] w + 4 * hpl [negOne, zero, negOne] w +
          2 * Real.log w * hpl [zero, negOne] w - 4 * Real.log w * hpl [negOne, negOne] w -
          Real.log w ^ 2 * hpl [negOne] w := by
  refine ⟨(i9M3X_P1_Li hw).1, (i9M3X_P1_Li hw).2.trans ?_⟩
  have hE := hpl_zero_negOne_negOne hw
  have hE2 := i9M3X_hpl_zero_negOne_negOne hw
  have hL1 := Li_two_div_one_add hw
  have hL2 := Li_two_inv_one_add hw
  rw [hpl_negOne_zero_negOne hw, hpl_zero_zero_negOne hw, hpl_zero_negOne hw,
    hpl_negOne_negOne hw, hpl_negOne hw]
  simp only [Li_two, Li_three] at hE hE2 hL1 hL2 ⊢
  rw [hL1]
  rw [hL2] at hE
  linear_combination 2 * hE + 2 * hE2

/-! ### `P₅ = ∫₀¹ log A log (1 - x) / (1 - x)` -/

/-- The antiderivative of `log A log (1 - x) / (1 - x)`. -/
noncomputable def i9M3XFP5 (w x : ℝ) : ℝ :=
  Real.log (1 - x) * Li₂ ((1 - w) * (1 - x)) - Li₃ ((1 - w) * (1 - x))

/-- `P₅` with its dilogarithm value: `P₅ = Li₃ (1 - w)`. -/
theorem i9M3X_P5_Li {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - x) / (1 - x))
        volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - x) / (1 - x) =
        Li₃ (1 - w) := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hg : ∀ x ∈ Ioo (0 : ℝ) 1, (1 - w) * (1 - x) ∈ Ioo (0 : ℝ) 1 := fun x hx =>
    ⟨mul_pos hu (by linarith [hx.2]), by nlinarith [hx.1, hx.2]⟩
  have hgI : ∀ x ∈ Ioo (0 : ℝ) 1, (1 - w) * (1 - x) ∈ Icc (-1 : ℝ) 1 := fun x hx =>
    ⟨by linarith [(hg x hx).1], (hg x hx).2.le⟩
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (i9M3XFP5 w)
      (Real.log (w + (1 - w) * x) * Real.log (1 - x) / (1 - x)) x := by
    intro x hx
    have hgd : HasDerivAt (fun x => (1 - w) * (1 - x)) (-(1 - w)) x := by
      simpa using ((hasDerivAt_id x).const_sub 1).const_mul (1 - w)
    have h2 := (hasDerivAt_Li₂' (hg x hx)).comp x hgd
    have h3 := (hasDerivAt_Li₃' (hg x hx)).comp x hgd
    have hq := hasDerivAt_log_one_sub hx.2
    refine ((hq.mul h2).sub h3).congr_deriv ?_
    have e : 1 - (1 - w) * (1 - x) = w + (1 - w) * x := by ring
    have h1x : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
    simp only [Function.comp_apply]
    rw [e]
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1,
      0 ≤ Real.log (w + (1 - w) * x) * Real.log (1 - x) / (1 - x) := fun x hx =>
    div_nonneg (mul_nonneg_of_nonpos_of_nonpos
      (Real.log_nonpos (i9M2_A_pos hw hx.1.le).le (i9M2_A_le hw hx.2.le))
      (Real.log_nonpos (by linarith [hx.2]) (by linarith [hx.1]))) (by linarith [hx.2])
  -- limits at `0⁺`
  have hz0 : Tendsto (fun x : ℝ => (1 - w) * (1 - x)) (𝓝[>] 0) (𝓝 ((1 - w) * (1 - 0))) :=
    i9M2_tendsto_of_continuousAt (f := fun x : ℝ => (1 - w) * (1 - x)) (by fun_prop)
  have hev0 : ∀ᶠ x in 𝓝[>] (0 : ℝ), (1 - w) * (1 - x) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx using hgI x hx
  have hmem : (1 - w) * (1 - 0) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hA := (tendsto_log_one_sub_zero.mul (tendsto_Li₂_comp hmem hz0 hev0)).sub
    (tendsto_Li₃_comp hmem hz0 hev0)
  -- limits at `1⁻`
  have hz1 : Tendsto (fun x : ℝ => (1 - w) * (1 - x)) (𝓝[<] 1) (𝓝 0) := by
    simpa using i9M2_tendsto_of_continuousAt (f := fun x : ℝ => (1 - w) * (1 - x))
      (a := 1) (s := Iio 1) (by fun_prop)
  have hev1 : ∀ᶠ x in 𝓝[<] (1 : ℝ), (1 - w) * (1 - x) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx using hgI x hx
  have h0I : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hL := tendsto_log_mul_Li_comp (k := 2) le_rfl hz1
    (hev1.mono fun x hx => abs_le.2 hx)
  have hB := (hL.sub ((tendsto_Li_comp (k := 2) le_rfl h0I hz1 hev1).const_mul
    (Real.log (1 - w)))).sub (tendsto_Li₃_comp h0I hz1 hev1)
  have hB' : Tendsto (i9M3XFP5 w) (𝓝[<] 1) (𝓝 0) := by
    simp only [Li_zero, Li₃_zero, mul_zero, sub_zero] at hB
    refine hB.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
    unfold i9M3XFP5
    rw [Real.log_mul hu.ne' (by linarith [hx.2]), Li_two]
    ring
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hf hA hB'
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp

/-- **`P₅`**: `∫₀¹ log A log (1 - x) / (1 - x) = ζ(3) + H(0,1,1) + H(1,0,1) - log w H(1,1)
- ζ(2) H(1)` (all `H` at `w`). -/
theorem i9M3X_P5 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - x) / (1 - x))
        volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - x) / (1 - x) =
        zeta3 + hpl [zero, one, one] w + hpl [one, zero, one] w -
          Real.log w * hpl [one, one] w - π ^ 2 / 6 * hpl [one] w := by
  refine ⟨(i9M3X_P5_Li hw).1, (i9M3X_P5_Li hw).2.trans ?_⟩
  rw [hpl_one_zero_one hw, hpl_one_one hw, hpl_one hw, hpl_zero_one_one hw,
    Li_two_one_sub' hw]
  simp only [Li_two, Li_three]
  ring

/-! ### `R₁ = ∫₀¹ (1 - w) log A log x / A` -/

/-- `w/A ∈ (0, 1]` for `x ∈ [0, 1]`. -/
theorem i9M3X_w_div_A_mem {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    w / (w + (1 - w) * x) ∈ Icc (-1 : ℝ) 1 :=
  ⟨by linarith [div_pos hw.1 (i9M2_A_pos hw hx.1)],
    by rw [div_le_one (i9M2_A_pos hw hx.1)]; nlinarith [hx.1, hw.2]⟩

/-- `w/A ∈ (0, 1)` for `x ∈ (0, 1)`. -/
theorem i9M3X_w_div_A_mem' {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    w / (w + (1 - w) * x) ∈ Ioo (0 : ℝ) 1 :=
  ⟨div_pos hw.1 (i9M2_A_pos hw hx.1.le),
    by rw [div_lt_one (i9M2_A_pos hw hx.1.le)]; nlinarith [hx.1, hw.2]⟩

/-- `w/A` tends to its value at a point of `[0, 1]` along any punctured side. -/
theorem i9M3X_tendsto_w_div_A {w a : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (ha : 0 ≤ a) {s : Set ℝ} :
    Tendsto (fun x => w / (w + (1 - w) * x)) (𝓝[s] a) (𝓝 (w / (w + (1 - w) * a))) :=
  tendsto_const_nhds.div (i9M3X_tendsto_A w) (i9M2_A_pos hw ha).ne'

/-- The antiderivative of `(1 - w) log A log x / A`. -/
noncomputable def i9M3XFR1 (w x : ℝ) : ℝ :=
  Real.log (w + (1 - w) * x) ^ 3 / 3 + Real.log (w + (1 - w) * x) * Li₂ (w / (w + (1 - w) * x)) -
    Real.log (1 - w) * Real.log (w + (1 - w) * x) ^ 2 / 2 + Li₃ (w / (w + (1 - w) * x))

/-- `R₁` with its polylogarithmic value. -/
theorem i9M3X_R1_Li {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) /
        (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) /
          (w + (1 - w) * x) =
        Li₃ w - Real.log w ^ 3 / 3 - π ^ 2 / 6 * Real.log w +
          Real.log (1 - w) * Real.log w ^ 2 / 2 - zeta3 := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (i9M3XFR1 w)
      ((1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (w + (1 - w) * x)) x := by
    intro x hx
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
    have hz := i9M3X_w_div_A_mem' hw hx
    have h1 := i9M2_hasDerivAt_A w x
    have hlA := h1.log hAx.ne'
    have hzd := (hasDerivAt_const x w).div h1 hAx.ne'
    have h2 := (hasDerivAt_Li₂' hz).comp x hzd
    have h3 := (hasDerivAt_Li₃' hz).comp x hzd
    refine (((((hlA.pow 3).div_const 3).add (hlA.mul h2)).sub
      (((hlA.pow 2).const_mul (Real.log (1 - w))).div_const 2)).add h3).congr_deriv ?_
    simp only [Function.comp_apply, Pi.div_apply]
    rw [show 1 - w / (w + (1 - w) * x) = (1 - w) * x / (w + (1 - w) * x) by
      field_simp; ring, Real.log_div (mul_pos hu hx.1).ne' hAx.ne',
      Real.log_mul hu.ne' hx.1.ne']
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1,
      0 ≤ (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (w + (1 - w) * x) :=
    fun x hx => div_nonneg (mul_nonneg hu.le (mul_nonneg_of_nonpos_of_nonpos
      (Real.log_nonpos (i9M2_A_pos hw hx.1.le).le (i9M2_A_le hw hx.2.le))
      (Real.log_nonpos hx.1.le hx.2.le))) (i9M2_A_pos hw hx.1.le).le
  -- limits at `0⁺`
  have h0 : ∀ᶠ x in 𝓝[>] (0 : ℝ), w / (w + (1 - w) * x) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx using
      i9M3X_w_div_A_mem hw ⟨hx.1.le, hx.2.le⟩
  have hm0 := i9M3X_w_div_A_mem hw (x := 0) ⟨le_rfl, zero_le_one⟩
  have hz0 := i9M3X_tendsto_w_div_A hw le_rfl (s := Ioi 0)
  have hlA0 := i9M3X_tendsto_logA hw le_rfl (s := Ioi 0)
  have hA := ((((hlA0.pow 3).div_const 3).add (hlA0.mul (tendsto_Li₂_comp hm0 hz0 h0))).sub
    (((hlA0.pow 2).const_mul (Real.log (1 - w))).div_const 2)).add (tendsto_Li₃_comp hm0 hz0 h0)
  -- limits at `1⁻`
  have h1 : ∀ᶠ x in 𝓝[<] (1 : ℝ), w / (w + (1 - w) * x) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx using
      i9M3X_w_div_A_mem hw ⟨hx.1.le, hx.2.le⟩
  have hm1 := i9M3X_w_div_A_mem hw (x := 1) ⟨zero_le_one, le_rfl⟩
  have hz1 := i9M3X_tendsto_w_div_A hw zero_le_one (s := Iio 1)
  have hlA1 := i9M3X_tendsto_logA hw zero_le_one (s := Iio 1)
  have hB := ((((hlA1.pow 3).div_const 3).add (hlA1.mul (tendsto_Li₂_comp hm1 hz1 h1))).sub
    (((hlA1.pow 2).const_mul (Real.log (1 - w))).div_const 2)).add (tendsto_Li₃_comp hm1 hz1 h1)
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hf hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [mul_one, mul_zero, add_zero, add_sub_cancel, div_one, div_self hw0.ne',
    Real.log_one, Li₂_one, Li₃_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, zero_mul]
  ring

/-- **`R₁`**: `∫₀¹ (1 - w) log A log x / A = -ζ(3) + H(0,0,1) - log² w H(1)/2 - log³ w/3
- ζ(2) log w` (all `H` at `w`). -/
theorem i9M3X_R1 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) /
        (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) /
          (w + (1 - w) * x) =
        -zeta3 + hpl [zero, zero, one] w - Real.log w ^ 2 * hpl [one] w / 2 -
          Real.log w ^ 3 / 3 - π ^ 2 / 6 * Real.log w := by
  refine ⟨(i9M3X_R1_Li hw).1, (i9M3X_R1_Li hw).2.trans ?_⟩
  rw [hpl_zero_zero_one hw, hpl_one hw]
  simp only [Li_three]
  ring

/-! ### `R₃ = ∫₀¹ (1 - w) log² x / A` -/

/-- `|log² x log (1 + t x)| ≤ t x log² x` for `x, t > 0`, so it tends to `0` at `0⁺`. -/
theorem i9M3X_tendsto_log_sq_mul_log_one_add {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun x => Real.log x ^ 2 * Real.log (1 + t * x)) (𝓝[>] 0) (𝓝 0) := by
  have hb : Tendsto (fun x => t * ‖x * Real.log x ^ 2‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_mul_log_sq_zero.norm).const_mul t
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  have h0 : 0 ≤ Real.log (1 + t * x) := Real.log_nonneg (by nlinarith)
  have h1 : Real.log (1 + t * x) ≤ t * x := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + t * x)
    linarith
  simp only [norm_mul, Real.norm_eq_abs, norm_pow]
  rw [abs_of_nonneg h0, abs_of_pos hx, sq_abs]
  calc Real.log x ^ 2 * Real.log (1 + t * x) ≤ Real.log x ^ 2 * (t * x) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = t * (x * Real.log x ^ 2) := by ring

/-- `(1 - w) x/A ∈ [0, 1)` for `x ∈ [0, 1]`. -/
theorem i9M3X_ux_div_A_mem {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    (1 - w) * x / (w + (1 - w) * x) ∈ Icc (-1 : ℝ) 1 :=
  ⟨by have hu : (0 : ℝ) ≤ 1 - w := by linarith [hw.2]
      linarith [div_nonneg (mul_nonneg hu hx.1) (i9M2_A_pos hw hx.1).le],
    by rw [div_le_one (i9M2_A_pos hw hx.1)]; linarith [hw.1]⟩

/-- The antiderivative of `(1 - w) log² x / A` (after Euler's reflection). -/
noncomputable def i9M3XFR3 (w x : ℝ) : ℝ :=
  2 * Li₃ (w / (w + (1 - w) * x)) + 2 * Li₃ ((1 - w) * x / (w + (1 - w) * x)) -
    2 * Real.log (w + (1 - w) * x) ^ 3 / 3 +
    Real.log (1 - w) * Real.log (w + (1 - w) * x) ^ 2 +
    Real.log w * Real.log (w + (1 - w) * x) ^ 2 + 2 * (π ^ 2 / 6) * Real.log (w + (1 - w) * x) -
    2 * Real.log (1 - w) * Real.log w * Real.log (w + (1 - w) * x) +
    Real.log x ^ 2 * (Real.log (w + (1 - w) * x) - Real.log w) -
    2 * Real.log x * Li₂ ((1 - w) * x / (w + (1 - w) * x))

/-- `R₃` with its polylogarithmic value. -/
theorem i9M3X_R3_Li {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (1 - w) * Real.log x ^ 2 / (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * Real.log x ^ 2 / (w + (1 - w) * x) =
        2 * Li₃ w + 2 * Li₃ (1 - w) - 2 * zeta3 - Real.log w ^ 3 / 3 +
          Real.log (1 - w) * Real.log w ^ 2 - 2 * (π ^ 2 / 6) * Real.log w := by
  have hw0 : 0 < w := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (i9M3XFR3 w)
      ((1 - w) * Real.log x ^ 2 / (w + (1 - w) * x)) x := by
    intro x hx
    have hAx : 0 < w + (1 - w) * x := i9M2_A_pos hw hx.1.le
    have hux : 0 < (1 - w) * x := mul_pos hu hx.1
    have hz := i9M3X_w_div_A_mem' hw hx
    have hy : (1 - w) * x / (w + (1 - w) * x) ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos hux hAx, by rw [div_lt_one hAx]; linarith⟩
    have h1 := i9M2_hasDerivAt_A w x
    have hlA := h1.log hAx.ne'
    have hlx := Real.hasDerivAt_log hx.1.ne'
    have hzd := (hasDerivAt_const x w).div h1 hAx.ne'
    have hyd := ((hasDerivAt_id x).const_mul (1 - w)).div h1 hAx.ne'
    have hz3 := (hasDerivAt_Li₃' hz).comp x hzd
    have hy3 := (hasDerivAt_Li₃' hy).comp x hyd
    have hy2 := (hasDerivAt_Li₂' hy).comp x hyd
    refine (((((((((hz3.const_mul 2).add (hy3.const_mul 2)).sub
      (((hlA.pow 3).const_mul 2).div_const 3)).add
      ((hlA.pow 2).const_mul (Real.log (1 - w)))).add
      ((hlA.pow 2).const_mul (Real.log w))).add (hlA.const_mul (2 * (π ^ 2 / 6)))).sub
      (hlA.const_mul (2 * Real.log (1 - w) * Real.log w))).add
      ((hlx.pow 2).mul (hlA.sub_const (Real.log w)))).sub
      ((hlx.const_mul 2).mul hy2)).congr_deriv ?_
    simp only [Function.comp_apply, Pi.div_apply, Pi.pow_apply, id]
    have hr := Li₂_add_Li₂_one_sub hz.1.le hz.2.le
    have e : 1 - w / (w + (1 - w) * x) = (1 - w) * x / (w + (1 - w) * x) := by
      field_simp; ring
    have e2 : 1 - (1 - w) * x / (w + (1 - w) * x) = w / (w + (1 - w) * x) := by
      field_simp; ring
    rw [e] at hr
    rw [e2]
    rw [Real.log_div hux.ne' hAx.ne', Real.log_mul hu.ne' hx.1.ne'] at hr
    rw [Real.log_div hw0.ne' hAx.ne'] at hr ⊢
    have hL : Li₂ (w / (w + (1 - w) * x)) = π ^ 2 / 6 -
        (Real.log w - Real.log (w + (1 - w) * x)) *
          (Real.log (1 - w) + Real.log x - Real.log (w + (1 - w) * x)) -
        Li₂ ((1 - w) * x / (w + (1 - w) * x)) := by linarith
    rw [hL]
    have hx0 : x ≠ 0 := hx.1.ne'
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ (1 - w) * Real.log x ^ 2 / (w + (1 - w) * x) :=
    fun x hx => div_nonneg (mul_nonneg hu.le (sq_nonneg _)) (i9M2_A_pos hw hx.1.le).le
  have hyt : ∀ (a : ℝ) (s : Set ℝ), 0 ≤ a → Tendsto (fun x => (1 - w) * x / (w + (1 - w) * x))
      (𝓝[s] a) (𝓝 ((1 - w) * a / (w + (1 - w) * a))) := fun a s ha =>
    i9M2_tendsto_of_continuousAt (f := fun x => (1 - w) * x / (w + (1 - w) * x))
      ((by fun_prop : ContinuousAt (fun x : ℝ => (1 - w) * x) a).div (by fun_prop)
        (i9M2_A_pos hw ha).ne')
  -- limits at `0⁺`
  have hz0 : ∀ᶠ x in 𝓝[>] (0 : ℝ), w / (w + (1 - w) * x) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx using
      i9M3X_w_div_A_mem hw ⟨hx.1.le, hx.2.le⟩
  have hy0 : ∀ᶠ x in 𝓝[>] (0 : ℝ), (1 - w) * x / (w + (1 - w) * x) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with x hx using
      i9M3X_ux_div_A_mem hw ⟨hx.1.le, hx.2.le⟩
  have hmz0 := i9M3X_w_div_A_mem hw (x := 0) ⟨le_rfl, zero_le_one⟩
  have hmy0 := i9M3X_ux_div_A_mem hw (x := 0) ⟨le_rfl, zero_le_one⟩
  have hlA0 := i9M3X_tendsto_logA hw le_rfl (s := Ioi 0)
  have hyt0 : Tendsto (fun x => (1 - w) * x / (w + (1 - w) * x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hyt 0 (Ioi 0) le_rfl
  have hpq : Tendsto (fun x => Real.log x ^ 2 * (Real.log (w + (1 - w) * x) - Real.log w))
      (𝓝[>] 0) (𝓝 0) := by
    refine (i9M3X_tendsto_log_sq_mul_log_one_add (t := (1 - w) / w) (by positivity)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    rw [← Real.log_div (i9M2_A_pos hw hx.le).ne' hw0.ne']
    congr 2
    field_simp
  have hpL : Tendsto (fun x => Real.log x * Li₂ ((1 - w) * x / (w + (1 - w) * x)))
      (𝓝[>] 0) (𝓝 0) := by
    have hL := tendsto_log_mul_Li_comp (k := 2) le_rfl hyt0 (hy0.mono fun x hx => abs_le.2 hx)
    have hL2 := ((hlA0.sub_const (Real.log (1 - w))).mul
      (tendsto_Li_comp (k := 2) le_rfl ⟨by norm_num, by norm_num⟩ hyt0 hy0))
    simp only [Li_zero, mul_zero] at hL2
    have h := hL.add hL2
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    rw [Real.log_div (mul_pos hu hx).ne' (i9M2_A_pos hw hx.le).ne',
      Real.log_mul hu.ne' hx.ne', Li_two]
    ring
  have hA := (((((((((tendsto_Li₃_comp hmz0 (i9M3X_tendsto_w_div_A hw le_rfl) hz0).const_mul
    2).add ((tendsto_Li₃_comp hmy0 (hyt 0 _ le_rfl) hy0).const_mul 2)).sub
    (((hlA0.pow 3).const_mul 2).div_const 3)).add
    ((hlA0.pow 2).const_mul (Real.log (1 - w)))).add
    ((hlA0.pow 2).const_mul (Real.log w))).add (hlA0.const_mul (2 * (π ^ 2 / 6)))).sub
    (hlA0.const_mul (2 * Real.log (1 - w) * Real.log w))).add hpq).sub (hpL.const_mul 2)
  -- limits at `1⁻`
  have hz1 : ∀ᶠ x in 𝓝[<] (1 : ℝ), w / (w + (1 - w) * x) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx using
      i9M3X_w_div_A_mem hw ⟨hx.1.le, hx.2.le⟩
  have hy1 : ∀ᶠ x in 𝓝[<] (1 : ℝ), (1 - w) * x / (w + (1 - w) * x) ∈ Icc (-1 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx using
      i9M3X_ux_div_A_mem hw ⟨hx.1.le, hx.2.le⟩
  have hmz1 := i9M3X_w_div_A_mem hw (x := 1) ⟨zero_le_one, le_rfl⟩
  have hmy1 := i9M3X_ux_div_A_mem hw (x := 1) ⟨zero_le_one, le_rfl⟩
  have hlA1 := i9M3X_tendsto_logA hw zero_le_one (s := Iio 1)
  have hl1 : Tendsto Real.log (𝓝[<] 1) (𝓝 (Real.log 1)) :=
    i9M2_tendsto_of_continuousAt (Real.continuousAt_log one_ne_zero)
  have hB := (((((((((tendsto_Li₃_comp hmz1 (i9M3X_tendsto_w_div_A hw zero_le_one) hz1).const_mul
    2).add ((tendsto_Li₃_comp hmy1 (hyt 1 _ zero_le_one) hy1).const_mul 2)).sub
    (((hlA1.pow 3).const_mul 2).div_const 3)).add
    ((hlA1.pow 2).const_mul (Real.log (1 - w)))).add
    ((hlA1.pow 2).const_mul (Real.log w))).add (hlA1.const_mul (2 * (π ^ 2 / 6)))).sub
    (hlA1.const_mul (2 * Real.log (1 - w) * Real.log w))).add
    ((hl1.pow 2).mul (hlA1.sub_const (Real.log w)))).sub
    ((hl1.const_mul 2).mul (tendsto_Li₂_comp hmy1 (hyt 1 _ zero_le_one) hy1))
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hf
    (hA.congr fun x => by unfold i9M3XFR3; ring) hB
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [mul_one, mul_zero, add_zero, add_sub_cancel, div_one, div_self hw0.ne',
    Real.log_one, Li₃_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, zero_mul, Li₃_zero]
  ring

/-- **`R₃`**: `∫₀¹ (1 - w) log² x / A = 2H(0,0,1) + 2H(0,1,1) + 2H(1,0,1) - 2 log w H(1,1)
- log² w H(1) - log³ w/3 - 2ζ(2) H(1) - 2ζ(2) log w` (all `H` at `w`). -/
theorem i9M3X_R3 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => (1 - w) * Real.log x ^ 2 / (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * Real.log x ^ 2 / (w + (1 - w) * x) =
        2 * hpl [zero, zero, one] w + 2 * hpl [zero, one, one] w + 2 * hpl [one, zero, one] w -
          2 * Real.log w * hpl [one, one] w - Real.log w ^ 2 * hpl [one] w -
          Real.log w ^ 3 / 3 - 2 * (π ^ 2 / 6) * hpl [one] w - 2 * (π ^ 2 / 6) * Real.log w := by
  refine ⟨(i9M3X_R3_Li hw).1, (i9M3X_R3_Li hw).2.trans ?_⟩
  rw [hpl_one_zero_one hw, hpl_one_one hw, hpl_one hw, hpl_zero_one_one hw,
    hpl_zero_zero_one hw, Li_two_one_sub' hw]
  simp only [Li_two, Li_three]
  ring

end QED.ThreeLoopD
