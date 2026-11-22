/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9KValB
public import QED.ThreeLoopD.SetDMastersI9MInner
public import QED.Polylog.HPLBasic
import QED.Polylog.HPLCalculus
import QED.Polylog.HPLLowWeight
import QED.Polylog.HPLValues
import QED.Polylog.DilogPM
import QED.Polylog.ExtraIntegrals

/-!
# Set (d), master `I₉`: `M₂ = -111/2 + 15π²/2 + 3ζ(3)`

The Taylor coefficient `M₂ = QED.ThreeLoopD.i9MCoeff 2` is an absolutely convergent integral
over the unit square (Cauchy estimates along the chain of `QED.ThreeLoopD.SetDMastersI9KValM`).
By Fubini we integrate first in `x`. At fixed `w ∈ (0, 1)` the integrand is
`-(3/2)(1 - w²)/w · (s(x) + s(1 - x))` with `s = QED.ThreeLoopD.i9M2S w`, whose integral is
known (`QED.ThreeLoopD.i9M2S_integral`). With the harmonic polylogarithms
`H₋ = H(-1, 0; w) = log w log (1 + w) + Li₂ (-w)` and `H₊ = H(1, 0; w) = Li₂ (1 - w) - π²/6`, the
dilogarithm identities of `QED.Polylog.DilogPM` give

  `∫₀¹ (integrand) dx = -(3/2) O(w)`,
  `O(w) = (1/w + 2 + w)(12 H₋ - 8 H₊) - (1 + w)(2π²/3 + 6 log² w + 8 log w)`.

The `w`-integral of `O` uses `∫₀¹ H(a, 0; w) dw / w = H(0, a, 0; 1)` (`-3ζ(3)/2` and `-2ζ(3)`)
and elementary antiderivatives for the rest: `∫₀¹ O = 37 - 5π² - 2ζ(3)`.

## Main results

* `QED.ThreeLoopD.integrable_i9MCoeffFun_two`: the integrand of `M₂` is integrable.
* `QED.ThreeLoopD.integral_i9M2O`: `∫₀¹ O = 37 - 5π² - 2ζ(3)`.
* `QED.ThreeLoopD.i9MCoeff_two`: `M₂ = -111/2 + 15π²/2 + 3ζ(3)`.
* `QED.ThreeLoopD.i9KCoeff_two`: `K₂ = -47 + 31π²/4 + 3ζ(3)`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The outer integrand `O(w)` of `M₂ = -(3/2) ∫₀¹ O`. -/
noncomputable def i9M2O (w : ℝ) : ℝ :=
  (1 / w + 2 + w) * (12 * hpl [negOne, zero] w - 8 * hpl [one, zero] w) -
    (1 + w) * (2 * π ^ 2 / 3 + 6 * Real.log w ^ 2 + 8 * Real.log w)

/-! ### The integrand of `M₂` -/

/-- **The integrand of `M₂` is integrable** on the unit square. -/
theorem integrable_i9MCoeffFun_two :
    Integrable (fun z : ℝ × ℝ => i9MCoeffFun 2 z.1 z.2)
      (volume.restrict (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1)) := by
  have hS : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    measurableSet_Ioo.prod measurableSet_Ioo
  refine (integrable_i9M_bound.const_mul 1800).mono' ?_ ?_
  · have : Measurable (fun z : ℝ × ℝ => i9MCoeffFun 2 z.1 z.2) := by
      unfold i9MCoeffFun i9KB1 i9KB3 i9Poly
      fun_prop
    exact this.aestronglyMeasurable
  refine ae_restrict_of_forall_mem hS fun z hz => ?_
  obtain ⟨x, w⟩ := z
  have hc := norm_le_of_hasDerivAt_chain (D := fun k e => i9MD k e (x, w)) (R := 1 / 20)
    (ρ := 1 / 60) (by norm_num) (fun k ε => hasDerivAt_i9MD k ε (x, w))
    (fun ε hε => norm_i9MD_le hε hz.1 hz.2) 2 0 (by norm_num)
  have he := i9MD_at_zero (x := x) hz.2 2
  have h : ‖(i9MCoeffFun 2 x w : ℂ)‖ ≤
      1800 * (w ^ (-(3 / 5) : ℝ) * (x * (1 - x)) ^ (-(7 / 10) : ℝ)) := by
    rw [← he, norm_div]
    norm_num [Nat.factorial] at hc ⊢
    linarith
  simpa only [Complex.norm_real] using h

/-- At fixed `x, w ∈ (0, 1)`, the integrand of `M₂` is `-(3/2)(1 - w²)/w · (s(x) + s(1 - x))`. -/
theorem i9MCoeffFun_two_eq {x w : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    i9MCoeffFun 2 x w = -(3 / 2) * ((1 - w ^ 2) / w) * (i9M2S w x + i9M2S w (1 - x)) := by
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hw0 := hw.1
  have hA := i9M2_A_pos hw hx0.le
  have hB := i9M2_B_pos hw hx.2.le
  unfold i9MCoeffFun i9KB1 i9KB3 i9Poly i9M2S
  rw [show x * (1 - x) * (1 - w) ^ 2 + w * 1 = (w + (1 - w) * x) * (1 - (1 - w) * x) by ring,
    show w + (1 - w) * (1 - x) = 1 - (1 - w) * x by ring,
    show 1 - (1 - w) * (1 - x) = w + (1 - w) * x by ring,
    show (1 - x) * (1 - (1 - x)) = x * (1 - x) by ring,
    Real.log_mul hA.ne' hB.ne', Real.log_mul hx0.ne' hx1.ne']
  simp only [Nat.factorial]
  field_simp
  ring

/-- **The `x`-integral of the integrand of `M₂`**. -/
theorem integral_i9MCoeffFun_two_x {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∫ x in Ioo (0 : ℝ) 1, i9MCoeffFun 2 x w =
      -(3 / 2) * ((1 - w ^ 2) / w) * (2 * i9M2Sig w) := by
  rw [setIntegral_congr_fun measurableSet_Ioo fun x hx => i9MCoeffFun_two_eq hx hw,
    integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  obtain ⟨hs, hv⟩ := i9M2S_integral hw
  have hs' : IntervalIntegrable (fun x => i9M2S w (1 - x)) volume 0 1 := by
    simpa using (hs.comp_sub_left 1).symm
  rw [intervalIntegral.integral_add hs hs', intervalIntegral.integral_comp_sub_left
    (fun x => i9M2S w x) 1]
  simp only [sub_self, sub_zero]
  rw [hv]
  ring

/-- **The `x`-integral in terms of `O`**: `(1 - w²)/w · 2 ∫₀¹ s = O(w)`. -/
theorem i9M2Sig_eq_O {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    (1 - w ^ 2) / w * (2 * i9M2Sig w) = i9M2O w := by
  have hw0 := hw.1
  have hu : 0 < 1 - w := by linarith [hw.2]
  have ha : 0 < 1 + w := by linarith
  have h1 := Li_two_one_sub' hw
  have h2 := Li_two_div_one_add hw
  have h3 := Li_two_inv_one_add hw
  rw [Li_two] at h1 h2 h3
  unfold i9M2Sig i9M2JAB i9M2O
  rw [hpl_one_zero hw, hpl_negOne_zero hw, Li_two, h1, h2, h3]
  field_simp
  ring

/-! ### The outer integral -/

/-- `H(a, 0; x) ≤ 0` on `(0, 1)` for `a = ±1`. -/
theorem i9M2_hpl_nonpos {a : Letter} (ha : a ≠ zero)
    (hk : ∀ t ∈ Icc (0 : ℝ) 1, t < 1 → 0 ≤ a.kernel t) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    hpl [a, zero] x ≤ 0 := by
  rw [hpl_cons_of_ne_zero ha]
  have h := intervalIntegral.integral_nonneg (μ := volume) hx.1.le
    (f := fun t => -(a.kernel t * hpl [zero] t)) fun t ht => by
      rw [hpl_zero]
      have ht1 : t < 1 := lt_of_le_of_lt ht.2 hx.2
      exact neg_nonneg.2 (mul_nonpos_iff.2 (Or.inl ⟨hk t ⟨ht.1, ht1.le⟩ ht1,
        Real.log_nonpos ht.1 ht1.le⟩))
  rw [intervalIntegral.integral_neg] at h
  linarith

theorem i9M2_hplNeg_nonpos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : hpl [negOne, zero] x ≤ 0 :=
  i9M2_hpl_nonpos (by decide) (fun t ht _ => by
    rw [kernel_negOne]; exact inv_nonneg.2 (by linarith [ht.1])) hx

theorem i9M2_hplOne_nonpos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : hpl [one, zero] x ≤ 0 :=
  i9M2_hpl_nonpos (by decide) (fun t _ ht1 => by
    rw [kernel_one]; exact inv_nonneg.2 (by linarith)) hx

/-- `∫₀¹ H(a, 0; w) dw / w = H(0, a, 0; 1)`. -/
theorem i9M2_div_hpl (a : Letter) (ha : a ≠ zero) :
    IntervalIntegrable (fun w => w⁻¹ * hpl [a, zero] w) volume 0 1 ∧
      ∫ w in (0 : ℝ)..1, w⁻¹ * hpl [a, zero] w = hpl [zero, a, zero] 1 := by
  have hnz : ¬AllZero [zero, a, zero] := fun h => ha (h a (by simp))
  have hi := intervalIntegrable_kernel_mul_hpl_one (a := zero) (w := [a, zero]) (by decide) hnz
  simp only [kernel_zero] at hi
  refine ⟨hi, ?_⟩
  rw [hpl_cons_of_not_allZero hnz]
  simp only [kernel_zero]

/-- `∫₀¹ -(2 + w) H(-1, 0; w) dw = π²/3 - 13/8`. -/
theorem i9M2_outer_neg :
    IntervalIntegrable (fun w => -((2 + w) * hpl [negOne, zero] w)) volume 0 1 ∧
      ∫ w in (0 : ℝ)..1, -((2 + w) * hpl [negOne, zero] w) = π ^ 2 / 3 - 13 / 8 := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun w => -((2 * w + w ^ 2 / 2 + 3 / 2) *
      hpl [negOne, zero] w - (w * (w * Real.log w) / 4 - w ^ 2 / 8 +
        3 / 2 * (w * Real.log w - w))))
      (-((2 + x) * hpl [negOne, zero] x)) x := by
    intro x hx
    have hx0 := hx.1
    have hH := hasDerivAt_hpl_cons negOne [zero] hx
    rw [kernel_negOne, hpl_zero] at hH
    have hid := hasDerivAt_id x
    have hl := Real.hasDerivAt_log hx0.ne'
    have hxl := hid.mul hl
    have hG := ((((hid.const_mul 2).add ((hid.pow 2).div_const 2)).add_const (3 / 2)).mul
      hH).sub ((((hid.mul hxl).div_const 4).sub ((hid.pow 2).div_const 8)).add
        ((hxl.sub hid).const_mul (3 / 2)))
    refine hG.neg.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id]
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ -((2 + x) * hpl [negOne, zero] x) := fun x hx =>
    neg_nonneg.2 (mul_nonpos_iff.2 (Or.inl ⟨by linarith [hx.1], i9M2_hplNeg_nonpos hx⟩))
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hH0 := tendsto_hpl_zero (w := [negOne, zero]) (fun h => by
    have := h negOne (by simp); exact absurd this (by decide))
  have hA := ((((hx0.const_mul 2).add ((hx0.pow 2).div_const 2)).add_const (3 / 2)).mul
    hH0).sub ((((hx0.mul tendsto_mul_log_zero).div_const 4).sub ((hx0.pow 2).div_const 8)).add
      ((tendsto_mul_log_zero.sub hx0).const_mul (3 / 2))) |>.neg
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hl1 : Tendsto Real.log (𝓝[<] 1) (𝓝 (Real.log 1)) :=
    i9M2_tendsto_of_continuousAt (Real.continuousAt_log one_ne_zero)
  have hH1 := tendsto_hpl_one (a := negOne) (by decide) [zero]
  have hB := ((((hx1.const_mul 2).add ((hx1.pow 2).div_const 2)).add_const (3 / 2)).mul
    hH1).sub ((((hx1.mul (hx1.mul hl1)).div_const 4).sub ((hx1.pow 2).div_const 8)).add
      (((hx1.mul hl1).sub hx1).const_mul (3 / 2))) |>.neg
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hf hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2, hpl_negOne_zero_at_one]
  simp only [Real.log_one]
  ring

/-- `∫₀¹ -(2 + w) H(1, 0; w) dw = 21/8`. -/
theorem i9M2_outer_one :
    IntervalIntegrable (fun w => -((2 + w) * hpl [one, zero] w)) volume 0 1 ∧
      ∫ w in (0 : ℝ)..1, -((2 + w) * hpl [one, zero] w) = 21 / 8 := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun w => -((2 * w + w ^ 2 / 2 - 5 / 2) *
      hpl [one, zero] w + (w * (w * Real.log w) / 4 - w ^ 2 / 8 +
        5 / 2 * (w * Real.log w - w))))
      (-((2 + x) * hpl [one, zero] x)) x := by
    intro x hx
    have hx0 := hx.1
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hH := hasDerivAt_hpl_cons one [zero] hx
    rw [kernel_one, hpl_zero] at hH
    have hid := hasDerivAt_id x
    have hl := Real.hasDerivAt_log hx0.ne'
    have hxl := hid.mul hl
    have hG := ((((hid.const_mul 2).add ((hid.pow 2).div_const 2)).sub_const (5 / 2)).mul
      hH).add ((((hid.mul hxl).div_const 4).sub ((hid.pow 2).div_const 8)).add
        ((hxl.sub hid).const_mul (5 / 2)))
    refine hG.neg.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id]
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ -((2 + x) * hpl [one, zero] x) := fun x hx =>
    neg_nonneg.2 (mul_nonpos_iff.2 (Or.inl ⟨by linarith [hx.1], i9M2_hplOne_nonpos hx⟩))
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hH0 := tendsto_hpl_zero (w := [one, zero]) (fun h => by
    have := h one (by simp); exact absurd this (by decide))
  have hA := ((((hx0.const_mul 2).add ((hx0.pow 2).div_const 2)).sub_const (5 / 2)).mul
    hH0).add ((((hx0.mul tendsto_mul_log_zero).div_const 4).sub ((hx0.pow 2).div_const 8)).add
      ((tendsto_mul_log_zero.sub hx0).const_mul (5 / 2))) |>.neg
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hl1 : Tendsto Real.log (𝓝[<] 1) (𝓝 (Real.log 1)) :=
    i9M2_tendsto_of_continuousAt (Real.continuousAt_log one_ne_zero)
  have hH1 : Tendsto (hpl [one, zero]) (𝓝[<] 1) (𝓝 (-0 - Li 2 1)) := by
    refine (tendsto_log_mul_log_one_sub_one.neg.sub (tendsto_Li_one_left le_rfl)).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    rw [hpl_one_zero hx, neg_mul]
  have hB := ((((hx1.const_mul 2).add ((hx1.pow 2).div_const 2)).sub_const (5 / 2)).mul
    hH1).add ((((hx1.mul (hx1.mul hl1)).div_const 4).sub ((hx1.pow 2).div_const 8)).add
      (((hx1.mul hl1).sub hx1).const_mul (5 / 2))) |>.neg
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hf hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [Real.log_one]
  ring

/-- `∫₀¹ (1 + w)(2π²/3 + 6 log² w + 8 log w) dw = π² + 7/2`. -/
theorem i9M2_outer_log :
    IntervalIntegrable (fun w => (1 + w) * (2 * π ^ 2 / 3 + 6 * Real.log w ^ 2 +
      8 * Real.log w)) volume 0 1 ∧
      ∫ w in (0 : ℝ)..1, (1 + w) * (2 * π ^ 2 / 3 + 6 * Real.log w ^ 2 + 8 * Real.log w) =
        π ^ 2 + 7 / 2 := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun w => 2 * π ^ 2 / 3 * (w + w ^ 2 / 2) +
      6 * ((w * Real.log w ^ 2 - 2 * (w * Real.log w) + 2 * w) +
        (w * (w * Real.log w ^ 2) / 2 - w * (w * Real.log w) / 2 + w ^ 2 / 4)) +
      8 * ((w * Real.log w - w) + (w * (w * Real.log w) / 2 - w ^ 2 / 4)))
      ((1 + x) * (2 * π ^ 2 / 3 + 6 * Real.log x ^ 2 + 8 * Real.log x)) x := by
    intro x hx
    have hx0 := hx.1
    have hid := hasDerivAt_id x
    have hl := Real.hasDerivAt_log hx0.ne'
    have hxl := hid.mul hl
    have hxl2 := hid.mul (hl.pow 2)
    have hG := (((hid.add ((hid.pow 2).div_const 2)).const_mul (2 * π ^ 2 / 3)).add
      ((((hxl2.sub (hxl.const_mul 2)).add (hid.const_mul 2)).add
        ((((hid.mul hxl2).div_const 2).sub ((hid.mul hxl).div_const 2)).add
          ((hid.pow 2).div_const 4))).const_mul 6)).add
      ((((hxl.sub hid)).add (((hid.mul hxl).div_const 2).sub
        ((hid.pow 2).div_const 4))).const_mul 8)
    refine hG.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.pow_apply, id]
    field_simp
    ring
  have hf : ∀ x ∈ Ioo (0 : ℝ) 1,
      0 ≤ (1 + x) * (2 * π ^ 2 / 3 + 6 * Real.log x ^ 2 + 8 * Real.log x) := by
    intro x hx
    have := Real.two_le_pi
    exact mul_nonneg (by linarith [hx.1]) (by nlinarith [sq_nonneg (Real.log x + 2 / 3)])
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hA := (((hx0.add ((hx0.pow 2).div_const 2)).const_mul (2 * π ^ 2 / 3)).add
      ((((tendsto_mul_log_sq_zero.sub (tendsto_mul_log_zero.const_mul 2)).add
        (hx0.const_mul 2)).add ((((hx0.mul tendsto_mul_log_sq_zero).div_const 2).sub
          ((hx0.mul tendsto_mul_log_zero).div_const 2)).add
          ((hx0.pow 2).div_const 4))).const_mul 6)).add
      ((((tendsto_mul_log_zero.sub hx0)).add (((hx0.mul tendsto_mul_log_zero).div_const 2).sub
        ((hx0.pow 2).div_const 4))).const_mul 8)
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hl1 : Tendsto Real.log (𝓝[<] 1) (𝓝 (Real.log 1)) :=
    i9M2_tendsto_of_continuousAt (Real.continuousAt_log one_ne_zero)
  have hxl1 := hx1.mul hl1
  have hxl21 := hx1.mul (hl1.pow 2)
  have hB := (((hx1.add ((hx1.pow 2).div_const 2)).const_mul (2 * π ^ 2 / 3)).add
      ((((hxl21.sub (hxl1.const_mul 2)).add (hx1.const_mul 2)).add
        ((((hx1.mul hxl21).div_const 2).sub ((hx1.mul hxl1).div_const 2)).add
          ((hx1.pow 2).div_const 4))).const_mul 6)).add
      ((((hxl1.sub hx1)).add (((hx1.mul hxl1).div_const 2).sub
        ((hx1.pow 2).div_const 4))).const_mul 8)
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd hf hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp only [Real.log_one]
  ring

/-- **`∫₀¹ O = 37 - 5π² - 2ζ(3)`**. -/
theorem integral_i9M2O :
    IntervalIntegrable i9M2O volume 0 1 ∧
      ∫ w in (0 : ℝ)..1, i9M2O w = 37 - 5 * π ^ 2 - 2 * zeta3 := by
  have h0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 1 ∧
      ∫ _ in (0 : ℝ)..1, (0 : ℝ) = 0 := ⟨intervalIntegrable_const, by simp⟩
  have h := i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step h0
    (i9M2_div_hpl negOne (by decide)) 12) (i9M2_div_hpl one (by decide)) (-8))
    i9M2_outer_neg (-12)) i9M2_outer_one 8) i9M2_outer_log (-1)
  have e : i9M2O = fun w => 0 + 12 * (w⁻¹ * hpl [negOne, zero] w) +
      -8 * (w⁻¹ * hpl [one, zero] w) + -12 * -((2 + w) * hpl [negOne, zero] w) +
      8 * -((2 + w) * hpl [one, zero] w) +
      -1 * ((1 + w) * (2 * π ^ 2 / 3 + 6 * Real.log w ^ 2 + 8 * Real.log w)) := by
    funext w
    unfold i9M2O
    ring
  rw [e]
  refine ⟨h.1, h.2.trans ?_⟩
  rw [hpl_zero_negOne_zero_at_one, hpl_zero_one_zero_at_one]
  ring

/-! ### `M₂` and `K₂` -/

/-- **`M₂ = -111/2 + 15π²/2 + 3ζ(3)`**. -/
theorem i9MCoeff_two : i9MCoeff 2 = -111 / 2 + 15 * π ^ 2 / 2 + 3 * zeta3 := by
  have hint := integrable_i9MCoeffFun_two
  rw [volume_restrict_prod2] at hint
  rw [i9MCoeff, volume_restrict_prod2,
    integral_prod_symm (fun z : ℝ × ℝ => i9MCoeffFun 2 z.1 z.2) hint]
  have hin : ∀ w ∈ Ioo (0 : ℝ) 1,
      ∫ x in Ioo (0 : ℝ) 1, i9MCoeffFun 2 x w = -(3 / 2) * i9M2O w := fun w hw => by
    rw [integral_i9MCoeffFun_two_x hw, ← i9M2Sig_eq_O hw]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hin, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_i9M2O.2]
  ring

/-- **`K₂ = -47 + 31π²/4 + 3ζ(3)`**. -/
theorem i9KCoeff_two : i9KCoeff 2 = -47 + 31 * π ^ 2 / 4 + 3 * zeta3 :=
  i9KCoeff_two_of_M i9MCoeff_two

end QED.ThreeLoopD
