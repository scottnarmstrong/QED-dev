/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValTwoA
import QED.Polylog.LiLimits
import QED.Polylog.DilogPM
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Set (d), master `I₁₅`: the `c`-weighted half of `∫ F₂`, inner integral

For `0 < x < 1/2` write `a = x`, `b = 1 - x`, `c = a b`, so `P = (a + b u)(b + a u)`. Then

  `A₁ = (b₁² - b₂²) / (2 c) = 2 f / c`,  `f = (log u - log P)(log c - log P) ≥ 0`,

and `f` has the explicit primitive `QED.ThreeLoopD.i15QPr` in `u` (from
`QED.ThreeLoopD.SetDMastersI15KValPrim`). In the variable `r = a / b ∈ (0, 1)` the inner
integral is

  `∫₀¹ f du = W(r) = (1/r - r)(3 Li₂(-r) + 2 Li₂ r + log r log (1+r) + 2 log r log (1-r))`
    `- (3r + 2 + 3/r) log (1+r) + r log² r / 2 + (3r + 1) log r + π² r / 6 + 4`.

Since `f ≥ 0`, the primitive also gives the integrability of each slice.

## Main results

* `QED.ThreeLoopD.integrableOn_and_integral_i15A1_inner`: for `0 < x < 1/2`, the slice
  `u ↦ A₁(x, u)` is integrable on `(0, 1)` with integral `2 W(x/(1-x)) / (x (1 - x))`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog

namespace QED.ThreeLoopD

/-- A nonnegative function on `(a, b)` with an antiderivative having one-sided limits at `a` and
`b` is interval integrable on `[a, b]`, with integral the difference of the limits. -/
theorem i15Q_ftc_nonneg {F f : ℝ → ℝ} {a b A B : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x) (hf : ∀ x ∈ Ioo a b, 0 ≤ f x)
    (h0 : Tendsto F (𝓝[>] a) (𝓝 A)) (h1 : Tendsto F (𝓝[<] b) (𝓝 B)) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = B - A := by
  have hFc : ContinuousOn F (Ioo a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  set G := extendFrom (Ioo a b) F with hG
  have hGc : ContinuousOn G (Icc a b) := continuousOn_Icc_extendFrom_Ioo hFc h0 h1
  have hGd : ∀ x ∈ Ioo a b, HasDerivAt G (f x) x := by
    intro x hx
    refine (hd x hx).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact extendFrom_extends hFc y hy
  have hint : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      (intervalIntegral.integrableOn_deriv_of_nonneg hGc hGd hf)
  exact ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hab hd hint h0 h1⟩

/-! ### The integrand -/

/-- `f = (log u - log P)(log c - log P)` with `P = (x + (1 - x) u)(1 - x + x u)`. -/
noncomputable def i15Qf (x u : ℝ) : ℝ :=
  (log u - log (x + (1 - x) * u) - log (1 - x + x * u)) *
    (log (x * (1 - x)) - log (x + (1 - x) * u) - log (1 - x + x * u))

theorem i15P_eq' (x u : ℝ) : i15P x u = (x + (1 - x) * u) * (1 - x + x * u) := by
  unfold i15P i9Poly; ring

theorem i15A1_eq {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i15A1 (x, u) = 2 * i15Qf x u / (x * (1 - x)) := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hu0, hu1⟩ := hu
  have hA : 0 < x + (1 - x) * u := by nlinarith
  have hB : 0 < 1 - x + x * u := by nlinarith
  have hc : x * (1 - x) ≠ 0 := (mul_pos hx0 (by linarith)).ne'
  unfold i15A1 i15Qf i15B1 i15B2
  rw [i15P_eq', Real.log_mul hA.ne' hB.ne']
  field_simp
  ring

theorem i15Qf_nonneg {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 ≤ i15Qf x u := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hu0, hu1⟩ := hu
  have hA : 0 < x + (1 - x) * u := by nlinarith
  have hB : 0 < 1 - x + x * u := by nlinarith
  have hc : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  have hP : 0 < (x + (1 - x) * u) * (1 - x + x * u) := mul_pos hA hB
  have h1 : log u - log (x + (1 - x) * u) - log (1 - x + x * u) ≤ 0 := by
    rw [sub_sub, ← Real.log_mul hA.ne' hB.ne', sub_nonpos]
    apply Real.log_le_log hu0
    nlinarith [mul_pos hc (mul_pos (by linarith : (0:ℝ) < 1 - u) (by linarith : (0:ℝ) < 1 - u))]
  have h2 : log (x * (1 - x)) - log (x + (1 - x) * u) - log (1 - x + x * u) ≤ 0 := by
    rw [sub_sub, ← Real.log_mul hA.ne' hB.ne', sub_nonpos]
    apply Real.log_le_log hc
    have hc4 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
    nlinarith [mul_pos hu0 hu0, mul_pos hc (mul_pos hu0 hu0)]
  unfold i15Qf
  exact mul_nonneg_of_nonpos_of_nonpos h1 h2

/-! ### The primitive in `u` -/

/-- **The primitive of `f` in `u`** (for `0 < x < 1/2`). -/
noncomputable def i15QPr (x u : ℝ) : ℝ :=
  log (x * (1 - x)) * i15WX u - log (x * (1 - x)) * i15VL x (1 - x) u -
    log (x * (1 - x)) * i15VL (1 - x) x u - i15VLL x (1 - x) u - i15VLL (1 - x) x u +
    i15VL2 x (1 - x) u + i15VL2 (1 - x) x u + 2 * i15VCR x (1 - x) u

theorem hasDerivAt_i15QPr {x u : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) (hu : 0 < u) :
    HasDerivAt (i15QPr x) (i15Qf x u) u := by
  obtain ⟨hx0, hx1⟩ := hx
  have hb : 0 < 1 - x := by linarith
  have hab : x < 1 - x := by linarith
  have hA : 0 < x + (1 - x) * u := by positivity
  have hB : 0 < 1 - x + x * u := by positivity
  have dX := hasDerivAt_i15WX hu
  have dA := hasDerivAt_i15VL (p := x) (q := 1 - x) (x := u) hb.ne' hA
  have dB := hasDerivAt_i15VL (p := 1 - x) (q := x) (x := u) hx0.ne' hB
  have dUA := hasDerivAt_i15VLL hx0 hb hu
  have dUB := hasDerivAt_i15VLL hb hx0 hu
  have dAA := hasDerivAt_i15VL2 (p := x) (q := 1 - x) (x := u) hb.ne' hA
  have dBB := hasDerivAt_i15VL2 (p := 1 - x) (q := x) (x := u) hx0.ne' hB
  have dAB := hasDerivAt_i15VCR hx0 hab (by ring) hu.le
  have h := (((((((dX.const_mul (log (x * (1 - x)))).sub (dA.const_mul (log (x * (1 - x))))).sub
    (dB.const_mul (log (x * (1 - x))))).sub dUA).sub dUB).add dAA).add dBB).add (dAB.const_mul 2)
  convert h using 1
  · funext y
    simp only [i15QPr, Pi.add_apply, Pi.sub_apply]
  · unfold i15Qf
    ring

/-! ### Values of the primitives at the endpoints -/

theorem i15WX_zero : i15WX 0 = 0 := by simp [i15WX]

theorem i15WX_one : i15WX 1 = -1 := by simp [i15WX]

theorem i15VL_zero (p q : ℝ) : i15VL p q 0 = (p * log p - p) / q := by simp [i15VL]

theorem i15VL_one {a b : ℝ} (h : a + b = 1) : i15VL a b 1 = -1 / b := by
  simp [i15VL, h]

theorem i15VL2_zero (p q : ℝ) :
    i15VL2 p q 0 = (p * log p ^ 2 - 2 * (p * log p) + 2 * p) / q := by simp [i15VL2]

theorem i15VL2_one {a b : ℝ} (h : a + b = 1) : i15VL2 a b 1 = 2 / b := by
  simp [i15VL2, h]

theorem i15VLL_one {a b : ℝ} (h : a + b = 1) :
    i15VLL a b 1 = 2 + a / b * (-Li₂ b - log a ^ 2 / 2) := by
  simp only [i15VLL, mul_one, h, Real.log_one, div_one, mul_zero, zero_sub]
  ring

theorem i15VCR_zero (a b : ℝ) :
    i15VCR a b 0 = i15VL a b 0 * log b - i15VL a b 0 -
      (a - b) / (a * b) * (log (b / a) * log b + log b ^ 2 / 2 + Li₂ ((b - a) / (b * b)) -
        log b) := by
  simp [i15VCR]

theorem i15VCR_one {a b : ℝ} (h : a + b = 1) :
    i15VCR a b 1 = -(i15VL a b 1 - 1) - (a - b) / (a * b) * Li₂ ((b - a) / b) := by
  have h' : b + a = 1 := by linarith
  simp [i15VCR, h']

/-! ### The inner integral -/

/-- The limit of `i15QPr x` at `0⁺`. -/
noncomputable def i15QPr0 (x : ℝ) : ℝ :=
  log (x * (1 - x)) * i15WX 0 - log (x * (1 - x)) * i15VL x (1 - x) 0 -
    log (x * (1 - x)) * i15VL (1 - x) x 0 - -(x / (1 - x) * log x) -
    -((1 - x) / x * log (1 - x)) + i15VL2 x (1 - x) 0 + i15VL2 (1 - x) x 0 +
    2 * i15VCR x (1 - x) 0

theorem tendsto_i15QPr_zero {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    Tendsto (i15QPr x) (𝓝[>] 0) (𝓝 (i15QPr0 x)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hb : 0 < 1 - x := by linarith
  have hab : x < 1 - x := by linarith
  have c1 := i15W_tendsto_of_continuousAt (continuousAt_i15WX 0) (Ioi 0)
  have c2 := i15W_tendsto_of_continuousAt
    (hasDerivAt_i15VL (p := x) (q := 1 - x) (x := 0) hb.ne' (by simpa using hx0)).continuousAt
    (Ioi 0)
  have c3 := i15W_tendsto_of_continuousAt
    (hasDerivAt_i15VL (p := 1 - x) (q := x) (x := 0) hx0.ne' (by simpa using hb)).continuousAt
    (Ioi 0)
  have c4 := i15W_tendsto_of_continuousAt
    (hasDerivAt_i15VL2 (p := x) (q := 1 - x) (x := 0) hb.ne' (by simpa using hx0)).continuousAt
    (Ioi 0)
  have c5 := i15W_tendsto_of_continuousAt
    (hasDerivAt_i15VL2 (p := 1 - x) (q := x) (x := 0) hx0.ne' (by simpa using hb)).continuousAt
    (Ioi 0)
  have c6 := i15W_tendsto_of_continuousAt
    (hasDerivAt_i15VCR hx0 hab (by ring) le_rfl).continuousAt (Ioi 0)
  have h := (((((((c1.const_mul (log (x * (1 - x)))).sub (c2.const_mul (log (x * (1 - x))))).sub
    (c3.const_mul (log (x * (1 - x))))).sub (tendsto_i15VLL_zero hx0 hb)).sub
    (tendsto_i15VLL_zero hb hx0)).add c4).add c5).add (c6.const_mul 2)
  exact h

/-- The value of `i15QPr x` at `1`. -/
theorem tendsto_i15QPr_one {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    Tendsto (i15QPr x) (𝓝[<] 1) (𝓝 (i15QPr x 1)) := by
  obtain ⟨hx0, hx1⟩ := hx
  have hb : 0 < 1 - x := by linarith
  have hab : x < 1 - x := by linarith
  have hc : ContinuousAt (i15QPr x) 1 := by
    have c1 := continuousAt_i15WX 1
    have c2 := (hasDerivAt_i15VL (p := x) (q := 1 - x) (x := 1) hb.ne'
      (by linarith)).continuousAt
    have c3 := (hasDerivAt_i15VL (p := 1 - x) (q := x) (x := 1) hx0.ne'
      (by linarith)).continuousAt
    have c4 := (hasDerivAt_i15VL2 (p := x) (q := 1 - x) (x := 1) hb.ne'
      (by linarith)).continuousAt
    have c5 := (hasDerivAt_i15VL2 (p := 1 - x) (q := x) (x := 1) hx0.ne'
      (by linarith)).continuousAt
    have c6 := (hasDerivAt_i15VCR hx0 hab (by ring) zero_le_one).continuousAt
    have c7 := continuousAt_i15VLL hx0 hb one_pos
    have c8 := continuousAt_i15VLL hb hx0 one_pos
    unfold i15QPr
    exact (((((((c1.const_mul _).sub (c2.const_mul _)).sub (c3.const_mul _)).sub c7).sub
      c8).add c4).add c5).add (c6.const_mul 2)
  exact i15W_tendsto_of_continuousAt hc _

/-- `W(r)`, the inner integral of `f` in the variable `r = x / (1 - x)`. -/
noncomputable def i15QWr (r : ℝ) : ℝ :=
  (1 / r - r) * (3 * Li₂ (-r) + 2 * Li₂ r + log r * log (1 + r) + 2 * (log r * log (1 - r))) -
    log (1 + r) * (3 * r + 2 + 3 / r) + r * log r ^ 2 / 2 + log r * (3 * r + 1) +
    r * π ^ 2 / 6 + 4

theorem i15QPr_sub_eq {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    i15QPr (r / (1 + r)) 1 - i15QPr0 (r / (1 + r)) = i15QWr r := by
  obtain ⟨hr0, hr1⟩ := hr
  have hs : 0 < 1 + r := by linarith
  set a := r / (1 + r) with ha
  have hb : 1 - a = 1 / (1 + r) := by rw [ha]; field_simp; ring
  have ha0 : 0 < a := by positivity
  have hab1 : a + (1 - a) = 1 := by ring
  have hba1 : 1 - a + a = 1 := by ring
  unfold i15QPr i15QPr0
  rw [i15VLL_one hab1, i15VLL_one hba1, i15VCR_one hab1, i15VCR_zero, i15VL_one hab1,
    i15VL_one hba1, i15VL2_one hab1, i15VL2_one hba1, i15VL_zero, i15VL_zero, i15VL2_zero,
    i15VL2_zero, i15WX_zero, i15WX_one]
  have e1 : (1 - a - a) / ((1 - a) * (1 - a)) = 1 - r ^ 2 := by
    rw [hb, ha]; field_simp; ring
  have e2 : (1 - a - a) / (1 - a) = 1 - r := by rw [hb, ha]; field_simp
  have la : log a = log r - log (1 + r) := by rw [ha, Real.log_div hr0.ne' hs.ne']
  have lb : log (1 - a) = -log (1 + r) := by rw [hb, one_div, Real.log_inv]
  have lba : log ((1 - a) / a) = -log r := by
    rw [Real.log_div (by rw [hb]; positivity) ha0.ne', la, lb]; ring
  have lc : log (a * (1 - a)) = log r - 2 * log (1 + r) := by
    rw [Real.log_mul ha0.ne' (by rw [hb]; positivity), la, lb]; ring
  have r1 := Li_two_one_sub' ⟨hr0, hr1⟩
  have r2 := Li_two_div_one_add ⟨hr0, hr1⟩
  have r3 := Li_two_inv_one_add ⟨hr0, hr1⟩
  have r4 := Li_two_one_sub_sq ⟨hr0, hr1⟩
  rw [Li_two] at r1 r2 r3 r4
  rw [← ha] at r2
  rw [e1, e2, la, lb, lba, lc, hb, r1, r4, r2, r3]
  unfold i15QWr
  rw [ha]
  field_simp
  ring

/-- **The inner integral of `A₁`** at `0 < x < 1/2`. -/
theorem integrableOn_and_integral_i15A1_inner {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
    IntegrableOn (fun u => i15A1 (x, u)) (Ioo 0 1) ∧
      ∫ u in Ioo (0 : ℝ) 1, i15A1 (x, u) = 2 * i15QWr (x / (1 - x)) / (x * (1 - x)) := by
  have hx1 : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
  obtain ⟨hI, hval⟩ := i15Q_ftc_nonneg (F := i15QPr x) (f := i15Qf x) zero_lt_one
    (fun u hu => hasDerivAt_i15QPr hx hu.1) (fun u hu => i15Qf_nonneg hx1 hu)
    (tendsto_i15QPr_zero hx) (tendsto_i15QPr_one hx)
  have hcongr : ∀ u ∈ Ioo (0 : ℝ) 1, i15A1 (x, u) = 2 * i15Qf x u / (x * (1 - x)) :=
    fun u hu => i15A1_eq hx1 hu
  have hIo : IntegrableOn (i15Qf x) (Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hI
  refine ⟨IntegrableOn.congr_fun ((hIo.const_mul 2).div_const (x * (1 - x)))
    (fun u hu => (hcongr u hu).symm) measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_div, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one, hval]
  have hr : x / (1 - x) ∈ Ioo (0 : ℝ) 1 := by
    have : 0 < 1 - x := by linarith [hx.2]
    exact ⟨div_pos hx.1 this, by rw [div_lt_one this]; linarith [hx.2]⟩
  have hxr : x / (1 - x) / (1 + x / (1 - x)) = x := by
    have : 1 - x ≠ 0 := by linarith [hx.2]
    field_simp
    ring
  have := i15QPr_sub_eq hr
  rw [hxr] at this
  rw [this]

end QED.ThreeLoopD
