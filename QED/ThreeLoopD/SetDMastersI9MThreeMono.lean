/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI9MInner
import QED.Polylog.ExtraIntegrals
import QED.ThreeLoopD.SetDMastersI9KValB

/-!
# Set (d), master `I₉`: the weight-three monomials behind `M₃`

Fix `w ∈ (0, 1)` and write `u = 1 - w`, `A = w + u x`, `B = 1 - u x`, `a = log A`, `b = log B`,
`p = log x`, `q = log (1 - x)`. The `x`-integrand of the Taylor coefficient `M₃` of
`QED.ThreeLoopD.i9M` is a polynomial in `a, b, p, q, log w`. Its eight monomials of weight three
that contain `a` are reduced, by one integration by parts each (`Φ = X m` with `X = x` or
`X = A / u`; all boundary terms vanish), to weight-two integrals and nine *pure* integrals
(a product of two logarithms against `dx / x`, `dx / (1 - x)`, `dx / A` or `dx / B`):

* `∫ a³ = -(w/u) log³ w - 3 ∫ a²`,
* `∫ a² b = -2 ∫ a b - ∫ a² + ((1 + w)/u) ∫ u a² / B`,
* `∫ a² p = -2 ∫ a p - ∫ a² + (2 w / u) ∫ u a p / A`,
* `∫ a² q = -2 ∫ a q - ∫ a² + (1/u) ∫ a² / (1 - x)`,
* `∫ a p² = -∫ p² - 2 ∫ a p + (w/u) ∫ u p² / A`,
* `∫ a q² = -∫ q² - 2 ∫ a q + (2/u) ∫ a q / (1 - x)`,
* `∫ a p q = -∫ p q - ∫ a q - ∫ a p - (w/u) ∫ a q / x + (1/u) ∫ a p / (1 - x)`,
* `∫ a b p = -∫ b p - ∫ a p - ∫ a b + ((1 + w)/u) ∫ u a p / B - (w/u) ∫ a b / x`.

Each statement takes the pure integral (with its integrability) as a hypothesis.

## Main results

* `QED.ThreeLoopD.i9M3_ibp`: an improper integration by parts on `(0, 1)`.
* `QED.ThreeLoopD.i9M3_intervalIntegrable_of_bound`: integrability from a bound
  `K (1 + log² (x (1 - x)))`.
* `QED.ThreeLoopD.i9M3_aaa` … `QED.ThreeLoopD.i9M3_abp`: the eight reductions.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog

namespace QED.ThreeLoopD

/-! ### Tools -/

/-- **Improper integration by parts on `(0, 1)`**: if `Φ' = m + r` on `(0, 1)` with `m` and `r`
integrable, then `∫₀¹ m = Φ(1⁻) - Φ(0⁺) - ∫₀¹ r`. -/
theorem i9M3_ibp {Φ m r : ℝ → ℝ} {L0 L1 R : ℝ}
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Φ (m x + r x) x) (hm : IntervalIntegrable m volume 0 1)
    (hr : IntervalIntegrable r volume 0 1 ∧ ∫ x in (0 : ℝ)..1, r x = R)
    (h0 : Tendsto Φ (𝓝[>] 0) (𝓝 L0)) (h1 : Tendsto Φ (𝓝[<] 1) (𝓝 L1)) :
    IntervalIntegrable m volume 0 1 ∧ ∫ x in (0 : ℝ)..1, m x = L1 - L0 - R := by
  refine ⟨hm, ?_⟩
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (f' := fun x => m x + r x)
    zero_lt_one hd (hm.add hr.1) h0 h1
  rw [intervalIntegral.integral_add hm hr.1, hr.2] at h
  linarith

/-- **Integrability from a logarithmic bound**: a measurable `f` with
`|f x| ≤ K (1 + log² (x (1 - x)))` on `(0, 1)` is integrable on `[0, 1]`. -/
theorem i9M3_intervalIntegrable_of_bound {f : ℝ → ℝ} {K : ℝ} (hf : Measurable f)
    (hb : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ K * (1 + Real.log (x * (1 - x)) ^ 2)) :
    IntervalIntegrable f volume 0 1 := by
  have hg : IntervalIntegrable (fun x => K * (1 + Real.log (x * (1 - x)) ^ 2)) volume 0 1 :=
    (intervalIntegrable_const.add i9M2_logc_sq.1).const_mul K
  refine hg.mono_fun' hf.aestronglyMeasurable ?_
  rw [uIoc_of_le zero_le_one]
  have h1 : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), x ≠ 1 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    have : ({(1 : ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
      compl_mem_ae_iff.2 (measure_singleton 1)
    filter_upwards [this] with x hx _ using hx
  filter_upwards [h1, ae_restrict_mem measurableSet_Ioc] with x hx1 hx
  rw [Real.norm_eq_abs]
  exact hb x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩

/-- The elementary bounds on `(0, 1)`: with `L = -log w` and `C = -log (x (1 - x))`,
`|a|, |b| ≤ L`, `|p|, |q| ≤ C`, `C ≤ 1 + C²`. -/
theorem i9M3_bounds {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |Real.log (w + (1 - w) * x)| ≤ -Real.log w ∧ |Real.log (1 - (1 - w) * x)| ≤ -Real.log w ∧
      |Real.log x| ≤ -Real.log (x * (1 - x)) ∧ |Real.log (1 - x)| ≤ -Real.log (x * (1 - x)) ∧
      0 ≤ -Real.log w ∧ -Real.log (x * (1 - x)) ≤ 1 + Real.log (x * (1 - x)) ^ 2 := by
  have hx0 := hx.1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hA := i9M2_A_pos hw hx0.le
  have hB := i9M2_B_pos hw hx.2.le
  have hlA : Real.log w ≤ Real.log (w + (1 - w) * x) :=
    Real.log_le_log hw.1 (by nlinarith [hw.2, hx0])
  have hlB : Real.log w ≤ Real.log (1 - (1 - w) * x) :=
    Real.log_le_log hw.1 (by nlinarith [hw.2, hx.2])
  have hA1 := Real.log_nonpos hA.le (i9M2_A_le hw hx.2.le)
  have hB1 := Real.log_nonpos hB.le (i9M2_B_le hw hx0.le)
  have hp := Real.log_nonpos hx0.le hx.2.le
  have hq := Real.log_nonpos hx1.le (by linarith)
  have hw0 := Real.log_nonpos hw.1.le hw.2.le
  rw [Real.log_mul hx0.ne' hx1.ne']
  refine ⟨?_, ?_, ?_, ?_, by linarith, ?_⟩
  · rw [abs_of_nonpos hA1]; linarith
  · rw [abs_of_nonpos hB1]; linarith
  · rw [abs_of_nonpos hp]; linarith
  · rw [abs_of_nonpos hq]; linarith
  · nlinarith [sq_nonneg (Real.log x + Real.log (1 - x) + 1 / 2)]


/-- A product `f g h` with `|f| ≤ L` and `|g|, |h| ≤ L + C` (`L = -log w`, `C = -log (x (1 - x))`)
is integrable on `[0, 1]`. -/
theorem i9M3_intervalIntegrable_mul3 {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {f g h : ℝ → ℝ}
    (hm : Measurable (fun x => f x * g x * h x))
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, |f x| ≤ -Real.log w)
    (hg : ∀ x ∈ Ioo (0 : ℝ) 1, |g x| ≤ -Real.log w + -Real.log (x * (1 - x)))
    (hh : ∀ x ∈ Ioo (0 : ℝ) 1, |h x| ≤ -Real.log w + -Real.log (x * (1 - x))) :
    IntervalIntegrable (fun x => f x * g x * h x) volume 0 1 := by
  refine i9M3_intervalIntegrable_of_bound
    (K := 2 * (-Real.log w) * (1 + (-Real.log w) ^ 2)) hm fun x hx => ?_
  obtain ⟨-, -, -, -, hL, hC2⟩ := i9M3_bounds hw hx
  set L := -Real.log w
  set C := -Real.log (x * (1 - x)) with hCd
  have hC : 0 ≤ C := by
    have := (i9M3_bounds hw hx).2.2.1
    linarith [abs_nonneg (Real.log x)]
  have h1 := hf x hx
  have h2 := hg x hx
  have h3 := hh x hx
  have e : Real.log (x * (1 - x)) ^ 2 = C ^ 2 := by rw [hCd, neg_sq]
  rw [abs_mul, abs_mul, e]
  have h23 : |g x| * |h x| ≤ 2 * L ^ 2 + 2 * C ^ 2 := by
    nlinarith [abs_nonneg (g x), abs_nonneg (h x), sq_nonneg (L - C)]
  have k1 : |f x| * (|g x| * |h x|) ≤ L * (2 * L ^ 2 + 2 * C ^ 2) :=
    mul_le_mul h1 h23 (by positivity) hL
  have k2 : 0 ≤ L * (L ^ 2 * C ^ 2) := mul_nonneg hL (mul_nonneg (sq_nonneg L) (sq_nonneg C))
  have k3 : 0 ≤ L * C ^ 2 := mul_nonneg hL (sq_nonneg C)
  have k4 : |f x| * |g x| * |h x| = |f x| * (|g x| * |h x|) := by ring
  rw [k4]
  nlinarith

theorem i9M3_absA {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∀ x ∈ Ioo (0 : ℝ) 1, |Real.log (w + (1 - w) * x)| ≤ -Real.log w :=
  fun _ hx => (i9M3_bounds hw hx).1

theorem i9M3_absB {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∀ x ∈ Ioo (0 : ℝ) 1, |Real.log (1 - (1 - w) * x)| ≤ -Real.log w :=
  fun _ hx => (i9M3_bounds hw hx).2.1

theorem i9M3_absA' {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∀ x ∈ Ioo (0 : ℝ) 1, |Real.log (w + (1 - w) * x)| ≤ -Real.log w + -Real.log (x * (1 - x)) :=
  fun x hx => by
    have h := i9M3_bounds hw hx
    linarith [h.1, abs_nonneg (Real.log x), h.2.2.1]

theorem i9M3_absB' {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∀ x ∈ Ioo (0 : ℝ) 1, |Real.log (1 - (1 - w) * x)| ≤ -Real.log w + -Real.log (x * (1 - x)) :=
  fun x hx => by
    have h := i9M3_bounds hw hx
    linarith [h.2.1, abs_nonneg (Real.log x), h.2.2.1]

theorem i9M3_absP {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∀ x ∈ Ioo (0 : ℝ) 1, |Real.log x| ≤ -Real.log w + -Real.log (x * (1 - x)) :=
  fun x hx => by
    have h := i9M3_bounds hw hx
    linarith [h.2.2.1, h.2.2.2.2.1]

theorem i9M3_absQ {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    ∀ x ∈ Ioo (0 : ℝ) 1, |Real.log (1 - x)| ≤ -Real.log w + -Real.log (x * (1 - x)) :=
  fun x hx => by
    have h := i9M3_bounds hw hx
    linarith [h.2.2.2.1, h.2.2.2.2.1]

/-! ### Weight-two integrals not in `QED.ThreeLoopD.SetDMastersI9MInner` -/

theorem i9M3_logQ_logA {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (1 - x) * Real.log (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (1 - x) * Real.log (w + (1 - w) * x) =
        2 + w * Real.log w / (1 - w) - Li₂ (1 - w) / (1 - w) := by
  obtain ⟨hi, hv⟩ := i9M2_logX_logB hw
  have e : (fun x => Real.log (1 - x) * Real.log (w + (1 - w) * x)) =
      fun x => (fun y => Real.log y * Real.log (1 - (1 - w) * y)) (1 - x) := by
    funext x
    show _ = Real.log (1 - x) * Real.log (1 - (1 - w) * (1 - x))
    rw [show 1 - (1 - w) * (1 - x) = w + (1 - w) * x by ring]
  rw [e]
  refine ⟨by simpa using (hi.comp_sub_left 1).symm, ?_⟩
  rw [intervalIntegral.integral_comp_sub_left (fun y => Real.log y * Real.log (1 - (1 - w) * y)) 1]
  simpa using hv

theorem i9M3_logX_sq :
    IntervalIntegrable (fun x => Real.log x * Real.log x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log x = 2 := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun x => x * (Real.log x * Real.log x) -
      2 * (x * Real.log x) + 2 * x) (Real.log x * Real.log x) x := by
    intro x hx
    have hl := Real.hasDerivAt_log hx.1.ne'
    have hid := hasDerivAt_id x
    refine (((hid.mul (hl.mul hl)).sub ((hid.mul hl).const_mul 2)).add
      (hid.const_mul 2)).congr_deriv ?_
    simp only [id, Pi.mul_apply]
    have := hx.1.ne'
    field_simp
    ring
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hA := ((tendsto_mul_log_sq_zero.congr (f₂ := fun x : ℝ => x * (Real.log x * Real.log x))
    fun x => by ring).sub
    (tendsto_mul_log_zero.const_mul 2)).add (hx0.const_mul 2)
  have hx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have hl1 : Tendsto Real.log (𝓝[<] 1) (𝓝 (Real.log 1)) :=
    i9M2_tendsto_of_continuousAt (Real.continuousAt_log one_ne_zero)
  have hB := ((hx1.mul (hl1.mul hl1)).sub ((hx1.mul hl1).const_mul 2)).add (hx1.const_mul 2)
  have h := intervalIntegrable_and_integral_eq_of_nonneg hd (fun x _ => mul_self_nonneg _) hA hB
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp

theorem i9M3_logQ_sq :
    IntervalIntegrable (fun x => Real.log (1 - x) * Real.log (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (1 - x) * Real.log (1 - x) = 2 := by
  obtain ⟨hi, hv⟩ := i9M3_logX_sq
  refine ⟨by simpa using (hi.comp_sub_left 1).symm, ?_⟩
  rw [intervalIntegral.integral_comp_sub_left (fun y => Real.log y * Real.log y) 1]
  simpa using hv

theorem i9M3_logX_logQ :
    IntervalIntegrable (fun x => Real.log x * Real.log (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log (1 - x) = 2 - π ^ 2 / 6 := by
  obtain ⟨hc, hcv⟩ := i9M2_logc_sq
  obtain ⟨hp, hpv⟩ := i9M3_logX_sq
  obtain ⟨hq, hqv⟩ := i9M3_logQ_sq
  have hi : IntervalIntegrable (fun x => Real.log x * Real.log (1 - x)) volume 0 1 := by
    refine i9M3_intervalIntegrable_of_bound (K := 1) (by fun_prop) fun x hx => ?_
    have h := i9M3_bounds (w := 1 / 2) ⟨by norm_num, by norm_num⟩ hx
    have hp0 := Real.log_nonpos hx.1.le hx.2.le
    have hq0 := Real.log_nonpos (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x) (by linarith [hx.1])
    rw [Real.log_mul hx.1.ne' (by linarith [hx.2]), abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos
      hp0 hq0)]
    nlinarith [sq_nonneg (Real.log x), sq_nonneg (Real.log (1 - x))]
  refine ⟨hi, ?_⟩
  have e : ∀ x ∈ Ioo (0 : ℝ) 1, Real.log (x * (1 - x)) ^ 2 =
      Real.log x * Real.log x + 2 * (Real.log x * Real.log (1 - x)) +
        Real.log (1 - x) * Real.log (1 - x) := fun x hx => by
    rw [Real.log_mul hx.1.ne' (by linarith [hx.2])]
    ring
  have h2 : ∫ x in (0 : ℝ)..1, Real.log (x * (1 - x)) ^ 2 = ∫ x in (0 : ℝ)..1,
      (Real.log x * Real.log x + 2 * (Real.log x * Real.log (1 - x)) +
        Real.log (1 - x) * Real.log (1 - x)) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le zero_le_one]
    have : ({(1 : ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) :=
      compl_mem_ae_iff.2 (measure_singleton 1)
    filter_upwards [this] with x hx1 hx
    exact e x ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  rw [hcv, intervalIntegral.integral_add (hp.add (hi.const_mul 2)) hq,
    intervalIntegral.integral_add hp (hi.const_mul 2), intervalIntegral.integral_const_mul,
    hpv, hqv] at h2
  linarith


/-- `|log A| ≤ ((1 - w)/w) (1 - x)` on `[0, 1]`. -/
theorem i9M3_abs_logA_le {w x : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.log (w + (1 - w) * x)| ≤ (1 - w) / w * (1 - x) := by
  have hA := i9M2_A_pos hw hx0
  have hA1 := Real.log_nonpos hA.le (i9M2_A_le hw hx1)
  have hwA : w ≤ w + (1 - w) * x := by nlinarith [hw.2]
  rw [abs_of_nonpos hA1]
  have h := Real.log_le_sub_one_of_pos (inv_pos.2 hA)
  rw [Real.log_inv] at h
  have e : (w + (1 - w) * x)⁻¹ - 1 = (1 - w) * (1 - x) / (w + (1 - w) * x) := by
    field_simp; ring
  rw [e] at h
  have h2 : (1 - w) * (1 - x) / (w + (1 - w) * x) ≤ (1 - w) * (1 - x) / w :=
    div_le_div_of_nonneg_left (mul_nonneg (by linarith [hw.2]) (by linarith)) hw.1 hwA
  calc -Real.log (w + (1 - w) * x) ≤ (1 - w) * (1 - x) / w := by linarith
    _ = (1 - w) / w * (1 - x) := by ring

/-- `log A · logᵏ (1 - x) → 0` as `x → 1⁻` (`k = 1, 2`), from `|log A| ≤ C (1 - x)`. -/
theorem i9M3_tendsto_logA_mul_one {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {g : ℝ → ℝ}
    (hg : Tendsto (fun x => (1 - x) * g x) (𝓝[<] 1) (𝓝 0)) :
    Tendsto (fun x => Real.log (w + (1 - w) * x) * g x) (𝓝[<] 1) (𝓝 0) := by
  have hb : Tendsto (fun x => (1 - w) / w * ‖(1 - x) * g x‖) (𝓝[<] 1) (𝓝 0) := by
    simpa using (hg.norm).const_mul ((1 - w) / w)
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with x hx
  have h := i9M3_abs_logA_le hw hx.1.le hx.2.le
  have hc : 0 ≤ 1 - x := by linarith [hx.2]
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc]
  calc |Real.log (w + (1 - w) * x)| * |g x| ≤ (1 - w) / w * (1 - x) * |g x| :=
        mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ = (1 - w) / w * ((1 - x) * |g x|) := by ring

theorem i9M3_tendsto_one_sub_mul_log_one_sub :
    Tendsto (fun x : ℝ => (1 - x) * Real.log (1 - x)) (𝓝[<] 1) (𝓝 0) :=
  tendsto_mul_log_zero.comp tendsto_one_sub_nhdsLT_one

theorem i9M3_tendsto_one_sub_mul_log_one_sub_sq :
    Tendsto (fun x : ℝ => (1 - x) * (Real.log (1 - x) * Real.log (1 - x))) (𝓝[<] 1) (𝓝 0) := by
  refine (tendsto_mul_log_sq_zero.comp tendsto_one_sub_nhdsLT_one).congr fun x => ?_
  simp only [Function.comp]
  ring

theorem i9M3_tendsto_A (w : ℝ) (s : Set ℝ) (c : ℝ) :
    Tendsto (fun x => w + (1 - w) * x) (𝓝[s] c) (𝓝 (w + (1 - w) * c)) :=
  i9M2_tendsto_of_continuousAt (by fun_prop)

theorem i9M3_tendsto_logA {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (s : Set ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun x => Real.log (w + (1 - w) * x)) (𝓝[s] c)
      (𝓝 (Real.log (w + (1 - w) * c))) :=
  ((Real.continuousAt_log (i9M2_A_pos hw hc).ne').tendsto.comp (i9M3_tendsto_A w s c))

theorem i9M3_tendsto_logB {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) (s : Set ℝ) {c : ℝ} (hc : c ≤ 1) :
    Tendsto (fun x => Real.log (1 - (1 - w) * x)) (𝓝[s] c)
      (𝓝 (Real.log (1 - (1 - w) * c))) :=
  ((Real.continuousAt_log (i9M2_B_pos hw hc).ne').tendsto.comp
    (i9M2_tendsto_of_continuousAt (by fun_prop)))

theorem i9M3_tendsto_log_one (s : Set ℝ) : Tendsto Real.log (𝓝[s] 1) (𝓝 0) := by
  simpa using i9M2_tendsto_of_continuousAt (s := s) (Real.continuousAt_log one_ne_zero)

theorem i9M3_tendsto_log_one_sub_zero (s : Set ℝ) :
    Tendsto (fun x : ℝ => Real.log (1 - x)) (𝓝[s] 0) (𝓝 0) := by
  have h : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) - 0 ≠ 0)).comp
      (continuousAt_const.sub continuousAt_id)
  simpa using i9M2_tendsto_of_continuousAt (s := s) h

/-! ### The eight monomials -/

theorem i9M3_zero_step : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 1 ∧
    ∫ _ in (0 : ℝ)..1, (0 : ℝ) = 0 := ⟨intervalIntegrable_const, by simp⟩

/-- `∫ a³ = -(w/u) log³ w - 3 ∫ a²`. -/
theorem i9M3_aaa {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) *
      Real.log (w + (1 - w) * x)) volume 0 1 ∧
    ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) *
      Real.log (w + (1 - w) * x) =
      -(w / (1 - w) * Real.log w ^ 3) -
        3 * (2 + (2 * w * Real.log w - w * Real.log w ^ 2) / (1 - w)) := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hr := i9M2_step i9M3_zero_step (i9M2_logA_sq hw) 3
  have hm := i9M3_intervalIntegrable_mul3 hw (by fun_prop) (i9M3_absA hw) (i9M3_absA' hw)
    (i9M3_absA' hw)
  have h := i9M3_ibp (L0 := w / (1 - w) * (Real.log w * Real.log w * Real.log w)) (L1 := 0)
    (Φ := fun x => (w + (1 - w) * x) / (1 - w) * (Real.log (w + (1 - w) * x) *
      Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x))) ?_ hm hr ?_ ?_
  · exact ⟨h.1, h.2.trans (by ring)⟩
  · intro x hx
    have hA := i9M2_A_pos hw hx.1.le
    have h1 := i9M2_hasDerivAt_A w x
    have hl := h1.log hA.ne'
    refine ((h1.div_const (1 - w)).mul ((hl.mul hl).mul hl)).congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp
    ring
  · have := (((i9M3_tendsto_A w (Ioi 0) 0).div_const (1 - w)).mul
      (((i9M3_tendsto_logA hw (Ioi 0) le_rfl).mul (i9M3_tendsto_logA hw (Ioi 0) le_rfl)).mul
        (i9M3_tendsto_logA hw (Ioi 0) le_rfl)))
    simpa using this
  · have := (((i9M3_tendsto_A w (Iio 1) 1).div_const (1 - w)).mul
      (((i9M3_tendsto_logA hw (Iio 1) zero_le_one).mul
        (i9M3_tendsto_logA hw (Iio 1) zero_le_one)).mul
        (i9M3_tendsto_logA hw (Iio 1) zero_le_one)))
    simpa using this


/-- `∫ a² b = -2 ∫ a b - ∫ a² + ((1 + w)/u) ∫ u a² / B`. -/
theorem i9M3_aab {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {Vab Vaa P1 : ℝ}
    (hab : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x))
        volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) = Vab)
    (haa : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) ^ 2 = Vaa)
    (hP1 : IntervalIntegrable (fun x => (1 - w) * Real.log (w + (1 - w) * x) ^ 2 / (1 - (1 - w) *
        x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * Real.log (w + (1 - w) * x) ^ 2 / (1 - (1 - w) * x) = P1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) *
        Real.log (1 - (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) * Real.log (1 -
          (1 - w) * x) = -2 * Vab - Vaa + (1 + w) / (1 - w) * P1 := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hu0 : (1 - w) ≠ 0 := hu.ne'
  have hr := i9M2_step (i9M2_step (i9M2_step (i9M3_zero_step) hab (2)) haa (1)) hP1 (-((1 + w) /
      (1 - w)))
  have hm := i9M3_intervalIntegrable_mul3 hw (by fun_prop) (i9M3_absA hw) (i9M3_absA' hw)
      (i9M3_absB' hw)
  have tA0 := i9M3_tendsto_A w (Ioi 0) 0
  have tA1 := i9M3_tendsto_A w (Iio 1) 1
  have ta0 := i9M3_tendsto_logA hw (Ioi 0) le_rfl
  have ta1 := i9M3_tendsto_logA hw (Iio 1) zero_le_one
  have tb0 := i9M3_tendsto_logB hw (Ioi 0) zero_le_one
  have tb1 := i9M3_tendsto_logB hw (Iio 1) le_rfl
  have tp1 := i9M3_tendsto_log_one (Iio 1)
  have tq0 := i9M3_tendsto_log_one_sub_zero (Ioi 0)
  have tx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have h := i9M3_ibp (L0 := 0) (L1 := 0)
    (Φ := fun x => (w + (1 - w) * x) / (1 - w) * (Real.log (w + (1 - w) * x) * Real.log (w + (1 -
        w) * x) * Real.log (1 - (1 - w) * x))) ?_ hm hr ?_ ?_
  · exact ⟨h.1, h.2.trans (by ring)⟩
  · intro x hx
    have hA := i9M2_A_pos hw hx.1.le
    have hB := i9M2_B_pos hw hx.2.le
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hAne := hA.ne'
    have hBne := hB.ne'
    have h1 := i9M2_hasDerivAt_A w x
    have hid := hasDerivAt_id x
    have ha := h1.log hA.ne'
    have hb := (i9M2_hasDerivAt_B w x).log hB.ne'
    have hp := Real.hasDerivAt_log hx0
    have hq := (hid.const_sub 1).log hx1
    refine ((h1.div_const (1 - w)).mul ((ha.mul ha).mul hb)).congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp
    ring
  · simpa using (tA0.div_const (1 - w)).mul ((ta0.mul ta0).mul tb0)
  · simpa using (tA1.div_const (1 - w)).mul ((ta1.mul ta1).mul tb1)
/-- `∫ a² p = -∫ a² - 2 ∫ a p + (2 w / u) ∫ u a p / A`. -/
theorem i9M3_aap {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {Vap Vaa R1 : ℝ}
    (hap : IntervalIntegrable (fun x => Real.log x * Real.log (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log (w + (1 - w) * x) = Vap)
    (haa : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) ^ 2 = Vaa)
    (hR1 : IntervalIntegrable (fun x => (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (w +
        (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (w + (1 - w) * x) =
          R1) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) *
        Real.log x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) * Real.log x =
          -Vaa - 2 * Vap + 2 * w / (1 - w) * R1 := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hu0 : (1 - w) ≠ 0 := hu.ne'
  have hr := i9M2_step (i9M2_step (i9M2_step (i9M3_zero_step) haa (1)) hap (2)) hR1 (-(2 * w / (1
      - w)))
  have hm := i9M3_intervalIntegrable_mul3 hw (by fun_prop) (i9M3_absA hw) (i9M3_absA' hw)
      (i9M3_absP hw)
  have tA0 := i9M3_tendsto_A w (Ioi 0) 0
  have tA1 := i9M3_tendsto_A w (Iio 1) 1
  have ta0 := i9M3_tendsto_logA hw (Ioi 0) le_rfl
  have ta1 := i9M3_tendsto_logA hw (Iio 1) zero_le_one
  have tb0 := i9M3_tendsto_logB hw (Ioi 0) zero_le_one
  have tb1 := i9M3_tendsto_logB hw (Iio 1) le_rfl
  have tp1 := i9M3_tendsto_log_one (Iio 1)
  have tq0 := i9M3_tendsto_log_one_sub_zero (Ioi 0)
  have tx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have h := i9M3_ibp (L0 := 0) (L1 := 0)
    (Φ := fun x => x * (Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) * Real.log x)) ?_
        hm hr ?_ ?_
  · exact ⟨h.1, h.2.trans (by ring)⟩
  · intro x hx
    have hA := i9M2_A_pos hw hx.1.le
    have hB := i9M2_B_pos hw hx.2.le
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hAne := hA.ne'
    have hBne := hB.ne'
    have h1 := i9M2_hasDerivAt_A w x
    have hid := hasDerivAt_id x
    have ha := h1.log hA.ne'
    have hb := (i9M2_hasDerivAt_B w x).log hB.ne'
    have hp := Real.hasDerivAt_log hx0
    have hq := (hid.const_sub 1).log hx1
    refine (hid.mul ((ha.mul ha).mul hp)).congr_deriv ?_
    simp only [id, Pi.mul_apply]
    field_simp
    ring
  · have h := tendsto_mul_log_zero.mul (ta0.mul ta0)
    rw [zero_mul] at h
    exact h.congr fun x => by ring
  · simpa using tx1.mul ((ta1.mul ta1).mul tp1)
/-- `∫ a² q = -2 ∫ a q - ∫ a² + (1/u) ∫ a² / (1 - x)`. -/
theorem i9M3_aaq {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {Vaq Vaa P3 : ℝ}
    (haq : IntervalIntegrable (fun x => Real.log (1 - x) * Real.log (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (1 - x) * Real.log (w + (1 - w) * x) = Vaq)
    (haa : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) ^ 2) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) ^ 2 = Vaa)
    (hP3 : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) ^ 2 / (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) ^ 2 / (1 - x) = P3) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) *
        Real.log (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (w + (1 - w) * x) * Real.log (1 -
          x) = -2 * Vaq - Vaa + P3 / (1 - w) := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hu0 : (1 - w) ≠ 0 := hu.ne'
  have hr := i9M2_step (i9M2_step (i9M2_step (i9M3_zero_step) haq (2)) haa (1)) hP3 (-(1 / (1 - w)))
  have hm := i9M3_intervalIntegrable_mul3 hw (by fun_prop) (i9M3_absA hw) (i9M3_absA' hw)
      (i9M3_absQ hw)
  have tA0 := i9M3_tendsto_A w (Ioi 0) 0
  have tA1 := i9M3_tendsto_A w (Iio 1) 1
  have ta0 := i9M3_tendsto_logA hw (Ioi 0) le_rfl
  have ta1 := i9M3_tendsto_logA hw (Iio 1) zero_le_one
  have tb0 := i9M3_tendsto_logB hw (Ioi 0) zero_le_one
  have tb1 := i9M3_tendsto_logB hw (Iio 1) le_rfl
  have tp1 := i9M3_tendsto_log_one (Iio 1)
  have tq0 := i9M3_tendsto_log_one_sub_zero (Ioi 0)
  have tx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have h := i9M3_ibp (L0 := 0) (L1 := 0)
    (Φ := fun x => (w + (1 - w) * x) / (1 - w) * (Real.log (w + (1 - w) * x) * Real.log (w + (1 -
        w) * x) * Real.log (1 - x))) ?_ hm hr ?_ ?_
  · exact ⟨h.1, h.2.trans (by ring)⟩
  · intro x hx
    have hA := i9M2_A_pos hw hx.1.le
    have hB := i9M2_B_pos hw hx.2.le
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hAne := hA.ne'
    have hBne := hB.ne'
    have h1 := i9M2_hasDerivAt_A w x
    have hid := hasDerivAt_id x
    have ha := h1.log hA.ne'
    have hb := (i9M2_hasDerivAt_B w x).log hB.ne'
    have hp := Real.hasDerivAt_log hx0
    have hq := (hid.const_sub 1).log hx1
    refine ((h1.div_const (1 - w)).mul ((ha.mul ha).mul hq)).congr_deriv ?_
    simp only [id, Pi.mul_apply]
    field_simp
    ring
  · simpa using (tA0.div_const (1 - w)).mul ((ta0.mul ta0).mul tq0)
  · have hg := ((tA1.div_const (1 - w)).mul ta1).mul i9M3_tendsto_one_sub_mul_log_one_sub
    rw [mul_zero] at hg
    exact (i9M3_tendsto_logA_mul_one hw (hg.congr (f₂ := fun x =>
      (1 - x) * ((w + (1 - w) * x) / (1 - w) * Real.log (w + (1 - w) * x) * Real.log (1 - x))) fun
          x => by ring)).congr fun x => by ring
/-- `∫ a p² = -∫ p² - 2 ∫ a p + (w/u) ∫ u p² / A`. -/
theorem i9M3_app {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {Vpp Vap R3 : ℝ}
    (hpp : IntervalIntegrable (fun x => Real.log x * Real.log x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log x = Vpp)
    (hap : IntervalIntegrable (fun x => Real.log x * Real.log (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log (w + (1 - w) * x) = Vap)
    (hR3 : IntervalIntegrable (fun x => (1 - w) * Real.log x ^ 2 / (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * Real.log x ^ 2 / (w + (1 - w) * x) = R3) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log x * Real.log x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log x * Real.log x = -Vpp - 2 * Vap + w
          / (1 - w) * R3 := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hu0 : (1 - w) ≠ 0 := hu.ne'
  have hr := i9M2_step (i9M2_step (i9M2_step (i9M3_zero_step) hpp (1)) hap (2)) hR3 (-(w / (1 - w)))
  have hm := i9M3_intervalIntegrable_mul3 hw (by fun_prop) (i9M3_absA hw) (i9M3_absP hw)
      (i9M3_absP hw)
  have tA0 := i9M3_tendsto_A w (Ioi 0) 0
  have tA1 := i9M3_tendsto_A w (Iio 1) 1
  have ta0 := i9M3_tendsto_logA hw (Ioi 0) le_rfl
  have ta1 := i9M3_tendsto_logA hw (Iio 1) zero_le_one
  have tb0 := i9M3_tendsto_logB hw (Ioi 0) zero_le_one
  have tb1 := i9M3_tendsto_logB hw (Iio 1) le_rfl
  have tp1 := i9M3_tendsto_log_one (Iio 1)
  have tq0 := i9M3_tendsto_log_one_sub_zero (Ioi 0)
  have tx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have h := i9M3_ibp (L0 := 0) (L1 := 0)
    (Φ := fun x => x * (Real.log (w + (1 - w) * x) * Real.log x * Real.log x)) ?_ hm hr ?_ ?_
  · exact ⟨h.1, h.2.trans (by ring)⟩
  · intro x hx
    have hA := i9M2_A_pos hw hx.1.le
    have hB := i9M2_B_pos hw hx.2.le
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hAne := hA.ne'
    have hBne := hB.ne'
    have h1 := i9M2_hasDerivAt_A w x
    have hid := hasDerivAt_id x
    have ha := h1.log hA.ne'
    have hb := (i9M2_hasDerivAt_B w x).log hB.ne'
    have hp := Real.hasDerivAt_log hx0
    have hq := (hid.const_sub 1).log hx1
    refine (hid.mul ((ha.mul hp).mul hp)).congr_deriv ?_
    simp only [id, Pi.mul_apply]
    field_simp
    ring
  · have h := tendsto_mul_log_sq_zero.mul ta0
    rw [zero_mul] at h
    exact h.congr fun x => by ring
  · simpa using tx1.mul ((ta1.mul tp1).mul tp1)
/-- `∫ a q² = -∫ q² - 2 ∫ a q + (2/u) ∫ a q / (1 - x)`. -/
theorem i9M3_aqq {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {Vqq Vaq P5 : ℝ}
    (hqq : IntervalIntegrable (fun x => Real.log (1 - x) * Real.log (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (1 - x) * Real.log (1 - x) = Vqq)
    (haq : IntervalIntegrable (fun x => Real.log (1 - x) * Real.log (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (1 - x) * Real.log (w + (1 - w) * x) = Vaq)
    (hP5 : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - x) / (1 - x))
        volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - x) / (1 - x) = P5) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - x) * Real.log (1 - x))
        volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - x) * Real.log (1 - x) = -Vqq -
          2 * Vaq + 2 / (1 - w) * P5 := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hu0 : (1 - w) ≠ 0 := hu.ne'
  have hr := i9M2_step (i9M2_step (i9M2_step (i9M3_zero_step) hqq (1)) haq (2)) hP5 (-(2 / (1 - w)))
  have hm := i9M3_intervalIntegrable_mul3 hw (by fun_prop) (i9M3_absA hw) (i9M3_absQ hw)
      (i9M3_absQ hw)
  have tA0 := i9M3_tendsto_A w (Ioi 0) 0
  have tA1 := i9M3_tendsto_A w (Iio 1) 1
  have ta0 := i9M3_tendsto_logA hw (Ioi 0) le_rfl
  have ta1 := i9M3_tendsto_logA hw (Iio 1) zero_le_one
  have tb0 := i9M3_tendsto_logB hw (Ioi 0) zero_le_one
  have tb1 := i9M3_tendsto_logB hw (Iio 1) le_rfl
  have tp1 := i9M3_tendsto_log_one (Iio 1)
  have tq0 := i9M3_tendsto_log_one_sub_zero (Ioi 0)
  have tx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have h := i9M3_ibp (L0 := 0) (L1 := 0)
    (Φ := fun x => (w + (1 - w) * x) / (1 - w) * (Real.log (w + (1 - w) * x) * Real.log (1 - x) *
        Real.log (1 - x))) ?_ hm hr ?_ ?_
  · exact ⟨h.1, h.2.trans (by ring)⟩
  · intro x hx
    have hA := i9M2_A_pos hw hx.1.le
    have hB := i9M2_B_pos hw hx.2.le
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hAne := hA.ne'
    have hBne := hB.ne'
    have h1 := i9M2_hasDerivAt_A w x
    have hid := hasDerivAt_id x
    have ha := h1.log hA.ne'
    have hb := (i9M2_hasDerivAt_B w x).log hB.ne'
    have hp := Real.hasDerivAt_log hx0
    have hq := (hid.const_sub 1).log hx1
    refine ((h1.div_const (1 - w)).mul ((ha.mul hq).mul hq)).congr_deriv ?_
    simp only [id, Pi.mul_apply]
    field_simp
    ring
  · simpa using (tA0.div_const (1 - w)).mul ((ta0.mul tq0).mul tq0)
  · have hg := (tA1.div_const (1 - w)).mul i9M3_tendsto_one_sub_mul_log_one_sub_sq
    rw [mul_zero] at hg
    exact (i9M3_tendsto_logA_mul_one hw (hg.congr (f₂ := fun x =>
      (1 - x) * ((w + (1 - w) * x) / (1 - w) * Real.log (1 - x) * Real.log (1 - x))) fun x => by
          ring)).congr fun x => by ring
/-- `∫ a p q = -∫ p q - ∫ a q - ∫ a p - (w/u) ∫ a q / x + (1/u) ∫ a p / (1 - x)`. -/
theorem i9M3_apq {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {Vpq Vaq Vap P6 P7 : ℝ}
    (hpq : IntervalIntegrable (fun x => Real.log x * Real.log (1 - x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log (1 - x) = Vpq)
    (haq : IntervalIntegrable (fun x => Real.log (1 - x) * Real.log (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (1 - x) * Real.log (w + (1 - w) * x) = Vaq)
    (hap : IntervalIntegrable (fun x => Real.log x * Real.log (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log (w + (1 - w) * x) = Vap)
    (hP6 : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - x) / x) volume
        0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - x) / x = P6)
    (hP7 : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log x / (1 - x)) volume
        0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log x / (1 - x) = P7) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log x * Real.log (1 - x))
        volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log x * Real.log (1 - x) = -Vpq - Vaq -
          Vap - w / (1 - w) * P6 + P7 / (1 - w) := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hu0 : (1 - w) ≠ 0 := hu.ne'
  have hr := i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M3_zero_step) hpq (1)) haq
      (1)) hap (1)) hP6 (w / (1 - w))) hP7 (-(1 / (1 - w)))
  have hm := i9M3_intervalIntegrable_mul3 hw (by fun_prop) (i9M3_absA hw) (i9M3_absP hw)
      (i9M3_absQ hw)
  have tA0 := i9M3_tendsto_A w (Ioi 0) 0
  have tA1 := i9M3_tendsto_A w (Iio 1) 1
  have ta0 := i9M3_tendsto_logA hw (Ioi 0) le_rfl
  have ta1 := i9M3_tendsto_logA hw (Iio 1) zero_le_one
  have tb0 := i9M3_tendsto_logB hw (Ioi 0) zero_le_one
  have tb1 := i9M3_tendsto_logB hw (Iio 1) le_rfl
  have tp1 := i9M3_tendsto_log_one (Iio 1)
  have tq0 := i9M3_tendsto_log_one_sub_zero (Ioi 0)
  have tx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have h := i9M3_ibp (L0 := 0) (L1 := 0)
    (Φ := fun x => (w + (1 - w) * x) / (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x *
        Real.log (1 - x))) ?_ hm hr ?_ ?_
  · exact ⟨h.1, h.2.trans (by ring)⟩
  · intro x hx
    have hA := i9M2_A_pos hw hx.1.le
    have hB := i9M2_B_pos hw hx.2.le
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hAne := hA.ne'
    have hBne := hB.ne'
    have h1 := i9M2_hasDerivAt_A w x
    have hid := hasDerivAt_id x
    have ha := h1.log hA.ne'
    have hb := (i9M2_hasDerivAt_B w x).log hB.ne'
    have hp := Real.hasDerivAt_log hx0
    have hq := (hid.const_sub 1).log hx1
    refine ((h1.div_const (1 - w)).mul ((ha.mul hp).mul hq)).congr_deriv ?_
    simp only [id, Pi.mul_apply]
    field_simp
    ring
  · have h := ((tA0.div_const (1 - w)).mul ta0).mul tendsto_log_mul_log_one_sub_zero
    rw [mul_zero] at h
    exact h.congr fun x => by ring
  · have hg := ((tA1.div_const (1 - w)).mul tp1).mul i9M3_tendsto_one_sub_mul_log_one_sub
    rw [mul_zero] at hg
    exact (i9M3_tendsto_logA_mul_one hw (hg.congr (f₂ := fun x =>
      (1 - x) * ((w + (1 - w) * x) / (1 - w) * Real.log x * Real.log (1 - x))) fun x => by
          ring)).congr fun x => by ring
/-- `∫ a b p = -∫ b p - ∫ a p - ∫ a b + ((1 + w)/u) ∫ u a p / B - (w/u) ∫ a b / x`. -/
theorem i9M3_abp {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) {Vbp Vap Vab P8 P9 : ℝ}
    (hbp : IntervalIntegrable (fun x => Real.log x * Real.log (1 - (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log (1 - (1 - w) * x) = Vbp)
    (hap : IntervalIntegrable (fun x => Real.log x * Real.log (w + (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log x * Real.log (w + (1 - w) * x) = Vap)
    (hab : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x))
        volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) = Vab)
    (hP8 : IntervalIntegrable (fun x => (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (1 -
        (1 - w) * x)) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, (1 - w) * (Real.log (w + (1 - w) * x) * Real.log x) / (1 - (1 - w) * x) =
          P8)
    (hP9 : IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) /
        x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) / x = P9) :
    IntervalIntegrable (fun x => Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) *
        Real.log x) volume 0 1 ∧
      ∫ x in (0 : ℝ)..1, Real.log (w + (1 - w) * x) * Real.log (1 - (1 - w) * x) * Real.log x =
          -Vbp - Vap - Vab + (1 + w) / (1 - w) * P8 - w / (1 - w) * P9 := by
  have hu : 0 < 1 - w := by linarith [hw.2]
  have hu0 : (1 - w) ≠ 0 := hu.ne'
  have hr := i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M2_step (i9M3_zero_step) hbp (1)) hap
      (1)) hab (1)) hP8 (-((1 + w) / (1 - w)))) hP9 (w / (1 - w))
  have hm := i9M3_intervalIntegrable_mul3 hw (by fun_prop) (i9M3_absA hw) (i9M3_absB' hw)
      (i9M3_absP hw)
  have tA0 := i9M3_tendsto_A w (Ioi 0) 0
  have tA1 := i9M3_tendsto_A w (Iio 1) 1
  have ta0 := i9M3_tendsto_logA hw (Ioi 0) le_rfl
  have ta1 := i9M3_tendsto_logA hw (Iio 1) zero_le_one
  have tb0 := i9M3_tendsto_logB hw (Ioi 0) zero_le_one
  have tb1 := i9M3_tendsto_logB hw (Iio 1) le_rfl
  have tp1 := i9M3_tendsto_log_one (Iio 1)
  have tq0 := i9M3_tendsto_log_one_sub_zero (Ioi 0)
  have tx1 : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    i9M2_tendsto_of_continuousAt continuousAt_id
  have h := i9M3_ibp (L0 := 0) (L1 := 0)
    (Φ := fun x => (w + (1 - w) * x) / (1 - w) * (Real.log (w + (1 - w) * x) * Real.log (1 - (1 -
        w) * x) * Real.log x)) ?_ hm hr ?_ ?_
  · exact ⟨h.1, h.2.trans (by ring)⟩
  · intro x hx
    have hA := i9M2_A_pos hw hx.1.le
    have hB := i9M2_B_pos hw hx.2.le
    have hx0 : x ≠ 0 := hx.1.ne'
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have hAne := hA.ne'
    have hBne := hB.ne'
    have h1 := i9M2_hasDerivAt_A w x
    have hid := hasDerivAt_id x
    have ha := h1.log hA.ne'
    have hb := (i9M2_hasDerivAt_B w x).log hB.ne'
    have hp := Real.hasDerivAt_log hx0
    have hq := (hid.const_sub 1).log hx1
    refine ((h1.div_const (1 - w)).mul ((ha.mul hb).mul hp)).congr_deriv ?_
    simp only [Pi.mul_apply]
    field_simp
    ring
  · have h := ((tA0.div_const (1 - w)).mul ta0).mul
      (i9M2_tendsto_log_mul_log_one_sub (t := 1 - w) hu.le (by linarith [hw.1]))
    rw [mul_zero] at h
    exact h.congr fun x => by ring
  · simpa using (tA1.div_const (1 - w)).mul ((ta1.mul tb1).mul tp1)
end QED.ThreeLoopD
