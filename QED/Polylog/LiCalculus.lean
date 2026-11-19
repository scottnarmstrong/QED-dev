/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.LiN
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ExtendFrom

/-!
# Calculus of the polylogarithms `Li k` along a curve

Tools for verifying polylogarithmic antiderivatives: the chain rule for `Li k ∘ f`, the two
`Li₃`-free combinations

* `Li 3 f - log f · Li 2 f`, with derivative `log f · log (1 - f) · f'/f`, and
* `Li 4 f - log f · Li 3 f`, with derivative `-log f · Li 2 f · f'/f`,

bounds and limits used at the endpoints of an interval, and the values `Li 4 (±1)`.
Here `log` is `Real.log`, so `log f = log |f|` and the formulas hold for `f < 0` as well.

## Main results

* `QED.Polylog.Li_four_one`, `QED.Polylog.Li_four_neg_one`: `Li 4 1 = π⁴/90`,
  `Li 4 (-1) = -7π⁴/720`.
* `QED.Polylog.abs_Li_le`: `|Li k y| ≤ (π²/6) |y|` for `2 ≤ k`, `|y| ≤ 1`.
* `QED.Polylog.abs_Li_sub_le`: `|Li k x - Li k y| ≤ 2 |x - y|` for `1 ≤ k`, `|x|, |y| ≤ 1/2`.
* `QED.Polylog.hasDerivAt_Li_comp`, `QED.Polylog.hasDerivAt_Li_two_comp`: the chain rule.
* `QED.Polylog.hasDerivAt_Li_three_sub_comp`, `QED.Polylog.hasDerivAt_Li_four_sub_comp`.
* `QED.Polylog.tendsto_Li_comp`, `QED.Polylog.tendsto_log_mul_Li_comp`: endpoint limits.
* `QED.Polylog.eq_of_hasDerivAt_zero_of_tendsto`: a function with derivative `0` on `(a, b)`
  equals its right limit at `a`.
* `QED.Polylog.intervalIntegrable_and_integral_eq_of_nonneg'`, `…_of_nonpos'`: a sign-definite
  derivative on `(a, b)` of a function with one-sided limits at `a` and `b` is integrable, with
  integral the difference of the limits.
-/

public section

open Real Set Filter Topology MeasureTheory

namespace QED.Polylog

/-! ### Values at `±1` -/

/-- `Li 4 1 = ζ(4) = π ^ 4 / 90`. -/
theorem Li_four_one : Li 4 1 = π ^ 4 / 90 := by
  have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_four
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at this
  simpa [Li] using this.tsum_eq

/-- `Li 4 (-1) = -(7/8) ζ(4) = -7 π ^ 4 / 720`. -/
theorem Li_four_neg_one : Li 4 (-1) = -(7 / 720) * π ^ 4 := by
  have := Li_add_Li_neg (k := 4) (by norm_num) (x := 1) (by norm_num)
  rw [one_pow, Li_four_one] at this
  linarith

/-! ### Bounds -/

/-- `|Li k y| ≤ (π ^ 2 / 6) |y|` for `2 ≤ k` and `|y| ≤ 1`. -/
theorem abs_Li_le {k : ℕ} (hk : 2 ≤ k) {y : ℝ} (hy : |y| ≤ 1) : |Li k y| ≤ π ^ 2 / 6 * |y| := by
  rw [← mul_tsum_pow_div_eq_Li, abs_mul, mul_comm]
  gcongr
  have hs : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  rw [← Real.norm_eq_abs]
  refine tsum_of_norm_bounded hs fun n => ?_
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
  rw [Real.norm_eq_abs, abs_div, abs_pow y,
    abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ k)]
  calc |y| ^ n / ((n : ℝ) + 1) ^ k ≤ 1 / ((n : ℝ) + 1) ^ k :=
        div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg y) hy) (by positivity)
    _ ≤ 1 / ((n : ℝ) + 1) ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 hk)

/-- On `[-1/2, 1/2]` the polylogarithm `Li k` (`1 ≤ k`) is `2`-Lipschitz. -/
theorem abs_Li_sub_le {k : ℕ} (hk : 1 ≤ k) {x y : ℝ} (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    |Li k x - Li k y| ≤ 2 * |x - y| := by
  have hd : ∀ z ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      HasDerivWithinAt (Li k) (∑' n : ℕ, z ^ n / ((n : ℝ) + 1) ^ (k - 1)) (Icc (-(1 / 2)) (1 / 2))
        z := fun z hz =>
    (hasDerivAt_Li_tsum hk ((abs_le.mpr hz).trans_lt (by norm_num))).hasDerivWithinAt
  have hb : ∀ z ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      ‖∑' n : ℕ, z ^ n / ((n : ℝ) + 1) ^ (k - 1)‖ ≤ 2 := by
    intro z hz
    have hz' : |z| ≤ 1 / 2 := abs_le.mpr hz
    have hs : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := by
      have := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      norm_num at this ⊢
      exact this
    refine tsum_of_norm_bounded hs fun n => ?_
    have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ (k - 1) :=
      one_le_pow₀ (by linarith [n.cast_nonneg (α := ℝ)])
    rw [Real.norm_eq_abs, abs_div, abs_pow z,
      abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ (k - 1))]
    calc |z| ^ n / ((n : ℝ) + 1) ^ (k - 1) ≤ |z| ^ n := div_le_self (by positivity) h1
      _ ≤ (1 / 2) ^ n := pow_le_pow_left₀ (abs_nonneg z) hz' n
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc _ _)
    (abs_le.mp hy) (abs_le.mp hx)
  simpa [Real.norm_eq_abs] using this

/-! ### The chain rule -/

/-- The chain rule for `Li k ∘ f` (`1 ≤ k`) at a point where `0 < |f x| < 1`. -/
theorem hasDerivAt_Li_comp {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (h1 : |f x| < 1) (h0 : f x ≠ 0) :
    HasDerivAt (fun y => Li k (f y)) (Li (k - 1) (f x) * (f' / f x)) x := by
  have h := (hasDerivAt_Li hk h1 h0).comp x hf
  refine h.congr_deriv ?_
  field_simp

/-- The chain rule for `Li 2 ∘ f` at a point where `0 < |f x| < 1`. -/
theorem hasDerivAt_Li_two_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (h1 : |f x| < 1) (h0 : f x ≠ 0) :
    HasDerivAt (fun y => Li 2 (f y)) (-log (1 - f x) * (f' / f x)) x := by
  have h := hasDerivAt_Li_comp (k := 2) (by norm_num) hf h1 h0
  rwa [show 2 - 1 = 1 from rfl, Li_one h1] at h

/-- `Li 3 f - log f · Li 2 f` has derivative `log f · log (1 - f) · f'/f`. -/
theorem hasDerivAt_Li_three_sub_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (h1 : |f x| < 1) (h0 : f x ≠ 0) :
    HasDerivAt (fun y => Li 3 (f y) - log (f y) * Li 2 (f y))
      (log (f x) * log (1 - f x) * (f' / f x)) x := by
  have h3 := hasDerivAt_Li_comp (k := 3) (by norm_num) hf h1 h0
  have h2 := hasDerivAt_Li_two_comp hf h1 h0
  have hl := hf.log h0
  refine (h3.sub (hl.mul h2)).congr_deriv ?_
  simp only [show 3 - 1 = 2 from rfl]
  ring

/-- `Li 4 f - log f · Li 3 f` has derivative `-log f · Li 2 f · f'/f`. -/
theorem hasDerivAt_Li_four_sub_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    (h1 : |f x| < 1) (h0 : f x ≠ 0) :
    HasDerivAt (fun y => Li 4 (f y) - log (f y) * Li 3 (f y))
      (-(log (f x) * Li 2 (f x)) * (f' / f x)) x := by
  have h4 := hasDerivAt_Li_comp (k := 4) (by norm_num) hf h1 h0
  have h3 := hasDerivAt_Li_comp (k := 3) (by norm_num) hf h1 h0
  have hl := hf.log h0
  refine (h4.sub (hl.mul h3)).congr_deriv ?_
  simp only [show 4 - 1 = 3 from rfl, show 3 - 1 = 2 from rfl]
  ring

/-! ### The same, with the derivative data supplied in a reduced form -/

/-- `Li 2 ∘ f`, with `f'/f = d` and `log (1 - f) = ℓ₁` supplied. -/
theorem hasDerivAt_Li_two_of {f : ℝ → ℝ} {f' x d ℓ₁ : ℝ} (hf : HasDerivAt f f' x)
    (h1 : |f x| < 1) (h0 : f x ≠ 0) (hd : f' / f x = d) (hl₁ : log (1 - f x) = ℓ₁) :
    HasDerivAt (fun y => Li 2 (f y)) (-ℓ₁ * d) x := by
  have h := hasDerivAt_Li_two_comp hf h1 h0
  rwa [hd, hl₁] at h

/-- `Li 3 ∘ f`, with `f'/f = d` and `Li 2 f = L` supplied. -/
theorem hasDerivAt_Li_three_of {f : ℝ → ℝ} {f' x d L : ℝ} (hf : HasDerivAt f f' x)
    (h1 : |f x| < 1) (h0 : f x ≠ 0) (hd : f' / f x = d) (hL : Li 2 (f x) = L) :
    HasDerivAt (fun y => Li 3 (f y)) (L * d) x := by
  have h := hasDerivAt_Li_comp (k := 3) (by norm_num) hf h1 h0
  rwa [show 3 - 1 = 2 from rfl, hd, hL] at h

/-- `Li 3 f - log f · Li 2 f`, with `f'/f = d`, `log f = ℓ`, `log (1 - f) = ℓ₁` supplied. -/
theorem hasDerivAt_Li_three_sub_of {f : ℝ → ℝ} {f' x d ℓ ℓ₁ : ℝ} (hf : HasDerivAt f f' x)
    (h1 : |f x| < 1) (h0 : f x ≠ 0) (hd : f' / f x = d) (hl : log (f x) = ℓ)
    (hl₁ : log (1 - f x) = ℓ₁) :
    HasDerivAt (fun y => Li 3 (f y) - log (f y) * Li 2 (f y)) (ℓ * ℓ₁ * d) x := by
  have h := hasDerivAt_Li_three_sub_comp hf h1 h0
  rwa [hd, hl, hl₁] at h

/-- `Li 4 f - log f · Li 3 f`, with `f'/f = d`, `log f = ℓ`, `Li 2 f = L` supplied. -/
theorem hasDerivAt_Li_four_sub_of {f : ℝ → ℝ} {f' x d ℓ L : ℝ} (hf : HasDerivAt f f' x)
    (h1 : |f x| < 1) (h0 : f x ≠ 0) (hd : f' / f x = d) (hl : log (f x) = ℓ)
    (hL : Li 2 (f x) = L) :
    HasDerivAt (fun y => Li 4 (f y) - log (f y) * Li 3 (f y)) (-(ℓ * L) * d) x := by
  have h := hasDerivAt_Li_four_sub_comp hf h1 h0
  rwa [hd, hl, hL] at h

/-- `log ∘ f`, with `f'/f = d` supplied. -/
theorem hasDerivAt_log_of {f : ℝ → ℝ} {f' x d : ℝ} (hf : HasDerivAt f f' x) (h0 : f x ≠ 0)
    (hd : f' / f x = d) : HasDerivAt (fun y => log (f y)) d x := by
  have h := hf.log h0
  rwa [hd] at h

/-! ### Limits -/

/-- `Li k ∘ g → Li k a` (`2 ≤ k`) when `g → a ∈ [-1, 1]` eventually inside `[-1, 1]`. -/
theorem tendsto_Li_comp {α : Type*} {l : Filter α} {k : ℕ} (hk : 2 ≤ k) {g : α → ℝ} {a : ℝ}
    (ha : a ∈ Icc (-1 : ℝ) 1) (hg : Tendsto g l (𝓝 a)) (hgs : ∀ᶠ x in l, g x ∈ Icc (-1 : ℝ) 1) :
    Tendsto (fun x => Li k (g x)) l (𝓝 (Li k a)) :=
  (continuousOn_Li hk a ha).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hg, hgs⟩)

/-- `g log g → 0` when `g → 0`. -/
theorem tendsto_mul_log_comp {α : Type*} {l : Filter α} {g : α → ℝ} (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => g x * log (g x)) l (𝓝 0) := by
  have := (continuous_mul_log.tendsto 0).comp hg
  simpa [Function.comp_def] using this

/-- `log g · Li k g → 0` (`2 ≤ k`) when `g → 0` eventually inside `[-1, 1]`. -/
theorem tendsto_log_mul_Li_comp {α : Type*} {l : Filter α} {k : ℕ} (hk : 2 ≤ k) {g : α → ℝ}
    (hg : Tendsto g l (𝓝 0)) (hgs : ∀ᶠ x in l, |g x| ≤ 1) :
    Tendsto (fun x => log (g x) * Li k (g x)) l (𝓝 0) := by
  have hb : Tendsto (fun x => π ^ 2 / 6 * |g x * log (g x)|) l (𝓝 0) := by
    simpa using ((tendsto_mul_log_comp hg).abs).const_mul (π ^ 2 / 6)
  refine squeeze_zero_norm' (hgs.mono fun x hx => ?_) hb
  rw [Real.norm_eq_abs, abs_mul, abs_mul, mul_comm (|g x|)]
  calc |log (g x)| * |Li k (g x)| ≤ |log (g x)| * (π ^ 2 / 6 * |g x|) :=
        mul_le_mul_of_nonneg_left (abs_Li_le hk hx) (abs_nonneg _)
    _ = π ^ 2 / 6 * (|log (g x)| * |g x|) := by ring

/-- A function with derivative `0` on `(a, b)` equals its right limit at `a` there. -/
theorem eq_of_hasDerivAt_zero_of_tendsto {F : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F 0 x) (hlim : Tendsto F (𝓝[>] a) (𝓝 c)) :
    ∀ x ∈ Ioo a b, F x = c := by
  intro x hx
  have hconst : ∀ y ∈ Ioo a b, F y = F x := fun y hy =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by simpa using (hd z hz).deriv) hy hx
  refine tendsto_nhds_unique ?_ hlim
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hab] with y hy
  exact (hconst y hy).symm

/-! ### Integration of sign-definite derivatives -/

/-- A nonnegative function on `(a, b)` with an antiderivative having one-sided limits at `a` and
`b` is interval integrable on `[a, b]`, with integral the difference of the limits. -/
theorem intervalIntegrable_and_integral_eq_of_nonneg' {F f : ℝ → ℝ} {a b A B : ℝ} (hab : a < b)
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

/-- The nonpositive version of `intervalIntegrable_and_integral_eq_of_nonneg'`. -/
theorem intervalIntegrable_and_integral_eq_of_nonpos' {F f : ℝ → ℝ} {a b A B : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x) (hf : ∀ x ∈ Ioo a b, f x ≤ 0)
    (h0 : Tendsto F (𝓝[>] a) (𝓝 A)) (h1 : Tendsto F (𝓝[<] b) (𝓝 B)) :
    IntervalIntegrable f volume a b ∧ ∫ x in a..b, f x = B - A := by
  obtain ⟨hi, hv⟩ := intervalIntegrable_and_integral_eq_of_nonneg' (F := fun x => -F x)
    (f := fun x => -f x) hab (fun x hx => (hd x hx).neg) (fun x hx => neg_nonneg.2 (hf x hx))
    h0.neg h1.neg
  have hi' : IntervalIntegrable (fun x => - -f x) volume a b := hi.neg
  refine ⟨by simpa only [neg_neg] using hi', ?_⟩
  rw [intervalIntegral.integral_neg] at hv
  linarith

end QED.Polylog
