/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLBasic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Harmonic polylogarithms: calculus

Analytic properties of the harmonic polylogarithms `QED.Polylog.HPL.hpl` on `(0, 1)`. They are
proved together, by induction on the word, from three bounds:

* near `0`, a word that is not all zeros satisfies `|H(w; t)| ≤ C √t` on `(0, b]`, `b < 1`;
  the all-zero words are `logⁿ t / n!`, bounded by `C t^(-δ)` for every `δ > 0`;
* near `1`, every word satisfies `|H(w; t)| ≤ C (1 - t)^(-ε)` on `[1/2, 1)`, for every `ε > 0`.

Hence the integrand `f a · H(w)` of each recursion step is bounded by `K t^(-1/2)` near `0`, so
it is integrable on `[0, x]` for `x < 1`, and the fundamental theorem of calculus applies.

## Main results

* `QED.Polylog.HPL.continuousOn_hpl`: `H(w)` is continuous on `(0, 1)`.
* `QED.Polylog.HPL.hasDerivAt_hpl_cons`: `d/dx H(a · w; x) = f a x · H(w; x)` on `(0, 1)`,
  for every word, including the all-zero words.
* `QED.Polylog.HPL.intervalIntegrable_kernel_mul_hpl`: the integrand of the recursion is
  integrable on `[0, x]` for `0 ≤ x < 1`.
* `QED.Polylog.HPL.abs_hpl_le_sqrt`, `QED.Polylog.HPL.tendsto_hpl_zero`: a word that is not
  all zeros has `H(w; x) = O(√x)`, so `H(w; x) → 0` as `x → 0⁺`.
* `QED.Polylog.HPL.tendsto_hpl_mul_hpl_zero`: `H(u; x) H(v; x) → 0` as `x → 0⁺` unless both
  words are all zeros.
* `QED.Polylog.HPL.abs_hpl_le_one_sub_rpow`: `H(w; x) = O((1 - x)^(-ε))` as `x → 1⁻`.
* `QED.Polylog.HPL.tendsto_hpl_one`: if the first letter is not `1` then
  `H(a · w; x) → H(a · w; 1)` as `x → 1⁻`, where `H(a · w; 1) = ∫₀¹ f a · H(w)`.
* `QED.Polylog.HPL.eq_hpl_cons_of_hasDerivAt`: an antiderivative of `f a · H(w)` on `(0, 1)`
  tending to `0` at `0⁺` is `H(a · w)`, when `a · w` is not all zeros.
-/

public section

open Real Set Filter Topology MeasureTheory

namespace QED.Polylog.HPL

/-! ### The kernels -/

/-- The kernels are continuous on `(0, 1)`. -/
theorem continuousOn_kernel (a : Letter) : ContinuousOn a.kernel (Ioo 0 1) := by
  cases a with
  | zero => exact continuousOn_inv₀.mono fun t ht => ht.1.ne'
  | one =>
    exact (continuousOn_const.sub continuousOn_id).inv₀ fun t ht =>
      (sub_pos.2 ht.2).ne'
  | negOne =>
    exact (continuousOn_const.add continuousOn_id).inv₀ fun t ht =>
      (by linarith [ht.1] : (0 : ℝ) < 1 + t).ne'

/-- On `[0, b]`, `b < 1`, the kernels of `1` and `-1` are bounded by `1 / (1 - b)`. -/
theorem abs_kernel_le {a : Letter} (ha : a ≠ Letter.zero) {b t : ℝ} (hb : b < 1) (ht0 : 0 ≤ t)
    (htb : t ≤ b) : |a.kernel t| ≤ (1 - b)⁻¹ := by
  have h1b : 0 < 1 - b := by linarith
  cases a with
  | zero => exact absurd rfl ha
  | one =>
    rw [Letter.kernel_one, abs_of_pos (inv_pos.2 (by linarith))]
    exact inv_anti₀ h1b (by linarith)
  | negOne =>
    rw [Letter.kernel_negOne, abs_of_pos (inv_pos.2 (by linarith))]
    calc (1 + t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      _ ≤ (1 - b)⁻¹ := one_le_inv₀ h1b |>.2 (by linarith)

/-- On `[1/2, 1)`, the kernels of `0` and `-1` are bounded by `2`. -/
theorem abs_kernel_le_two {a : Letter} (ha : a ≠ Letter.one) {t : ℝ} (ht : t ∈ Ico (1 / 2) 1) :
    |a.kernel t| ≤ 2 := by
  have ht0 : 0 < t := by linarith [ht.1]
  cases a with
  | zero =>
    rw [Letter.kernel_zero, abs_of_pos (inv_pos.2 ht0)]
    calc t⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) ht.1
      _ = 2 := by norm_num
  | one => exact absurd rfl ha
  | negOne =>
    rw [Letter.kernel_negOne, abs_of_pos (inv_pos.2 (by linarith))]
    calc (1 + t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      _ ≤ 2 := by norm_num

/-! ### Elementary bounds -/

/-- `|log t| ^ n ≤ C t ^ (-δ)` on `(0, 1]`, for every `δ > 0`. -/
theorem abs_log_pow_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, |log t| ^ n ≤ C * t ^ (-δ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, zero_le_one, fun t ht => ?_⟩
    rw [pow_zero, one_mul]
    exact one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 (by linarith)
  set ε := δ / n with hε
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hε0 : 0 < ε := div_pos hδ hn'
  refine ⟨(1 / ε) ^ n, by positivity, fun t ht => ?_⟩
  have h1 := abs_log_mul_self_rpow_lt t ε ht.1 ht.2 hε0
  have htε : 0 < t ^ ε := rpow_pos_of_pos ht.1 ε
  have h2 : |log t| ≤ 1 / ε * t ^ (-ε) := by
    rw [abs_mul, abs_of_pos htε] at h1
    rw [rpow_neg ht.1.le, ← div_eq_mul_inv, le_div_iff₀ htε]
    exact h1.le
  calc |log t| ^ n ≤ (1 / ε * t ^ (-ε)) ^ n := pow_le_pow_left₀ (abs_nonneg _) h2 n
    _ = (1 / ε) ^ n * t ^ (-δ) := by
      rw [mul_pow, ← rpow_natCast (t ^ (-ε)), ← rpow_mul ht.1.le]
      congr 2
      rw [hε]
      field_simp

/-- `|∫₀ˣ g| ≤ K x ^ (r + 1) / (r + 1)` when `|g t| ≤ K t ^ r` on `(0, x]`, `-1 < r`. -/
theorem abs_integral_le_of_le_rpow {g : ℝ → ℝ} {K r x : ℝ} (hx : 0 ≤ x) (hr : -1 < r)
    (hg : ∀ t ∈ Ioc 0 x, |g t| ≤ K * t ^ r) :
    |∫ t in (0 : ℝ)..x, g t| ≤ K * (x ^ (r + 1) / (r + 1)) := by
  have hint : IntervalIntegrable (fun t => K * t ^ r) volume 0 x :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul K
  have := intervalIntegral.norm_integral_le_of_norm_le hx
    (ae_of_all _ fun t ht => by rw [Real.norm_eq_abs]; exact hg t ht) hint
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr),
    zero_rpow (by linarith), sub_zero] at this
  exact this

/-- A function continuous on `(0, 1)` and bounded by `K t ^ (-1/2)` on `(0, b]` is integrable
on `[0, b]`. -/
theorem intervalIntegrable_of_le_rpow {g : ℝ → ℝ} {K b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1)
    (hc : ContinuousOn g (Ioo 0 1)) (hg : ∀ t ∈ Ioc 0 b, |g t| ≤ K * t ^ (-(1 / 2) : ℝ)) :
    IntervalIntegrable g volume 0 b := by
  have hint : IntervalIntegrable (fun t => K * t ^ (-(1 / 2) : ℝ)) volume 0 b :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb0] at hint ⊢
  refine hint.mono' ((hc.mono fun t ht => ⟨ht.1, by linarith [ht.2]⟩).aestronglyMeasurable
    measurableSet_Ioc) ?_
  exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => by
    rw [Real.norm_eq_abs]; exact hg t ht)

/-- `∫_{1/2}^x |g| ≤ K ((1/2) ^ (r + 1) - (1 - x) ^ (r + 1)) / (r + 1)` when
`|g t| ≤ K (1 - t) ^ r` on `[1/2, 1)`, `r ≠ -1`, `x ∈ [1/2, 1)`. -/
theorem abs_integral_half_le {g : ℝ → ℝ} {K r x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1)
    (hr : r ≠ -1) (hg : ∀ t ∈ Ico (1 / 2 : ℝ) 1, |g t| ≤ K * (1 - t) ^ r) :
    |∫ t in (1 / 2 : ℝ)..x, g t| ≤
      K * (((1 / 2 : ℝ) ^ (r + 1) - (1 - x) ^ (r + 1)) / (r + 1)) := by
  have hcont : ContinuousOn (fun t : ℝ => K * (1 - t) ^ r) (uIcc (1 / 2) x) := by
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    exact (continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).rpow_const
      (Or.inl (by show (1 : ℝ) - t ≠ 0; exact (sub_pos.2 (by linarith [ht.2, hx.2])).ne'))))
      |>.continuousWithinAt
  have := intervalIntegral.norm_integral_le_of_norm_le hx.1
    (ae_of_all _ fun t ht => by
      rw [Real.norm_eq_abs]
      exact hg t ⟨ht.1.le, lt_of_le_of_lt ht.2 hx.2⟩) (hcont.intervalIntegrable (μ := volume))
  rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun s => s ^ r) 1,
    integral_rpow (Or.inr ⟨hr, ?_⟩)] at this
  · convert this using 3
    norm_num
  · rw [uIcc_of_le (by linarith [hx.1])]
    intro h
    linarith [h.1, hx.2]

/-- A function with derivative `0` on `(a, b)` equals its left limit at `b` there. -/
theorem eq_of_hasDerivAt_zero_of_tendsto_left {F : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F 0 x) (hlim : Tendsto F (𝓝[<] b) (𝓝 c)) :
    ∀ x ∈ Ioo a b, F x = c := by
  intro x hx
  have hconst : ∀ y ∈ Ioo a b, F y = F x := fun y hy =>
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by simpa using (hd z hz).deriv) hy hx
  refine tendsto_nhds_unique ?_ hlim
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with y hy
  exact (hconst y hy).symm

/-- A function with derivative `0` on `(a, b)` equals its right limit at `a` there. -/
theorem eq_of_hasDerivAt_zero_of_tendsto_right {F : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
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

/-! ### The all-zero words -/

/-- `d/dx logⁿ⁺¹ x / (n + 1)! = (1/x) logⁿ x / n!` for `0 < x`. -/
theorem hasDerivAt_log_pow_div {n : ℕ} {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => log x ^ (n + 1) / ((n + 1).factorial : ℝ))
      (x⁻¹ * (log x ^ n / (n.factorial : ℝ))) x := by
  have h := ((hasDerivAt_log hx.ne').pow (n + 1)).div_const ((n + 1).factorial : ℝ)
  refine h.congr_deriv ?_
  rw [Nat.factorial_succ]
  push_cast
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The bound `|logⁿ t / n!| ≤ C t ^ (-δ)` on `(0, 1]`. -/
theorem abs_hpl_allZero_le {w : List Letter} (hw : AllZero w) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, |hpl w t| ≤ C * t ^ (-δ) := by
  obtain ⟨C, hC, h⟩ := abs_log_pow_le w.length hδ
  refine ⟨C, hC, fun t ht => ?_⟩
  rw [hpl_of_allZero hw, abs_div, abs_pow, Nat.abs_cast]
  calc |log t| ^ w.length / (w.length.factorial : ℝ) ≤ |log t| ^ w.length :=
        div_le_self (by positivity) (Nat.one_le_cast.2 (Nat.factorial_pos _))
    _ ≤ C * t ^ (-δ) := h t ht

/-- `|log t| ≤ 1` on `[1/2, 1)`. -/
theorem abs_log_le_one {t : ℝ} (ht : t ∈ Ico (1 / 2 : ℝ) 1) : |log t| ≤ 1 := by
  have ht0 : 0 < t := by linarith [ht.1]
  rw [abs_of_nonpos (log_nonpos ht0.le ht.2.le), ← log_inv]
  calc log t⁻¹ ≤ t⁻¹ - 1 := log_le_sub_one_of_pos (inv_pos.2 ht0)
    _ ≤ 1 := by
      have : t⁻¹ ≤ 2 := by
        calc t⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) ht.1
          _ = 2 := by norm_num
      linarith

/-- `1 ≤ (1 - t) ^ (-ε)` on `[1/2, 1)` for `0 ≤ ε`. -/
theorem one_le_one_sub_rpow {t ε : ℝ} (ht : t ∈ Ico (1 / 2 : ℝ) 1) (hε : 0 ≤ ε) :
    1 ≤ (1 - t) ^ (-ε) :=
  one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith [ht.2]) (by linarith [ht.1])
    (by linarith)

/-! ### The inductive invariant -/

/-- The properties of `H(w)` carried through the induction on the word. -/
private def Good (w : List Letter) : Prop :=
  ContinuousOn (hpl w) (Ioo 0 1) ∧
  (¬AllZero w → ∀ b < 1, ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc 0 b, |hpl w t| ≤ C * t ^ (1 / 2 : ℝ)) ∧
  (∀ ε : ℝ, 0 < ε → ∃ C, 0 ≤ C ∧ ∀ t ∈ Ico (1 / 2 : ℝ) 1, |hpl w t| ≤ C * (1 - t) ^ (-ε))

/-- The integrand of a recursion step is bounded by `K t ^ (-1/2)` on `(0, b]`. -/
private theorem integrand_le {a : Letter} {w : List Letter} (hw : Good w)
    (ha : ¬AllZero (a :: w)) {b : ℝ} (hb : b < 1) :
    ∃ K, 0 ≤ K ∧ ∀ t ∈ Ioc 0 b, |a.kernel t * hpl w t| ≤ K * t ^ (-(1 / 2) : ℝ) := by
  have h1b : 0 < 1 - b := by linarith
  by_cases hz : AllZero w
  · have ha0 : a ≠ Letter.zero := fun h => ha (allZero_cons.2 ⟨h, hz⟩)
    obtain ⟨C, hC, h⟩ := abs_hpl_allZero_le hz (δ := 1 / 2) (by norm_num)
    refine ⟨(1 - b)⁻¹ * C, by positivity, fun t ht => ?_⟩
    rw [abs_mul, mul_assoc]
    exact mul_le_mul (abs_kernel_le ha0 hb ht.1.le ht.2) (h t ⟨ht.1, by linarith [ht.2]⟩)
      (abs_nonneg _) (by positivity)
  · obtain ⟨C, hC, h⟩ := hw.2.1 hz b hb
    by_cases ha0 : a = Letter.zero
    · subst ha0
      refine ⟨C, hC, fun t ht => ?_⟩
      rw [Letter.kernel_zero, abs_mul, abs_of_pos (inv_pos.2 ht.1)]
      calc t⁻¹ * |hpl w t| ≤ t⁻¹ * (C * t ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (h t ht) (inv_nonneg.2 ht.1.le)
        _ = C * t ^ (-(1 / 2) : ℝ) := by
          rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by norm_num, rpow_sub_one ht.1.ne']
          field_simp
    · refine ⟨(1 - b)⁻¹ * C, by positivity, fun t ht => ?_⟩
      rw [abs_mul, mul_assoc]
      refine mul_le_mul (abs_kernel_le ha0 hb ht.1.le ht.2) ?_ (abs_nonneg _) (by positivity)
      refine (h t ht).trans (mul_le_mul_of_nonneg_left ?_ hC)
      exact rpow_le_rpow_of_exponent_ge ht.1 (by linarith [ht.2]) (by norm_num)

private theorem integrand_continuousOn (a : Letter) {w : List Letter} (hw : Good w) :
    ContinuousOn (fun t => a.kernel t * hpl w t) (Ioo 0 1) :=
  (continuousOn_kernel a).mul hw.1

private theorem integrand_intervalIntegrable {a : Letter} {w : List Letter} (hw : Good w)
    (ha : ¬AllZero (a :: w)) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1) :
    IntervalIntegrable (fun t => a.kernel t * hpl w t) volume 0 b := by
  obtain ⟨K, -, hK⟩ := integrand_le hw ha hb
  exact intervalIntegrable_of_le_rpow hb0 hb (integrand_continuousOn a hw) hK

private theorem hasDerivAt_of_good {a : Letter} {w : List Letter} (hw : Good w)
    (ha : ¬AllZero (a :: w)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (hpl (a :: w)) (a.kernel x * hpl w x) x := by
  rw [hpl_cons_of_not_allZero ha]
  exact intervalIntegral.integral_hasDerivAt_right
    (integrand_intervalIntegrable hw ha hx.1.le hx.2)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (integrand_continuousOn a hw) x hx)
    ((integrand_continuousOn a hw).continuousAt (isOpen_Ioo.mem_nhds hx))

private theorem good_cons (a : Letter) {w : List Letter} (hw : Good w) : Good (a :: w) := by
  by_cases ha : AllZero (a :: w)
  · refine ⟨?_, fun h => absurd ha h, fun ε hε => ⟨1, zero_le_one, fun t ht => ?_⟩⟩
    · rw [show hpl (a :: w) = fun x => log x ^ (a :: w).length / ((a :: w).length.factorial : ℝ)
        from funext (hpl_of_allZero ha)]
      exact ((continuousOn_log.mono fun t ht => ht.1.ne').pow _).div_const _
    · rw [hpl_of_allZero ha, one_mul, abs_div, abs_pow, Nat.abs_cast]
      calc |log t| ^ (a :: w).length / ((a :: w).length.factorial : ℝ) ≤ 1 := by
            rw [div_le_one (by positivity)]
            calc |log t| ^ (a :: w).length ≤ 1 := pow_le_one₀ (abs_nonneg _) (abs_log_le_one ht)
              _ ≤ _ := Nat.one_le_cast.2 (Nat.factorial_pos _)
        _ ≤ (1 - t) ^ (-ε) := one_le_one_sub_rpow ht hε.le
  set g := fun t => a.kernel t * hpl w t with hg
  have hH : hpl (a :: w) = fun x => ∫ t in (0 : ℝ)..x, g t := hpl_cons_of_not_allZero ha
  refine ⟨fun x hx => (hasDerivAt_of_good hw ha hx).continuousAt.continuousWithinAt,
    fun _ b hb => ?_, fun ε hε => ?_⟩
  · -- the bound near `0`
    obtain ⟨K, hK, hKb⟩ := integrand_le hw ha hb
    refine ⟨2 * K, by positivity, fun t ht => ?_⟩
    rw [hH]
    have := abs_integral_le_of_le_rpow ht.1.le (by norm_num : (-1 : ℝ) < -(1 / 2))
      (g := g) (K := K) fun s hs => hKb s ⟨hs.1, hs.2.trans ht.2⟩
    convert this using 1
    norm_num
    ring
  · -- the bound near `1`
    have hhalf : IntervalIntegrable g volume 0 (1 / 2) :=
      integrand_intervalIntegrable hw ha (by norm_num) (by norm_num)
    have hsplit : ∀ x ∈ Ico (1 / 2 : ℝ) 1,
        hpl (a :: w) x = hpl (a :: w) (1 / 2) + ∫ t in (1 / 2 : ℝ)..x, g t := by
      intro x hx
      have hx0 : IntervalIntegrable g volume 0 x :=
        integrand_intervalIntegrable hw ha (by linarith [hx.1]) hx.2
      rw [hH]
      exact (intervalIntegral.integral_add_adjacent_intervals hhalf
        (hx0.mono_set (by
          rw [uIcc_of_le hx.1, uIcc_of_le (by linarith [hx.1] : (0 : ℝ) ≤ x)]
          exact Icc_subset_Icc (by norm_num) le_rfl))).symm
    set A := |hpl (a :: w) (1 / 2)|
    by_cases ha1 : a = Letter.one
    · subst ha1
      obtain ⟨C, hC, h⟩ := hw.2.2 ε hε
      refine ⟨A + C / ε, by positivity, fun x hx => ?_⟩
      have hb : ∀ t ∈ Ico (1 / 2 : ℝ) 1, |g t| ≤ C * (1 - t) ^ (-1 - ε) := by
        intro t ht
        have h1t : 0 < 1 - t := by linarith [ht.2]
        simp only [hg, Letter.kernel_one, abs_mul, abs_of_pos (inv_pos.2 h1t)]
        calc (1 - t)⁻¹ * |hpl w t| ≤ (1 - t)⁻¹ * (C * (1 - t) ^ (-ε)) :=
              mul_le_mul_of_nonneg_left (h t ht) (by positivity)
          _ = C * (1 - t) ^ (-1 - ε) := by
            rw [show -1 - ε = -ε - 1 by ring, rpow_sub_one h1t.ne']
            field_simp
      have hI := abs_integral_half_le hx (by linarith : (-1 - ε) ≠ -1) hb
      rw [show -1 - ε + 1 = -ε by ring] at hI
      have h1x : 0 < 1 - x := by linarith [hx.2]
      have hpos : 0 ≤ (1 / 2 : ℝ) ^ (-ε) := by positivity
      have hI' : |∫ t in (1 / 2 : ℝ)..x, g t| ≤ C / ε * (1 - x) ^ (-ε) := by
        have e : C * (((1 / 2 : ℝ) ^ (-ε) - (1 - x) ^ (-ε)) / -ε) =
            C / ε * (1 - x) ^ (-ε) - C / ε * (1 / 2 : ℝ) ^ (-ε) := by
          have := hε.ne'
          field_simp
          ring
        have : 0 ≤ C / ε * (1 / 2 : ℝ) ^ (-ε) := by positivity
        linarith
      rw [hsplit x hx]
      calc |hpl (Letter.one :: w) (1 / 2) + ∫ t in (1 / 2 : ℝ)..x, g t|
          ≤ A + C / ε * (1 - x) ^ (-ε) := (abs_add_le _ _).trans (by linarith)
        _ ≤ A * (1 - x) ^ (-ε) + C / ε * (1 - x) ^ (-ε) := by
          have := one_le_one_sub_rpow hx hε.le
          nlinarith [abs_nonneg (hpl (Letter.one :: w) (1 / 2))]
        _ = (A + C / ε) * (1 - x) ^ (-ε) := by ring
    · obtain ⟨C, hC, h⟩ := hw.2.2 (1 / 2) (by norm_num)
      refine ⟨A + 2 * C * 2, by positivity, fun x hx => ?_⟩
      have hb : ∀ t ∈ Ico (1 / 2 : ℝ) 1, |g t| ≤ (2 * C) * (1 - t) ^ (-(1 / 2) : ℝ) := by
        intro t ht
        simp only [hg, abs_mul, mul_assoc]
        exact mul_le_mul (abs_kernel_le_two ha1 ht) (h t ht) (abs_nonneg _) (by norm_num)
      have hI := abs_integral_half_le hx (by norm_num : (-(1 / 2) : ℝ) ≠ -1) hb
      have h1x : 0 < 1 - x := by linarith [hx.2]
      have hI' : |∫ t in (1 / 2 : ℝ)..x, g t| ≤ 2 * C * 2 := by
        refine hI.trans ?_
        have e : (-(1 / 2) : ℝ) + 1 = 1 / 2 := by norm_num
        rw [e]
        have h1 : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) ≤ 1 := rpow_le_one (by norm_num) (by norm_num)
          (by norm_num)
        have h2 : 0 ≤ (1 - x) ^ (1 / 2 : ℝ) := by positivity
        have : ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) - (1 - x) ^ (1 / 2 : ℝ)) / (1 / 2) ≤ 2 := by
          rw [div_le_iff₀ (by norm_num)]
          linarith
        exact mul_le_mul_of_nonneg_left this (by positivity)
      rw [hsplit x hx]
      have := one_le_one_sub_rpow hx hε.le
      calc |hpl (a :: w) (1 / 2) + ∫ t in (1 / 2 : ℝ)..x, g t| ≤ A + 2 * C * 2 :=
            (abs_add_le _ _).trans (by linarith)
        _ ≤ (A + 2 * C * 2) * (1 - x) ^ (-ε) := le_mul_of_one_le_right (by positivity) this

private theorem good : ∀ w : List Letter, Good w
  | [] => ⟨continuousOn_const, fun h => absurd allZero_nil h,
      fun _ _ => ⟨1, zero_le_one, fun t ht => by
        rw [hpl_nil, abs_one, one_mul]; exact one_le_one_sub_rpow ht (by positivity)⟩⟩
  | a :: w => good_cons a (good w)

/-! ### The public API -/

/-- `H(w)` is continuous on `(0, 1)`. -/
theorem continuousOn_hpl (w : List Letter) : ContinuousOn (hpl w) (Ioo 0 1) :=
  (good w).1

/-- The integrand `f a · H(w)` of the recursion is integrable on `[0, x]` for `0 ≤ x < 1`, when
`a · w` is not all zeros. -/
theorem intervalIntegrable_kernel_mul_hpl {a : Letter} {w : List Letter}
    (ha : ¬AllZero (a :: w)) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    IntervalIntegrable (fun t => a.kernel t * hpl w t) volume 0 x :=
  integrand_intervalIntegrable (good w) ha hx0 hx

/-- The derivative `d/dx H(a · w; x) = f a x · H(w; x)` on `(0, 1)`, for every letter and word
(for the all-zero words this is `d/dx logⁿ⁺¹ x / (n + 1)! = (1/x) logⁿ x / n!`). -/
theorem hasDerivAt_hpl_cons (a : Letter) (w : List Letter) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (hpl (a :: w)) (a.kernel x * hpl w x) x := by
  by_cases ha : AllZero (a :: w)
  · obtain ⟨rfl, hw⟩ := allZero_cons.1 ha
    rw [show hpl (Letter.zero :: w) = fun x =>
        log x ^ (w.length + 1) / ((w.length + 1).factorial : ℝ) from
        funext (hpl_of_allZero ha), Letter.kernel_zero, hpl_of_allZero hw]
    exact hasDerivAt_log_pow_div hx.1
  · exact hasDerivAt_of_good (good w) ha hx

/-- A word that is not all zeros has `|H(w; t)| ≤ C √t` on `(0, b]`, for each `b < 1`. -/
theorem abs_hpl_le_sqrt {w : List Letter} (hw : ¬AllZero w) {b : ℝ} (hb : b < 1) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc 0 b, |hpl w t| ≤ C * t ^ (1 / 2 : ℝ) :=
  (good w).2.1 hw b hb

/-- Every word has `|H(w; t)| ≤ C (1 - t) ^ (-ε)` on `[1/2, 1)`, for each `ε > 0`. -/
theorem abs_hpl_le_one_sub_rpow (w : List Letter) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ico (1 / 2 : ℝ) 1, |hpl w t| ≤ C * (1 - t) ^ (-ε) :=
  (good w).2.2 ε hε

/-- Every word has `|H(w; t)| ≤ C t ^ (-δ)` on `(0, b]`, `b < 1`, for each `δ > 0`. -/
theorem abs_hpl_le_rpow_neg (w : List Letter) {δ : ℝ} (hδ : 0 < δ) {b : ℝ} (hb : b < 1) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc 0 b, |hpl w t| ≤ C * t ^ (-δ) := by
  by_cases hw : AllZero w
  · obtain ⟨C, hC, h⟩ := abs_hpl_allZero_le hw hδ
    exact ⟨C, hC, fun t ht => h t ⟨ht.1, by linarith [ht.2]⟩⟩
  · obtain ⟨C, hC, h⟩ := abs_hpl_le_sqrt hw hb
    refine ⟨C, hC, fun t ht => (h t ht).trans (mul_le_mul_of_nonneg_left ?_ hC)⟩
    exact rpow_le_rpow_of_exponent_ge ht.1 (by linarith [ht.2]) (by linarith)

/-- `t ^ r → 0` as `t → 0⁺`, for `0 < r`. -/
theorem tendsto_rpow_nhdsGT_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun t : ℝ => t ^ r) (𝓝[>] 0) (𝓝 0) := by
  have := (continuousAt_id.rpow_const (Or.inr hr.le) : ContinuousAt (fun t : ℝ => t ^ r) 0)
  simpa [zero_rpow hr.ne'] using this.tendsto.mono_left nhdsWithin_le_nhds

/-- A bound `|F t| ≤ C t ^ r` on `(0, b]`, `0 < b`, `0 < r`, gives `F t → 0` as `t → 0⁺`. -/
theorem tendsto_zero_of_abs_le_rpow {F : ℝ → ℝ} {C r b : ℝ} (hr : 0 < r) (hb : 0 < b)
    (h : ∀ t ∈ Ioc 0 b, |F t| ≤ C * t ^ r) : Tendsto F (𝓝[>] 0) (𝓝 0) := by
  have hC : Tendsto (fun t : ℝ => C * t ^ r) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_rpow_nhdsGT_zero hr).const_mul C
  refine squeeze_zero_norm' ?_ hC
  filter_upwards [Ioc_mem_nhdsGT hb] with t ht
  rw [Real.norm_eq_abs]
  exact h t ht

/-- A word that is not all zeros has `H(w; x) → 0` as `x → 0⁺`. -/
theorem tendsto_hpl_zero {w : List Letter} (hw : ¬AllZero w) :
    Tendsto (hpl w) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, -, h⟩ := abs_hpl_le_sqrt hw (b := 1 / 2) (by norm_num)
  exact tendsto_zero_of_abs_le_rpow (by norm_num) (by norm_num) h

/-- `H(u; x) H(v; x) → 0` as `x → 0⁺` unless `u` and `v` are both all zeros. -/
theorem tendsto_hpl_mul_hpl_zero {u v : List Letter} (h : ¬(AllZero u ∧ AllZero v)) :
    Tendsto (fun x => hpl u x * hpl v x) (𝓝[>] 0) (𝓝 0) := by
  have key : ∀ {u v : List Letter}, ¬AllZero u →
      Tendsto (fun x => hpl u x * hpl v x) (𝓝[>] 0) (𝓝 0) := by
    intro u v hu
    obtain ⟨C, hC, hCu⟩ := abs_hpl_le_sqrt hu (b := 1 / 2) (by norm_num)
    obtain ⟨D, hD, hDv⟩ := abs_hpl_le_rpow_neg v (δ := 1 / 4) (by norm_num) (b := 1 / 2)
      (by norm_num)
    refine tendsto_zero_of_abs_le_rpow (C := C * D) (r := 1 / 4) (b := 1 / 2) (by norm_num)
      (by norm_num)
      fun t ht => ?_
    rw [abs_mul]
    calc |hpl u t| * |hpl v t| ≤ (C * t ^ (1 / 2 : ℝ)) * (D * t ^ (-(1 / 4) : ℝ)) :=
          mul_le_mul (hCu t ht) (hDv t ht) (abs_nonneg _) (mul_nonneg hC (rpow_nonneg ht.1.le _))
      _ = C * D * (t ^ (1 / 2 : ℝ) * t ^ (-(1 / 4) : ℝ)) := by ring
      _ = C * D * t ^ (1 / 4 : ℝ) := by
        rw [← rpow_add ht.1]
        norm_num
  by_cases hu : AllZero u
  · have hv : ¬AllZero v := fun hv => h ⟨hu, hv⟩
    simpa only [mul_comm] using key (v := u) hv
  · exact key hu

/-- If the first letter is not `1`, the integrand `f a · H(w)` is integrable on `[0, 1]`. -/
theorem intervalIntegrable_kernel_mul_hpl_one {a : Letter} (ha : a ≠ Letter.one)
    {w : List Letter} (haw : ¬AllZero (a :: w)) :
    IntervalIntegrable (fun t => a.kernel t * hpl w t) volume 0 1 := by
  set g := fun t => a.kernel t * hpl w t with hg
  have h0 : IntervalIntegrable g volume 0 (1 / 2) :=
    intervalIntegrable_kernel_mul_hpl haw (by norm_num) (by norm_num)
  refine h0.trans ?_
  obtain ⟨C, hC, h⟩ := abs_hpl_le_one_sub_rpow w (ε := 1 / 2) (by norm_num)
  have hdom : IntervalIntegrable (fun t : ℝ => 2 * C * (1 - t) ^ (-(1 / 2) : ℝ)) volume
      (1 / 2) 1 := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 / 2)
      (by norm_num : (-1 : ℝ) < -(1 / 2))).comp_sub_left 1
    have := this.const_mul (2 * C)
    norm_num at this ⊢
    exact this.symm
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)] at hdom ⊢
  refine hdom.mono' (((integrand_continuousOn a (good w)).mono
    (fun t ht => ⟨by linarith [ht.1], ht.2⟩ : Ioo (1 / 2 : ℝ) 1 ⊆ Ioo 0 1)).aestronglyMeasurable
    measurableSet_Ioo) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun t ht => ?_)
  rw [Real.norm_eq_abs, hg]
  simp only [abs_mul, mul_assoc]
  exact mul_le_mul (abs_kernel_le_two ha ⟨ht.1.le, ht.2⟩) (h t ⟨ht.1.le, ht.2⟩) (abs_nonneg _)
    (by norm_num)

/-- If the first letter is not `1`, `H(a · w)` is continuous on `[0, 1]` at `1`. -/
theorem continuousWithinAt_hpl_one {a : Letter} (ha : a ≠ Letter.one) (w : List Letter) :
    ContinuousWithinAt (hpl (a :: w)) (Icc 0 1) 1 := by
  by_cases haw : AllZero (a :: w)
  · rw [show hpl (a :: w) = fun x => log x ^ (a :: w).length /
        ((a :: w).length.factorial : ℝ) from funext (hpl_of_allZero haw)]
    exact (((continuousAt_log one_ne_zero).pow _).div_const _).continuousWithinAt
  · rw [hpl_cons_of_not_allZero haw]
    have hI := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1
      (intervalIntegrable_kernel_mul_hpl_one ha haw)
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := 1)
      (by rwa [uIcc_of_le zero_le_one])
    rw [uIcc_of_le zero_le_one] at this
    exact this 1 ⟨zero_le_one, le_rfl⟩

/-- If the first letter is not `1`, `H(a · w; x) → H(a · w; 1)` as `x → 1⁻`; here
`H(a · w; 1) = ∫₀¹ f a · H(w)` (or `0` for the all-zero words). -/
theorem tendsto_hpl_one {a : Letter} (ha : a ≠ Letter.one) (w : List Letter) :
    Tendsto (hpl (a :: w)) (𝓝[<] 1) (𝓝 (hpl (a :: w) 1)) :=
  (continuousWithinAt_hpl_one ha w).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))

/-- Uniqueness: an antiderivative of `f a · H(w)` on `(0, 1)` tending to `0` at `0⁺` is
`H(a · w)` there, when `a · w` is not all zeros. -/
theorem eq_hpl_cons_of_hasDerivAt {a : Letter} {w : List Letter} (haw : ¬AllZero (a :: w))
    {F : ℝ → ℝ} (hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (a.kernel x * hpl w x) x)
    (h0 : Tendsto F (𝓝[>] 0) (𝓝 0)) : ∀ x ∈ Ioo (0 : ℝ) 1, hpl (a :: w) x = F x := by
  have := eq_of_hasDerivAt_zero_of_tendsto_right (F := fun x => hpl (a :: w) x - F x)
    (c := 0) zero_lt_one
    (fun x hx => by
      have h := (hasDerivAt_hpl_cons a w hx).sub (hd x hx)
      rwa [sub_self] at h)
    (by simpa using (tendsto_hpl_zero haw).sub h0)
  intro x hx
  linarith [this x hx]

end QED.Polylog.HPL
