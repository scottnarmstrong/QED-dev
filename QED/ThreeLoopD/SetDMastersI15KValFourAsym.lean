/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI15KValThreeSum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Set (d), master `I₁₅`: the leading behaviour of harmonic polylogarithms at `0`

For a word `w` over `{0, 1, -1}` that is not all zeros, `H(w; t) = t ℓ_w(log t) + O(t^{3/2})`
as `t → 0⁺`, where `ℓ_w` is an explicit polynomial: `ℓ_w = 0` when `w` has two or more nonzero
letters, and for `w = 0ᵏ a 0ᵐ` (`a = ±1`), `ℓ_w = ± P_{k+1,m}`, with
`P_{0,m}(L) = Lᵐ / m!`, `P_{k+1,0} = 1`, `P_{k+1,m+1} = P_{k,m+1} - P_{k+1,m}`
(so that `d/dt (t P_{k+1,m}(log t)) = P_{k,m}(log t)`).

This gives the limit at `0⁺` of a sum `Σ (aₜ/u + bₜ + cₜ u + dₜ u²) H(wₜ; u)` whose terms
diverge individually (`H(w; u)/u` and powers of `log u`): when every all-zero word has `aₜ = 0`
and the polynomial `Σ aₜ ℓ_{wₜ} + Σ_{wₜ = 0ᵐ} bₜ Lᵐ/m!` is a constant `K`, the sum tends to `K`.

## Main definitions

* `QED.ThreeLoopD.i15AsP`: the polynomials `P_{k,m}(L)`.
* `QED.ThreeLoopD.i15AsLead`: the leading polynomial `ℓ` of `H(0ᵏ w)`.
* `QED.ThreeLoopD.i15AsSum`: the polynomial `Σ aₜ ℓ_{wₜ} + Σ_{wₜ = 0ᵐ} bₜ Lᵐ/m!` of a sum.

## Main results

* `QED.ThreeLoopD.abs_hpl_sub_lead_le`: `|H(w; t) - t ℓ_w(log t)| ≤ C t^{3/2}` on `(0, 1/2]`.
* `QED.ThreeLoopD.tendsto_i15T3Sum_zero_of_lead`: the limit `K` of the sum at `0⁺`.
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory QED.Polylog.HPL

namespace QED.ThreeLoopD

/-- The polynomials `P_{0,m}(L) = Lᵐ/m!`, `P_{k+1,0} = 1`, `P_{k+1,m+1} = P_{k,m+1} - P_{k+1,m}`. -/
noncomputable def i15AsP : ℕ → ℕ → ℝ → ℝ
  | 0, m, L => L ^ m / (m.factorial : ℝ)
  | _ + 1, 0, _ => 1
  | k + 1, m + 1, L => i15AsP k (m + 1) L - i15AsP (k + 1) m L

@[simp] theorem i15AsP_zero (m : ℕ) (L : ℝ) : i15AsP 0 m L = L ^ m / (m.factorial : ℝ) := by
  simp [i15AsP]

@[simp] theorem i15AsP_succ_zero (k : ℕ) (L : ℝ) : i15AsP (k + 1) 0 L = 1 := by
  simp [i15AsP]

@[simp] theorem i15AsP_succ_succ (k m : ℕ) (L : ℝ) :
    i15AsP (k + 1) (m + 1) L = i15AsP k (m + 1) L - i15AsP (k + 1) m L := by
  simp [i15AsP]

theorem i15AsP_zero_right (k : ℕ) (L : ℝ) : i15AsP k 0 L = 1 := by
  cases k <;> simp

/-- `d/dL P_{k,m+1} = P_{k,m}`. -/
theorem hasDerivAt_i15AsP (k m : ℕ) (L : ℝ) :
    HasDerivAt (i15AsP k (m + 1)) (i15AsP k m L) L := by
  induction k generalizing m with
  | zero =>
    have h := (hasDerivAt_pow (m + 1) L).div_const ((m + 1).factorial : ℝ)
    rw [show i15AsP 0 (m + 1) = fun L => L ^ (m + 1) / ((m + 1).factorial : ℝ) from
      funext fun L => i15AsP_zero _ L]
    refine h.congr_deriv ?_
    rw [i15AsP_zero, Nat.factorial_succ]
    push_cast
    have : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  | succ k ih =>
    induction m with
    | zero =>
      rw [show i15AsP (k + 1) (0 + 1) = fun L => i15AsP k 1 L - 1 from
        funext fun L => by simp]
      have := (ih 0).sub_const 1
      refine this.congr_deriv ?_
      rw [i15AsP_zero_right, i15AsP_zero_right]
    | succ m ihm =>
      rw [show i15AsP (k + 1) (m + 1 + 1) = fun L => i15AsP k (m + 2) L - i15AsP (k + 1) (m + 1) L
        from funext fun L => by simp]
      refine ((ih (m + 1)).sub ihm).congr_deriv ?_
      simp

/-- `d/dt (t P_{k+1,m}(log t)) = P_{k,m}(log t)` for `0 < t`. -/
theorem hasDerivAt_mul_i15AsP (k m : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t * i15AsP (k + 1) m (log t)) (i15AsP k m (log t)) t := by
  cases m with
  | zero =>
    simp only [i15AsP_succ_zero, mul_one, i15AsP_zero_right]
    exact hasDerivAt_id' t
  | succ m =>
    have h := (hasDerivAt_id' t).mul ((hasDerivAt_i15AsP (k + 1) m (log t)).comp t
      (hasDerivAt_log ht.ne'))
    refine h.congr_deriv ?_
    simp only [Function.comp_apply, i15AsP_succ_succ]
    field_simp
    ring

/-- `|P_{k,m}(log t)| ≤ C t^{-1/2}` on `(0, 1]`. -/
theorem abs_i15AsP_le (k m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, |i15AsP k m (log t)| ≤ C * t ^ (-(1 / 2) : ℝ) := by
  induction k generalizing m with
  | zero =>
    obtain ⟨C, hC, h⟩ := abs_log_pow_le m (δ := 1 / 2) (by norm_num)
    refine ⟨C, hC, fun t ht => ?_⟩
    rw [i15AsP_zero, abs_div, abs_pow, Nat.abs_cast]
    exact (div_le_self (by positivity) (Nat.one_le_cast.2 (Nat.factorial_pos _))).trans (h t ht)
  | succ k ih =>
    induction m with
    | zero =>
      refine ⟨1, zero_le_one, fun t ht => ?_⟩
      rw [i15AsP_succ_zero, abs_one, one_mul]
      exact one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 (by norm_num)
    | succ m ihm =>
      obtain ⟨C₁, hC₁, h₁⟩ := ih (m + 1)
      obtain ⟨C₂, hC₂, h₂⟩ := ihm
      refine ⟨C₁ + C₂, by positivity, fun t ht => ?_⟩
      rw [i15AsP_succ_succ]
      calc |i15AsP k (m + 1) (log t) - i15AsP (k + 1) m (log t)|
          ≤ |i15AsP k (m + 1) (log t)| + |i15AsP (k + 1) m (log t)| := abs_sub _ _
        _ ≤ C₁ * t ^ (-(1 / 2) : ℝ) + C₂ * t ^ (-(1 / 2) : ℝ) := add_le_add (h₁ t ht) (h₂ t ht)
        _ = (C₁ + C₂) * t ^ (-(1 / 2) : ℝ) := by ring

theorem continuousOn_i15AsP_log (k m : ℕ) :
    ContinuousOn (fun t => i15AsP k m (log t)) (Ioo 0 1) := by
  intro t ht
  cases m with
  | zero => simp only [i15AsP_zero_right]; exact continuousWithinAt_const
  | succ m =>
    exact ((hasDerivAt_i15AsP k m (log t)).continuousAt.comp
      (continuousAt_log ht.1.ne')).continuousWithinAt

theorem intervalIntegrable_i15AsP_log (k m : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    IntervalIntegrable (fun t => i15AsP k m (log t)) volume 0 x := by
  obtain ⟨C, -, h⟩ := abs_i15AsP_le k m
  exact intervalIntegrable_of_le_rpow hx0 hx (continuousOn_i15AsP_log k m)
    fun t ht => h t ⟨ht.1, by linarith [ht.2]⟩

/-- `t P_{k,m}(log t) → 0` as `t → 0⁺`. -/
theorem tendsto_mul_i15AsP_zero (k m : ℕ) :
    Tendsto (fun t => t * i15AsP k m (log t)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, -, h⟩ := abs_i15AsP_le k m
  refine tendsto_zero_of_abs_le_rpow (C := C) (r := 1 / 2) (b := 1) (by norm_num)
    (by norm_num) fun t ht => ?_
  rw [abs_mul, abs_of_pos ht.1]
  calc t * |i15AsP k m (log t)| ≤ t * (C * t ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left (h t ht) ht.1.le
    _ = C * (t ^ (1 : ℝ) * t ^ (-(1 / 2) : ℝ)) := by rw [rpow_one]; ring
    _ = C * t ^ (1 / 2 : ℝ) := by rw [← rpow_add ht.1]; norm_num

/-- `∫₀ˣ P_{k,m}(log t) dt = x P_{k+1,m}(log x)` for `0 < x < 1`. -/
theorem integral_i15AsP_log (k m : ℕ) {x : ℝ} (hx0 : 0 < x) (hx : x < 1) :
    ∫ t in (0 : ℝ)..x, i15AsP k m (log t) = x * i15AsP (k + 1) m (log x) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx0
    (f := fun t => t * i15AsP (k + 1) m (log t)) (fun t ht => hasDerivAt_mul_i15AsP k m ht.1)
    (intervalIntegrable_i15AsP_log k m hx0.le hx) (tendsto_mul_i15AsP_zero (k + 1) m)
    ((hasDerivAt_mul_i15AsP k m hx0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds),
    sub_zero]

/-! ### The leading polynomial of a word -/

/-- The leading polynomial `ℓ` of `H(0ᵏ w)`: `P_{k+j+1,m}` for `w = 0ʲ a 0ᵐ` (`a = ±1`), else
`0`. -/
noncomputable def i15AsLead : ℕ → List Letter → ℝ → ℝ
  | _, [], _ => 0
  | k, Letter.zero :: w, L => i15AsLead (k + 1) w L
  | k, Letter.one :: w, L => if AllZero w then i15AsP (k + 1) w.length L else 0
  | k, Letter.negOne :: w, L => if AllZero w then i15AsP (k + 1) w.length L else 0

@[simp] theorem i15AsLead_nil (k : ℕ) (L : ℝ) : i15AsLead k [] L = 0 := rfl

@[simp] theorem i15AsLead_zero (k : ℕ) (w : List Letter) (L : ℝ) :
    i15AsLead k (Letter.zero :: w) L = i15AsLead (k + 1) w L := rfl

theorem i15AsLead_cons_ne {a : Letter} (ha : a ≠ Letter.zero) (k : ℕ) (w : List Letter)
    (L : ℝ) : i15AsLead k (a :: w) L = if AllZero w then i15AsP (k + 1) w.length L else 0 := by
  cases a with
  | zero => exact absurd rfl ha
  | one => rfl
  | negOne => rfl

@[simp] theorem i15AsLead_one (k : ℕ) (w : List Letter) (L : ℝ) :
    i15AsLead k (Letter.one :: w) L = if AllZero w then i15AsP (k + 1) w.length L else 0 :=
  i15AsLead_cons_ne (by decide) k w L

@[simp] theorem i15AsLead_negOne (k : ℕ) (w : List Letter) (L : ℝ) :
    i15AsLead k (Letter.negOne :: w) L = if AllZero w then i15AsP (k + 1) w.length L else 0 :=
  i15AsLead_cons_ne (by decide) k w L

theorem abs_i15AsLead_le (k : ℕ) (w : List Letter) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, |i15AsLead k w (log t)| ≤ C * t ^ (-(1 / 2) : ℝ) := by
  induction w generalizing k with
  | nil => exact ⟨0, le_rfl, fun t _ => by simp⟩
  | cons a w ih =>
    by_cases ha : a = Letter.zero
    · subst ha; simpa using ih (k + 1)
    · simp only [i15AsLead_cons_ne ha]
      obtain ⟨C, hC, h⟩ := abs_i15AsP_le (k + 1) w.length
      refine ⟨C, hC, fun t ht => ?_⟩
      split_ifs
      · exact h t ht
      · rw [abs_zero]; exact mul_nonneg hC (rpow_nonneg ht.1.le _)

/-! ### The bounds -/

/-- `t^{1/2} · t = t^{3/2}`-type integral bound: `|∫₀ˣ g| ≤ (2K/3) x^{3/2}` when
`|g t| ≤ K t^{1/2}` on `(0, x]`. -/
theorem i15As_abs_integral_le_sqrt {g : ℝ → ℝ} {K x : ℝ} (hx : 0 ≤ x)
    (hg : ∀ t ∈ Ioc 0 x, |g t| ≤ K * t ^ (1 / 2 : ℝ)) :
    |∫ t in (0 : ℝ)..x, g t| ≤ (2 * K / 3) * x ^ (3 / 2 : ℝ) := by
  have := abs_integral_le_of_le_rpow hx (r := 1 / 2) (by norm_num) hg
  calc _ ≤ K * (x ^ (1 / 2 + 1 : ℝ) / (1 / 2 + 1)) := this
    _ = (2 * K / 3) * x ^ (3 / 2 : ℝ) := by norm_num; ring

theorem i15As_abs_kernel_sub_one_le {a : Letter} (ha : a ≠ Letter.zero) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ 1 / 2) : |a.kernel t - 1| ≤ 2 * t := by
  cases a with
  | zero => exact absurd rfl ha
  | one =>
    have h1 : 0 < 1 - t := by linarith
    simp only [Letter.kernel_one]
    rw [show (1 - t)⁻¹ - 1 = t / (1 - t) by field_simp; ring, abs_div, abs_of_nonneg ht0,
      abs_of_pos h1, div_le_iff₀ h1]
    nlinarith
  | negOne =>
    have h1 : 0 < 1 + t := by linarith
    simp only [Letter.kernel_negOne]
    rw [show (1 + t)⁻¹ - 1 = -(t / (1 + t)) by field_simp; ring, abs_neg, abs_div,
      abs_of_nonneg ht0, abs_of_pos h1, div_le_iff₀ h1]
    nlinarith

theorem i15As_rpow_three_halves_div {t : ℝ} (ht : 0 < t) :
    t ^ (3 / 2 : ℝ) / t = t ^ (1 / 2 : ℝ) := by
  rw [div_eq_iff ht.ne']
  calc t ^ (3 / 2 : ℝ) = t ^ (1 / 2 + 1 : ℝ) := by norm_num
    _ = t ^ (1 / 2 : ℝ) * t := by rw [rpow_add ht, rpow_one]

/-- The difference of two integrals over `[0, x]` whose integrands differ by `≤ K t^{1/2}`. -/
theorem i15As_abs_integral_sub_le_sqrt {f g : ℝ → ℝ} {K x : ℝ} (hx : 0 ≤ x)
    (hf : IntervalIntegrable f volume 0 x) (hg : IntervalIntegrable g volume 0 x)
    (h : ∀ t ∈ Ioc 0 x, |f t - g t| ≤ K * t ^ (1 / 2 : ℝ)) :
    |(∫ t in (0 : ℝ)..x, f t) - ∫ t in (0 : ℝ)..x, g t| ≤ (2 * K / 3) * x ^ (3 / 2 : ℝ) := by
  rw [← intervalIntegral.integral_sub hf hg]
  exact i15As_abs_integral_le_sqrt hx h

theorem i15As_allZero_replicate (k : ℕ) : AllZero (List.replicate k Letter.zero) := by
  intro a ha; exact List.eq_of_mem_replicate ha

/-- **The words with one nonzero letter**: `H(0ᵏ a 0ᵐ; t) = t P_{k+1,m}(log t) + O(t^{3/2})`. -/
theorem abs_hpl_single_sub_le {a : Letter} (ha : a ≠ Letter.zero) (k m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) (1 / 2),
      |hpl (List.replicate k Letter.zero ++ a :: List.replicate m Letter.zero) t -
        t * i15AsP (k + 1) m (log t)| ≤ C * t ^ (3 / 2 : ℝ) := by
  have hna : ∀ k, ¬AllZero (List.replicate k Letter.zero ++ a :: List.replicate m Letter.zero) :=
    fun k h => ha ((allZero_append.1 h).2 a List.mem_cons_self)
  induction k with
  | zero =>
    obtain ⟨C, hC, hP⟩ := abs_i15AsP_le 0 m
    refine ⟨2 * (2 * C) / 3, by positivity, fun t ht => ?_⟩
    have ht1 : t < 1 := by linarith [ht.2]
    rw [List.replicate_zero, List.nil_append, hpl_cons_of_ne_zero ha,
      ← integral_i15AsP_log 0 m ht.1 ht1]
    refine i15As_abs_integral_sub_le_sqrt ht.1.le
      (intervalIntegrable_kernel_mul_hpl (hna 0) ht.1.le ht1)
      (intervalIntegrable_i15AsP_log 0 m ht.1.le ht1) fun s hs => ?_
    have hs1 : s ≤ 1 / 2 := hs.2.trans ht.2
    rw [hpl_of_allZero (i15As_allZero_replicate m), List.length_replicate, ← i15AsP_zero,
      ← sub_one_mul, abs_mul]
    calc |a.kernel s - 1| * |i15AsP 0 m (log s)| ≤ (2 * s) * (C * s ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul (i15As_abs_kernel_sub_one_le ha hs.1.le hs1) (hP s ⟨hs.1, by linarith⟩)
            (abs_nonneg _) (by linarith [hs.1])
      _ = 2 * C * (s ^ (1 : ℝ) * s ^ (-(1 / 2) : ℝ)) := by rw [rpow_one]; ring
      _ = 2 * C * s ^ (1 / 2 : ℝ) := by rw [← rpow_add hs.1]; norm_num
  | succ k ih =>
    obtain ⟨C, hC, hk⟩ := ih
    refine ⟨2 * C / 3, by positivity, fun t ht => ?_⟩
    have ht1 : t < 1 := by linarith [ht.2]
    have hw : List.replicate (k + 1) Letter.zero ++ a :: List.replicate m Letter.zero =
        Letter.zero :: (List.replicate k Letter.zero ++ a :: List.replicate m Letter.zero) := by
      rw [List.replicate_succ, List.cons_append]
    rw [hw, hpl_cons_of_not_allZero (hw ▸ hna (k + 1)), ← integral_i15AsP_log (k + 1) m ht.1 ht1]
    refine i15As_abs_integral_sub_le_sqrt ht.1.le
      (intervalIntegrable_kernel_mul_hpl (hw ▸ hna (k + 1)) ht.1.le ht1)
      (intervalIntegrable_i15AsP_log (k + 1) m ht.1.le ht1) fun s hs => ?_
    have hs0 := hs.1
    have e : Letter.zero.kernel s *
        hpl (List.replicate k Letter.zero ++ a :: List.replicate m Letter.zero) s -
        i15AsP (k + 1) m (log s) =
        (hpl (List.replicate k Letter.zero ++ a :: List.replicate m Letter.zero) s -
          s * i15AsP (k + 1) m (log s)) / s := by
      rw [Letter.kernel_zero]; field_simp
    rw [e, abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    calc _ ≤ C * s ^ (3 / 2 : ℝ) := hk s ⟨hs0, hs.2.trans ht.2⟩
      _ = C * s ^ (1 / 2 : ℝ) * s := by rw [← i15As_rpow_three_halves_div hs0]; field_simp

/-- The number of nonzero letters of a word. -/
def i15AsNZ (w : List Letter) : ℕ := w.countP fun a => a != Letter.zero

theorem i15AsNZ_eq_zero_iff {w : List Letter} : i15AsNZ w = 0 ↔ AllZero w := by
  simp [i15AsNZ, List.countP_eq_zero, AllZero]

/-- **The words with two nonzero letters**: `H(w; t) = O(t^{3/2})`. -/
theorem abs_hpl_le_of_two_le_nz {w : List Letter} (hw : 2 ≤ i15AsNZ w) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) (1 / 2), |hpl w t| ≤ C * t ^ (3 / 2 : ℝ) := by
  induction w with
  | nil => simp [i15AsNZ] at hw
  | cons a w ih =>
    by_cases ha : a = Letter.zero
    · subst ha
      have hw' : 2 ≤ i15AsNZ w := by simpa [i15AsNZ] using hw
      have hnz : ¬AllZero w := fun h => by rw [← i15AsNZ_eq_zero_iff] at h; omega
      obtain ⟨C, hC, h⟩ := ih hw'
      refine ⟨2 * C / 3, by positivity, fun t ht => ?_⟩
      rw [hpl_cons_of_not_allZero (by simpa using hnz)]
      refine i15As_abs_integral_le_sqrt ht.1.le fun s hs => ?_
      have hs0 := hs.1
      rw [Letter.kernel_zero, abs_mul, abs_inv, abs_of_pos hs0, inv_mul_le_iff₀ hs0]
      calc _ ≤ C * s ^ (3 / 2 : ℝ) := h s ⟨hs0, hs.2.trans ht.2⟩
        _ = s * (C * s ^ (1 / 2 : ℝ)) := by rw [← i15As_rpow_three_halves_div hs0]; field_simp
    · have hw' : 1 ≤ i15AsNZ w := by
        have : i15AsNZ (a :: w) = i15AsNZ w + 1 := by simp [i15AsNZ, ha]
        omega
      have hnz : ¬AllZero w := fun h => by rw [← i15AsNZ_eq_zero_iff] at h; omega
      obtain ⟨C, hC, h⟩ := abs_hpl_le_sqrt hnz (b := 1 / 2) (by norm_num)
      refine ⟨2 * (2 * C) / 3, by positivity, fun t ht => ?_⟩
      rw [hpl_cons_of_ne_zero ha]
      refine i15As_abs_integral_le_sqrt ht.1.le fun s hs => ?_
      have hs1 : s ≤ 1 / 2 := hs.2.trans ht.2
      rw [abs_mul]
      calc |a.kernel s| * |hpl w s| ≤ 2 * (C * s ^ (1 / 2 : ℝ)) :=
            mul_le_mul ((abs_kernel_le ha (b := 1 / 2) (by norm_num) hs.1.le hs1).trans
                (by norm_num))
              (h s ⟨hs.1, hs1⟩) (abs_nonneg _) (by norm_num)
        _ = 2 * C * s ^ (1 / 2 : ℝ) := by ring

theorem i15AsLead_of_allZero {w : List Letter} (hw : AllZero w) (k : ℕ) (L : ℝ) :
    i15AsLead k w L = 0 := by
  induction w generalizing k with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨rfl, hw'⟩ := allZero_cons.1 hw
    exact ih hw' (k + 1)

theorem abs_hpl_sub_lead_le_aux (w : List Letter) (hw : ¬AllZero w) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) (1 / 2),
      |hpl (List.replicate k Letter.zero ++ w) t - t * i15AsLead k w (log t)| ≤
        C * t ^ (3 / 2 : ℝ) := by
  induction w generalizing k with
  | nil => exact absurd allZero_nil hw
  | cons a w ih =>
    by_cases ha : a = Letter.zero
    · subst ha
      have hw' : ¬AllZero w := by simpa using hw
      obtain ⟨C, hC, h⟩ := ih hw' (k + 1)
      refine ⟨C, hC, fun t ht => ?_⟩
      rw [i15AsLead_zero, show List.replicate k Letter.zero ++ Letter.zero :: w =
        List.replicate (k + 1) Letter.zero ++ w by
          rw [List.replicate_succ', List.append_assoc, List.singleton_append]]
      exact h t ht
    · simp only [i15AsLead_cons_ne ha]
      by_cases hw0 : AllZero w
      · simp only [hw0, ↓reduceIte]
        have : w = List.replicate w.length Letter.zero :=
          List.eq_replicate_iff.2 ⟨rfl, hw0⟩
        obtain ⟨C, hC, h⟩ := abs_hpl_single_sub_le ha k w.length
        rw [← this] at h
        exact ⟨C, hC, h⟩
      · simp only [hw0, ↓reduceIte, mul_zero, sub_zero]
        refine abs_hpl_le_of_two_le_nz ?_
        have h1 : 1 ≤ i15AsNZ w := by
          rcases Nat.eq_zero_or_pos (i15AsNZ w) with h | h
          · exact absurd (i15AsNZ_eq_zero_iff.1 h) hw0
          · exact h
        have : i15AsNZ (List.replicate k Letter.zero ++ a :: w) = i15AsNZ w + 1 := by
          simp [i15AsNZ, ha, List.countP_append, List.countP_replicate]
        omega

/-- **`H(w; t) = t ℓ_w(log t) + O(t^{3/2})`** on `(0, 1/2]`, for `w` not all zeros. -/
theorem abs_hpl_sub_lead_le {w : List Letter} (hw : ¬AllZero w) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) (1 / 2),
      |hpl w t - t * i15AsLead 0 w (log t)| ≤ C * t ^ (3 / 2 : ℝ) := by
  simpa using abs_hpl_sub_lead_le_aux w hw 0

/-! ### Limits of sums at `0` -/

/-- The polynomial `Σ aₜ ℓ_{wₜ} + Σ_{wₜ = 0ᵐ} bₜ Lᵐ/m!` of a sum `Σ qₜ H(wₜ)`. -/
noncomputable def i15AsSum (L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter)) (x : ℝ) : ℝ :=
  (L.map fun t => t.1.1 * i15AsLead 0 t.2 x +
    if AllZero t.2 then t.1.2.1 * i15AsP 0 t.2.length x else 0).sum

theorem tendsto_mul_i15AsLead_zero (k : ℕ) (w : List Letter) :
    Tendsto (fun t => t * i15AsLead k w (log t)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, -, h⟩ := abs_i15AsLead_le k w
  refine tendsto_zero_of_abs_le_rpow (C := C) (r := 1 / 2) (b := 1) (by norm_num)
    (by norm_num) fun t ht => ?_
  rw [abs_mul, abs_of_pos ht.1]
  calc t * |i15AsLead k w (log t)| ≤ t * (C * t ^ (-(1 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left (h t ht) ht.1.le
    _ = C * (t ^ (1 : ℝ) * t ^ (-(1 / 2) : ℝ)) := by rw [rpow_one]; ring
    _ = C * t ^ (1 / 2 : ℝ) := by rw [← rpow_add ht.1]; norm_num

theorem tendsto_i15T3q_mul_hpl_sub_lead (q : ℝ × ℝ × ℝ × ℝ) (w : List Letter)
    (h : AllZero w → q.1 = 0) :
    Tendsto (fun u => i15T3q q u * hpl w u - (q.1 * i15AsLead 0 w (log u) +
      if AllZero w then q.2.1 * i15AsP 0 w.length (log u) else 0)) (𝓝[>] 0) (𝓝 0) := by
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  by_cases hw : AllZero w
  · have ha := h hw
    have e : ∀ u, i15T3q q u * hpl w u - (q.1 * i15AsLead 0 w (log u) +
        if AllZero w then q.2.1 * i15AsP 0 w.length (log u) else 0) =
        (q.2.2.1 + q.2.2.2 * u) * (u * i15AsP 0 w.length (log u)) := by
      intro u
      simp only [hw, ↓reduceIte, i15AsLead_of_allZero hw, hpl_of_allZero hw, i15AsP_zero,
        i15T3q, ha]
      ring
    simp only [e]
    simpa using (tendsto_const_nhds.add (hx0.const_mul q.2.2.2)).mul
      (tendsto_mul_i15AsP_zero 0 w.length)
  · obtain ⟨C, -, hE⟩ := abs_hpl_sub_lead_le hw
    have hE' : Tendsto (fun u => (hpl w u - u * i15AsLead 0 w (log u)) / u) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_zero_of_abs_le_rpow (C := C) (r := 1 / 2) (b := 1 / 2) (by norm_num)
        (by norm_num) fun t ht => ?_
      rw [abs_div, abs_of_pos ht.1, div_le_iff₀ ht.1]
      calc _ ≤ C * t ^ (3 / 2 : ℝ) := hE t ht
        _ = C * t ^ (1 / 2 : ℝ) * t := by
          rw [← i15As_rpow_three_halves_div ht.1, mul_assoc, div_mul_cancel₀ _ ht.1.ne']
    have hp : Tendsto (fun u : ℝ => q.1 + q.2.1 * u + q.2.2.1 * u ^ 2 + q.2.2.2 * u ^ 3)
        (𝓝[>] 0) (𝓝 q.1) := by
      have : Continuous fun u : ℝ => q.1 + q.2.1 * u + q.2.2.1 * u ^ 2 + q.2.2.2 * u ^ 3 := by
        fun_prop
      simpa using this.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    have hq : Tendsto (fun u : ℝ => q.2.1 + q.2.2.1 * u + q.2.2.2 * u ^ 2) (𝓝[>] 0)
        (𝓝 q.2.1) := by
      have : Continuous fun u : ℝ => q.2.1 + q.2.2.1 * u + q.2.2.2 * u ^ 2 := by fun_prop
      simpa using this.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    have hlim := (hp.mul hE').add (hq.mul (tendsto_mul_i15AsLead_zero 0 w))
    rw [mul_zero, mul_zero, add_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
    simp only [hw, ↓reduceIte, add_zero, i15T3q]
    field_simp
    ring

/-- `Σ qₜ H(wₜ; u) - ℓ(log u) → 0` as `u → 0⁺`, when every all-zero word has `aₜ = 0`. -/
theorem tendsto_i15T3Sum_sub_i15AsSum {L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter)}
    (h : ∀ t ∈ L, AllZero t.2 → t.1.1 = 0) :
    Tendsto (fun u => i15T3Sum L u - i15AsSum L (log u)) (𝓝[>] 0) (𝓝 0) := by
  induction L with
  | nil => simp [i15AsSum]
  | cons t L ih =>
    have h1 := tendsto_i15T3q_mul_hpl_sub_lead t.1 t.2 (h t List.mem_cons_self)
    have h2 := ih fun s hs => h s (List.mem_cons_of_mem t hs)
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr' (Eventually.of_forall fun u => ?_)
    simp only [i15T3Sum_cons, i15AsSum, List.map_cons, List.sum_cons]
    ring

/-- **The limit at `0⁺` of `Σ qₜ H(wₜ)`**: `K`, when every all-zero word has `aₜ = 0` and the
leading polynomial `Σ aₜ ℓ_{wₜ} + Σ_{wₜ = 0ᵐ} bₜ Lᵐ/m!` is the constant `K`. -/
theorem tendsto_i15T3Sum_zero_of_lead {L : List ((ℝ × ℝ × ℝ × ℝ) × List Letter)}
    (h : ∀ t ∈ L, AllZero t.2 → t.1.1 = 0) {K : ℝ} (hK : ∀ x, i15AsSum L x = K) :
    Tendsto (i15T3Sum L) (𝓝[>] 0) (𝓝 K) := by
  have := (tendsto_i15T3Sum_sub_i15AsSum h).add_const K
  rw [zero_add] at this
  refine this.congr' (Eventually.of_forall fun u => ?_)
  simp [hK]

end QED.ThreeLoopD
