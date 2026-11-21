/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Polylog.HPLCalculus
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Harmonic polylogarithms as nested sums

Every harmonic polylogarithm `H(w; x)` whose word `w` has no trailing zero is a power series
`∑ₙ c_w(n) xⁿ` on `(0, 1)` whose coefficients are nested (harmonic) sums. The coefficients
`QED.Polylog.HPL.coef w n` are defined by recursion on the word, mirroring the integral
recursion of `H`:

* `c_[](n) = δ_{n,0}`;
* `c_{0·w}(n) = c_w(n) / n`;
* `c_{a·w}(n) = (1/n) ∑_{m<n} aⁿ⁻¹⁻ᵐ c_w(m)` for `a = ±1` (the kernel `1/(1 - a t)`).

Unfolding the recursion, for `w = (a₁, …, a_k)` with no zero letters this is the Z-sum
`c_w(n) = ∑_{n = n₁ > n₂ > ⋯ > n_k ≥ 1} ∏ⱼ (a_{j}^{n_j - n_{j+1}} / n_j)` (with `n_{k+1} = 0`),
and zero letters raise the powers of the denominators; so the coefficients are the S-sums and
Z-sums of Moch–Uwer–Weinzierl and Vermaseren. The twisted partial sums are
`QED.Polylog.HPL.twistSum σ c n = ∑_{m<n} σⁿ⁻¹⁻ᵐ c m` (`QED.Polylog.HPL.twistSum_eq_sum`).

At `x = 1`: for a word whose first letter is not `1` (and with no trailing zero), the series
`∑ₙ c_w(n)` converges, absolutely when the first letter is `0` and by pairing consecutive
terms when it is `-1`, and its sum is `H(w; 1)` (Abel's limit theorem). This identifies
`H(w; 1)` with a convergent (alternating) multiple zeta value.

## Main definitions

* `QED.Polylog.HPL.Letter.toReal`: the letter as the real number `0`, `1`, `-1`.
* `QED.Polylog.HPL.twistSum`: the twisted partial sums.
* `QED.Polylog.HPL.coef`: the nested-sum coefficients `c_w(n)`.

## Main results

* `QED.Polylog.HPL.abs_coef_le_one`, `QED.Polylog.HPL.abs_coef_le`: `|c_w(n)| ≤ 1` and
  `|c_w(n)| ≤ 3^|w| / √(n + 1)`.
* `QED.Polylog.HPL.hasSum_coef_mul_pow`: `H(w; x) = ∑ₙ c_w(n) xⁿ` on `(0, 1)` when `w` has no
  trailing zero (proved by induction on the word).
* `QED.Polylog.HPL.tendsto_sum_coef_hpl_one`: `∑_{n<N} c_w(n) → H(w; 1)` when the first
  letter of `w` is not `1` and `w` has no trailing zero.
-/

@[expose] public section

open Real Set Filter Topology Finset

namespace QED.Polylog.HPL

open Letter

/-- A letter as a real number: `0`, `1`, `-1`. -/
def Letter.toReal : Letter → ℝ
  | zero => 0
  | one => 1
  | negOne => -1

/-- The kernel of a nonzero letter `a` is `1 / (1 - a t)`. -/
theorem Letter.kernel_eq_of_ne_zero {a : Letter} (ha : a ≠ zero) (t : ℝ) :
    a.kernel t = (1 - a.toReal * t)⁻¹ := by
  cases a with
  | zero => exact absurd rfl ha
  | one => simp [Letter.toReal]
  | negOne => simp [Letter.toReal, sub_eq_add_neg]

theorem Letter.abs_toReal_le_one (a : Letter) : |a.toReal| ≤ 1 := by
  cases a <;> simp [Letter.toReal]

/-! ### Twisted partial sums -/

/-- The twisted partial sums `twistSum σ c n = ∑_{m<n} σⁿ⁻¹⁻ᵐ c m`, defined by
`twistSum σ c 0 = 0` and `twistSum σ c (n + 1) = σ twistSum σ c n + c n`. -/
def twistSum (σ : ℝ) (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => σ * twistSum σ c n + c n

@[simp] theorem twistSum_zero (σ : ℝ) (c : ℕ → ℝ) : twistSum σ c 0 = 0 := rfl

theorem twistSum_succ (σ : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    twistSum σ c (n + 1) = σ * twistSum σ c n + c n := rfl

/-- The twisted partial sum as a finite sum. -/
theorem twistSum_eq_sum (σ : ℝ) (c : ℕ → ℝ) (n : ℕ) :
    twistSum σ c n = ∑ m ∈ range n, σ ^ (n - 1 - m) * c m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [twistSum_succ, ih, sum_range_succ, mul_sum, Nat.add_sub_cancel, Nat.sub_self, pow_zero,
      one_mul]
    congr 1
    refine sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [← mul_assoc, ← pow_succ']
    congr 2
    omega

theorem abs_twistSum_le {σ : ℝ} (hσ : |σ| ≤ 1) (c : ℕ → ℝ) (n : ℕ) :
    |twistSum σ c n| ≤ ∑ m ∈ range n, |c m| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [twistSum_succ, sum_range_succ]
    calc |σ * twistSum σ c n + c n| ≤ |σ| * |twistSum σ c n| + |c n| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * ∑ m ∈ range n, |c m| + |c n| := by gcongr
      _ = _ := by ring

/-! ### The coefficients -/

/-- The nested-sum coefficients `c_w(n)` of `H(w; x) = ∑ₙ c_w(n) xⁿ`: `c_[](n) = δ_{n,0}`,
`c_{0·w}(n) = c_w(n) / n` and `c_{a·w}(n) = (1/n) ∑_{m<n} aⁿ⁻¹⁻ᵐ c_w(m)` for `a = ±1`. -/
noncomputable def coef : List Letter → ℕ → ℝ
  | [], n => if n = 0 then 1 else 0
  | zero :: w, n => coef w n / n
  | one :: w, n => twistSum 1 (coef w) n / n
  | negOne :: w, n => twistSum (-1) (coef w) n / n

theorem coef_nil (n : ℕ) : coef [] n = if n = 0 then 1 else 0 := rfl

theorem coef_zero_cons (w : List Letter) (n : ℕ) : coef (zero :: w) n = coef w n / n := rfl

theorem coef_cons_of_ne_zero {a : Letter} (ha : a ≠ zero) (w : List Letter) (n : ℕ) :
    coef (a :: w) n = twistSum a.toReal (coef w) n / n := by
  cases a with
  | zero => exact absurd rfl ha
  | one => rfl
  | negOne => rfl

/-- `c_w(0) = 0` for a nonempty word. -/
@[simp] theorem coef_cons_zero (a : Letter) (w : List Letter) : coef (a :: w) 0 = 0 := by
  cases a <;> simp [coef]

/-- `|c_w(n)| ≤ 1`. -/
theorem abs_coef_le_one : ∀ (w : List Letter) (n : ℕ), |coef w n| ≤ 1
  | [], n => by by_cases h : n = 0 <;> simp [coef, h]
  | a :: w, n => by
    rcases n with _ | n
    · simp
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    by_cases ha : a = zero
    · subst ha
      rw [coef_zero_cons, abs_div, Nat.abs_cast]
      exact (div_le_self (abs_nonneg _) (by norm_cast; omega)).trans (abs_coef_le_one w _)
    · rw [coef_cons_of_ne_zero ha, abs_div, Nat.abs_cast, div_le_one hn]
      calc |twistSum a.toReal (coef w) (n + 1)| ≤ ∑ m ∈ range (n + 1), |coef w m| :=
            abs_twistSum_le a.abs_toReal_le_one _ _
        _ ≤ ∑ m ∈ range (n + 1), (1 : ℝ) := sum_le_sum fun m _ => abs_coef_le_one w m
        _ = _ := by simp

/-- `∑_{m<n} 1/√(m+1) ≤ 2√n`. -/
theorem sum_one_div_sqrt_le (n : ℕ) : ∑ m ∈ range n, 1 / √((m : ℝ) + 1) ≤ 2 * √(n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have ha := Real.sqrt_nonneg (n : ℝ)
    have hb := Real.sqrt_pos.2 (by positivity : (0 : ℝ) < n + 1)
    have ha2 := Real.sq_sqrt (n.cast_nonneg : (0 : ℝ) ≤ n)
    have hb2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
    have h : 1 / √((n : ℝ) + 1) ≤ 2 * √((n : ℝ) + 1) - 2 * √(n : ℝ) := by
      rw [div_le_iff₀ hb]
      nlinarith [sq_nonneg (√(n : ℝ) - √((n : ℝ) + 1))]
    push_cast
    linarith

/-- The decay `|c_w(n)| ≤ 3^|w| / √(n + 1)`. -/
theorem abs_coef_le : ∀ (w : List Letter) (n : ℕ), |coef w n| ≤ 3 ^ w.length / √((n : ℝ) + 1)
  | [], n => by
    rcases n with _ | n
    · simp [coef]
    · simp only [coef, n.succ_ne_zero, ↓reduceIte, abs_zero]
      positivity
  | a :: w, n => by
    rcases n with _ | n
    · simp only [coef_cons_zero, abs_zero]
      positivity
    have ih := abs_coef_le w
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hb := Real.sqrt_pos.2 (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1)
    have h3 : (3 : ℝ) ^ w.length ≤ 3 ^ (a :: w).length :=
      pow_le_pow_right₀ (by norm_num) (by simp)
    by_cases ha : a = zero
    · subst ha
      rw [coef_zero_cons, abs_div, Nat.abs_cast]
      calc |coef w (n + 1)| / ((n + 1 : ℕ) : ℝ) ≤ |coef w (n + 1)| :=
            div_le_self (abs_nonneg _) (by norm_cast; omega)
        _ ≤ _ := ih _
        _ ≤ _ := by gcongr
    · rw [coef_cons_of_ne_zero ha, abs_div, Nat.abs_cast, List.length_cons, pow_succ]
      set C : ℝ := 3 ^ w.length
      have hC : 0 ≤ C := by positivity
      have hsum : |twistSum a.toReal (coef w) (n + 1)| ≤ C * (2 * √((n + 1 : ℕ) : ℝ)) := by
        calc |twistSum a.toReal (coef w) (n + 1)| ≤ ∑ m ∈ range (n + 1), |coef w m| :=
              abs_twistSum_le a.abs_toReal_le_one _ _
          _ ≤ ∑ m ∈ range (n + 1), C * (1 / √((m : ℝ) + 1)) :=
              sum_le_sum fun m _ => by rw [mul_one_div]; exact ih m
          _ = C * ∑ m ∈ range (n + 1), 1 / √((m : ℝ) + 1) := by rw [mul_sum]
          _ ≤ C * (2 * √((n + 1 : ℕ) : ℝ)) := by gcongr; exact sum_one_div_sqrt_le _
      set s := √((n + 1 : ℕ) : ℝ)
      set t := √(((n + 1 : ℕ) : ℝ) + 1)
      have hs : 0 < s := Real.sqrt_pos.2 hn
      have hs2 : s ^ 2 = ((n + 1 : ℕ) : ℝ) := Real.sq_sqrt hn.le
      have ht2 : t ^ 2 = ((n + 1 : ℕ) : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have hts : 2 * t ≤ 3 * s := by
        have h1 : (2 * t) ^ 2 ≤ (3 * s) ^ 2 := by
          have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
          nlinarith
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
      rw [div_le_div_iff₀ hn hb]
      calc |twistSum a.toReal (coef w) (n + 1)| * t ≤ C * (2 * s) * t := by gcongr
        _ = C * s * (2 * t) := by ring
        _ ≤ C * s * (3 * s) := by gcongr
        _ = C * 3 * ((n + 1 : ℕ) : ℝ) := by rw [← hs2]; ring

/-! ### Power series -/

theorem summable_mul_pow_of_abs_le_one {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) {x : ℝ}
    (hx : |x| < 1) : Summable fun n => c n * x ^ n :=
  .of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg x) hx) fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_of_le_one_left (by positivity) (hc n)

/-- Termwise differentiation of a power series with coefficients bounded by `1`. -/
theorem hasDerivAt_tsum_mul_pow {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun y => ∑' n, c n * y ^ n) (∑' n, c n * ((n : ℝ) * x ^ (n - 1))) x := by
  set r : ℝ := (|x| + 1) / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hxr : |x| < r := by rw [hr]; linarith
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => (n : ℝ) ^ 1 * r ^ n / r)
    (t := Ioo (-r) r) (g := fun n y => c n * y ^ n)
    (g' := fun n y => c n * ((n : ℝ) * y ^ (n - 1))) (y₀ := 0) ?_ isOpen_Ioo
    isPreconnected_Ioo (fun n y _ => (hasDerivAt_pow n y).const_mul (c n)) ?_
    ⟨by linarith, hr0⟩ (summable_mul_pow_of_abs_le_one hc (by simp)) (abs_lt.mp hxr)
  · have hr' : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr0]
    have h : Summable fun n : ℕ => (n : ℝ) ^ 1 * r ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr'
    exact h.div_const r
  · intro n y hy
    have hy' : |y| ≤ r := (abs_lt.mpr hy).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    rcases n with _ | n
    · simp
    calc |c (n + 1)| * (((n + 1 : ℕ) : ℝ) * |y| ^ (n + 1 - 1))
        ≤ 1 * (((n + 1 : ℕ) : ℝ) * r ^ n) := by
          rw [Nat.add_sub_cancel]
          gcongr
          exact hc _
      _ = _ := by field_simp; ring

theorem getLast?_ne_of_cons {a : Letter} {w : List Letter}
    (hw : (a :: w).getLast? ≠ some zero) : w.getLast? ≠ some zero := by
  cases w with
  | nil => simp
  | cons b w => simpa [List.getLast?_cons_cons] using hw

theorem not_allZero_of_getLast? {w : List Letter} (hne : w ≠ [])
    (hw : w.getLast? ≠ some zero) : ¬AllZero w := by
  intro h
  apply hw
  rw [List.getLast?_eq_some_getLast hne, h _ (List.getLast_mem hne)]

/-- The derivative series: if `H = ∑ c_w(n) yⁿ` then `∑ c_{a·w}(n) n yⁿ⁻¹ = f a (y) H`. -/
theorem hasSum_coef_deriv (a : Letter) {w : List Letter}
    (hw : (a :: w).getLast? ≠ some zero) {y H : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1)
    (hH : HasSum (fun n => coef w n * y ^ n) H) :
    HasSum (fun n => coef (a :: w) n * ((n : ℝ) * y ^ (n - 1))) (a.kernel y * H) := by
  have hy0 : y ≠ 0 := hy.1.ne'
  by_cases ha : a = zero
  · subst ha
    obtain ⟨b, w, rfl⟩ : ∃ b w', w = b :: w' := by
      cases w with
      | nil => simp at hw
      | cons b w' => exact ⟨b, w', rfl⟩
    rw [kernel_zero]
    convert hH.mul_left y⁻¹ using 1
    funext n
    rcases n with _ | n
    · simp
    · rw [coef_zero_cons, Nat.add_sub_cancel, pow_succ]
      push_cast
      field_simp
  · set σ := a.toReal
    set P := twistSum σ (coef w)
    have hσ : |σ| ≤ 1 := a.abs_toReal_le_one
    have hy1 : |y| < 1 := abs_lt.2 ⟨by linarith [hy.1], hy.2⟩
    have hden : 0 < 1 - σ * y := by
      have h1 : σ * y ≤ |y| := (le_abs_self _).trans (by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hσ)
      linarith [(abs_lt.1 hy1).2, le_abs_self y]
    -- the shifted derivative series `∑ P (k + 1) yᵏ`
    have hPk : ∀ k, |P k| ≤ k := fun k => by
      calc |P k| ≤ ∑ m ∈ range k, |coef w m| := abs_twistSum_le hσ _ _
        _ ≤ ∑ m ∈ range k, (1 : ℝ) := sum_le_sum fun m _ => abs_coef_le_one w m
        _ = k := by simp
    have hgs : Summable fun k : ℕ => P (k + 1) * y ^ k := by
      refine .of_norm_bounded (((summable_pow_mul_geometric_of_norm_lt_one 1
        (by rwa [Real.norm_eq_abs, abs_abs])).add (summable_geometric_of_lt_one (abs_nonneg y)
        hy1))) fun k => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have := hPk (k + 1)
      push_cast at this
      calc |P (k + 1)| * |y| ^ k ≤ ((k : ℝ) + 1) * |y| ^ k := by gcongr
        _ = (k : ℝ) ^ 1 * |y| ^ k + |y| ^ k := by ring
    set A := ∑' k : ℕ, P (k + 1) * y ^ k
    have hg : HasSum (fun k : ℕ => P (k + 1) * y ^ k) A := hgs.hasSum
    have hP : HasSum (fun k => P k * y ^ k) (y * A) := by
      have hP0 : P 0 = 0 := rfl
      rw [← hasSum_nat_add_iff' 1]
      simp only [Finset.range_one, sum_singleton, hP0, zero_mul, sub_zero]
      convert hg.mul_left y using 1
      funext k
      ring
    have hA : A = σ * (y * A) + H := by
      refine hg.unique ?_
      convert (hP.mul_left σ).add hH using 1
      funext k
      simp only [P, twistSum_succ]
      ring
    have hA' : A = (1 - σ * y)⁻¹ * H := by
      field_simp
      linarith
    rw [Letter.kernel_eq_of_ne_zero ha, ← hA', ← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, sum_singleton, coef_cons_zero, zero_mul, sub_zero]
    convert hg using 1
    funext k
    have hk : twistSum a.toReal (coef w) (k + 1) = P (k + 1) := rfl
    rw [coef_cons_of_ne_zero ha, Nat.add_sub_cancel, hk]
    push_cast
    field_simp

/-- **Nested-sum representation.** For a word `w` with no trailing zero,
`H(w; x) = ∑ₙ c_w(n) xⁿ` on `(0, 1)`. -/
theorem hasSum_coef_mul_pow (w : List Letter) (hw : w.getLast? ≠ some zero) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : HasSum (fun n => coef w n * x ^ n) (hpl w x) := by
  induction w generalizing x with
  | nil =>
    rw [hpl_nil]
    convert hasSum_ite_eq 0 (1 : ℝ) using 1
    funext n
    by_cases h : n = 0 <;> simp [coef, h]
  | cons a w ih =>
    have hw' := getLast?_ne_of_cons hw
    have hne := not_allZero_of_getLast? (List.cons_ne_nil a w) hw
    have hc := abs_coef_le_one (a :: w)
    have hF : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun z => ∑' n, coef (a :: w) n * z ^ n)
        (a.kernel y * hpl w y) y := by
      intro y hy
      have hd := hasDerivAt_tsum_mul_pow hc (abs_lt.2 ⟨by linarith [hy.1], hy.2⟩)
      rwa [(hasSum_coef_deriv a hw hy (ih hw' hy)).tsum_eq] at hd
    have h0 : Tendsto (fun z => ∑' n, coef (a :: w) n * z ^ n) (𝓝[>] 0) (𝓝 0) := by
      have hc0 := (hasDerivAt_tsum_mul_pow hc (x := 0) (by simp)).continuousAt
      have h00 : (∑' n, coef (a :: w) n * (0 : ℝ) ^ n) = 0 := by
        rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
        simp
      have := hc0.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      rwa [h00] at this
    rw [eq_hpl_cons_of_hasDerivAt hne hF h0 x hx]
    exact (summable_mul_pow_of_abs_le_one hc (abs_lt.2 ⟨by linarith [hx.1], hx.2⟩)).hasSum

/-! ### Convergence at `1` -/

/-- The summable majorant `1 / ((n + 1) √(n + 1))`. -/
theorem summable_one_div_mul_sqrt :
    Summable fun n : ℕ => 1 / (((n : ℝ) + 1) * √((n : ℝ) + 1)) := by
  have h := (summable_nat_add_iff 1).2
    (Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 3 / 2))
  refine h.congr fun n => ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  push_cast
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one,
    ← Real.sqrt_eq_rpow, one_div]

/-- `c_w(n) → 0`. -/
theorem tendsto_coef_zero (w : List Letter) : Tendsto (coef w) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (3 : ℝ) ^ w.length * (√((n : ℝ) + 1))⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => √((n : ℝ) + 1)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    simpa using h1.inv_tendsto_atTop.const_mul ((3 : ℝ) ^ w.length)
  refine squeeze_zero_norm (fun n => ?_) h
  rw [Real.norm_eq_abs, ← div_eq_mul_inv]
  exact abs_coef_le w n

/-- If the pairs `c (2k+1) + c (2k+2)` are summable, `c 0 = 0` and `c n → 0`, then the
partial sums of `c` converge. -/
theorem tendsto_sum_of_pairs {c : ℕ → ℝ} (h0 : c 0 = 0) (hc : Tendsto c atTop (𝓝 0))
    {L : ℝ} (hp : HasSum (fun k => c (2 * k + 1) + c (2 * k + 2)) L) :
    Tendsto (fun N => ∑ n ∈ range N, c n) atTop (𝓝 L) := by
  set t : ℕ → ℝ := fun K => ∑ k ∈ range K, (c (2 * k + 1) + c (2 * k + 2))
  have hodd : ∀ K, ∑ n ∈ range (2 * K + 1), c n = t K := by
    intro K
    induction K with
    | zero => simp [t, h0]
    | succ K ih =>
      rw [show 2 * (K + 1) + 1 = 2 * K + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
      simp only [t, sum_range_succ]
      rw [show 2 * K + 1 + 1 = 2 * K + 2 from rfl]
      ring
  have ht : Tendsto (fun N => t (N / 2)) atTop (𝓝 L) :=
    hp.tendsto_sum_nat.comp (tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun a ha => by omega⟩)
  have hr : Tendsto (fun N => t (N / 2) - ∑ n ∈ range N, c n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (by simpa using hc.norm)
    obtain ⟨K, rfl | rfl⟩ := Nat.even_or_odd' N
    · rw [show 2 * K / 2 = K by omega, ← hodd, sum_range_succ]
      simp
    · rw [show (2 * K + 1) / 2 = K by omega, ← hodd]
      simp
  simpa using ht.sub hr

/-- For a word with first letter not `1` and no trailing zero, the partial sums of the
coefficients converge. -/
theorem exists_tendsto_sum_coef {a : Letter} (ha : a ≠ one) {w : List Letter}
    (hw : (a :: w).getLast? ≠ some zero) :
    ∃ L, Tendsto (fun N => ∑ n ∈ range N, coef (a :: w) n) atTop (𝓝 L) := by
  set C : ℝ := 3 ^ w.length
  have hC : 0 ≤ C := by positivity
  cases a with
  | one => exact absurd rfl ha
  | zero =>
    refine ⟨_, (Summable.of_norm_bounded (summable_one_div_mul_sqrt.mul_left (2 * C))
      fun n => ?_).hasSum.tendsto_sum_nat⟩
    rw [Real.norm_eq_abs]
    rcases n with _ | n
    · simp only [coef_cons_zero, abs_zero]
      positivity
    rw [coef_zero_cons, abs_div, Nat.abs_cast]
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hs : 0 < √(((n + 1 : ℕ) : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have h1 := abs_coef_le w (n + 1)
    rw [div_le_iff₀ hn]
    calc |coef w (n + 1)| ≤ C / √(((n + 1 : ℕ) : ℝ) + 1) := h1
      _ ≤ 2 * C * (1 / ((((n + 1 : ℕ) : ℝ) + 1) * √(((n + 1 : ℕ) : ℝ) + 1))) *
          ((n + 1 : ℕ) : ℝ) := by
        rw [div_le_iff₀ hs]
        field_simp
        have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
        nlinarith
      _ = _ := by push_cast; ring
  | negOne =>
    set c := coef (negOne :: w)
    set d := coef w
    set P := twistSum (-1) d
    refine ⟨_, tendsto_sum_of_pairs (coef_cons_zero _ _) (tendsto_coef_zero _)
      (Summable.of_norm_bounded (summable_one_div_mul_sqrt.mul_left (3 * C))
        fun k => ?_).hasSum⟩
    have hP1 : P (2 * k + 1 + 1) = -1 * P (2 * k + 1) + d (2 * k + 1) := rfl
    change |P (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) + P (2 * k + 1 + 1) / ((2 * k + 1 + 1 : ℕ) : ℝ)|
      ≤ _
    rw [hP1]
    set p := P (2 * k + 1)
    have hp : |p| ≤ C * (2 * √(((2 * k + 1 : ℕ) : ℝ))) := by
      calc |p| ≤ ∑ m ∈ range (2 * k + 1), |d m| := abs_twistSum_le (by simp) _ _
        _ ≤ ∑ m ∈ range (2 * k + 1), C * (1 / √((m : ℝ) + 1)) :=
            sum_le_sum fun m _ => by rw [mul_one_div]; exact abs_coef_le w m
        _ = C * ∑ m ∈ range (2 * k + 1), 1 / √((m : ℝ) + 1) := by rw [mul_sum]
        _ ≤ _ := by gcongr; exact sum_one_div_sqrt_le _
    have hd : |d (2 * k + 1)| ≤ C / √(((2 * k + 1 : ℕ) : ℝ) + 1) := abs_coef_le w _
    push_cast at hp hd ⊢
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    set s := √(2 * (k : ℝ) + 1)
    set u := √(2 * (k : ℝ) + 1 + 1)
    set t := √((k : ℝ) + 1)
    have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
    have ht : 0 < t := Real.sqrt_pos.2 (by positivity)
    have hs2 : s ^ 2 = 2 * k + 1 := Real.sq_sqrt (by positivity)
    have hts : t ≤ s := Real.sqrt_le_sqrt (by linarith)
    have htu : t ≤ u := Real.sqrt_le_sqrt (by linarith)
    -- the pair is `p / ((2k+1)(2k+2)) + d (2k+1) / (2k+2)`
    have hpair : p / (2 * (k : ℝ) + 1) + (-1 * p + d (2 * k + 1)) / (2 * (k : ℝ) + 1 + 1) =
        p / ((2 * (k : ℝ) + 1) * (2 * k + 2)) + d (2 * k + 1) / (2 * k + 2) := by
      field_simp
      ring
    rw [hpair]
    have h1 : |p / ((2 * (k : ℝ) + 1) * (2 * k + 2))| ≤ 2 * C * (1 / (((k : ℝ) + 1) * t)) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 * (k : ℝ) + 1) * (2 * k + 2)),
        div_le_iff₀ (by positivity)]
      calc |p| ≤ C * (2 * s) := hp
        _ ≤ 2 * C * (1 / (((k : ℝ) + 1) * t)) * ((2 * k + 1) * (2 * k + 2)) := by
          rw [← hs2]
          field_simp
          have : s * ((k : ℝ) + 1) * t ≤ s * (2 * k + 2) * s := by gcongr <;> linarith
          nlinarith [mul_nonneg hC (mul_nonneg hs.le (mul_nonneg hk ht.le))]
    have h2 : |d (2 * k + 1) / (2 * k + 2)| ≤ C * (1 / (((k : ℝ) + 1) * t)) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * k + 2), div_le_iff₀ (by positivity)]
      calc |d (2 * k + 1)| ≤ C / u := hd
        _ ≤ C / t := div_le_div_of_nonneg_left hC ht htu
        _ = C * (1 / (((k : ℝ) + 1) * t)) * ((k : ℝ) + 1) := by field_simp
        _ ≤ C * (1 / (((k : ℝ) + 1) * t)) * (2 * k + 2) := by gcongr <;> linarith
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 2 * C * (1 / (((k : ℝ) + 1) * t)) + C * (1 / (((k : ℝ) + 1) * t)) := add_le_add h1 h2
      _ = _ := by ring

/-- **`H(w; 1)` as a convergent (alternating) multiple zeta value.** For a word with first
letter not `1` and no trailing zero, `∑_{n<N} c_w(n) → H(w; 1)`. -/
theorem tendsto_sum_coef_hpl_one {a : Letter} (ha : a ≠ one) {w : List Letter}
    (hw : (a :: w).getLast? ≠ some zero) :
    Tendsto (fun N => ∑ n ∈ range N, coef (a :: w) n) atTop (𝓝 (hpl (a :: w) 1)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_sum_coef ha hw
  have hAbel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt hL
  have hH : Tendsto (hpl (a :: w)) (𝓝[<] 1) (𝓝 L) :=
    hAbel.congr' (by
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx using
        (hasSum_coef_mul_pow _ hw hx).tsum_eq)
  rwa [tendsto_nhds_unique (tendsto_hpl_one ha w) hH]

end QED.Polylog.HPL
