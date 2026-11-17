/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ZetaValues

/-!
# The dilogarithm and trilogarithm on `[-1, 1]`

The real dilogarithm and trilogarithm, defined by their power series
`Li₂ x = ∑ x ^ (n + 1) / (n + 1) ^ 2` and `Li₃ x = ∑ x ^ (n + 1) / (n + 1) ^ 3`, and Apéry's
constant `zeta3 = ∑ 1 / (n + 1) ^ 3`. The series converge absolutely for `|x| ≤ 1`; outside that
range the `tsum` is `0`, so every result is stated for `|x| ≤ 1`.

## Main results

* `QED.Polylog.summable_pow_div_pow`: the series `∑ x ^ (n + 1) / (n + 1) ^ k` converges for
  `2 ≤ k` and `|x| ≤ 1`.
* `QED.Polylog.tsum_pow_div_pow_add_tsum_neg`: the duplication formula
  `Liₖ x + Liₖ (-x) = 2 ^ (1 - k) Liₖ (x ^ 2)`, in series form.
* `QED.Polylog.continuousOn_Li₂`, `QED.Polylog.continuousOn_Li₃`: continuity on `[-1, 1]`.
* `QED.Polylog.riemannZeta_three`: `riemannZeta 3 = zeta3`.
* `QED.Polylog.Li₂_one`, `QED.Polylog.Li₂_neg_one`: `Li₂ 1 = π ^ 2 / 6` and
  `Li₂ (-1) = -π ^ 2 / 12`.
* `QED.Polylog.Li₃_one`, `QED.Polylog.Li₃_neg_one`: `Li₃ 1 = zeta3` and
  `Li₃ (-1) = -(3 / 4) zeta3`.
-/

@[expose] public section

open Real

namespace QED.Polylog

/-- The real dilogarithm `Li₂ x = ∑_{n ≥ 1} x ^ n / n ^ 2`. The series converges for `|x| ≤ 1`;
outside that range this `tsum` is `0`. -/
noncomputable def Li₂ (x : ℝ) : ℝ := ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2

/-- The real trilogarithm `Li₃ x = ∑_{n ≥ 1} x ^ n / n ^ 3`. The series converges for `|x| ≤ 1`;
outside that range this `tsum` is `0`. -/
noncomputable def Li₃ (x : ℝ) : ℝ := ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 3

/-- Apéry's constant `ζ(3) = ∑_{n ≥ 1} 1 / n ^ 3`, as a real number. -/
noncomputable def zeta3 : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3

/-- The shifted `p`-series `∑ 1 / (n + 1) ^ k` converges for `2 ≤ k`. -/
theorem summable_one_div_add_one_pow {k : ℕ} (hk : 2 ≤ k) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ k := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < k))
  simpa using this

/-- For `|x| ≤ 1` the terms of the polylogarithm series `∑ x ^ (n + 1) / (n + 1) ^ k` are bounded
by `1 / (n + 1) ^ k`. -/
theorem norm_pow_div_pow_le {k : ℕ} {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    ‖x ^ (n + 1) / ((n : ℝ) + 1) ^ k‖ ≤ 1 / ((n : ℝ) + 1) ^ k := by
  rw [Real.norm_eq_abs, abs_div, abs_pow x, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ k)]
  exact div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg x) hx) (by positivity)

/-- The polylogarithm series `∑ x ^ (n + 1) / (n + 1) ^ k` converges for `2 ≤ k` and
`|x| ≤ 1`. -/
theorem summable_pow_div_pow {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : |x| ≤ 1) :
    Summable fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1) ^ k :=
  .of_norm_bounded (summable_one_div_add_one_pow hk) (norm_pow_div_pow_le hx)

/-- The duplication formula `Liₖ x + Liₖ (-x) = (2 / 2 ^ k) Liₖ (x ^ 2)`, in series form, for
`2 ≤ k` and `|x| ≤ 1`: the odd powers cancel and the even powers give the series at `x ^ 2`. -/
theorem tsum_pow_div_pow_add_tsum_neg {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : |x| ≤ 1) :
    (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ k) + ∑' n : ℕ, (-x) ^ (n + 1) / ((n : ℝ) + 1) ^ k =
      2 / 2 ^ k * ∑' n : ℕ, (x ^ 2) ^ (n + 1) / ((n : ℝ) + 1) ^ k := by
  have h1 := (summable_pow_div_pow hk hx).hasSum
  have h2 := (summable_pow_div_pow hk (x := -x) (by rwa [abs_neg])).hasSum
  have hsq : |x ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hx
  have h3 := (summable_pow_div_pow hk hsq).hasSum.mul_left (2 / 2 ^ k)
  set f : ℕ → ℝ := fun n => x ^ (n + 1) / ((n : ℝ) + 1) ^ k + (-x) ^ (n + 1) / ((n : ℝ) + 1) ^ k
    with hf
  have he : HasSum (fun m => f (2 * m)) 0 := by
    have : (fun m => f (2 * m)) = fun _ => 0 := by
      funext m
      simp only [hf]
      rw [Odd.neg_pow ⟨m, rfl⟩]
      ring
    rw [this]
    exact hasSum_zero
  have ho : HasSum (fun m => f (2 * m + 1))
      (2 / 2 ^ k * ∑' n : ℕ, (x ^ 2) ^ (n + 1) / ((n : ℝ) + 1) ^ k) := by
    convert h3 using 1
    funext m
    simp only [hf]
    rw [Even.neg_pow ⟨m + 1, by ring⟩, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
    push_cast
    rw [show (2 * (m : ℝ) + 1 + 1) = 2 * ((m : ℝ) + 1) by ring, mul_pow]
    have : (2 : ℝ) ^ k ≠ 0 := by positivity
    have : ((m : ℝ) + 1) ^ k ≠ 0 := by positivity
    field_simp
    ring
  have := he.even_add_odd ho
  rw [zero_add] at this
  exact (h1.add h2).unique this

/-- The series `∑ x ^ (n + 1) / (n + 1) ^ k`, `2 ≤ k`, is continuous on `[-1, 1]`, by uniform
convergence (Weierstrass M-test). -/
theorem continuousOn_tsum_pow_div_pow {k : ℕ} (hk : 2 ≤ k) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ k) (Set.Icc (-1) 1) :=
  continuousOn_tsum (fun n => by fun_prop) (summable_one_div_add_one_pow hk)
    fun n _ hx => norm_pow_div_pow_le (abs_le.mpr hx) n

/-- `Li₂` is continuous on `[-1, 1]`. -/
theorem continuousOn_Li₂ : ContinuousOn Li₂ (Set.Icc (-1) 1) :=
  continuousOn_tsum_pow_div_pow le_rfl

/-- `Li₃` is continuous on `[-1, 1]`. -/
theorem continuousOn_Li₃ : ContinuousOn Li₃ (Set.Icc (-1) 1) :=
  continuousOn_tsum_pow_div_pow (by norm_num)

/-- `Li₂ 0 = 0`. -/
@[simp] theorem Li₂_zero : Li₂ 0 = 0 := by simp [Li₂]

/-- `Li₃ 0 = 0`. -/
@[simp] theorem Li₃_zero : Li₃ 0 = 0 := by simp [Li₃]

/-- The dilogarithm series converges for `|x| ≤ 1`. -/
theorem hasSum_Li₂ {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) (Li₂ x) :=
  (summable_pow_div_pow le_rfl hx).hasSum

/-- The trilogarithm series converges for `|x| ≤ 1`. -/
theorem hasSum_Li₃ {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1) ^ 3) (Li₃ x) :=
  (summable_pow_div_pow (by norm_num) hx).hasSum

/-- The series defining `zeta3` converges. -/
theorem hasSum_zeta3 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3) zeta3 :=
  (summable_one_div_add_one_pow (by norm_num)).hasSum

/-- `zeta3` is the value of the Riemann zeta function at `3`. -/
theorem riemannZeta_three : riemannZeta 3 = (zeta3 : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by norm_num : 1 < (3 : ℂ).re), zeta3,
    Complex.ofReal_tsum]
  congr 1
  funext n
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  push_cast
  rfl

/-- `zeta3` is the real part of `riemannZeta 3`. -/
theorem riemannZeta_three_re : (riemannZeta 3).re = zeta3 := by
  rw [riemannZeta_three, Complex.ofReal_re]

/-- `zeta3` is positive. -/
theorem zeta3_pos : 0 < zeta3 := by
  have h := hasSum_zeta3
  refine lt_of_lt_of_le ?_ (sum_le_hasSum (Finset.range 1) (fun n _ => by positivity) h)
  norm_num

/-- The duplication formula `Li₂ x + Li₂ (-x) = Li₂ (x ^ 2) / 2` for `|x| ≤ 1`. -/
theorem Li₂_add_Li₂_neg {x : ℝ} (hx : |x| ≤ 1) : Li₂ x + Li₂ (-x) = Li₂ (x ^ 2) / 2 := by
  have := tsum_pow_div_pow_add_tsum_neg le_rfl hx
  rw [Li₂, Li₂, Li₂, this]
  ring

/-- The duplication formula `Li₃ x + Li₃ (-x) = Li₃ (x ^ 2) / 4` for `|x| ≤ 1`. -/
theorem Li₃_add_Li₃_neg {x : ℝ} (hx : |x| ≤ 1) : Li₃ x + Li₃ (-x) = Li₃ (x ^ 2) / 4 := by
  have := tsum_pow_div_pow_add_tsum_neg (k := 3) (by norm_num) hx
  rw [Li₃, Li₃, Li₃, this]
  ring

/-- `Li₂ 1 = ζ(2) = π ^ 2 / 6`. -/
theorem Li₂_one : Li₂ 1 = π ^ 2 / 6 := by
  have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at this
  simpa [Li₂] using this.tsum_eq

/-- `Li₂ (-1) = -ζ(2) / 2 = -π ^ 2 / 12`. -/
theorem Li₂_neg_one : Li₂ (-1) = -π ^ 2 / 12 := by
  have := Li₂_add_Li₂_neg (x := 1) (by norm_num)
  rw [one_pow, Li₂_one] at this
  linarith

/-- `Li₃ 1 = ζ(3)`. -/
theorem Li₃_one : Li₃ 1 = zeta3 := by
  simp [Li₃, zeta3]

/-- `Li₃ (-1) = -(3 / 4) ζ(3)`. -/
theorem Li₃_neg_one : Li₃ (-1) = -(3 / 4) * zeta3 := by
  have := Li₃_add_Li₃_neg (x := 1) (by norm_num)
  rw [one_pow, Li₃_one] at this
  linarith

end QED.Polylog
