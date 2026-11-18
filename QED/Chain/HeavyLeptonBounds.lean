/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.Chain.HeavyLepton
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The heavy-lepton VP insertion: certified enclosures at the muon and tau mass ratios

Helper-level enclosures for obligation O3-M3 of `docs/HIGHER-LOOP-PLAN.md` (and a first piece of
O3-M5). They are **not** frozen.

## Method

The closed form `QED.Chain.HeavyLepton.a2Heavy` cancels heavily at small `y` (terms of size `y⁻⁴`
add up to `≈ y²/45`). Each of `log(1-y)`, `log(1+y)`, `log(1-y²)`, `Li₂(y)`, `Li₂(-y)`, `Li₂(y²)` is
replaced by its Taylor polynomial with `n` terms, with remainder at most `|t|^{n+1}/(1-|t|)`
(`Real.abs_log_sub_add_sum_range_le`, `abs_Li₂_sub_sum_le`). The polynomial part is
`hlSerP n y + hlSerQ n y · log y` with rational `hlSerP`, `hlSerQ` (the cancellation is exact in
rational arithmetic), and the remainder is bounded by `hlSerE n y Λ` for `|log y| ≤ Λ`
(`abs_a2Heavy_sub_ser_le`). The value of `log y` is enclosed with the series of `log(1 - u)` at
`u = 1 - 2ᵏ y` and Mathlib's nine-digit bounds on `log 2` (`log_mem_of_series`). By monotonicity
(`QED.Chain.HeavyLepton.heavyIntegral_mono`) the bounds at the two ends of an input interval for `y`
enclose `A(y)` on the whole interval.

## Inputs (AKN Table 1)

* `mₑ/m_μ = 4.83633170(11)·10⁻³`, so `y ∈ [4.83633159, 4.83633181]·10⁻³`;
* `mₑ/m_τ = 2.87585(19)·10⁻⁴`, so `y ∈ [2.87566, 2.87604]·10⁻⁴`.

## Main statements

* `heavyIntegral_mu_bounds`: `5.197386525·10⁻⁷ ≤ A(y) ≤ 5.197386998·10⁻⁷` on the muon interval
  (AKN: `0.519738676(24)·10⁻⁶`).
* `heavyIntegral_tau_bounds`: `1.8376481·10⁻⁹ ≤ A(y) ≤ 1.8381339·10⁻⁹` on the tau interval
  (AKN: `0.183790(25)·10⁻⁸`).
-/

@[expose] public section

open Real Set Filter Topology QED.Polylog

namespace QED.Chain.HeavyLepton

/-! ### Series with remainders -/

/-- The Taylor polynomial `∑_{i<n} t^{i+1}/(i+1)` of `-log(1-t)`. -/
noncomputable def lS (n : ℕ) (t : ℝ) : ℝ := ∑ i ∈ Finset.range n, t ^ (i + 1) / ((i : ℝ) + 1)

/-- The Taylor polynomial `∑_{i<n} t^{i+1}/(i+1)²` of `Li₂ t`. -/
noncomputable def lT (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, t ^ (i + 1) / ((i : ℝ) + 1) ^ 2

/-- `|Li₂ t - ∑_{i<n} t^{i+1}/(i+1)²| ≤ |t|^{n+1}/(1-|t|)` for `|t| < 1`. -/
theorem abs_Li₂_sub_lT_le {t : ℝ} (ht : |t| < 1) (n : ℕ) :
    |Li₂ t - lT n t| ≤ |t| ^ (n + 1) / (1 - |t|) := by
  set f : ℕ → ℝ := fun i => t ^ (i + 1) / ((i : ℝ) + 1) ^ 2 with hf
  have hs : HasSum f (Li₂ t) := hasSum_Li₂ ht.le
  have htail : HasSum (fun i => f (i + n)) (Li₂ t - lT n t) := (hasSum_nat_add_iff' n).mpr hs
  have hg : HasSum (fun i : ℕ => |t| ^ (n + 1) * |t| ^ i) (|t| ^ (n + 1) * (1 - |t|)⁻¹) :=
    (hasSum_geometric_of_lt_one (abs_nonneg t) ht).mul_left _
  have hb : ∀ i, |f (i + n)| ≤ |t| ^ (n + 1) * |t| ^ i := by
    intro i
    have h1 : (1 : ℝ) ≤ (((i + n : ℕ) : ℝ) + 1) ^ 2 :=
      one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
    simp only [hf]
    rw [abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (((i + n : ℕ) : ℝ) + 1) ^ 2)]
    calc |t| ^ (i + n + 1) / (((i + n : ℕ) : ℝ) + 1) ^ 2 ≤ |t| ^ (i + n + 1) :=
          div_le_self (by positivity) h1
      _ = |t| ^ (n + 1) * |t| ^ i := by ring
  rw [abs_le, div_eq_mul_inv]
  exact ⟨hasSum_le (fun i => (abs_le.mp (hb i)).1) hg.neg htail,
    hasSum_le (fun i => (abs_le.mp (hb i)).2) htail hg⟩

/-- `|log(1-t) + ∑_{i<n} t^{i+1}/(i+1)| ≤ |t|^{n+1}/(1-|t|)` for `|t| < 1` (Mathlib). -/
theorem abs_lS_add_log_le {t : ℝ} (ht : |t| < 1) (n : ℕ) :
    |lS n t + log (1 - t)| ≤ |t| ^ (n + 1) / (1 - |t|) :=
  Real.abs_log_sub_add_sum_range_le ht n

/-! ### The closed form as a polynomial in `log y` plus a remainder -/

/-- The `log`-free part of the truncated closed form. -/
noncomputable def hlSerP (n : ℕ) (y : ℝ) : ℝ :=
  -25 / 36 + 4 / y ^ 2 + (y ^ 2 - 5) / (2 * y ^ 3) * (lT n y - lT n (-y)) + lT n (y ^ 2) / y ^ 4

/-- The coefficient of `log y` in the truncated closed form. -/
noncomputable def hlSerQ (n : ℕ) (y : ℝ) : ℝ :=
  1 / 3 - 3 / y ^ 2 + (y ^ 2 - 5) / (2 * y ^ 3) * (lS n (-y) - lS n y) - 2 * lS n (y ^ 2) / y ^ 4

/-- The remainder bound, for `|log y| ≤ Λ`. -/
noncomputable def hlSerE (n : ℕ) (y Λ : ℝ) : ℝ :=
  (5 - y ^ 2) / (2 * y ^ 3) * (2 * Λ + 2) * (y ^ (n + 1) / (1 - y)) +
    (2 * Λ + 1) * ((y ^ 2) ^ (n + 1) / (1 - y ^ 2)) / y ^ 4

/-- **The closed form with a remainder.** For `0 < y < 1` and `|log y| ≤ Λ`,
`|a2Heavy y - (hlSerP n y + hlSerQ n y · log y)| ≤ hlSerE n y Λ`. -/
theorem abs_a2Heavy_sub_ser_le {y Λ : ℝ} (n : ℕ) (hy0 : 0 < y) (hy1 : y < 1)
    (hΛ : |log y| ≤ Λ) :
    |a2Heavy y - (hlSerP n y + hlSerQ n y * log y)| ≤ hlSerE n y Λ := by
  have hyp : 0 < 1 + y := by linarith
  have hym : 0 < 1 - y := by linarith
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith
  have hy2' : y ^ 2 < 1 := by nlinarith
  have ay : |y| = y := abs_of_pos hy0
  have ay' : |-y| = y := by rw [abs_neg, ay]
  have ay2 : |y ^ 2| = y ^ 2 := abs_of_pos (by positivity)
  set b1 := y ^ (n + 1) / (1 - y)
  set b2 := (y ^ 2) ^ (n + 1) / (1 - y ^ 2)
  set e1 := lS n y + log (1 - y)
  set e2 := lS n (-y) + log (1 + y)
  set e3 := lS n (y ^ 2) + log (1 - y ^ 2)
  set d1 := Li₂ y - lT n y
  set d2 := Li₂ (-y) - lT n (-y)
  set d3 := Li₂ (y ^ 2) - lT n (y ^ 2)
  have he1 : |e1| ≤ b1 := by
    have := abs_lS_add_log_le (t := y) (by rw [ay]; exact hy1) n
    rwa [ay] at this
  have he2 : |e2| ≤ b1 := by
    have := abs_lS_add_log_le (t := -y) (by rw [ay']; exact hy1) n
    rwa [ay', sub_neg_eq_add] at this
  have he3 : |e3| ≤ b2 := by
    have := abs_lS_add_log_le (t := y ^ 2) (by rw [ay2]; exact hy2') n
    rwa [ay2] at this
  have hd1 : |d1| ≤ b1 := by
    have := abs_Li₂_sub_lT_le (t := y) (by rw [ay]; exact hy1) n
    rwa [ay] at this
  have hd2 : |d2| ≤ b1 := by
    have := abs_Li₂_sub_lT_le (t := -y) (by rw [ay']; exact hy1) n
    rwa [ay'] at this
  have hd3 : |d3| ≤ b2 := by
    have := abs_Li₂_sub_lT_le (t := y ^ 2) (by rw [ay2]; exact hy2') n
    rwa [ay2] at this
  set a := (y ^ 2 - 5) / (2 * y ^ 3)
  set L := log y
  have key : a2Heavy y - (hlSerP n y + hlSerQ n y * L) =
      a * (L * (e1 - e2) + (d1 - d2)) + (2 * L * e3 + d3) / y ^ 4 := by
    unfold a2Heavy hlSerP hlSerQ
    rw [log_div hym.ne' hyp.ne']
    ring
  have ha : |a| = (5 - y ^ 2) / (2 * y ^ 3) := by
    rw [abs_of_neg (div_neg_of_neg_of_pos (by nlinarith) (by positivity))]
    ring
  have hb1 : 0 ≤ b1 := div_nonneg (by positivity) hym.le
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans hΛ
  have hX : |L * (e1 - e2) + (d1 - d2)| ≤ (2 * Λ + 2) * b1 := by
    calc |L * (e1 - e2) + (d1 - d2)| ≤ |L| * (|e1| + |e2|) + (|d1| + |d2|) := by
          refine (abs_add_le _ _).trans (add_le_add ?_ (abs_sub _ _))
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ Λ * (b1 + b1) + (b1 + b1) := by
          gcongr
      _ = (2 * Λ + 2) * b1 := by ring
  have hY : |2 * L * e3 + d3| ≤ (2 * Λ + 1) * b2 := by
    calc |2 * L * e3 + d3| ≤ 2 * |L| * |e3| + |d3| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          rw [abs_mul, abs_mul, abs_two]
      _ ≤ 2 * Λ * b2 + b2 := by gcongr
      _ = (2 * Λ + 1) * b2 := by ring
  rw [key]
  calc |a * (L * (e1 - e2) + (d1 - d2)) + (2 * L * e3 + d3) / y ^ 4|
      ≤ |a| * |L * (e1 - e2) + (d1 - d2)| + |2 * L * e3 + d3| / y ^ 4 := by
        refine (abs_add_le _ _).trans (add_le_add (abs_mul _ _).le ?_)
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < y ^ 4)]
    _ ≤ (5 - y ^ 2) / (2 * y ^ 3) * ((2 * Λ + 2) * b1) + (2 * Λ + 1) * b2 / y ^ 4 := by
        rw [ha]
        have hc : 0 ≤ (5 - y ^ 2) / (2 * y ^ 3) := div_nonneg (by nlinarith) (by positivity)
        gcongr
    _ = hlSerE n y Λ := by
        unfold hlSerE
        ring

/-! ### Enclosing `log y` -/

/-- With `z = 2ᵏ y ∈ [1/2, 1]` and the series of `log(1 - u)` at `u = 1 - z`, `log y` lies within
`(1-z)^{n+1}/z + k · 5·10⁻¹⁰` of `-lS n (1 - z) - k log 2`. -/
theorem log_mem_of_series {y : ℝ} (k n : ℕ) (hy : 0 < y) (h2 : 2 ^ k * y ≤ 1) :
    -lS n (1 - 2 ^ k * y) - (1 - 2 ^ k * y) ^ (n + 1) / (2 ^ k * y) - k * 0.6931471808 ≤ log y ∧
      log y ≤ -lS n (1 - 2 ^ k * y) + (1 - 2 ^ k * y) ^ (n + 1) / (2 ^ k * y) -
        k * 0.6931471803 := by
  have hz : 0 < 2 ^ k * y := by positivity
  have hu0 : 0 ≤ 1 - 2 ^ k * y := by linarith
  have hu : |1 - 2 ^ k * y| < 1 := by rw [abs_of_nonneg hu0]; linarith
  have h := abs_lS_add_log_le hu n
  rw [abs_of_nonneg hu0, sub_sub_cancel] at h
  have hlog : log (2 ^ k * y) = k * log 2 + log y := by
    rw [log_mul (by positivity) hy.ne', log_pow]
  rw [hlog] at h
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have l1 := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hk
  have l2 := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hk
  obtain ⟨h3, h4⟩ := abs_le.mp h
  constructor <;> linarith

/-! ### The muon -/

theorem log_mu_lo : -53315987857 / 10 ^ 10 ≤ log (483633159 / 10 ^ 11 : ℝ) := by
  have h := (log_mem_of_series 7 20 (y := 483633159 / 10 ^ 11) (by norm_num)
    (by norm_num)).1
  refine le_trans ?_ h
  norm_num [lS, Finset.sum_range_succ]

theorem log_mu_hi : log (483633181 / 10 ^ 11 : ℝ) ≤ -53315987316 / 10 ^ 10 := by
  have h := (log_mem_of_series 7 20 (y := 483633181 / 10 ^ 11) (by norm_num)
    (by norm_num)).2
  refine h.trans ?_
  norm_num [lS, Finset.sum_range_succ]

theorem a2Heavy_mu_lo : (5197386525 : ℝ) / 10 ^ 16 ≤ a2Heavy (483633159 / 10 ^ 11) := by
  have hL := log_mu_lo
  generalize hy : (483633159 / 10 ^ 11 : ℝ) = y at hL ⊢
  have hL6 : |log y| ≤ 6 := by
    have : log y < 0 := log_neg (by rw [← hy]; norm_num) (by rw [← hy]; norm_num)
    rw [abs_of_neg this]
    linarith
  have h := abs_le.mp (abs_a2Heavy_sub_ser_le 11 (by rw [← hy]; norm_num)
    (by rw [← hy]; norm_num) hL6)
  have hQ : 0 < hlSerQ 11 y := by norm_num [← hy, hlSerQ, lS, Finset.sum_range_succ]
  have hQL := mul_le_mul_of_nonneg_left hL hQ.le
  have hnum : (5197386525 : ℝ) / 10 ^ 16 ≤
      hlSerP 11 y + hlSerQ 11 y * (-53315987857 / 10 ^ 10) - hlSerE 11 y 6 := by
    norm_num [← hy, hlSerP, hlSerQ, hlSerE, lS, lT, Finset.sum_range_succ]
  linarith [h.1]

theorem a2Heavy_mu_hi : a2Heavy (483633181 / 10 ^ 11) ≤ (5197386998 : ℝ) / 10 ^ 16 := by
  have hL := log_mu_hi
  generalize hy : (483633181 / 10 ^ 11 : ℝ) = y at hL ⊢
  have hL6 : |log y| ≤ 6 := by
    have h0 : log y < 0 := log_neg (by rw [← hy]; norm_num) (by rw [← hy]; norm_num)
    have h1 : -6 ≤ log y := by
      have := (log_mem_of_series 7 20 (y := y) (by rw [← hy]; norm_num)
        (by rw [← hy]; norm_num)).1
      refine le_trans ?_ this
      norm_num [← hy, lS, Finset.sum_range_succ]
    rw [abs_of_neg h0]
    linarith
  have h := abs_le.mp (abs_a2Heavy_sub_ser_le 11 (by rw [← hy]; norm_num)
    (by rw [← hy]; norm_num) hL6)
  have hQ : 0 < hlSerQ 11 y := by norm_num [← hy, hlSerQ, lS, Finset.sum_range_succ]
  have hQL := mul_le_mul_of_nonneg_left hL hQ.le
  have hnum : hlSerP 11 y + hlSerQ 11 y * (-53315987316 / 10 ^ 10) + hlSerE 11 y 6 ≤
      (5197386998 : ℝ) / 10 ^ 16 := by
    norm_num [← hy, hlSerP, hlSerQ, hlSerE, lS, lT, Finset.sum_range_succ]
  linarith [h.2]

/-- **The muon enclosure.** For `mₑ/m_μ = y ∈ [4.83633159, 4.83633181]·10⁻³` (AKN Table 1,
`4.83633170(11)·10⁻³`), `5.197386525·10⁻⁷ ≤ A(y) ≤ 5.197386998·10⁻⁷`. -/
theorem heavyIntegral_mu_bounds {y : ℝ} (h1 : 483633159 / 10 ^ 11 ≤ y)
    (h2 : y ≤ 483633181 / 10 ^ 11) :
    (5197386525 : ℝ) / 10 ^ 16 ≤ heavyIntegral y ∧
      heavyIntegral y ≤ (5197386998 : ℝ) / 10 ^ 16 := by
  constructor
  · calc (5197386525 : ℝ) / 10 ^ 16 ≤ a2Heavy (483633159 / 10 ^ 11) := a2Heavy_mu_lo
      _ = heavyIntegral (483633159 / 10 ^ 11) :=
          (heavyIntegral_eq ⟨by norm_num, by norm_num⟩).symm
      _ ≤ heavyIntegral y := heavyIntegral_mono (by norm_num) h1 (by linarith)
  · calc heavyIntegral y ≤ heavyIntegral (483633181 / 10 ^ 11) :=
          heavyIntegral_mono (by linarith) h2 (by norm_num)
      _ = a2Heavy (483633181 / 10 ^ 11) := heavyIntegral_eq ⟨by norm_num, by norm_num⟩
      _ ≤ (5197386998 : ℝ) / 10 ^ 16 := a2Heavy_mu_hi

/-! ### The tau -/

theorem log_tau_lo : -40770290871 / 5000000000 ≤ log (287566 / 10 ^ 9 : ℝ) := by
  have h := (log_mem_of_series 11 20 (y := 287566 / 10 ^ 9) (by norm_num)
    (by norm_num)).1
  refine le_trans ?_ h
  norm_num [lS, Finset.sum_range_succ]

theorem log_tau_hi : log (287604 / 10 ^ 9 : ℝ) ≤ -81539260073 / 10 ^ 10 := by
  have h := (log_mem_of_series 11 20 (y := 287604 / 10 ^ 9) (by norm_num)
    (by norm_num)).2
  refine h.trans ?_
  norm_num [lS, Finset.sum_range_succ]

theorem a2Heavy_tau_lo : (18376481 : ℝ) / 10 ^ 16 ≤ a2Heavy (287566 / 10 ^ 9) := by
  have hL := log_tau_lo
  generalize hy : (287566 / 10 ^ 9 : ℝ) = y at hL ⊢
  have hL9 : |log y| ≤ 9 := by
    have : log y < 0 := log_neg (by rw [← hy]; norm_num) (by rw [← hy]; norm_num)
    rw [abs_of_neg this]
    linarith
  have h := abs_le.mp (abs_a2Heavy_sub_ser_le 11 (by rw [← hy]; norm_num)
    (by rw [← hy]; norm_num) hL9)
  have hQ : 0 < hlSerQ 11 y := by norm_num [← hy, hlSerQ, lS, Finset.sum_range_succ]
  have hQL := mul_le_mul_of_nonneg_left hL hQ.le
  have hnum : (18376481 : ℝ) / 10 ^ 16 ≤
      hlSerP 11 y + hlSerQ 11 y * (-40770290871 / 5000000000) - hlSerE 11 y 9 := by
    norm_num [← hy, hlSerP, hlSerQ, hlSerE, lS, lT, Finset.sum_range_succ]
  linarith [h.1]

theorem a2Heavy_tau_hi : a2Heavy (287604 / 10 ^ 9) ≤ (18381339 : ℝ) / 10 ^ 16 := by
  have hL := log_tau_hi
  generalize hy : (287604 / 10 ^ 9 : ℝ) = y at hL ⊢
  have hL9 : |log y| ≤ 9 := by
    have h0 : log y < 0 := log_neg (by rw [← hy]; norm_num) (by rw [← hy]; norm_num)
    have h1 : -9 ≤ log y := by
      have := (log_mem_of_series 11 20 (y := y) (by rw [← hy]; norm_num)
        (by rw [← hy]; norm_num)).1
      refine le_trans ?_ this
      norm_num [← hy, lS, Finset.sum_range_succ]
    rw [abs_of_neg h0]
    linarith
  have h := abs_le.mp (abs_a2Heavy_sub_ser_le 11 (by rw [← hy]; norm_num)
    (by rw [← hy]; norm_num) hL9)
  have hQ : 0 < hlSerQ 11 y := by norm_num [← hy, hlSerQ, lS, Finset.sum_range_succ]
  have hQL := mul_le_mul_of_nonneg_left hL hQ.le
  have hnum : hlSerP 11 y + hlSerQ 11 y * (-81539260073 / 10 ^ 10) + hlSerE 11 y 9 ≤
      (18381339 : ℝ) / 10 ^ 16 := by
    norm_num [← hy, hlSerP, hlSerQ, hlSerE, lS, lT, Finset.sum_range_succ]
  linarith [h.2]

/-- **The tau enclosure.** For `mₑ/m_τ = y ∈ [2.87566, 2.87604]·10⁻⁴` (AKN Table 1,
`2.87585(19)·10⁻⁴`), `1.8376481·10⁻⁹ ≤ A(y) ≤ 1.8381339·10⁻⁹`. -/
theorem heavyIntegral_tau_bounds {y : ℝ} (h1 : 287566 / 10 ^ 9 ≤ y) (h2 : y ≤ 287604 / 10 ^ 9) :
    (18376481 : ℝ) / 10 ^ 16 ≤ heavyIntegral y ∧ heavyIntegral y ≤ (18381339 : ℝ) / 10 ^ 16 := by
  constructor
  · calc (18376481 : ℝ) / 10 ^ 16 ≤ a2Heavy (287566 / 10 ^ 9) := a2Heavy_tau_lo
      _ = heavyIntegral (287566 / 10 ^ 9) := (heavyIntegral_eq ⟨by norm_num, by norm_num⟩).symm
      _ ≤ heavyIntegral y := heavyIntegral_mono (by norm_num) h1 (by linarith)
  · calc heavyIntegral y ≤ heavyIntegral (287604 / 10 ^ 9) :=
          heavyIntegral_mono (by linarith) h2 (by norm_num)
      _ = a2Heavy (287604 / 10 ^ 9) := heavyIntegral_eq ⟨by norm_num, by norm_num⟩
      _ ≤ (18381339 : ℝ) / 10 ^ 16 := a2Heavy_tau_hi

end QED.Chain.HeavyLepton
