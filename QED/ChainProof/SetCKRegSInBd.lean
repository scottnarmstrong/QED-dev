/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKRegLInBd
public import QED.TwoLoop.UnitSCLimitSMasters

/-!
# Set (c), Stage K: the self-energy integrand with a massive inner photon, bound

Helper level (no frozen statement). In the self-energy unit with the inner photon of mass² `t`
(`M = M_t(Y) ∈ [m₀, 1 + t]`, `m₀ = (3/4) min(1, t)`) and outer photon mass `λ`
(`h = M_λ(x)/x ≥ x`), the `x`-integrand of eq. (5.3) is `G_S = selfGm λ √t + k₂/h²` (the engine's
`E - e₀`). With `c = Y(1-Y)`, `0 ≤ k₁ ≤ (3/2) x`, `|k₂| ≤ (3/4) x²` every term of `G_S` is bounded
by a constant or by a constant times `log(1 + M/(ch)) ≤ 1 + t + ℓ(Y, x)`; no cancellation is
needed:

* **`abs_sForm_add_le`**: `|sForm(k₁, k₂, c, h, M, log(M + ch), log(1 + M/(ch))) + k₂/h²| ≤
  (1 + 1/m)² (4 + 4N) (1 + ℓ(Y, x))` for `h ≥ x`, `0 < m ≤ M ≤ N`;
* **`abs_selfInS_le`**: `|G_S(λ; Y, x)| ≤ K_S(t) (1 + ℓ(Y, x))` for every outer mass `λ`
  (`selfInS`, `selfInSBd`).
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology Function

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitLLink QED.TwoLoop.UnitSCLimit

/-- The self-energy `x`-integrand at outer photon mass `λ` and inner photon mass² `t`. -/
noncomputable def selfInS (t lam Y x : ℝ) : ℝ :=
  selfGm lam (√t) Y x + selfK2 Y x / (ladderInnerMass 1 lam x / x) ^ 2

/-- The constant of the bound on `selfInS`. -/
noncomputable def selfInSBd (t : ℝ) : ℝ := (1 + 1 / (3 / 4 * min 1 t)) ^ 2 * (8 + 4 * t)

theorem selfK1_bounds {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 ≤ selfK1 Y x ∧ selfK1 Y x ≤ 3 / 2 * x ∧ selfK1 Y x ≤ 3 / 8 := by
  unfold selfK1
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hg0 : 0 ≤ 2 * Y * x + Y - 2 * x + 2 := by nlinarith [mul_pos hx.1 hY.1, hY.1]
  have hg3 : 2 * Y * x + Y - 2 * x + 2 ≤ 3 := by
    have : 0 ≤ (1 - Y) * (1 + 2 * x) := mul_nonneg hY1.le (by linarith [hx.1])
    nlinarith [this]
  have e : -(x * (x - 1) * (2 * Y * x + Y - 2 * x + 2)) / 2 =
      x * (1 - x) * (2 * Y * x + Y - 2 * x + 2) / 2 := by ring
  rw [e]
  have hxx : x * (1 - x) ≤ 1 / 4 := c_le_quarter x
  have h0 : 0 ≤ x * (1 - x) := by nlinarith [hx.1]
  refine ⟨by positivity, ?_, ?_⟩
  · have : (1 - x) * (2 * Y * x + Y - 2 * x + 2) ≤ 1 * 3 :=
      mul_le_mul (by linarith [hx.1]) hg3 hg0 zero_le_one
    nlinarith [hx.1]
  · have := mul_le_mul hxx hg3 hg0 (by norm_num)
    linarith

theorem abs_selfK2_le {Y x : ℝ} (hY : Y ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |selfK2 Y x| ≤ 3 / 4 * x ^ 2 := by
  unfold selfK2
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have e : x ^ 2 * (x - 1) * (Y * x - Y - x + 3) / 4 =
      -(x ^ 2 * ((1 - x) * (2 + (1 - Y) * (1 - x))) / 4) := by ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  have : (1 - x) * (2 + (1 - Y) * (1 - x)) ≤ 1 * 3 :=
    mul_le_mul (by linarith [hx.1]) (by nlinarith [mul_pos hY1 hx1, hY.1, hx.1]) (by positivity)
      zero_le_one
  have := mul_le_mul_of_nonneg_left this (sq_nonneg x)
  linarith

theorem selfK_coeff_bounds {k₁ k₂ x h : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxh : x ≤ h)
    (k10 : 0 ≤ k₁) (k1x : k₁ ≤ 3 / 2 * x) (k2x : |k₂| ≤ 3 / 4 * x ^ 2) :
    k₁ / h ≤ 3 / 2 ∧ |k₂| / h ^ 2 ≤ 3 / 4 ∧ |k₂| / h ≤ 3 / 4 ∧ |k₂| ≤ 3 / 4 := by
  have hh : 0 < h := lt_of_lt_of_le hx.1 hxh
  have hx2 : x ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ hx.1.le hxh 2
  have hx2' : x ^ 2 ≤ h := by nlinarith [hx.1, hx.2]
  have hx2'' : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hh]; linarith
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [div_le_iff₀ hh]; linarith
  · linarith

/-- The algebraic splitting of `sForm + k₂/h²` into ten terms. -/
theorem sForm_add_eq {k₁ k₂ c h M A B : ℝ} (hh : h ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) :
    sForm k₁ k₂ c h M A B + k₂ / h ^ 2 =
      -(k₁ / h * A) - k₂ / h ^ 2 * A - k₂ / h ^ 2 * (M / (M + c * h)) -
        2 * c * (k₂ / h) / (M + c * h) + k₂ * c ^ 2 * B / M ^ 2 - k₂ * c ^ 2 / (M * (M + c * h)) -
        2 * c * k₁ * B / M + k₁ * c / M - k₁ * c ^ 2 * h * B / M ^ 2 + k₂ / h ^ 2 := by
  unfold sForm
  field_simp
  ring

/-- The final polynomial comparison of `abs_sForm_add_le`. -/
theorem selfInSBd_poly {r N l : ℝ} (hr : 0 ≤ r) (hN : 0 ≤ N) (hl : 0 ≤ l) :
    9 / 4 * N + 105 / 32 + 39 / 16 * r + 3 / 64 * r ^ 2 + (3 / 64 * r ^ 2 + 3 / 16 * r) * (N + l) ≤
      (1 + r) ^ 2 * (4 + 4 * N) * (1 + l) := by
  have e : (1 + r) ^ 2 * (4 + 4 * N) * (1 + l) = (1 + 2 * r + r ^ 2) * (4 + 4 * N) +
      (1 + 2 * r + r ^ 2) * (4 + 4 * N) * l := by ring
  rw [e]
  have h1 : 0 ≤ r * N := mul_nonneg hr hN
  have h2 : 0 ≤ r ^ 2 * N := mul_nonneg (sq_nonneg r) hN
  have h3 : (3 / 64 * r ^ 2 + 3 / 16 * r) * l ≤ (1 + 2 * r + r ^ 2) * (4 + 4 * N) * l := by
    refine mul_le_mul_of_nonneg_right ?_ hl
    nlinarith [sq_nonneg r]
  nlinarith [sq_nonneg r]

theorem abs_ten_le {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 S : ℝ}
    (h1 : |T1| ≤ b1) (h2 : |T2| ≤ b2) (h3 : |T3| ≤ b3) (h4 : |T4| ≤ b4) (h5 : |T5| ≤ b5)
    (h6 : |T6| ≤ b6) (h7 : |T7| ≤ b7) (h8 : |T8| ≤ b8) (h9 : |T9| ≤ b9) (h10 : |T10| ≤ b10)
    (hS : b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 ≤ S) :
    |T1 - T2 - T3 - T4 + T5 - T6 - T7 + T8 - T9 + T10| ≤ S := by
  rw [abs_le] at *
  constructor <;> linarith

/-- **The bound on the self-energy integrand**, in the variables of `sForm`. -/
theorem abs_sForm_add_le {x Y h M m N : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hxh : x ≤ h) (hm : 0 < m) (hmM : m ≤ M) (hMN : M ≤ N) :
    |sForm (selfK1 Y x) (selfK2 Y x) (Y * (1 - Y)) h M (log (M + Y * (1 - Y) * h))
        (log (1 + M / (Y * (1 - Y) * h))) + selfK2 Y x / h ^ 2| ≤
      (1 + 1 / m) ^ 2 * (4 + 4 * N) * (1 + ladderEll Y x) := by
  have hY1 : 0 < 1 - Y := by linarith [hY.2]
  have hc : 0 < Y * (1 - Y) := mul_pos hY.1 hY1
  have hh : 0 < h := lt_of_lt_of_le hx.1 hxh
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hN : 0 ≤ N := hM.le.trans hMN
  have hl := ladderEll_nonneg hY hx
  have hBl := log_one_add_div_le_ell hx hY hxh hM hMN
  obtain ⟨k10, k1x, k18⟩ := selfK1_bounds hY hx
  have k2x := abs_selfK2_le hY hx
  have hcq : Y * (1 - Y) ≤ 1 / 4 := c_le_quarter Y
  have hz0 : 0 < M + Y * (1 - Y) * h := by positivity
  rw [sForm_add_eq hh.ne' hM.ne' hc.ne']
  generalize selfK1 Y x = k₁ at *
  generalize selfK2 Y x = k₂ at *
  generalize Y * (1 - Y) = c at *
  set z := M + c * h with hz_def
  set r := 1 / m with hr_def
  have hr : 0 < r := by positivity
  set u := M / (c * h) with hu_def
  have hu0 : 0 ≤ u := by positivity
  set B := log (1 + u) with hB_def
  have hB0 : 0 ≤ B := log_one_add_nonneg hu0
  have hBu : B ≤ u := log_one_add_le_self hu0
  have hiM : 1 / M ≤ r := one_div_le_one_div_of_le hm hmM
  have hiz : 1 / z ≤ r := one_div_le_one_div_of_le hm
    (by have : 0 ≤ c * h := by positivity
        rw [hz_def]; linarith)
  have hMz : M / z ≤ 1 := by
    rw [div_le_one hz0]
    have : 0 ≤ c * h := by positivity
    rw [hz_def]; linarith
  have hchz : c * h ≤ z := by rw [hz_def]; linarith
  -- elementary coefficient bounds
  obtain ⟨q1, q2, q2', q3⟩ := selfK_coeff_bounds hx hxh k10 k1x k2x
  have q1' : 0 ≤ k₁ / h := by positivity
  have hch0 : 0 ≤ c * h := by positivity
  have hmz : m ≤ z := by rw [hz_def]; linarith
  have hlz := abs_log_le_add_inv (lt_of_lt_of_le hm hmz)
  -- the ten terms
  have a1 : |-(k₁ / h * log z)| ≤ 3 / 2 * N + 3 / 32 + 3 / 2 * r := by
    rw [abs_neg, abs_mul, abs_of_nonneg q1']
    calc k₁ / h * |log z| ≤ k₁ / h * (z + 1 / z) := mul_le_mul_of_nonneg_left hlz q1'
      _ = k₁ / h * M + k₁ * c + k₁ / h * (1 / z) := by rw [hz_def]; field_simp
      _ ≤ 3 / 2 * N + 3 / 8 * (1 / 4) + 3 / 2 * r := by
          have := mul_le_mul q1 hMN hM.le (by norm_num)
          have := mul_le_mul k18 hcq hc.le (by norm_num)
          have := mul_le_mul q1 hiz (by positivity) (by norm_num)
          linarith
      _ = 3 / 2 * N + 3 / 32 + 3 / 2 * r := by ring
  have a2 : |k₂ / h ^ 2 * log z| ≤ 3 / 4 * N + 3 / 16 + 3 / 4 * r := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : 0 < h ^ 2)]
    calc |k₂| / h ^ 2 * |log z| ≤ |k₂| / h ^ 2 * (z + 1 / z) :=
          mul_le_mul_of_nonneg_left hlz (by positivity)
      _ = |k₂| / h ^ 2 * M + |k₂| / h * c + |k₂| / h ^ 2 * (1 / z) := by
          rw [hz_def]; field_simp
      _ ≤ 3 / 4 * N + 3 / 4 * (1 / 4) + 3 / 4 * r := by
          have := mul_le_mul q2 hMN hM.le (by norm_num)
          have := mul_le_mul q2' hcq hc.le (by norm_num)
          have := mul_le_mul q2 hiz (by positivity) (by norm_num)
          linarith
      _ = 3 / 4 * N + 3 / 16 + 3 / 4 * r := by ring
  have a3 : |k₂ / h ^ 2 * (M / z)| ≤ 3 / 4 := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : 0 < h ^ 2),
      abs_of_nonneg (by positivity : 0 ≤ M / z)]
    have := mul_le_mul q2 hMz (by positivity) (by norm_num)
    linarith
  have a4 : |2 * c * (k₂ / h) / z| ≤ 3 / 2 := by
    rw [abs_div, abs_mul, abs_div, abs_of_pos hh, abs_of_pos hz0,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * c)]
    rw [div_le_iff₀ hz0]
    have : 2 * c * (|k₂| / h) = 2 * (|k₂| / h ^ 2) * (c * h) := by field_simp
    rw [this]
    have := mul_le_mul q2 hchz (by positivity) (by norm_num)
    linarith only [this]
  have hc2 : c ^ 2 ≤ 1 / 16 := by
    calc c ^ 2 = c * c := sq c
      _ ≤ 1 / 4 * (1 / 4) := mul_le_mul hcq hcq hc.le (by norm_num)
      _ = 1 / 16 := by norm_num
  have hM2 : 1 / M ^ 2 ≤ r ^ 2 := by
    rw [one_div, ← inv_pow, ← one_div]; exact pow_le_pow_left₀ (by positivity) hiM 2
  have a5 : |k₂ * c ^ 2 * B / M ^ 2| ≤ 3 / 64 * r ^ 2 * B := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hB0, abs_of_nonneg (sq_nonneg c),
      abs_of_pos (by positivity : 0 < M ^ 2)]
    calc |k₂| * c ^ 2 * B / M ^ 2 = |k₂| * c ^ 2 * B * (1 / M ^ 2) := by ring
      _ ≤ 3 / 4 * (1 / 16) * B * r ^ 2 := by gcongr
      _ = 3 / 64 * r ^ 2 * B := by ring
  have a6 : |k₂ * c ^ 2 / (M * z)| ≤ 3 / 64 * r ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg c), abs_of_pos (by positivity : 0 < M * z)]
    calc |k₂| * c ^ 2 / (M * z) = |k₂| * c ^ 2 * ((1 / M) * (1 / z)) := by field_simp
      _ ≤ 3 / 4 * (1 / 16) * (r * r) := by gcongr
      _ = 3 / 64 * r ^ 2 := by ring
  have a7 : |2 * c * k₁ * B / M| ≤ 3 / 16 * r * B := by
    rw [abs_of_nonneg (by positivity)]
    calc 2 * c * k₁ * B / M = 2 * c * k₁ * B * (1 / M) := by ring
      _ ≤ 2 * (1 / 4) * (3 / 8) * B * r := by gcongr
      _ = 3 / 16 * r * B := by ring
  have a8 : |k₁ * c / M| ≤ 3 / 32 * r := by
    rw [abs_of_nonneg (by positivity)]
    calc k₁ * c / M = k₁ * c * (1 / M) := by ring
      _ ≤ 3 / 8 * (1 / 4) * r := by gcongr
      _ = 3 / 32 * r := by ring
  have a9 : |k₁ * c ^ 2 * h * B / M ^ 2| ≤ 3 / 32 * r := by
    rw [abs_of_nonneg (by positivity)]
    have : k₁ * c ^ 2 * h * B / M ^ 2 ≤ k₁ * c ^ 2 * h * u / M ^ 2 := by gcongr
    have e : k₁ * c ^ 2 * h * u / M ^ 2 = k₁ * c / M := by rw [hu_def]; field_simp
    rw [e] at this
    exact this.trans (by rw [abs_of_nonneg (by positivity)] at a8; exact a8)
  have a10 : |k₂ / h ^ 2| ≤ 3 / 4 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < h ^ 2)]; exact q2
  have hfin := selfInSBd_poly hr.le hN hl
  have e3 : (1 + 1 / m) = 1 + r := by rw [hr_def]
  rw [e3]
  have hBr : 3 / 64 * r ^ 2 * B + 3 / 16 * r * B ≤
      (3 / 64 * r ^ 2 + 3 / 16 * r) * (N + ladderEll Y x) := by
    rw [← add_mul]; exact mul_le_mul_of_nonneg_left hBl (by positivity)
  have hS : 3 / 2 * N + 3 / 32 + 3 / 2 * r + (3 / 4 * N + 3 / 16 + 3 / 4 * r) + 3 / 4 + 3 / 2 +
      3 / 64 * r ^ 2 * B + 3 / 64 * r ^ 2 + 3 / 16 * r * B + 3 / 32 * r + 3 / 32 * r + 3 / 4 ≤
      (1 + r) ^ 2 * (4 + 4 * N) * (1 + ladderEll Y x) := by
    linarith only [hfin, hBr]
  exact abs_ten_le a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 hS

/-- **The uniform bound on the self-energy integrand**: for every outer mass `λ`,
`|G_S(λ; Y, x)| ≤ K_S(t) (1 + ℓ(Y, x))` on `(0, 1)²`. -/
theorem abs_selfInS_le {t lam Y x : ℝ} (ht : 0 < t) (hY : Y ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) : |selfInS t lam Y x| ≤ selfInSBd t * (1 + ladderEll Y x) := by
  have hm : 0 < 3 / 4 * min 1 t := by have := lt_min one_pos ht; positivity
  have hxh : x ≤ ladderInnerMass 1 lam x / x := by
    rw [le_div_iff₀ hx.1]; unfold ladderInnerMass
    nlinarith [mul_nonneg (sub_nonneg.2 hx.2.le) (sq_nonneg lam)]
  have h := abs_sForm_add_le hx hY hxh hm (massIn_ge ht (Ioo_subset_Icc_self hY))
    (massIn_le ht (Ioo_subset_Icc_self hY))
  refine (le_of_eq ?_).trans (h.trans (le_of_eq ?_))
  · rfl
  · unfold selfInSBd; ring

end QED.ChainProof.SetCK
