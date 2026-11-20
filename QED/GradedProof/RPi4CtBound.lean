/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.GradedProof.RPi4PairF

/-!
# (R-Π₄) step L7: the mass insertion of a light photon pair is small

Helper level for the Phase 5 Stage 2 goal (R-Π₄)
`QED.Graded.vacuumPolarizationPart_two_lepton_limit` (decision D-57), step L7 (mass part). The
on-shell mass insertion at the photon pair `(a, b)` is
`ctPair e m a b = -(e²/4π²) ∫₀¹ L + (e²/8π²) ∫₀¹ (1 - x) L`,
`L(x) = log((x²m² + (1-x)b²)/(x²m² + (1-x)a²))`. For `0 < a ≤ b`:

* `onShellL_nonneg`, `onShellL_le`: `0 ≤ L(x) ≤ 4 √(b/(m x))` on `(0, 1)` (from
  `log(1 + v⁴) ≤ 4 log(1 + v) ≤ 4 v`);
* `abs_ctPair_le`: `|ctPair e m a b| ≤ 3 e² √(b/m) / π²`.
-/

@[expose] public section

open Set intervalIntegral

namespace QED.GradedProof.RPi4

theorem onShellL_nonneg {m a b x : ℝ} (hm : m ≠ 0) (ha : 0 < a) (hab : a ≤ b)
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ onShellL m a b x := by
  have pa := onShell_denom_pos hm hx (pow_pos ha 2)
  have h1x : 0 ≤ 1 - x := by linarith [hx.2]
  refine Real.log_nonneg ?_
  rw [le_div_iff₀ pa, one_mul]
  have : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  nlinarith

theorem onShellL_le {m a b x : ℝ} (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b)
    (hx : x ∈ Ioo (0 : ℝ) 1) : onShellL m a b x ≤ 4 * Real.sqrt (b / (m * x)) := by
  have hx' : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have pa := onShell_denom_pos hm.ne' hx' (pow_pos ha 2)
  have pb := onShell_denom_pos hm.ne' hx' (pow_pos (ha.trans_le hab) 2)
  have hx0 := hx.1
  have h1x : 0 ≤ 1 - x := by linarith [hx.2]
  have hmx : 0 < m * x := mul_pos hm hx0
  set v := Real.sqrt (b / (m * x)) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv2 : v ^ 2 = b / (m * x) := Real.sq_sqrt (div_nonneg (ha.trans_le hab).le hmx.le)
  have hv4 : v ^ 4 = b ^ 2 / (x ^ 2 * m ^ 2) := by
    rw [show v ^ 4 = (v ^ 2) ^ 2 by ring, hv2]
    field_simp
  -- the ratio is at most `1 + v⁴`
  have hrat : (x ^ 2 * m ^ 2 + (1 - x) * b ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * a ^ 2) ≤
      1 + v ^ 4 := by
    rw [div_le_iff₀ pa, hv4]
    have hxm : 0 < x ^ 2 * m ^ 2 := by positivity
    have hq : (1 - x) * b ^ 2 ≤ b ^ 2 / (x ^ 2 * m ^ 2) * (x ^ 2 * m ^ 2) := by
      rw [div_mul_cancel₀ _ hxm.ne']
      nlinarith [sq_nonneg b]
    have hq2 : 0 ≤ b ^ 2 / (x ^ 2 * m ^ 2) * ((1 - x) * a ^ 2) := by positivity
    nlinarith
  have hratpos : 0 < (x ^ 2 * m ^ 2 + (1 - x) * b ^ 2) / (x ^ 2 * m ^ 2 + (1 - x) * a ^ 2) :=
    div_pos pb pa
  calc onShellL m a b x
      ≤ Real.log (1 + v ^ 4) := Real.log_le_log hratpos hrat
    _ ≤ Real.log ((1 + v) ^ 4) := by
        refine Real.log_le_log (by positivity) ?_
        nlinarith [pow_nonneg hv0 2, pow_nonneg hv0 3]
    _ = 4 * Real.log (1 + v) := by rw [Real.log_pow]; norm_num
    _ ≤ 4 * v := by
        have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + v)
        linarith

theorem sqrt_div_mul_eq {m b x : ℝ} (hx : 0 < x) :
    Real.sqrt (b / (m * x)) = Real.sqrt (b / m) * x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, div_mul_eq_div_div, Real.sqrt_div' _ hx.le]
  · rw [div_eq_mul_inv]

theorem integral_onShellL_le {m a b : ℝ} (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in (0 : ℝ)..1, onShellL m a b x ≤ 8 * Real.sqrt (b / m) := by
  have hc := continuousOn_onShellL hm.ne' ha (ha.trans_le hab)
  have hint : IntervalIntegrable (fun x : ℝ => 4 * Real.sqrt (b / m) * x ^ (-(1 / 2 : ℝ)))
      MeasureTheory.volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have hval : ∫ x in (0 : ℝ)..1, 4 * Real.sqrt (b / m) * x ^ (-(1 / 2 : ℝ)) =
      8 * Real.sqrt (b / m) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
    norm_num
    ring
  calc ∫ x in (0 : ℝ)..1, onShellL m a b x
      ≤ ∫ x in (0 : ℝ)..1, 4 * Real.sqrt (b / m) * x ^ (-(1 / 2 : ℝ)) := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hc.intervalIntegrable hint
          fun x hx => ?_
        rw [mul_assoc, ← sqrt_div_mul_eq hx.1]
        exact onShellL_le hm ha hab hx
    _ = 8 * Real.sqrt (b / m) := hval

/-- **The on-shell mass insertion of a light photon pair is `O(√b)`.** -/
theorem abs_ctPair_le (e : ℝ) {m a b : ℝ} (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b) :
    |ctPair e m a b| ≤ 3 * e ^ 2 * Real.sqrt (b / m) / Real.pi ^ 2 := by
  have hc := continuousOn_onShellL hm.ne' ha (ha.trans_le hab)
  set I₁ := ∫ x in (0 : ℝ)..1, onShellL m a b x
  set I₂ := ∫ x in (0 : ℝ)..1, (1 - x) * onShellL m a b x
  have hI₁ := integral_onShellL_le hm ha hab
  have hnn : ∀ x ∈ uIcc (0 : ℝ) 1, 0 ≤ onShellL m a b x := fun x hx =>
    onShellL_nonneg hm.ne' ha hab (by rwa [uIcc_of_le zero_le_one] at hx)
  have h0 : 0 ≤ I₂ := intervalIntegral.integral_nonneg zero_le_one fun x hx =>
    mul_nonneg (by linarith [hx.2]) (hnn x (by rw [uIcc_of_le zero_le_one]; exact hx))
  have h0' : 0 ≤ I₁ := intervalIntegral.integral_nonneg zero_le_one fun x hx =>
    hnn x (by rw [uIcc_of_le zero_le_one]; exact hx)
  have h12 : I₂ ≤ I₁ := intervalIntegral.integral_mono_on zero_le_one
    ((ContinuousOn.mul (by fun_prop) hc).intervalIntegrable) hc.intervalIntegrable
    fun x hx => by
      have := hnn x (by rw [uIcc_of_le zero_le_one]; exact hx)
      nlinarith [hx.1]
  have hπ : 0 < Real.pi ^ 2 := by positivity
  have he : 0 ≤ e ^ 2 := sq_nonneg e
  have hs : 0 ≤ Real.sqrt (b / m) := Real.sqrt_nonneg _
  simp only [ctPair]
  rw [abs_le]
  constructor
  · have : e ^ 2 / (4 * Real.pi ^ 2) * I₁ ≤ e ^ 2 / (4 * Real.pi ^ 2) * (8 * Real.sqrt (b / m)) :=
      mul_le_mul_of_nonneg_left hI₁ (by positivity)
    have h2 : 0 ≤ e ^ 2 / (8 * Real.pi ^ 2) * I₂ := by positivity
    have h3 : e ^ 2 / (4 * Real.pi ^ 2) * (8 * Real.sqrt (b / m)) ≤
        3 * e ^ 2 * Real.sqrt (b / m) / Real.pi ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hπ]
      nlinarith [mul_nonneg he hs]
    linarith
  · have : e ^ 2 / (8 * Real.pi ^ 2) * I₂ ≤ e ^ 2 / (8 * Real.pi ^ 2) * (8 * Real.sqrt (b / m)) :=
      mul_le_mul_of_nonneg_left (h12.trans hI₁) (by positivity)
    have h2 : 0 ≤ e ^ 2 / (4 * Real.pi ^ 2) * I₁ := by positivity
    have h3 : e ^ 2 / (8 * Real.pi ^ 2) * (8 * Real.sqrt (b / m)) ≤
        3 * e ^ 2 * Real.sqrt (b / m) / Real.pi ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hπ]
      nlinarith [mul_nonneg he hs]
    linarith

end QED.GradedProof.RPi4

end
