/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RHighPt
public import QED.ThreeLoopD.SetDMastersI12RFirst

/-!
# Set (d), master `I₁₂`: the face integrands of all orders in the variable `r`

The pointwise `N`-th `ε`-derivatives `QED.ThreeLoopD.i12TAd N θ u`, `QED.ThreeLoopD.i12TBd N θ u`
of the face integrands of `T_A`, `T_B` depend on `θ` only through `r = kθ` (for `T_A`) and
`r = θ/k` (for `T_B`), `k = 2u/(1 - u)` (`QED.ThreeLoopD.i12Rk`):

  `i12TAd N θ u = (2/θ) f_N(kθ; -log 2 - log u)`,   `i12TBd N θ u = (2/θ) f_N(θ/k; -log (1 - u))`,

with (`QED.ThreeLoopD.i12Tf`)

  `f_N(r; c) = (1 + r)²/r (c + 2 log r - 3 log (1 + r))ᴺ - r (c - log r)ᴺ`
    `- (1/r + 2) (c + 2 log r)ᴺ + 3N (c + 2 log r)ᴺ⁻¹`.

The logarithmic moments: with `P_N(Y) = ∑_{i ≤ N} N!/(N - i)! Y^{N - i}`
(`QED.ThreeLoopD.i12TPn`, so that `P_N - P_N' = Yᴺ`),

  `∫_s^1 (Y - log t)ᴺ dt = P_N(Y) - s P_N(Y - log s)`,
  `∫_0^s (Y - log (1 - t))ᴺ dt = P_N(Y) - (1 - s) P_N(Y - log (1 - s))`.

## Main results

* `QED.ThreeLoopD.i12TAd_eq`, `QED.ThreeLoopD.i12TBd_eq`.
* `QED.ThreeLoopD.integral_Ioo_sub_log_pow`, `QED.ThreeLoopD.integral_Ioo_sub_log_one_sub_pow`.
-/

@[expose] public section

open Real Set MeasureTheory Filter Topology

namespace QED.ThreeLoopD

/-- `f_N(r; c)`, the face integrand of order `N` in the variable `r`. -/
noncomputable def i12Tf (N : ℕ) (c r : ℝ) : ℝ :=
  (1 + r) ^ 2 / r * (c + 2 * log r - 3 * log (1 + r)) ^ N - r * (c - log r) ^ N -
    (1 / r + 2) * (c + 2 * log r) ^ N + 3 * N * (c + 2 * log r) ^ (N - 1)

/-- The bracket of `i12TAd` with `X = rY`. -/
theorem i12T_bracket_left {N : ℕ} {B Y r : ℝ} (hY : 0 < Y) (hr : 0 < r) :
    (r * Y + Y) ^ 2 / (r * Y * Y) * (B + -3 * log (r * Y + Y)) ^ N -
      r * Y / Y * (B + -3 * log (r * Y)) ^ N - Y / (r * Y) * (B + -3 * log Y) ^ N -
      2 * (B + -3 * log Y) ^ N + 3 * N * (B + -3 * log Y) ^ (N - 1) =
    i12Tf N (B - 3 * log Y - 2 * log r) r := by
  have h1 : 0 < 1 + r := by linarith
  rw [show r * Y + Y = (1 + r) * Y by ring, log_mul h1.ne' hY.ne', log_mul hr.ne' hY.ne']
  unfold i12Tf
  rw [show B + -3 * (log (1 + r) + log Y) =
      B - 3 * log Y - 2 * log r + 2 * log r - 3 * log (1 + r) by ring,
    show B + -3 * (log r + log Y) = B - 3 * log Y - 2 * log r - log r by ring,
    show B + -3 * log Y = B - 3 * log Y - 2 * log r + 2 * log r by ring]
  generalize (B - 3 * log Y - 2 * log r + 2 * log r - 3 * log (1 + r)) ^ N = P1
  generalize (B - 3 * log Y - 2 * log r - log r) ^ N = P2
  generalize (B - 3 * log Y - 2 * log r + 2 * log r) ^ N = P3
  generalize (B - 3 * log Y - 2 * log r + 2 * log r) ^ (N - 1) = P4
  field_simp
  ring

/-- The bracket of `i12TBd` with `Y = rX`. -/
theorem i12T_bracket_right {N : ℕ} {B X r : ℝ} (hX : 0 < X) (hr : 0 < r) :
    (X + r * X) ^ 2 / (X * (r * X)) * (B + -3 * log (X + r * X)) ^ N -
      X / (r * X) * (B + -3 * log X) ^ N - r * X / X * (B + -3 * log (r * X)) ^ N -
      2 * (B + -3 * log X) ^ N + 3 * N * (B + -3 * log X) ^ (N - 1) =
    i12Tf N (B - 3 * log X - 2 * log r) r := by
  rw [← i12T_bracket_left hX hr, add_comm X (r * X), mul_comm X (r * X)]
  ring

theorem i12_log_i12Rk {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    log (i12Rk u) = log 2 + log u - log (1 - u) := by
  have h1u : 0 < 1 - u := by linarith [hu.2]
  unfold i12Rk
  rw [log_div (by linarith [hu.1]) h1u.ne', log_mul (by norm_num) hu.1.ne']

/-- **The face integrand of `T_A` in the variable `r = kθ`.** -/
theorem i12TAd_eq (N : ℕ) {θ u : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i12TAd N θ u = 2 / θ * i12Tf N (-log 2 - log u) (i12Rk u * θ) := by
  obtain ⟨hθ0, -⟩ := hθ
  have hu0 := hu.1
  have h1u : 0 < 1 - u := by linarith [hu.2]
  have hk := i12Rk_pos hu
  have hY : 0 < (1 - u) * (1 / 2 : ℝ) := by positivity
  have hr : 0 < i12Rk u * θ := mul_pos hk hθ0
  have hX : u * θ = i12Rk u * θ * ((1 - u) * (1 / 2)) := by
    unfold i12Rk; field_simp
  simp only [i12TAd]
  rw [hX, i12T_bracket_left hY hr]
  have hc : 2 * log θ + 2 * log (1 / 2) + log (u * (1 - u)) - 3 * log ((1 - u) * (1 / 2)) -
      2 * log (i12Rk u * θ) = -log 2 - log u := by
    rw [log_mul hk.ne' hθ0.ne', i12_log_i12Rk hu, log_mul hu0.ne' h1u.ne',
      log_mul h1u.ne' (by norm_num), one_div, log_inv]
    ring
  rw [hc]
  field_simp

/-- **The face integrand of `T_B` in the variable `r = θ/k`.** -/
theorem i12TBd_eq (N : ℕ) {θ u : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    i12TBd N θ u = 2 / θ * i12Tf N (-log (1 - u)) (θ / i12Rk u) := by
  obtain ⟨hθ0, -⟩ := hθ
  have hu0 := hu.1
  have h1u : 0 < 1 - u := by linarith [hu.2]
  have hk := i12Rk_pos hu
  have hr : 0 < θ / i12Rk u := div_pos hθ0 hk
  have hY : (1 - u) * θ * (1 / 2) = θ / i12Rk u * u := by
    unfold i12Rk; field_simp
  simp only [i12TBd]
  rw [hY, i12T_bracket_right hu0 hr]
  have hc : 2 * log θ + 2 * log (1 / 2) + log (u * (1 - u)) - 3 * log u -
      2 * log (θ / i12Rk u) = -log (1 - u) := by
    rw [log_div hθ0.ne' hk.ne', i12_log_i12Rk hu, log_mul hu0.ne' h1u.ne', one_div, log_inv]
    ring
  rw [hc]
  field_simp

/-! ### The logarithmic moments -/

/-- `P_N(Y) = ∑_{i ≤ N} N!/(N - i)! Y^{N - i}`, by `P_0 = 1`, `P_{N+1} = Y^{N+1} + (N+1) P_N`. -/
noncomputable def i12TPn : ℕ → ℝ → ℝ
  | 0, _ => 1
  | N + 1, Y => Y ^ (N + 1) + (N + 1) * i12TPn N Y

theorem i12TPn_eq (N : ℕ) (Y : ℝ) : i12TPn N Y = Y ^ N + N * i12TPn (N - 1) Y := by
  cases N with
  | zero => simp [i12TPn]
  | succ N => simp [i12TPn]

theorem hasDerivAt_i12TPn (N : ℕ) (Y : ℝ) :
    HasDerivAt (i12TPn N) (N * i12TPn (N - 1) Y) Y := by
  induction N generalizing Y with
  | zero => simpa [i12TPn] using hasDerivAt_const Y (1 : ℝ)
  | succ N ih =>
    have h := ((hasDerivAt_pow (N + 1) Y).add ((ih Y).const_mul ((N : ℝ) + 1)))
    have e : ((fun x : ℝ => x ^ (N + 1)) + fun y => ((N : ℝ) + 1) * i12TPn N y) =
        i12TPn (N + 1) := by
      funext Y; simp [i12TPn]
    rw [e] at h
    refine h.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    rw [i12TPn_eq N Y]
    push_cast
    ring

/-- The primitive `t P_N(Y - log t)` of `(Y - log t)ᴺ`. -/
theorem hasDerivAt_mul_i12TPn_sub_log (N : ℕ) (Y : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => t * i12TPn N (Y - log t)) ((Y - log t) ^ N) t := by
  have hl : HasDerivAt (fun t => Y - log t) (-t⁻¹) t := (hasDerivAt_log ht.ne').const_sub Y
  have h := (hasDerivAt_id' t).mul ((hasDerivAt_i12TPn N (Y - log t)).comp t hl)
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [i12TPn_eq N (Y - log t)]
  field_simp
  ring

/-- The primitive `-(1 - t) P_N(Y - log (1 - t))` of `(Y - log (1 - t))ᴺ`. -/
theorem hasDerivAt_mul_i12TPn_sub_log_one_sub (N : ℕ) (Y : ℝ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (fun t => -((1 - t) * i12TPn N (Y - log (1 - t)))) ((Y - log (1 - t)) ^ N) t := by
  have h1 : 0 < 1 - t := by linarith
  have hs : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := (hasDerivAt_id' t).const_sub 1
  have hl : HasDerivAt (fun t => Y - log (1 - t)) (-(-1 / (1 - t))) t :=
    (hs.log h1.ne').const_sub Y
  have h := (hs.mul ((hasDerivAt_i12TPn N (Y - log (1 - t))).comp t hl)).neg
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [i12TPn_eq N (Y - log (1 - t))]
  field_simp
  ring

/-- **`∫_s^1 (Y - log t)ᴺ dt = P_N(Y) - s P_N(Y - log s)`.** -/
theorem integral_Ioo_sub_log_pow (N : ℕ) (Y : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    IntegrableOn (fun t => (Y - log t) ^ N) (Ioo s 1) ∧
      ∫ t in Ioo s 1, (Y - log t) ^ N = i12TPn N Y - s * i12TPn N (Y - log s) := by
  have hc : ContinuousOn (fun t => (Y - log t) ^ N) (Icc s 1) :=
    (continuousOn_const.sub (continuousOn_log.mono fun t ht => (by
      linarith [ht.1] : (0 : ℝ) < t).ne')).pow N
  refine ⟨(hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs1.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => t * i12TPn N (Y - log t))
      (fun t ht => hasDerivAt_mul_i12TPn_sub_log N Y (by
        rw [uIcc_of_le hs1.le] at ht; linarith [ht.1]))
      ((hc.mono (by rw [uIcc_of_le hs1.le])).intervalIntegrable)]
  simp

/-- **`∫_0^s (Y - log (1 - t))ᴺ dt = P_N(Y) - (1 - s) P_N(Y - log (1 - s))`.** -/
theorem integral_Ioo_sub_log_one_sub_pow (N : ℕ) (Y : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    IntegrableOn (fun t => (Y - log (1 - t)) ^ N) (Ioo 0 s) ∧
      ∫ t in Ioo 0 s, (Y - log (1 - t)) ^ N =
        i12TPn N Y - (1 - s) * i12TPn N (Y - log (1 - s)) := by
  have hc : ContinuousOn (fun t => (Y - log (1 - t)) ^ N) (Icc 0 s) :=
    (continuousOn_const.sub ((continuousOn_const.sub continuousOn_id).log fun t ht => (by
      linarith [ht.2] : (0 : ℝ) < 1 - t).ne')).pow N
  refine ⟨(hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self, ?_⟩
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => -((1 - t) * i12TPn N (Y - log (1 - t))))
      (fun t ht => hasDerivAt_mul_i12TPn_sub_log_one_sub N Y (by
        rw [uIcc_of_le hs.le] at ht; linarith [ht.2]))
      ((hc.mono (by rw [uIcc_of_le hs.le])).intervalIntegrable)]
  simp
  ring

end QED.ThreeLoopD
