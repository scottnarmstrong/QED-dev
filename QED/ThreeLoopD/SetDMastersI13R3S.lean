/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI13R3V
public import QED.Polylog.HPLSeries

/-!
# Set (d), master `I₁₃`: the basis functions near `ξ = 0`

A word `w ≠ []` with no trailing `0` has `H(w; x) = ∑ₙ c_w(n) xⁿ` with `|c_w(n)| ≤ 1`
(`QED.Polylog.HPL.hasSum_coef_mul_pow`), so the normalized remainder
`ρ_w(x) = (H(w; x) - c_w(1) x - c_w(2) x²)/x³` (`QED.ThreeLoopD.i13Rho`) has `|ρ_w(x)| ≤ 2` for
`0 < x < 1/2` (`QED.ThreeLoopD.abs_i13Rho_le`). The Lyndon words used by the limit of `F₃ - A₃`
are written as `c₁ x + c₂ x² + x³ ρ_w(x)` with their first two coefficients
(`QED.ThreeLoopD.i13hpl_rho_01` and its companions).

## Main results

* `QED.ThreeLoopD.abs_i13Rho_le`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real QED.Polylog QED.Polylog.HPL QED.Polylog.HPL.Letter

namespace QED.ThreeLoopD

/-- The normalized remainder `ρ_w(x) = (H(w; x) - c_w(1) x - c_w(2) x²)/x³`. -/
noncomputable def i13Rho (w : List Letter) (x : ℝ) : ℝ :=
  (hpl w x - coef w 1 * x - coef w 2 * x ^ 2) / x ^ 3

theorem abs_i13Rho_le {w : List Letter} (hw : w.getLast? ≠ some zero) (hne : w ≠ []) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : |i13Rho w x| ≤ 2 := by
  have hs := hasSum_coef_mul_pow w hw ⟨hx.1, by linarith [hx.2]⟩
  have ht := (hasSum_nat_add_iff' 3).mpr hs
  have hg : HasSum (fun n : ℕ => x ^ 3 * (1 / 2 : ℝ) ^ n) (x ^ 3 * 2) := by
    have := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at this
    simpa using this.mul_left (x ^ 3)
  have hle := ht.norm_le_of_bounded hg fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hx.1, pow_add, mul_comm (x ^ n)]
    calc |coef w (n + 3)| * (x ^ 3 * x ^ n) ≤ 1 * (x ^ 3 * (1 / 2) ^ n) :=
          mul_le_mul (abs_coef_le_one w _) (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hx.1.le hx.2.le n) (pow_nonneg hx.1.le 3))
            (mul_nonneg (pow_nonneg hx.1.le 3) (pow_nonneg hx.1.le n))
            zero_le_one
      _ = x ^ 3 * (1 / 2) ^ n := one_mul _
  obtain ⟨a, u, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, coef_cons_zero, Real.norm_eq_abs]
    at hle
  unfold i13Rho
  rw [abs_div, abs_of_pos (pow_pos hx.1 3), div_le_iff₀ (pow_pos hx.1 3)]
  calc |hpl (a :: u) x - coef (a :: u) 1 * x - coef (a :: u) 2 * x ^ 2|
      = |hpl (a :: u) x - (0 + 0 * x ^ 0 + coef (a :: u) 1 * x ^ 1 + coef (a :: u) 2 * x ^ 2)| := by
        ring_nf
    _ ≤ x ^ 3 * 2 := hle
    _ = 2 * x ^ 3 := by ring

theorem i13hpl_rho_0001 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, zero, one] x = x + x ^ 2 / 16 + i13Rho [zero, zero, zero, one] x * x ^ 3 := by
  have h1 : coef [zero, zero, zero, one] 1 = 1 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, zero, zero, one] 2 = 1 / 16 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_000m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, zero, negOne] x = x - x ^ 2 / 16 +
      i13Rho [zero, zero, zero, negOne] x * x ^ 3 := by
  have h1 : coef [zero, zero, zero, negOne] 1 = 1 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, zero, zero, negOne] 2 = -1 / 16 := by norm_num [coef, twistSum,
    Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_001 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, one] x = x + x ^ 2 / 8 + i13Rho [zero, zero, one] x * x ^ 3 := by
  have h1 : coef [zero, zero, one] 1 = 1 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, zero, one] 2 = 1 / 8 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_0011 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, one, one] x = x ^ 2 / 8 + i13Rho [zero, zero, one, one] x * x ^ 3 := by
  have h1 : coef [zero, zero, one, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, zero, one, one] 2 = 1 / 8 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_00m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, zero, negOne] x = x - x ^ 2 / 8 + i13Rho [zero, zero, negOne] x * x ^ 3 := by
  have h1 : coef [zero, zero, negOne] 1 = 1 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, zero, negOne] 2 = -1 / 8 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_01 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one] x = x + x ^ 2 / 4 + i13Rho [zero, one] x * x ^ 3 := by
  have h1 : coef [zero, one] 1 = 1 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, one] 2 = 1 / 4 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_011 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one, one] x = x ^ 2 / 4 + i13Rho [zero, one, one] x * x ^ 3 := by
  have h1 : coef [zero, one, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, one, one] 2 = 1 / 4 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_01m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, one, negOne] x = x ^ 2 / 4 + i13Rho [zero, one, negOne] x * x ^ 3 := by
  have h1 : coef [zero, one, negOne] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, one, negOne] 2 = 1 / 4 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_0m {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne] x = x - x ^ 2 / 4 + i13Rho [zero, negOne] x * x ^ 3 := by
  have h1 : coef [zero, negOne] 1 = 1 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, negOne] 2 = -1 / 4 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_0m01 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, zero, one] x = x ^ 2 / 4 + i13Rho [zero, negOne, zero, one] x * x ^ 3 := by
  have h1 : coef [zero, negOne, zero, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, negOne, zero, one] 2 = 1 / 4 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_0m1 {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, one] x = x ^ 2 / 4 + i13Rho [zero, negOne, one] x * x ^ 3 := by
  have h1 : coef [zero, negOne, one] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, negOne, one] 2 = 1 / 4 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_0mm {x : ℝ} (hx : x ≠ 0) :
    hpl [zero, negOne, negOne] x = x ^ 2 / 4 + i13Rho [zero, negOne, negOne] x * x ^ 3 := by
  have h1 : coef [zero, negOne, negOne] 1 = 0 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [zero, negOne, negOne] 2 = 1 / 4 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_1 {x : ℝ} (hx : x ≠ 0) :
    hpl [one] x = x + x ^ 2 / 2 + i13Rho [one] x * x ^ 3 := by
  have h1 : coef [one] 1 = 1 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [one] 2 = 1 / 2 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

theorem i13hpl_rho_m {x : ℝ} (hx : x ≠ 0) :
    hpl [negOne] x = x - x ^ 2 / 2 + i13Rho [negOne] x * x ^ 3 := by
  have h1 : coef [negOne] 1 = 1 := by norm_num [coef, twistSum, Letter.toReal]
  have h2 : coef [negOne] 2 = -1 / 2 := by norm_num [coef, twistSum, Letter.toReal]
  unfold i13Rho
  rw [h1, h2]
  field_simp
  ring

end QED.ThreeLoopD
