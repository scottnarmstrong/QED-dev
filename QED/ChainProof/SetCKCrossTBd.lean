/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetCKCrossT
public import QED.ChainProof.SetCKCornInBd
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Set (c), Stage K, group G3: an integrable bound for the crossed node weight

Helper level (no frozen statement). The size bound `crossT_abs_integral_le` of `SetCKCrossTW`
involves `|a₂|/β`, `|c₂|/β` and `|c₃|/β²`. On both branches of `β(x) = max(g, e x/(1-x))`,
`β ≥ x y₃ (1 - y₃)` (**`crossT_beta_ge`**: on the first branch `x(1-y₃) ≤ 1 - Y`, on the second
`(1-x)(1-y₃) ≤ Y - y₃`), and `a₂ = x y₃² P_a`, `c₂ = x y₃ N₂/2`, `c₃ = (x y₃(1-y₃))² P₃`, so

`|a₂|/β ≤ |P_a|/(1-y₃)`, `|c₂|/β ≤ |N₂|/(2(1-y₃))`, `|c₃|/β² ≤ |P₃|`.

With `L = log(1 + M/w₀) ≤ M - log y₃ - log(1-Y) - log x` (`w₀ ≥ y₃(1-Y)x`), `M ≥ m = min(1,t)/2`,
`1/(1-y₃) ≤ (√(1-Y))⁻¹ (√(1-y₃))⁻¹` for `y₃ < Y`, and a bound `C` of the polynomials on the cube
(compactness), this gives (**`crossT_exists_bound`**)

`∫₀^∞ |T(v)|/(M + v)² dv ≤ C (1 + 1/m)² (1 + (-log y₃ - log(1-Y) - log x)
  + (√(1-Y))⁻¹ (√(1-y₃))⁻¹)`  (`crossTDom`).
-/

@[expose] public section

open Real Set Filter Topology MeasureTheory

namespace QED.ChainProof.SetCK

open QED.TwoLoop.UnitSCLimit QED.TwoLoop.UnitLLink

/-- **The dominating function** of the crossed node weight. -/
noncomputable def crossTDom (t C Y y3 x : ℝ) : ℝ :=
  C * (1 + 1 / cornInM0 t) ^ 2 *
    (1 + (-log y3 - log (1 - Y) - log x) + (√(1 - Y))⁻¹ * (√(1 - y3))⁻¹)

/-- The sum of the polynomial sizes, bounded on the cube. -/
noncomputable def crossTSz (Y y3 x : ℝ) : ℝ :=
  |crossTA1 x y3 (Y - y3)| + |crossTPa x y3 (Y - y3)| + |crossTC1 x y3 (Y - y3)| +
    |crossTN2 x y3 (Y - y3)| + |crossTP3 y3 (Y - y3)|

theorem exists_bound_crossTSz : ∃ C : ℝ, 0 ≤ C ∧ ∀ Y ∈ Icc (0 : ℝ) 1, ∀ y3 ∈ Icc (0 : ℝ) 1,
    ∀ x ∈ Icc (0 : ℝ) 1, crossTSz Y y3 x ≤ C := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hc : Continuous fun p : ℝ × ℝ × ℝ => crossTSz p.1 p.2.1 p.2.2 := by
    simp only [crossTSz, crossTA1, crossTN1, crossTPa, crossTC1, crossTN2, crossTP3]
    fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun Y hY y3 h3 x hx => ?_⟩
  have := hC (Y, y3, x) ⟨hY, h3, hx⟩
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

section

variable {Y y3 x : ℝ}

/-- **`β ≥ x y₃ (1 - y₃)`** on both branches. -/
theorem crossT_beta_ge (h3 : 0 < y3) (_h34 : y3 < Y) (_hY : Y < 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    x * (y3 * (1 - y3)) ≤ betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x := by
  have h1x : 0 < 1 - x := by linarith [hx.2]
  by_cases hb : x * (1 - y3) ≤ 1 - Y
  · refine le_trans ?_ (le_max_left _ _)
    unfold cornerG
    have : 1 - y3 - (Y - y3) = 1 - Y := by ring
    rw [this]
    nlinarith
  · push Not at hb
    refine le_trans ?_ (le_max_right _ _)
    rw [le_div_iff₀ h1x]
    have : (1 - x) * (1 - y3) ≤ Y - y3 := by nlinarith
    have hy : 0 ≤ y3 * x := by nlinarith [hx.1]
    nlinarith [mul_le_mul_of_nonneg_left this hy]

theorem crossT_abs_a2_div_le (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    |crossTA2 x y3 (Y - y3)| / betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x ≤
      |crossTPa x y3 (Y - y3)| / (1 - y3) := by
  have hβ := betaG_pos (e := y3 * (Y - y3)) (x := x) (cornerG_pos hY h3)
  have hb := crossT_beta_ge h3 h34 hY hx
  have h13 : 0 < 1 - y3 := by linarith
  rw [div_le_div_iff₀ hβ h13]
  unfold crossTA2
  rw [abs_mul, abs_mul, abs_of_pos hx.1, abs_of_pos (by positivity : (0 : ℝ) < y3 ^ 2)]
  have hP := abs_nonneg (crossTPa x y3 (Y - y3))
  have key : x * y3 ^ 2 * (1 - y3) ≤ betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x := by
    have : y3 ^ 2 ≤ y3 := by nlinarith
    have : x * y3 ^ 2 * (1 - y3) ≤ x * (y3 * (1 - y3)) := by
      nlinarith [mul_nonneg (mul_nonneg hx.1.le h13.le) (sub_nonneg.2 this)]
    exact this.trans hb
  calc x * y3 ^ 2 * |crossTPa x y3 (Y - y3)| * (1 - y3) =
        |crossTPa x y3 (Y - y3)| * (x * y3 ^ 2 * (1 - y3)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hP

theorem crossT_abs_c2_div_le (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    |crossTC2 x y3 (Y - y3)| / betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x ≤
      |crossTN2 x y3 (Y - y3)| / (1 - y3) := by
  have hβ := betaG_pos (e := y3 * (Y - y3)) (x := x) (cornerG_pos hY h3)
  have hb := crossT_beta_ge h3 h34 hY hx
  have h13 : 0 < 1 - y3 := by linarith
  rw [div_le_div_iff₀ hβ h13]
  unfold crossTC2
  rw [abs_div, abs_mul, abs_mul, abs_of_pos hx.1, abs_of_pos h3, abs_two]
  have hN := abs_nonneg (crossTN2 x y3 (Y - y3))
  calc x * y3 * |crossTN2 x y3 (Y - y3)| / 2 * (1 - y3) =
        |crossTN2 x y3 (Y - y3)| / 2 * (x * (y3 * (1 - y3))) := by ring
    _ ≤ |crossTN2 x y3 (Y - y3)| / 2 * betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg hN hβ.le]

theorem crossT_abs_c3_div_le (h3 : 0 < y3) (h34 : y3 < Y) (hY : Y < 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    |crossTC3 x y3 (Y - y3)| / (2 * betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x ^ 2) ≤
      |crossTP3 y3 (Y - y3)| := by
  have hβ := betaG_pos (e := y3 * (Y - y3)) (x := x) (cornerG_pos hY h3)
  have hb := crossT_beta_ge h3 h34 hY hx
  have h0 : 0 ≤ x * (y3 * (1 - y3)) := by
    have : 0 < 1 - y3 := by linarith
    have := hx.1
    positivity
  rw [div_le_iff₀ (by positivity)]
  unfold crossTC3
  have e : x ^ 2 * y3 ^ 2 * (1 - y3) ^ 2 = (x * (y3 * (1 - y3))) ^ 2 := by ring
  rw [e, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hP := abs_nonneg (crossTP3 y3 (Y - y3))
  have hsq : (x * (y3 * (1 - y3))) ^ 2 ≤ betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x ^ 2 :=
    pow_le_pow_left₀ h0 hb 2
  nlinarith [mul_le_mul_of_nonneg_right hsq hP]

end

/-- **The integrable bound on the crossed node weight.** -/
theorem crossT_exists_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {t Y y3 x : ℝ}, 0 < t → 0 < y3 → y3 < Y → Y < 1 → x ∈ Ioo (0 : ℝ) 1 →
      ∫ v in Ioi 0, |crossTT Y y3 x v / (massIn t Y + v) ^ 2| ≤ crossTDom t C Y y3 x := by
  obtain ⟨C, hC, hB⟩ := exists_bound_crossTSz
  refine ⟨C, hC, fun {t Y y3 x} ht h3 h34 hY hx => ?_⟩
  have hY0 : 0 < Y := h3.trans h34
  have hM := massIn_pos ht ⟨hY0.le, hY.le⟩
  have hm := cornInM0_pos ht
  have hmM := cornInM0_le_massIn ht ⟨hY0.le, hY.le⟩
  set M := massIn t Y
  set β := betaG (cornerG y3 (Y - y3)) (y3 * (Y - y3)) x with hβdef
  have hβ : 0 < β := betaG_pos (cornerG_pos hY h3)
  have h1Y : 0 < 1 - Y := by linarith
  have h13 : 0 < 1 - y3 := by linarith
  have hmain := crossT_abs_integral_le (a₁ := crossTA1 x y3 (Y - y3))
    (a₂ := crossTA2 x y3 (Y - y3)) (c₁ := crossTC1 x y3 (Y - y3)) (c₂ := crossTC2 x y3 (Y - y3))
    (c₃ := crossTC3 x y3 (Y - y3)) hM hβ hx.1
  have hS := hB Y ⟨hY0.le, hY.le⟩ y3 ⟨h3.le, by linarith⟩ x ⟨hx.1.le, hx.2.le⟩
  unfold crossTSz at hS
  have hA1 := abs_nonneg (crossTA1 x y3 (Y - y3))
  have hPa := abs_nonneg (crossTPa x y3 (Y - y3))
  have hC1 := abs_nonneg (crossTC1 x y3 (Y - y3))
  have hN2 := abs_nonneg (crossTN2 x y3 (Y - y3))
  have hP3 := abs_nonneg (crossTP3 y3 (Y - y3))
  -- the logarithms
  have lY := log_nonpos h1Y.le (by linarith)
  have l3 := log_nonpos h3.le (by linarith)
  have lx := log_nonpos hx.1.le hx.2.le
  obtain ⟨Lg, hLg⟩ : ∃ Lg, Lg = -log y3 - log (1 - Y) - log x := ⟨_, rfl⟩
  have hLg0 : 0 ≤ Lg := by rw [hLg]; linarith
  have hgx : y3 * (1 - Y) * x ≤ β * x := by
    have h := cornerG_mul_le_cornInW0 Y y3 x hx.1.le
    have e : cornerG y3 (Y - y3) = y3 * (1 - Y) := by unfold cornerG; ring
    rw [e] at h
    exact h
  have hpos : 0 < y3 * (1 - Y) * x := by have := hx.1; positivity
  set L := log (1 + M / (β * x)) with hLdef
  have hL0 : 0 ≤ L := log_nonneg (by
    have : 0 ≤ M / (β * x) := by have := hx.1; positivity
    linarith)
  have hL : L ≤ M + Lg := by
    have hgx1 : y3 * (1 - Y) * x ≤ 1 := by
      have : y3 * (1 - Y) ≤ 1 := by nlinarith
      nlinarith [hx.2, mul_nonneg h3.le h1Y.le]
    have a1 : 1 + M / (β * x) ≤ (1 + M) / (y3 * (1 - Y) * x) := by
      have : M / (β * x) ≤ M / (y3 * (1 - Y) * x) := div_le_div_of_nonneg_left hM.le hpos hgx
      have : 1 ≤ 1 / (y3 * (1 - Y) * x) := by rw [le_div_iff₀ hpos, one_mul]; exact hgx1
      rw [add_div]
      linarith
    have hMx : 0 < M / (β * x) := div_pos hM (mul_pos hβ hx.1)
    have a2 := log_le_log (by linarith) a1
    rw [log_div (by linarith) hpos.ne', log_mul (by positivity) hx.1.ne',
      log_mul h3.ne' h1Y.ne'] at a2
    have a3 : log (1 + M) ≤ M := by
      have := log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + M)
      linarith
    rw [hLg]
    linarith
  -- the pieces
  obtain ⟨k, hk⟩ : ∃ k, k = 1 / cornInM0 t := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; exact one_div_pos.2 hm
  have hiM : 1 / M ≤ k := by rw [hk]; exact one_div_le_one_div_of_le hm hmM
  have hiM2 : 1 / M ^ 2 ≤ k ^ 2 := by
    rw [show (1 : ℝ) / M ^ 2 = (1 / M) ^ 2 by ring]
    exact pow_le_pow_left₀ (by positivity) hiM 2
  obtain ⟨S, hSdef⟩ : ∃ S, S = (√(1 - Y))⁻¹ * (√(1 - y3))⁻¹ := ⟨_, rfl⟩
  have hS1 : 1 / (1 - y3) ≤ S := by
    have hs1 : √(1 - Y) ≤ √(1 - y3) := sqrt_le_sqrt (by linarith)
    have hs0 : 0 < √(1 - Y) := sqrt_pos.2 h1Y
    have hs3 : 0 < √(1 - y3) := sqrt_pos.2 h13
    rw [hSdef, ← mul_inv, inv_eq_one_div, one_div_le_one_div h13 (by positivity)]
    calc √(1 - Y) * √(1 - y3) ≤ √(1 - y3) * √(1 - y3) :=
          mul_le_mul_of_nonneg_right hs1 hs3.le
      _ = 1 - y3 := mul_self_sqrt h13.le
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hone : 1 ≤ 1 / (1 - y3) := by rw [le_div_iff₀ h13]; linarith
  -- term 1: `|a₁| L/M² ≤ C (k + Lg k²)`
  have t1 : |crossTA1 x y3 (Y - y3)| * (L / M ^ 2) ≤ C * (k + Lg * k ^ 2) := by
    have : L / M ^ 2 ≤ k + Lg * k ^ 2 := by
      have e : L / M ^ 2 ≤ (M + Lg) / M ^ 2 := div_le_div_of_nonneg_right hL (by positivity)
      have e2 : (M + Lg) / M ^ 2 = 1 / M + Lg * (1 / M ^ 2) := by field_simp
      have e3 : Lg * (1 / M ^ 2) ≤ Lg * k ^ 2 := mul_le_mul_of_nonneg_left hiM2 hLg0
      linarith
    exact mul_le_mul (by linarith) this (by positivity) hC
  -- term 2: `|a₂|/(β M²) ≤ C S k²`
  have t2 : |crossTA2 x y3 (Y - y3)| / (β * M ^ 2) ≤ C * (S * k ^ 2) := by
    have e : |crossTA2 x y3 (Y - y3)| / (β * M ^ 2) =
        |crossTA2 x y3 (Y - y3)| / β * (1 / M ^ 2) := by field_simp
    have a := crossT_abs_a2_div_le h3 h34 hY hx
    rw [← hβdef] at a
    have b : |crossTPa x y3 (Y - y3)| / (1 - y3) ≤ C * S := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul (by linarith) hS1 (by positivity) hC
    rw [e]
    calc _ ≤ C * S * k ^ 2 := mul_le_mul (a.trans b) hiM2 (by positivity) (by positivity)
      _ = _ := by ring
  -- term 3: `|c₁| L/M ≤ C (1 + Lg k)`
  have t3 : |crossTC1 x y3 (Y - y3)| * (L / M) ≤ C * (1 + Lg * k) := by
    have : L / M ≤ 1 + Lg * k := by
      have e : L / M ≤ (M + Lg) / M := div_le_div_of_nonneg_right hL hM.le
      have e2 : (M + Lg) / M = 1 + Lg * (1 / M) := by field_simp
      have e3 : Lg * (1 / M) ≤ Lg * k := mul_le_mul_of_nonneg_left hiM hLg0
      linarith
    exact mul_le_mul (by linarith) this (by positivity) hC
  -- term 4: `(|c₂|/β + |c₃|/(2β²))/M ≤ C (S + 1) k`
  have t4 : (|crossTC2 x y3 (Y - y3)| / β + |crossTC3 x y3 (Y - y3)| / (2 * β ^ 2)) / M ≤
      C * ((S + 1) * k) := by
    have a := crossT_abs_c2_div_le h3 h34 hY hx
    have b := crossT_abs_c3_div_le h3 h34 hY hx
    rw [← hβdef] at a b
    have a' : |crossTN2 x y3 (Y - y3)| / (1 - y3) ≤ C * S := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul (by linarith) hS1 (by positivity) hC
    have hsum : |crossTC2 x y3 (Y - y3)| / β + |crossTC3 x y3 (Y - y3)| / (2 * β ^ 2) ≤
        C * (S + 1) := by
      have : |crossTP3 y3 (Y - y3)| ≤ C := by linarith
      have := a.trans a'
      have e : C * (S + 1) = C * S + C := by ring
      rw [e]
      linarith
    have hs0 : 0 ≤ |crossTC2 x y3 (Y - y3)| / β + |crossTC3 x y3 (Y - y3)| / (2 * β ^ 2) := by
      positivity
    rw [div_eq_mul_one_div]
    calc _ ≤ C * (S + 1) * k := mul_le_mul hsum hiM (by positivity) (by positivity)
      _ = _ := by ring
  refine hmain.trans ?_
  unfold crossTDom
  rw [← hk, ← hLg, ← hSdef]
  have hfin : (k + Lg * k ^ 2) + S * k ^ 2 + (1 + Lg * k) + (S + 1) * k ≤
      (1 + k) ^ 2 * (1 + Lg + S) := by
    have e : (1 + k) ^ 2 * (1 + Lg + S) - ((k + Lg * k ^ 2) + S * k ^ 2 + (1 + Lg * k) +
        (S + 1) * k) = Lg + S + k * Lg + k * S + k ^ 2 := by ring
    have := mul_nonneg hk0.le hLg0
    have := mul_nonneg hk0.le hS0
    have := sq_nonneg k
    linarith
  have := mul_le_mul_of_nonneg_left hfin hC
  have e : C * ((k + Lg * k ^ 2) + S * k ^ 2 + (1 + Lg * k) + (S + 1) * k) =
      C * (k + Lg * k ^ 2) + C * (S * k ^ 2) + C * (1 + Lg * k) + C * ((S + 1) * k) := by ring
  have e2 : C * ((1 + k) ^ 2 * (1 + Lg + S)) = C * (1 + k) ^ 2 * (1 + Lg + S) := by ring
  rw [e, e2] at this
  linarith

end QED.ChainProof.SetCK

end
