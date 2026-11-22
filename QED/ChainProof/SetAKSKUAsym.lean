/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUElem

/-!
# Set (a), stage D: the large-slope expansion of the `VA` antiderivative

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral). The photon-mass integral of a
`VA` node up to the cutoff `Λ` is `ksUPhi(B) - ksUPhi(b₀)` (`ksU_integral_ksDLin`) with
`B = b₀ + Λ/x → ∞`. This file splits `ksUPhi(B)` into a quadratic polynomial in `ℓ = log B`,

  `ksUPhiInf A Y a₀ a₁ ℓ = a₀ (Y/A)(ℓ + log Y) + 2a₁ (-Y(ℓ + log Y) + Y((ℓ + log Y - log A)²/2
    + 2K(1)))`,

and a remainder bounded by `8(|a₀| + |a₁|)(1 + A)(1 + A⁻¹)/√B` for `B ≥ 1`, `0 < Y ≤ 1`
(uniform on the nodes, since there `A` stays in a compact subset of `(0, ∞)`).

Main results:

* `ksUPhiInf`;
* `ksU_ksUPhi_eq`: `ksUPhi = ksUPhiInf(log B) + a₀ E₀ + 2a₁ E₁` with explicit `E₀, E₁`;
* **`ksU_abs_ksUPhi_sub_le`**: the remainder bound.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace QED.ChainProof.SetAKS

/-- **The large-slope form of `ksUPhi`**, a quadratic polynomial in `ℓ = log B`. -/
noncomputable def ksUPhiInf (A Y a₀ a₁ ℓ : ℝ) : ℝ :=
  a₀ * (Y / A) * (ℓ + Real.log Y) +
    2 * a₁ * (-(Y * (ℓ + Real.log Y)) +
      Y * ((ℓ + Real.log Y - Real.log A) ^ 2 / 2 + 2 * ksUK 1))

/-- The decomposition of `ksUPhi` at a large slope `B`, with `t = A/(BY)`. -/
theorem ksU_ksUPhi_eq {A B Y : ℝ} (a₀ a₁ : ℝ) (hA : 0 < A) (hB : 0 < B) (hY : 0 < Y) :
    ksUPhi A B Y a₀ a₁ = ksUPhiInf A Y a₀ a₁ (Real.log B) +
      a₀ * (Real.log ((A + B * Y) / A) / B + Y / A * Real.log (1 + A / (B * Y))) +
      2 * a₁ * (-(A * Real.log ((A + B * Y) / A) / B) - Y * Real.log (1 + A / (B * Y)) -
        Y * ksUK (A / (B * Y))) := by
  have hBY : 0 < B * Y := mul_pos hB hY
  have hz : 0 < B * Y / A := div_pos hBY hA
  have hK := ksU_ksUK_inv hz
  have hinv : (B * Y / A)⁻¹ = A / (B * Y) := inv_div _ _
  have hlz : Real.log (B * Y / A) = Real.log B + Real.log Y - Real.log A := by
    rw [Real.log_div hBY.ne' hA.ne', Real.log_mul hB.ne' hY.ne']
  have h1t : 0 < 1 + A / (B * Y) := by positivity
  have hlog : Real.log (A + B * Y) = Real.log B + Real.log Y + Real.log (1 + A / (B * Y)) := by
    rw [← Real.log_mul hB.ne' hY.ne', ← Real.log_mul hBY.ne' h1t.ne']
    congr 1
    field_simp
    ring
  rw [hinv, hlz] at hK
  simp only [ksUPhi, ksUPhiInf, hlog]
  have hK' : ksUK (B * Y / A) = (Real.log B + Real.log Y - Real.log A) ^ 2 / 2 + 2 * ksUK 1 -
      ksUK (A / (B * Y)) := by linarith
  rw [hK']
  ring

/-- `log y ≤ 2√y` for `y > 0`. -/
theorem ksU_log_le_two_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hy)
  rw [Real.log_sqrt hy.le] at h
  linarith

/-- The arithmetic of the final constant in `ksU_abs_ksUPhi_sub_le`. -/
theorem ksU_bound_aux {a b A r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 < A) (hr : 0 ≤ r) :
    a * (3 * (1 + A⁻¹) * r) + 2 * b * (4 * (1 + A) * r) ≤
      8 * (a + b) * (1 + A) * (1 + A⁻¹) * r := by
  set c := A⁻¹ with hc
  have hc0 : 0 ≤ c := (inv_pos.2 hA).le
  have hAc : A * c = 1 := mul_inv_cancel₀ hA.ne'
  have e1 : a * r * (A * c) = a * r := by rw [hAc, mul_one]
  have e2 : b * r * (A * c) = b * r := by rw [hAc, mul_one]
  nlinarith [mul_nonneg (mul_nonneg ha hr) hA.le, mul_nonneg (mul_nonneg ha hr) hc0,
    mul_nonneg (mul_nonneg hb hr) hA.le, mul_nonneg (mul_nonneg hb hr) hc0, mul_nonneg ha hr,
    mul_nonneg hb hr]

/-- **The remainder bound of the large-slope expansion**: for `A > 0`, `0 < Y ≤ 1`, `B ≥ 1`,
`|ksUPhi A B Y a₀ a₁ - ksUPhiInf A Y a₀ a₁ (log B)| ≤ 8(|a₀| + |a₁|)(1 + A)(1 + A⁻¹)/√B`. -/
theorem ksU_abs_ksUPhi_sub_le {A B Y : ℝ} (a₀ a₁ : ℝ) (hA : 0 < A) (hB : 1 ≤ B) (hY : 0 < Y)
    (hY1 : Y ≤ 1) :
    |ksUPhi A B Y a₀ a₁ - ksUPhiInf A Y a₀ a₁ (Real.log B)| ≤
      8 * (|a₀| + |a₁|) * (1 + A) * (1 + A⁻¹) / Real.sqrt B := by
  have hB0 : 0 < B := lt_of_lt_of_le one_pos hB
  have hBY : 0 < B * Y := mul_pos hB0 hY
  rw [ksU_ksUPhi_eq a₀ a₁ hA hB0 hY]
  set r := (Real.sqrt B)⁻¹ with hr
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB0
  have hs1 : 1 ≤ Real.sqrt B := by simpa using Real.sqrt_le_sqrt hB
  have hss : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB0.le
  have hr0 : 0 < r := inv_pos.2 hsB
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ hs1
  have hBr : B⁻¹ = r * r := by rw [hr, ← mul_inv, hss]
  have hr2 : r * r ≤ r := by nlinarith
  set t := A / (B * Y) with ht
  have ht0 : 0 < t := div_pos hA hBY
  have hlt := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + t)
  have hlt0 : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hK0 := ksU_ksUK_nonneg ht0.le
  have hK1 := ksU_ksUK_le ht0.le
  have hYt : Y * t = A * B⁻¹ := by rw [ht]; field_simp
  have hYAt : Y / A * t = B⁻¹ := by rw [ht]; field_simp
  -- the logarithm `L = log((A + BY)/A)`
  set L := Real.log ((A + B * Y) / A) with hL
  have hy : 0 < (A + B * Y) / A := by positivity
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hA]; nlinarith)
  have hyle : (A + B * Y) / A ≤ B * (1 + A⁻¹) ^ 2 := by
    rw [div_le_iff₀ hA]
    have hAi : 0 < A⁻¹ := inv_pos.2 hA
    have hAA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA.ne'
    have : B * (1 + A⁻¹) ^ 2 * A = B * A + 2 * B + B * A⁻¹ := by
      rw [show B * (1 + A⁻¹) ^ 2 * A = B * A + 2 * B * (A * A⁻¹) + B * A⁻¹ * (A * A⁻¹) by ring,
        hAA]
      ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hY1 hB0.le, mul_pos hB0 hAi]
  have hsy : Real.sqrt ((A + B * Y) / A) ≤ Real.sqrt B * (1 + A⁻¹) := by
    calc Real.sqrt ((A + B * Y) / A) ≤ Real.sqrt (B * (1 + A⁻¹) ^ 2) := Real.sqrt_le_sqrt hyle
      _ = Real.sqrt B * (1 + A⁻¹) := by
        rw [Real.sqrt_mul hB0.le, Real.sqrt_sq (by positivity)]
  have hLB : L / B ≤ 2 * (1 + A⁻¹) * r := by
    have h := (ksU_log_le_two_sqrt hy).trans (mul_le_mul_of_nonneg_left hsy (by norm_num))
    rw [div_eq_mul_inv, hBr]
    have : L * (r * r) ≤ 2 * (Real.sqrt B * (1 + A⁻¹)) * (r * r) :=
      mul_le_mul_of_nonneg_right h (by positivity)
    have hsr : Real.sqrt B * r = 1 := mul_inv_cancel₀ hsB.ne'
    calc L * (r * r) ≤ 2 * (Real.sqrt B * (1 + A⁻¹)) * (r * r) := this
      _ = 2 * (1 + A⁻¹) * r * (Real.sqrt B * r) := by ring
      _ = 2 * (1 + A⁻¹) * r := by rw [hsr, mul_one]
  have hLB0 : 0 ≤ L / B := div_nonneg hL0 hB0.le
  -- the two error terms
  have hAi0 : 0 ≤ A⁻¹ := (inv_pos.2 hA).le
  have hE₀ : |L / B + Y / A * Real.log (1 + t)| ≤ 3 * (1 + A⁻¹) * r := by
    have h1 : Y / A * Real.log (1 + t) ≤ r * r := by
      rw [← hBr, ← hYAt]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hE₁ : |-(A * L / B) - Y * Real.log (1 + t) - Y * ksUK t| ≤ 4 * (1 + A) * r := by
    have h1 : Y * Real.log (1 + t) ≤ A * (r * r) := by
      rw [← hBr, ← hYt]
      exact mul_le_mul_of_nonneg_left (by linarith) hY.le
    have h2 : Y * ksUK t ≤ A * (r * r) := by
      rw [← hBr, ← hYt]
      exact mul_le_mul_of_nonneg_left hK1 hY.le
    have h3 : A * L / B ≤ 2 * (A + 1) * r := by
      rw [mul_div_assoc]
      have := mul_le_mul_of_nonneg_left hLB hA.le
      have hAA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA.ne'
      nlinarith
    have h4 : 0 ≤ A * L / B := by positivity
    have h5 : 0 ≤ Y * ksUK t := mul_nonneg hY.le hK0
    have h6 : 0 ≤ Y * Real.log (1 + t) := mul_nonneg hY.le hlt0
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hr2 hA.le]
  have hfin : |a₀ * (L / B + Y / A * Real.log (1 + t)) +
      2 * a₁ * (-(A * L / B) - Y * Real.log (1 + t) - Y * ksUK t)| ≤
      |a₀| * (3 * (1 + A⁻¹) * r) + 2 * |a₁| * (4 * (1 + A) * r) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hE₀ (abs_nonneg _)
    · rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left hE₁ (by positivity)
  have hgoal : |a₀| * (3 * (1 + A⁻¹) * r) + 2 * |a₁| * (4 * (1 + A) * r) ≤
      8 * (|a₀| + |a₁|) * (1 + A) * (1 + A⁻¹) / Real.sqrt B := by
    rw [div_eq_mul_inv, ← hr]
    exact ksU_bound_aux (abs_nonneg _) (abs_nonneg _) hA hr0.le
  have hsum : ksUPhiInf A Y a₀ a₁ (Real.log B) + a₀ * (L / B + Y / A * Real.log (1 + t)) +
      2 * a₁ * (-(A * L / B) - Y * Real.log (1 + t) - Y * ksUK t) -
        ksUPhiInf A Y a₀ a₁ (Real.log B) = a₀ * (L / B + Y / A * Real.log (1 + t)) +
      2 * a₁ * (-(A * L / B) - Y * Real.log (1 + t) - Y * ksUK t) := by ring
  rw [hsum]
  exact hfin.trans hgoal

end QED.ChainProof.SetAKS

end
