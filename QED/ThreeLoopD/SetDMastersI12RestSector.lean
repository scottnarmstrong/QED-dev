/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ThreeLoopD.SetDMastersI12RestBounds
public import QED.ThreeLoopD.SetDMastersI9Analytic

/-!
# Set (d), master `I₁₂`: the mixed differences of the two sectors

For `‖ε‖ < 1/100` and `ρ, θ, u ∈ (0, 1)` the product subtraction
`G(ρ, θ) - G(0, θ) - G₀(ρ) + G₀(0)` of each sector of `QED.ThreeLoopD.i12RA3`,
`QED.ThreeLoopD.i12RB3` is bounded by

  `20000 ρ ^ (1/4) θ ^ (1/8) (u (1 - u)) ^ (-1/100) Λ T`

with `Λ = (1 - ρθ) ^ (-3/5)`, `T = (1 - u) ^ (-3/4)` for the sector `t < v`
(`QED.ThreeLoopD.norm_i12RA3_diff_le`) and `Λ = (1 - ρ) ^ (-3/5)`, `T = u ^ (-3/4)` for the sector
`v < t` (`QED.ThreeLoopD.norm_i12RB3_diff_le`).

Each mixed difference is written in two ways, as a sum of terms each carrying a difference in
`ρ` (`h(ρ) ^ (2ε - 1) - h(0) ^ (2ε - 1)`, `(1 - ρθ) ^ (-ε) - 1`, `Φ₀` at two values of its second
argument) or each carrying a difference in `θ` (`Φ₀(X, Y) - (2 - 3ε) Y ^ (-3ε)`, with `X = uθ`).
The first gives a bound `C √ρ Λ T`, the second `C θ ^ (1/4) Λ T` (the abstract lemmas
`QED.ThreeLoopD.i12_mixA_le`, `QED.ThreeLoopD.i12_mixB_le`), and their geometric mean is the bound
above (`QED.ThreeLoopD.i12_combine`). The pointwise inputs are those of
`QED.ThreeLoopD.SetDMastersI12RestBounds`, with `Φ₀(X, Y) - (2 - 3ε) Y ^ (-3ε)` interpolated
between `27 √X / Y` and `27 / √Y` (`QED.ThreeLoopD.i12_interp`), a Lipschitz bound for complex
powers away from `0` (`QED.ThreeLoopD.i12_norm_cpow_sub_le_lip`) and
`‖x ^ (-ε) - 1‖ ≤ √(1 - x) x ^ (-3/5)` (`QED.ThreeLoopD.i12_norm_cpow_neg_sub_one_le`).
-/

@[expose] public section

open Complex Set QED.DimReg MeasureTheory
open scoped Interval

namespace QED.ThreeLoopD

/-! ### Real-power helpers -/

theorem i12_le_of_sq {n A B R : ℝ} (hn : 0 ≤ n) (hR : 0 ≤ R) (hA : n ≤ A) (hB : n ≤ B)
    (h : A * B ≤ R ^ 2) : n ≤ R := by
  nlinarith [mul_le_mul hA hB hn (hn.trans hA)]

theorem i12_rpow_le_64 {t r : ℝ} (ht : 1 / 4 ≤ t) (hr : -3 ≤ r) (hr0 : r ≤ 0) :
    t ^ r ≤ 64 := by
  calc t ^ r ≤ (1 / 4 : ℝ) ^ r := Real.rpow_le_rpow_of_nonpos (by norm_num) ht hr0
    _ ≤ (1 / 4 : ℝ) ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hr
    _ = 64 := by
        rw [Real.rpow_neg (by norm_num), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
        norm_num

/-- `Y ^ r ≤ 4 a ^ r` for `a / 4 ≤ Y` and `-1 ≤ r ≤ 0`. -/
theorem i12_rpow_le_of_quarter {a Y r : ℝ} (ha : 0 < a) (hY : a / 4 ≤ Y) (hr : -1 ≤ r)
    (hr0 : r ≤ 0) : Y ^ r ≤ 4 * a ^ r := by
  calc Y ^ r ≤ (a / 4) ^ r := Real.rpow_le_rpow_of_nonpos (by positivity) hY hr0
    _ = a ^ r * (1 / 4 : ℝ) ^ r := by
        rw [div_eq_mul_one_div a 4, Real.mul_rpow ha.le (by norm_num)]
    _ ≤ a ^ r * (1 / 4 : ℝ) ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hr) (by positivity)
    _ = 4 * a ^ r := by rw [Real.rpow_neg_one]; norm_num; ring

theorem i12_inv_sqrt_eq {t : ℝ} (ht : 0 < t) : 1 / √t = t ^ (-(1 / 2) : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg ht.le, one_div]

theorem i12_sqrt_eq (t : ℝ) : √t = t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow t

/-- **Lipschitz bound for complex powers away from `0`.** For `0 < m ≤ q ≤ p` and `re v ≤ 1`,
`‖p ^ v - q ^ v‖ ≤ ‖v‖ (p - q) m ^ (re v - 1)`. -/
theorem i12_norm_cpow_sub_le_lip {m q p : ℝ} (hm : 0 < m) (hmq : m ≤ q) (hqp : q ≤ p) {v : ℂ}
    (hv : v.re ≤ 1) : ‖(p : ℂ) ^ v - (q : ℂ) ^ v‖ ≤ ‖v‖ * ((p - q) * m ^ (v.re - 1)) := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  have h0 : (0 : ℝ) ∉ [[q, p]] := by
    rw [uIcc_of_le hqp]; intro h; linarith [h.1]
  have hv1 : v - 1 ≠ -1 := fun h => hv0 (by linear_combination h)
  have hint := integral_cpow (a := q) (b := p) (r := v - 1) (Or.inr ⟨hv1, h0⟩)
  rw [sub_add_cancel] at hint
  have e : (p : ℂ) ^ v - (q : ℂ) ^ v = v * ∫ t in q..p, (t : ℂ) ^ (v - 1) := by
    rw [hint]; field_simp
  rw [e]
  refine i12_norm_int_le hqp (fun t ht => ?_) v
  have ht0 : 0 < t := by linarith [ht.1]
  rw [norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]
  exact Real.rpow_le_rpow_of_nonpos hm (by linarith [ht.1]) (by linarith)

/-- `‖x ^ (-ε) - 1‖ ≤ √(1 - x) x ^ (-3/5)` for `0 < x ≤ 1`, `‖ε‖ < 1/100`. -/
theorem i12_norm_cpow_neg_sub_one_le {ε : ℂ} (hε : ‖ε‖ < 1 / 100) {x : ℝ} (hx : 0 < x)
    (hx1 : x ≤ 1) : ‖(x : ℂ) ^ (-ε) - 1‖ ≤ √(1 - x) * x ^ (-(3 / 5) : ℝ) := by
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have hA := i12_norm_cpow_sub_le_lip hx le_rfl hx1 (v := -ε) (by simp; linarith)
  rw [ofReal_one, one_cpow, norm_sub_rev, norm_neg] at hA
  have hA' : ‖(x : ℂ) ^ (-ε) - 1‖ ≤ 1 / 100 * ((1 - x) * x ^ (-(101 / 100) : ℝ)) := by
    refine hA.trans (mul_le_mul hε.le (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by rw [neg_re]; linarith)) (by linarith))
      (by positivity) (by norm_num))
  have hB : ‖(x : ℂ) ^ (-ε) - 1‖ ≤ 2 * x ^ (-(1 / 100) : ℝ) := by
    have h1 : ‖(x : ℂ) ^ (-ε)‖ ≤ x ^ (-(1 / 100) : ℝ) :=
      norm_cpow_le_rpow_of_le hx hx1 (by rw [neg_re]; linarith)
    have h2 : (1 : ℝ) ≤ x ^ (-(1 / 100) : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hx1 (by norm_num)
    calc _ ≤ ‖(x : ℂ) ^ (-ε)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_one]; linarith
  refine i12_le_of_sq (norm_nonneg _) (by positivity) hA' hB ?_
  have h1x : 0 ≤ 1 - x := by linarith
  have e1 : x ^ (-(101 / 100) : ℝ) * x ^ (-(1 / 100) : ℝ) = x ^ (-(102 / 100) : ℝ) := by
    rw [← Real.rpow_add hx]; norm_num
  have e2 : (x ^ (-(3 / 5) : ℝ)) ^ 2 = x ^ (-(6 / 5) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  have hm : x ^ (-(102 / 100) : ℝ) ≤ x ^ (-(6 / 5) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num)
  calc 1 / 100 * ((1 - x) * x ^ (-(101 / 100) : ℝ)) * (2 * x ^ (-(1 / 100) : ℝ)) =
      1 / 50 * ((1 - x) * x ^ (-(102 / 100) : ℝ)) := by rw [← e1]; ring
    _ ≤ (1 - x) * x ^ (-(6 / 5) : ℝ) := by
        have : 0 ≤ (1 - x) * x ^ (-(102 / 100) : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hm h1x]
    _ = _ := by rw [mul_pow, Real.sq_sqrt h1x, e2]


/-- Interpolation: `n ≤ a √X / Y` and `n ≤ a / √Y` give `n ≤ a X ^ (1/4) Y ^ (-3/4)`. -/
theorem i12_interp {n a X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (hn : 0 ≤ n) (ha : 0 ≤ a)
    (h1 : n ≤ a * √X / Y) (h2 : n ≤ a / √Y) : n ≤ a * (X ^ (1 / 4 : ℝ) * Y ^ (-(3 / 4) : ℝ)) := by
  refine i12_le_of_sq hn (by positivity) h1 h2 (le_of_eq ?_)
  have hsY := Real.sqrt_pos.mpr hY
  have eX : (X ^ (1 / 4 : ℝ)) ^ 2 = √X := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le, Real.sqrt_eq_rpow]; norm_num
  have eY : (Y ^ (-(3 / 4) : ℝ)) ^ 2 = 1 / (Y * √Y) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY.le, Real.sqrt_eq_rpow,
      show (-(3 / 4) : ℝ) * ((2 : ℕ) : ℝ) = -(1 + 1 / 2) by norm_num, Real.rpow_neg hY.le,
      Real.rpow_add hY, Real.rpow_one, one_div, one_div]
  rw [mul_pow, mul_pow, eX, eY]
  field_simp

/-- Combination of a `ρ`-bound and a `θ`-bound with a common factor `S`. -/
theorem i12_combine {n C a b S : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hn : 0 ≤ n) (h1 : n ≤ C * √a * S) (h2 : n ≤ C * b ^ (1 / 4 : ℝ) * S) :
    n ≤ C * (a ^ (1 / 4 : ℝ) * b ^ (1 / 8 : ℝ)) * S := by
  refine i12_le_of_sq hn (by positivity) h1 h2 (le_of_eq ?_)
  have ea : (a ^ (1 / 4 : ℝ)) ^ 2 = √a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le, Real.sqrt_eq_rpow]; norm_num
  have eb : (b ^ (1 / 8 : ℝ)) ^ 2 = b ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]; norm_num
  rw [mul_pow, mul_pow, mul_pow, ea, eb]; ring

/-! ### Elementary facts on the unit interval -/

theorem i12H_mem {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) : 1 / 4 ≤ i12H ρ ∧ i12H ρ ≤ 1 / 2 := by
  unfold i12H; constructor <;> linarith [hρ.1, hρ.2]

theorem i12H_zero : i12H 0 = 1 / 2 := by unfold i12H; norm_num

theorem norm_i12_hpow_le {ε : ℂ} (hε : ‖ε‖ < 1 / 100) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    ‖((i12H ρ : ℝ) : ℂ) ^ (2 * ε - 1)‖ ≤ 64 := by
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have hh := i12H_mem hρ
  rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact i12_rpow_le_64 hh.1 (by simp; linarith) (by simp; linarith)

theorem norm_i12_hpow_sub_le {ε : ℂ} (hε : ‖ε‖ < 1 / 100) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    ‖((i12H ρ : ℝ) : ℂ) ^ (2 * ε - 1) - ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1)‖ ≤ 32 * ρ := by
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have hh := i12H_mem hρ
  have hle : i12H ρ ≤ i12H 0 := by unfold i12H; linarith [hρ.1]
  have h := i12_norm_cpow_sub_le_lip (by linarith) le_rfl hle (v := 2 * ε - 1)
    (by simp; linarith)
  rw [norm_sub_rev]
  have hv : ‖2 * ε - 1‖ ≤ 2 := by
    calc ‖2 * ε - 1‖ ≤ ‖2 * ε‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_mul, norm_one]; norm_num; linarith
  have h64 : i12H ρ ^ ((2 * ε - 1).re - 1) ≤ 64 :=
    i12_rpow_le_64 hh.1 (by simp; linarith) (by simp; linarith)
  have hd : i12H 0 - i12H ρ = ρ / 4 := by unfold i12H; ring
  refine h.trans ?_
  rw [hd]
  calc ‖2 * ε - 1‖ * (ρ / 4 * i12H ρ ^ ((2 * ε - 1).re - 1)) ≤ 2 * (ρ / 4 * 64) := by
        have : 0 ≤ i12H ρ ^ ((2 * ε - 1).re - 1) := Real.rpow_nonneg (by linarith) _
        have : 0 ≤ ρ := hρ.1
        gcongr
    _ = 32 * ρ := by ring

theorem norm_i12_upow_le {ε : ℂ} (hε : ‖ε‖ < 1 / 100) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ‖((u * (1 - u) : ℝ) : ℂ) ^ ε‖ ≤ (u * (1 - u)) ^ (-(1 / 100) : ℝ) := by
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have h1 : 0 < 1 - u := by linarith [hu.2]
  exact norm_cpow_le_rpow_of_le (mul_pos hu.1 h1)
    (by nlinarith [hu.1, hu.2]) (by linarith)


/-! ### `Φ₀` with one argument comparable to a parameter `a` -/

section Quarter

variable {ε : ℂ} (hε : ‖ε‖ < 1 / 100) {a Y : ℝ} (ha : 0 < a) (hYa : a / 4 ≤ Y) (hY1 : Y ≤ 1)
include hε ha hYa hY1

omit hε hY1 in
theorem i12_inv_sqrt_le_quarter : 1 / √Y ≤ 4 * a ^ (-(1 / 2) : ℝ) := by
  rw [i12_inv_sqrt_eq (by linarith)]
  exact i12_rpow_le_of_quarter ha hYa (by norm_num) (by norm_num)

theorem norm_i12_ypow_le : ‖(Y : ℂ) ^ (-3 * ε)‖ ≤ 1 / √Y := by
  obtain ⟨hr, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have hY : 0 < Y := by linarith
  rw [i12_inv_sqrt_eq hY]
  exact norm_cpow_le_rpow_of_le hY hY1 (by simp; linarith)

theorem norm_i12Phi0_le_quarter {X : ℝ} (hX : 0 < X) (hX1 : X ≤ 1) :
    ‖i12Phi0 ε X Y‖ ≤ 96 * a ^ (-(1 / 2) : ℝ) := by
  have h := norm_i12Phi0_le_right hε hX (by linarith) hX1 hY1
  have h2 := i12_inv_sqrt_le_quarter ha hYa
  calc _ ≤ 24 / √Y := h
    _ = 24 * (1 / √Y) := by ring
    _ ≤ 24 * (4 * a ^ (-(1 / 2) : ℝ)) := by gcongr
    _ = _ := by ring

theorem norm_i12_wypow_le : ‖(2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε)‖ ≤ 12 * a ^ (-(1 / 2) : ℝ) := by
  obtain ⟨-, -, -, hw, -⟩ := i12_eps_facts hε
  have h1 := norm_i12_ypow_le hε ha hYa hY1
  have h2 := i12_inv_sqrt_le_quarter ha hYa
  rw [norm_mul]
  calc _ ≤ 3 * (4 * a ^ (-(1 / 2) : ℝ)) := by gcongr; exact h1.trans h2
    _ = _ := by ring

theorem norm_i12Phi0_sub_le_quarter {X : ℝ} (hX : 0 < X) (hX1 : X ≤ 1) :
    ‖i12Phi0 ε X Y - (2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε)‖ ≤
      108 * (X ^ (1 / 4 : ℝ) * a ^ (-(3 / 4) : ℝ)) := by
  obtain ⟨-, -, -, hw, -⟩ := i12_eps_facts hε
  have hY : 0 < Y := by linarith
  have h1 := norm_i12Phi0_sub_le hε hX hY hX1 hY1
  have h2 : ‖i12Phi0 ε X Y - (2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε)‖ ≤ 27 / √Y := by
    have hP := norm_i12Phi0_le_right hε hX hY hX1 hY1
    have hq := norm_i12_ypow_le hε ha hYa hY1
    calc _ ≤ ‖i12Phi0 ε X Y‖ + ‖(2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε)‖ := norm_sub_le _ _
      _ ≤ 24 / √Y + 3 * (1 / √Y) := by rw [norm_mul]; gcongr
      _ = _ := by ring
  have h := i12_interp hX hY (norm_nonneg _) (by norm_num) (by linarith [h1]) h2
  have hq : Y ^ (-(3 / 4) : ℝ) ≤ 4 * a ^ (-(3 / 4) : ℝ) :=
    i12_rpow_le_of_quarter ha hYa (by norm_num) (by norm_num)
  calc _ ≤ 27 * (X ^ (1 / 4 : ℝ) * Y ^ (-(3 / 4) : ℝ)) := h
    _ ≤ 27 * (X ^ (1 / 4 : ℝ) * (4 * a ^ (-(3 / 4) : ℝ))) := by gcongr
    _ = _ := by ring

theorem norm_i12_wypow_sub_le {Y₁ : ℝ} (hY : Y ≤ Y₁) :
    ‖(2 - 3 * ε) * (Y₁ : ℂ) ^ (-3 * ε) - (2 - 3 * ε) * (Y : ℂ) ^ (-3 * ε)‖ ≤
      (Y₁ - Y) / Y * a ^ (-(1 / 2) : ℝ) := by
  obtain ⟨hr, -, -, hw, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have hY0 : 0 < Y := by linarith
  have h := i12_norm_cpow_sub_le_lip hY0 le_rfl hY (v := -3 * ε) (by simp; linarith)
  have hv : ‖-3 * ε‖ ≤ 3 / 100 := by rw [norm_mul]; norm_num; linarith
  have hre : Y ^ ((-3 * ε).re - 1) = Y ^ (-3 * ε).re / Y := Real.rpow_sub_one hY0.ne' _
  have hYr : Y ^ (-3 * ε).re ≤ 4 * a ^ (-(1 / 2) : ℝ) := by
    have := norm_i12_ypow_le hε ha hYa hY1
    rw [norm_cpow_eq_rpow_re_of_pos hY0] at this
    exact this.trans (i12_inv_sqrt_le_quarter ha hYa)
  have hd : 0 ≤ (Y₁ - Y) / Y := div_nonneg (by linarith) hY0.le
  rw [← mul_sub, norm_mul]
  calc _ ≤ 3 * (‖-3 * ε‖ * ((Y₁ - Y) * (Y ^ (-3 * ε).re / Y))) := by
        rw [← hre]; gcongr
    _ = 3 * ‖-3 * ε‖ * ((Y₁ - Y) / Y * Y ^ (-3 * ε).re) := by ring
    _ ≤ 3 * (3 / 100) * ((Y₁ - Y) / Y * (4 * a ^ (-(1 / 2) : ℝ))) := by gcongr
    _ ≤ _ := by
        have : 0 ≤ (Y₁ - Y) / Y * a ^ (-(1 / 2) : ℝ) := by positivity
        nlinarith

end Quarter

/-- The mirror of `QED.ThreeLoopD.norm_i12Phi0_sub_le_quarter` with `X = u`:
`‖Φ₀(u, Y) - (2 - 3ε) u ^ (-3ε)‖ ≤ 27 Y ^ (1/4) u ^ (-3/4)`. -/
theorem norm_i12Phi0_sub_le_mirror {ε : ℂ} (hε : ‖ε‖ < 1 / 100) {X Y : ℝ} (hX : 0 < X)
    (hY : 0 < Y) (hX1 : X ≤ 1) (hY1 : Y ≤ 1) :
    ‖i12Phi0 ε X Y - (2 - 3 * ε) * (X : ℂ) ^ (-3 * ε)‖ ≤
      27 * (Y ^ (1 / 4 : ℝ) * X ^ (-(3 / 4) : ℝ)) := by
  obtain ⟨-, -, -, hw, -⟩ := i12_eps_facts hε
  have h1 := norm_i12Phi0_sub_le' hε hX hY hX1 hY1
  have h2 : ‖i12Phi0 ε X Y - (2 - 3 * ε) * (X : ℂ) ^ (-3 * ε)‖ ≤ 27 / √X := by
    have hP := norm_i12Phi0_le_left hε hX hY hX1 hY1
    have hq := norm_i12_ypow_le hε hX (by linarith) hX1
    calc _ ≤ ‖i12Phi0 ε X Y‖ + ‖(2 - 3 * ε) * (X : ℂ) ^ (-3 * ε)‖ := norm_sub_le _ _
      _ ≤ 24 / √X + 3 * (1 / √X) := by rw [norm_mul]; gcongr
      _ = _ := by ring
  exact i12_interp hY hX (norm_nonneg _) (by norm_num) h1 h2


/-! ### Abstract mixed differences -/

theorem i12_le_sqrt_self {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) : ρ ≤ √ρ :=
  (Real.le_sqrt h0 h0).mpr (by nlinarith)

theorem i12_le_rpow_quarter {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ 1) : θ ≤ θ ^ (1 / 4 : ℝ) := by
  have := Real.rpow_le_rpow_of_exponent_ge h0 h1 (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  rwa [Real.rpow_one] at this

theorem i12_norm5_le (A B C D E : ℂ) :
    ‖A + B + C - D - E‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by
  calc _ ≤ ‖A + B + C - D‖ + ‖E‖ := norm_sub_le _ _
    _ ≤ ‖A + B + C‖ + ‖D‖ + ‖E‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖A + B‖ + ‖C‖ + ‖D‖ + ‖E‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_add_le _ _

theorem i12_norm3_le (A B C : ℂ) : ‖A + B - C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ :=
  (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)

theorem i12_norm_mul_add_sub_le (L A B C : ℂ) :
    ‖L * (A + B) - C‖ ≤ ‖L‖ * (‖A‖ + ‖B‖) + ‖C‖ :=
  (norm_sub_le _ _).trans (by rw [norm_mul]; gcongr; exact norm_add_le _ _)

/-- **The mixed difference of the sector `t < v`**, abstractly. -/
theorem i12_mixA_le {Hρ H0 L U P Pθ Q Q0 : ℂ} {ρ θ Λ T Uc : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hθ0 : 0 < θ) (hΛ : 1 ≤ Λ) (hT : 1 ≤ T) (hU : ‖U‖ ≤ Uc)
    (hH : ‖Hρ‖ ≤ 64) (hH0 : ‖H0‖ ≤ 64) (hHd : ‖Hρ - H0‖ ≤ 32 * ρ)
    (hLθ : ‖L - 1‖ ≤ θ ^ (1 / 4 : ℝ) * Λ) (hLρ : ‖L - 1‖ ≤ √ρ * Λ)
    (hP : ‖P‖ ≤ 96 * T) (hPQ : ‖P - Q‖ ≤ 108 * θ ^ (1 / 4 : ℝ) * T)
    (hPQ0 : ‖Pθ - Q0‖ ≤ 108 * θ ^ (1 / 4 : ℝ) * T) (hPP : ‖P - Pθ‖ ≤ 144 * √ρ * T)
    (hQ : ‖Q‖ ≤ 12 * T) (hQQ : ‖Q - Q0‖ ≤ ρ * T) :
    ‖Hρ * L * U * P - H0 * U * Pθ - Hρ * U * Q + H0 * U * Q0‖ ≤
      20000 * (ρ ^ (1 / 4 : ℝ) * θ ^ (1 / 8 : ℝ)) * (Uc * Λ * T) := by
  have hUc : 0 ≤ Uc := (norm_nonneg _).trans hU
  have hs := i12_le_sqrt_self hρ0.le hρ1
  have hsq : 0 ≤ √ρ := Real.sqrt_nonneg _
  have hθq : 0 ≤ θ ^ (1 / 4 : ℝ) := by positivity
  refine i12_combine hρ0 hθ0 (by norm_num) (by positivity) (norm_nonneg _) ?_ ?_
  · have e : Hρ * L * U * P - H0 * U * Pθ - Hρ * U * Q + H0 * U * Q0 = U * (Hρ * (L - 1) * P +
        (Hρ - H0) * P + H0 * (P - Pθ) - (Hρ - H0) * Q - H0 * (Q - Q0)) := by ring
    have hT0 : (0 : ℝ) ≤ T := by linarith
    have k2 : √ρ * T ≤ √ρ * Λ * T := by
      calc √ρ * T = √ρ * 1 * T := by ring
        _ ≤ √ρ * Λ * T := by gcongr
    have k1 : ρ * T ≤ √ρ * Λ * T := (mul_le_mul_of_nonneg_right hs hT0).trans k2
    rw [e, norm_mul]
    calc _ ≤ ‖U‖ * (‖Hρ‖ * ‖L - 1‖ * ‖P‖ + ‖Hρ - H0‖ * ‖P‖ + ‖H0‖ * ‖P - Pθ‖ +
          ‖Hρ - H0‖ * ‖Q‖ + ‖H0‖ * ‖Q - Q0‖) := by
          gcongr; exact (i12_norm5_le _ _ _ _ _).trans (le_of_eq (by simp only [norm_mul]))
      _ ≤ Uc * (64 * (√ρ * Λ) * (96 * T) + 32 * ρ * (96 * T) + 64 * (144 * √ρ * T) +
          32 * ρ * (12 * T) + 64 * (ρ * T)) := by gcongr
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left k1 hUc
          have := mul_le_mul_of_nonneg_left k2 hUc
          have : 0 ≤ Uc * (√ρ * Λ * T) :=
            mul_nonneg hUc (mul_nonneg (mul_nonneg hsq (by linarith)) hT0)
          nlinarith
  · have e : Hρ * L * U * P - H0 * U * Pθ - Hρ * U * Q + H0 * U * Q0 =
        U * (Hρ * (L - 1) * P + Hρ * (P - Q) - H0 * (Pθ - Q0)) := by ring
    have k1 : θ ^ (1 / 4 : ℝ) * T ≤ θ ^ (1 / 4 : ℝ) * Λ * T := by
      have hT0 : (0 : ℝ) ≤ T := by linarith
      calc θ ^ (1 / 4 : ℝ) * T = θ ^ (1 / 4 : ℝ) * 1 * T := by ring
        _ ≤ θ ^ (1 / 4 : ℝ) * Λ * T := by gcongr
    rw [e, norm_mul]
    calc _ ≤ ‖U‖ * (‖Hρ‖ * ‖L - 1‖ * ‖P‖ + ‖Hρ‖ * ‖P - Q‖ + ‖H0‖ * ‖Pθ - Q0‖) := by
          gcongr
          exact (i12_norm3_le _ _ _).trans (le_of_eq (by simp only [norm_mul]))
      _ ≤ Uc * (64 * (θ ^ (1 / 4 : ℝ) * Λ) * (96 * T) + 64 * (108 * θ ^ (1 / 4 : ℝ) * T) +
          64 * (108 * θ ^ (1 / 4 : ℝ) * T)) := by gcongr
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left k1 hUc
          have : 0 ≤ Uc * (θ ^ (1 / 4 : ℝ) * Λ * T) :=
            mul_nonneg hUc (mul_nonneg (mul_nonneg hθq (by linarith)) (by linarith))
          nlinarith

/-- **The mixed difference of the sector `v < t`**, abstractly. -/
theorem i12_mixB_le {H H0 L U Q Qθ Q0 : ℂ} {ρ θ Λ T Uc : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hΛ : 1 ≤ Λ) (hT : 1 ≤ T) (hU : ‖U‖ ≤ Uc)
    (hH0 : ‖H0‖ ≤ 64) (hHd : ‖H - H0‖ ≤ 32 * (ρ * θ))
    (hL : ‖L‖ ≤ Λ) (hLρ : ‖L - 1‖ ≤ √ρ * Λ)
    (hQ : ‖Q‖ ≤ 24 * T) (hQQ0 : ‖Q - Q0‖ ≤ 27 * θ ^ (1 / 4 : ℝ) * T)
    (hQθ : ‖Qθ - Q0‖ ≤ 27 * θ ^ (1 / 4 : ℝ) * T) (hQQ : ‖Q - Qθ‖ ≤ 48 * ρ * T)
    (hQ0 : ‖Q0‖ ≤ 3 * T) :
    ‖H * L * U * Q - H0 * U * Qθ - H0 * L * U * Q0 + H0 * U * Q0‖ ≤
      20000 * (ρ ^ (1 / 4 : ℝ) * θ ^ (1 / 8 : ℝ)) * (Uc * Λ * T) := by
  have hUc : 0 ≤ Uc := (norm_nonneg _).trans hU
  have hs := i12_le_sqrt_self hρ0.le hρ1
  have hsq : 0 ≤ √ρ := Real.sqrt_nonneg _
  have hθq := i12_le_rpow_quarter hθ0 hθ1
  have hρθ : ρ * θ ≤ θ := by nlinarith
  refine i12_combine hρ0 hθ0 (by norm_num) (by positivity) (norm_nonneg _) ?_ ?_
  · have e : H * L * U * Q - H0 * U * Qθ - H0 * L * U * Q0 + H0 * U * Q0 = U * ((H - H0) * L * Q
        + H0 * (L - 1) * Q + H0 * (Q - Qθ) - H0 * Q0 * (L - 1) - 0) := by ring
    have hρθ' : ρ * θ ≤ √ρ := by nlinarith
    have hT0 : (0 : ℝ) ≤ T := by linarith
    have k2 : √ρ * T ≤ √ρ * Λ * T := by
      calc √ρ * T = √ρ * 1 * T := by ring
        _ ≤ √ρ * Λ * T := by gcongr
    have k1 : ρ * T ≤ √ρ * Λ * T := (mul_le_mul_of_nonneg_right hs hT0).trans k2
    have k3 : ρ * θ * Λ * T ≤ √ρ * Λ * T := by
      have : 0 ≤ Λ * T := by positivity
      nlinarith
    rw [e, norm_mul]
    calc _ ≤ ‖U‖ * (‖H - H0‖ * ‖L‖ * ‖Q‖ + ‖H0‖ * ‖L - 1‖ * ‖Q‖ + ‖H0‖ * ‖Q - Qθ‖ +
          ‖H0‖ * ‖Q0‖ * ‖L - 1‖ + ‖(0 : ℂ)‖) := by
          gcongr; exact (i12_norm5_le _ _ _ _ _).trans (le_of_eq (by simp only [norm_mul]))
      _ ≤ Uc * (32 * (ρ * θ) * Λ * (24 * T) + 64 * (√ρ * Λ) * (24 * T) + 64 * (48 * ρ * T) +
          64 * (3 * T) * (√ρ * Λ) + 0) := by rw [norm_zero]; gcongr
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left k1 hUc
          have := mul_le_mul_of_nonneg_left k3 hUc
          have : 0 ≤ Uc * (√ρ * Λ * T) :=
            mul_nonneg hUc (mul_nonneg (mul_nonneg hsq (by linarith)) hT0)
          nlinarith
  · have e : H * L * U * Q - H0 * U * Qθ - H0 * L * U * Q0 + H0 * U * Q0 =
        U * (L * ((H - H0) * Q + H0 * (Q - Q0)) - H0 * (Qθ - Q0)) := by ring
    have k1 : θ ^ (1 / 4 : ℝ) * T ≤ θ ^ (1 / 4 : ℝ) * Λ * T := by
      have hT0 : (0 : ℝ) ≤ T := by linarith
      calc θ ^ (1 / 4 : ℝ) * T = θ ^ (1 / 4 : ℝ) * 1 * T := by ring
        _ ≤ θ ^ (1 / 4 : ℝ) * Λ * T := by gcongr
    have k2 : ρ * θ * Λ * T ≤ θ ^ (1 / 4 : ℝ) * Λ * T := by
      have : 0 ≤ Λ * T := by positivity
      nlinarith
    rw [e, norm_mul]
    calc _ ≤ ‖U‖ * (‖L‖ * (‖H - H0‖ * ‖Q‖ + ‖H0‖ * ‖Q - Q0‖) + ‖H0‖ * ‖Qθ - Q0‖) := by
          gcongr
          exact (i12_norm_mul_add_sub_le _ _ _ _).trans (le_of_eq (by simp only [norm_mul]))
      _ ≤ Uc * (Λ * (32 * (ρ * θ) * (24 * T) + 64 * (27 * θ ^ (1 / 4 : ℝ) * T)) +
          64 * (27 * θ ^ (1 / 4 : ℝ) * T)) := by gcongr
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left k1 hUc
          have := mul_le_mul_of_nonneg_left k2 hUc
          have : 0 ≤ Uc * (θ ^ (1 / 4 : ℝ) * Λ * T) := by positivity
          nlinarith


/-! ### The sector `t < v` -/

section SectorA

variable {ε : ℂ} (hε : ‖ε‖ < 1 / 100) {ρ θ u : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
  (hθ : θ ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
include hε hρ hθ hu

omit hε hu in
theorem i12_sqrt_mul_le_quarter : √(ρ * θ) ≤ θ ^ (1 / 4 : ℝ) := by
  calc √(ρ * θ) ≤ √θ := Real.sqrt_le_sqrt (by nlinarith [hρ.2, hθ.1])
    _ = θ ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow θ
    _ ≤ θ ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hθ.1 hθ.2.le (by norm_num)

omit hε hu in
theorem i12_one_sub_mul_mem : 0 < 1 - ρ * θ ∧ 1 - ρ * θ ≤ 1 := by
  constructor <;> nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]

/-- **The mixed difference of the sector `t < v`.** -/
theorem norm_i12RA3_diff_le :
    ‖i12GA ε ρ θ u - i12GA ε 0 θ u - i12GA0 ε ρ u + i12GA0 ε 0 u‖ ≤
      20000 * (ρ ^ (1 / 4 : ℝ) * θ ^ (1 / 8 : ℝ)) * ((u * (1 - u)) ^ (-(1 / 100) : ℝ) *
        (1 - ρ * θ) ^ (-(3 / 5) : ℝ) * (1 - u) ^ (-(3 / 4) : ℝ)) := by
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have hρI : ρ ∈ Icc (0 : ℝ) 1 := ⟨hρ.1.le, hρ.2.le⟩
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hhρ := i12H_mem hρI
  have hh0 := i12H_zero
  obtain ⟨hx0, hx1⟩ := i12_one_sub_mul_mem hρ hθ
  have hX : 0 < u * θ := mul_pos hu.1 hθ.1
  have hX1 : u * θ ≤ 1 := by nlinarith [hu.2, hθ.2, hu.1, hθ.1]
  have hYρ : (1 - u) / 4 ≤ (1 - u) * i12H ρ := by nlinarith [hhρ.1]
  have hYρ1 : (1 - u) * i12H ρ ≤ 1 := by nlinarith [hhρ.2, hu.1]
  have hY0 : (1 - u) / 4 ≤ (1 - u) * i12H 0 := by rw [hh0]; nlinarith
  have hY01 : (1 - u) * i12H 0 ≤ 1 := by rw [hh0]; nlinarith [hu.1]
  have hYle : (1 - u) * i12H ρ ≤ (1 - u) * i12H 0 := by
    rw [hh0]; unfold i12H; nlinarith [hρ.1]
  have hT : (1 - u) ^ (-(1 / 2) : ℝ) ≤ (1 - u) ^ (-(3 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hu1 (by linarith [hu.1]) (by norm_num)
  have hT1 : 1 ≤ (1 - u) ^ (-(3 / 4) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu1 (by linarith [hu.1]) (by norm_num)
  have hΛ : 1 ≤ (1 - ρ * θ) ^ (-(3 / 5) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx0 hx1 (by norm_num)
  have hθq : (u * θ) ^ (1 / 4 : ℝ) ≤ θ ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hX.le (by nlinarith [hu.2, hθ.1]) (by norm_num)
  have hL := i12_norm_cpow_neg_sub_one_le hε hx0 hx1
  rw [show 1 - (1 - ρ * θ) = ρ * θ by ring] at hL
  have hsθ := i12_sqrt_mul_le_quarter hρ hθ
  have hsρ : √(ρ * θ) ≤ √ρ := Real.sqrt_le_sqrt (by nlinarith [hρ.1, hθ.2])
  have e : i12GA ε ρ θ u - i12GA ε 0 θ u - i12GA0 ε ρ u + i12GA0 ε 0 u =
      ((i12H ρ : ℝ) : ℂ) ^ (2 * ε - 1) * ((1 - ρ * θ : ℝ) : ℂ) ^ (-ε) *
        ((u * (1 - u) : ℝ) : ℂ) ^ ε * i12Phi0 ε (u * θ) ((1 - u) * i12H ρ) -
      ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
        i12Phi0 ε (u * θ) ((1 - u) * i12H 0) -
      ((i12H ρ : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
        ((2 - 3 * ε) * (((1 - u) * i12H ρ : ℝ) : ℂ) ^ (-3 * ε)) +
      ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
        ((2 - 3 * ε) * (((1 - u) * i12H 0 : ℝ) : ℂ) ^ (-3 * ε)) := by
    simp only [i12GA, i12GA0, zero_mul, sub_zero, ofReal_one, one_cpow, mul_one]
  rw [e]
  refine i12_mixA_le hρ.1 hρ.2.le hθ.1 hΛ hT1 (norm_i12_upow_le hε hu)
    (norm_i12_hpow_le hε hρI) (norm_i12_hpow_le hε h0I) (norm_i12_hpow_sub_le hε hρI)
    (hL.trans (by gcongr)) (hL.trans (by gcongr)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact (norm_i12Phi0_le_quarter hε hu1 hYρ hYρ1 hX hX1).trans (by gcongr)
  · refine (norm_i12Phi0_sub_le_quarter hε hu1 hYρ hYρ1 hX hX1).trans ?_
    rw [← mul_assoc]; gcongr
  · refine (norm_i12Phi0_sub_le_quarter hε hu1 hY0 hY01 hX hX1).trans ?_
    rw [← mul_assoc]; gcongr
  · -- the difference in `ρ` of `Φ₀`
    have hYρ0 : 0 < (1 - u) * i12H ρ := by nlinarith [hhρ.1]
    have hY00 : 0 < (1 - u) * i12H 0 := by rw [hh0]; nlinarith
    rw [norm_sub_rev]
    refine (norm_i12Phi0_sub_right_le hε hX hX1 hYρ0 hYle hY01).trans ?_
    have hd : (1 - u) * i12H 0 - (1 - u) * i12H ρ = ρ / 2 * ((1 - u) * i12H 0) := by
      rw [hh0]; unfold i12H; ring
    have hs1 : √((1 - u) * i12H 0 - (1 - u) * i12H ρ) ≤ √ρ * √((1 - u) * i12H 0) := by
      rw [← Real.sqrt_mul hρ.1.le, hd]
      exact Real.sqrt_le_sqrt (by nlinarith [hρ.1])
    have hq0 := i12_inv_sqrt_le_quarter hu1 hY0
    have hqρ := i12_inv_sqrt_le_quarter hu1 hYρ
    have hsρ' := i12_le_sqrt_self hρ.1.le hρ.2.le
    have hsY0 := Real.sqrt_pos.mpr hY00
    have hsYρ := Real.sqrt_pos.mpr hYρ0
    have e1 : 24 * √((1 - u) * i12H 0 - (1 - u) * i12H ρ) / ((1 - u) * i12H 0) ≤
        24 * √ρ * (1 / √((1 - u) * i12H 0)) := by
      rw [div_le_iff₀ hY00]
      calc _ ≤ 24 * (√ρ * √((1 - u) * i12H 0)) := by gcongr
        _ = _ := by
            field_simp
            rw [Real.sq_sqrt hY00.le]; ring
    have e2 : 24 * ((1 - u) * i12H 0 - (1 - u) * i12H ρ) / ((1 - u) * i12H 0 *
        √((1 - u) * i12H ρ)) = 12 * ρ * (1 / √((1 - u) * i12H ρ)) := by
      rw [hd]; field_simp; ring
    rw [e2]
    have := mul_le_mul_of_nonneg_left hq0 (by positivity : (0 : ℝ) ≤ 24 * √ρ)
    have := mul_le_mul_of_nonneg_left hqρ (by linarith [hρ.1] : (0 : ℝ) ≤ 12 * ρ)
    have : 0 ≤ (1 - u) ^ (-(1 / 2) : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ √ρ)
    nlinarith
  · exact (norm_i12_wypow_le hε hu1 hYρ hYρ1).trans (by gcongr)
  · rw [norm_sub_rev]
    refine (norm_i12_wypow_sub_le hε hu1 hYρ hYρ1 hYle).trans ?_
    have hYρ0 : 0 < (1 - u) * i12H ρ := by nlinarith [hhρ.1]
    have hr : ((1 - u) * i12H 0 - (1 - u) * i12H ρ) / ((1 - u) * i12H ρ) ≤ ρ := by
      rw [div_le_iff₀ hYρ0, hh0]; unfold i12H
      nlinarith [mul_pos (mul_pos hu1 hρ.1) (by linarith [hρ.2] : (0 : ℝ) < 1 - ρ)]
    have : 0 ≤ (1 - u) ^ (-(1 / 2) : ℝ) := by positivity
    exact (mul_le_mul_of_nonneg_right hr this).trans (mul_le_mul_of_nonneg_left hT hρ.1.le)

/-- **The mixed difference of the sector `v < t`.** -/
theorem norm_i12RB3_diff_le :
    ‖i12GB ε ρ θ u - i12GB ε 0 θ u - i12GB0 ε ρ u + i12GB0 ε 0 u‖ ≤
      20000 * (ρ ^ (1 / 4 : ℝ) * θ ^ (1 / 8 : ℝ)) * ((u * (1 - u)) ^ (-(1 / 100) : ℝ) *
        (1 - ρ) ^ (-(3 / 5) : ℝ) * u ^ (-(3 / 4) : ℝ)) := by
  obtain ⟨hr, -, -, hw, -⟩ := i12_eps_facts hε
  have hr' := abs_le.mp hr
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  have hρ1 : 0 < 1 - ρ := by linarith [hρ.2]
  have hρθI : ρ * θ ∈ Icc (0 : ℝ) 1 :=
    ⟨by nlinarith [hρ.1, hθ.1], by nlinarith [hρ.1, hρ.2, hθ.1, hθ.2]⟩
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hh := i12H_mem hρθI
  have hh0 := i12H_zero
  have hu1' : u ≤ 1 := hu.2.le
  have hT : u ^ (-(1 / 2) : ℝ) ≤ u ^ (-(3 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hu.1 hu1' (by norm_num)
  have hT1 : 1 ≤ u ^ (-(3 / 4) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu.1 hu1' (by norm_num)
  have hΛ : 1 ≤ (1 - ρ) ^ (-(3 / 5) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ1 (by linarith [hρ.1]) (by norm_num)
  have hiu : 24 / √u ≤ 24 * u ^ (-(3 / 4) : ℝ) := by
    rw [div_eq_mul_one_div, i12_inv_sqrt_eq hu.1]; gcongr
  have hY : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → 0 < (1 - u) * θ * i12H s ∧
      (1 - u) * θ * i12H s ≤ θ := fun s hs => by
    have := i12H_mem hs
    have h1 : 0 < (1 - u) * θ := mul_pos hu1 hθ.1
    constructor
    · nlinarith
    · nlinarith [hu.1, hθ.1]
  obtain ⟨hYρ0, hYρθ⟩ := hY _ hρθI
  obtain ⟨hY00, hY0θ⟩ := hY _ h0I
  have hθq : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ((1 - u) * θ * i12H s) ^ (1 / 4 : ℝ) ≤
      θ ^ (1 / 4 : ℝ) := fun s hs =>
    Real.rpow_le_rpow (hY s hs).1.le (hY s hs).2 (by norm_num)
  have hL := i12_norm_cpow_neg_sub_one_le hε hρ1 (by linarith [hρ.1])
  rw [show 1 - (1 - ρ) = ρ by ring] at hL
  have e : i12GB ε ρ θ u - i12GB ε 0 θ u - i12GB0 ε ρ u + i12GB0 ε 0 u =
      ((i12H (ρ * θ) : ℝ) : ℂ) ^ (2 * ε - 1) * ((1 - ρ : ℝ) : ℂ) ^ (-ε) *
        ((u * (1 - u) : ℝ) : ℂ) ^ ε * i12Phi0 ε u ((1 - u) * θ * i12H (ρ * θ)) -
      ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
        i12Phi0 ε u ((1 - u) * θ * i12H 0) -
      ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * ((1 - ρ : ℝ) : ℂ) ^ (-ε) *
        ((u * (1 - u) : ℝ) : ℂ) ^ ε * ((2 - 3 * ε) * (u : ℂ) ^ (-3 * ε)) +
      ((i12H 0 : ℝ) : ℂ) ^ (2 * ε - 1) * ((u * (1 - u) : ℝ) : ℂ) ^ ε *
        ((2 - 3 * ε) * (u : ℂ) ^ (-3 * ε)) := by
    simp only [i12GB, i12GB0, zero_mul, sub_zero, ofReal_one, one_cpow, mul_one]
  rw [e]
  refine i12_mixB_le hρ.1 hρ.2.le hθ.1 hθ.2.le hΛ hT1 (norm_i12_upow_le hε hu)
    (norm_i12_hpow_le hε h0I) (norm_i12_hpow_sub_le hε hρθI) ?_ hL ?_ ?_ ?_ ?_ ?_
  · refine (norm_cpow_le_rpow_of_le hρ1 (by linarith [hρ.1]) (a := -(3 / 5)) ?_)
    rw [neg_re]; linarith
  · exact (norm_i12Phi0_le_left hε hu.1 hYρ0 hu1' (hYρθ.trans hθ.2.le)).trans hiu
  · refine (norm_i12Phi0_sub_le_mirror hε hu.1 hYρ0 hu1' (hYρθ.trans hθ.2.le)).trans ?_
    rw [← mul_assoc]; gcongr
  · refine (norm_i12Phi0_sub_le_mirror hε hu.1 hY00 hu1' (hY0θ.trans hθ.2.le)).trans ?_
    rw [← mul_assoc]; gcongr
  · have hle : (1 - u) * θ * i12H (ρ * θ) ≤ (1 - u) * θ * i12H 0 := by
      have : i12H (ρ * θ) ≤ i12H 0 := by unfold i12H; linarith [hρθI.1]
      exact mul_le_mul_of_nonneg_left this (mul_pos hu1 hθ.1).le
    rw [norm_sub_rev]
    refine (norm_i12Phi0_sub_right_le' hε hu.1 hu1' hYρ0 hle (hY0θ.trans hθ.2.le)).trans ?_
    have hd : ((1 - u) * θ * i12H 0 - (1 - u) * θ * i12H (ρ * θ)) /
        ((1 - u) * θ * i12H 0) = ρ * θ / 2 := by
      have : θ ≠ 0 := hθ.1.ne'
      have : (1 : ℝ) - u ≠ 0 := hu1.ne'
      rw [hh0]; unfold i12H; field_simp; ring
    have hsu := Real.sqrt_pos.mpr hu.1
    calc 48 * ((1 - u) * θ * i12H 0 - (1 - u) * θ * i12H (ρ * θ)) /
          ((1 - u) * θ * i12H 0 * √u) = 48 * (ρ * θ / 2) * (24 / √u) / 24 := by
          rw [← hd]; field_simp
      _ ≤ 48 * ρ * (24 * u ^ (-(3 / 4) : ℝ)) / 24 := by
          have : ρ * θ / 2 ≤ ρ := by nlinarith [hρ.1, hθ.2]
          have : 0 ≤ 48 * ρ := by linarith [hρ.1]
          gcongr
      _ = _ := by ring
  · rw [norm_mul]
    have := norm_i12_ypow_le hε hu.1 (by linarith [hu.1] : u / 4 ≤ u) hu1'
    rw [i12_inv_sqrt_eq hu.1] at this
    calc _ ≤ 3 * u ^ (-(1 / 2) : ℝ) := by gcongr
      _ ≤ _ := by gcongr

end SectorA

end QED.ThreeLoopD
