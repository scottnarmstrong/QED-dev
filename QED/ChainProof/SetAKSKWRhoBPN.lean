/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBNP

/-!
# Set (a), stage D: the `VB` density after the `ρ`-integral off `(σ₋, σ₊)` for `β ∈ (σ₋, σ₊)`

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. For
`β ∈ (σ₋, σ₊)` and `w ∉ [σ₋, σ₊]` (`σ± = (1 ± δ)/2`, `T = 4/(1-δ²)`) the node denominators have
`A_β < 0 < A_w`. With `Y = ksDYmax β w`, `A_w - Y A_β = T (w - β)(w - w₁)`, `w₁ = 1/(βT)`, for
`w < β`, and `T (w - β)(w - w₀)`, `w₀ = 1 - 1/((1-β)T)`, for `w > β`. The `ρ`-integral of
`ksWnB` (`ksWV_integral_pos_neg`) is a polynomial-logarithmic combination `ksWPe` plus a simple
and a double pole at `w₁` resp. `w₀` (outside the `w`-interval).

Main results:

* **`ksWW_rho_4A`**: on `0 < w < σ₋`, `∫₀¹ ksWnB dρ = ksWPe (ksWW4AL β δ) (ksWW4AP β δ) w +
  ksWPq w₁ c₁ c₂ w`;
* **`ksWW_rho_4B`**: on `σ₊ < w < 1`, the same with `ksWW4BL`, `ksWW4BP` and the pole `w₀`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

/-- The log part of the `w`-integrand `ksWW4A`. -/
noncomputable def ksWW4AL (b d : ℝ) : List (ℝ × ℕ × ℝ) := [
  (-((16 * b - 16)), 1, 0),
  (-((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1)), 1, ((1 - d) / 2)),
  ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1), 2, ((1 - d) / 2)),
  (-((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1)), 1, ((1 + d) / 2)),
  ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1), 2, ((1 + d) / 2)),
  ((16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b
    + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1), 1, b),
  (-((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1)), 2, b),
  ((16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b
    + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1), 1, (1 / (b * ksDT 1 d))),
  (-((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1)), 2, (1 / (b * ksDT 1 d)))]

/-- The polynomial part of the `w`-integrand `ksWW4A`. -/
noncomputable def ksWW4AP (b d : ℝ) : List (ℝ × ℕ) := [
  ((16 * ksDT 1 d * b ^ 2 + 16 * ksDT 1 d * b - 48) / (ksDT 1 d ^ 2 * b ^ 2), 0),
  ((16 * log (ksDT 1 d) * ksDT 1 d * b ^ 2 - 16 * log (ksDT 1 d) * ksDT 1 d * b + 16 * log b
    * ksDT 1 d * b ^ 2 - 16 * log b * ksDT 1 d * b + 24 * ksDT 1 d * b ^ 2 - 24 * ksDT 1 d * b
    + 16 * ksDT 1 d - 40) / (ksDT 1 d * b), 1)]

/-- The simple-pole coefficient of the `w`-integrand `ksWW4A` at `1 / (ksDT 1 d * b)`. -/
noncomputable def ksWW4Ac (b d : ℝ) : ℝ :=
  (8 * ksDT 1 d * b ^ 2 + 24 * ksDT 1 d * b - 56) / (ksDT 1 d ^ 3 * b ^ 3)

/-- The double-pole coefficient of the `w`-integrand `ksWW4A` at `1 / (ksDT 1 d * b)`. -/
noncomputable def ksWW4Ae (b d : ℝ) : ℝ :=
  -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4 * b ^ 4))

/-- The log part of the `w`-integrand `ksWW4B`. -/
noncomputable def ksWW4BL (b d : ℝ) : List (ℝ × ℕ × ℝ) := [
  (16 * b, 0, 1),
  (-(16 * b), 1, 1),
  (-((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1)), 1, ((1 - d) / 2)),
  ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1), 2, ((1 - d) / 2)),
  (-((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1)), 1, ((1 + d) / 2)),
  ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1), 2, ((1 + d) / 2)),
  (-(16 * b), 0, b),
  ((16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40)
    / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1), 1, b),
  (-((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1)), 2, b),
  (-(16 * b), 0, (1 - 1 / ((1 - b) * ksDT 1 d))),
  ((16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b + 40)
    / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1), 1, (1 - 1 / ((1 - b) * ksDT 1 d))),
  (-((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1)), 2, (1 - 1 / ((1 - b) * ksDT 1 d)))]

/-- The polynomial part of the `w`-integrand `ksWW4B`. -/
noncomputable def ksWW4BP (b d : ℝ) : List (ℝ × ℕ) := [
  (-((16 * log (1 - b) * ksDT 1 d ^ 2 * b ^ 3 - 32 * log (1 - b) * ksDT 1 d ^ 2 * b ^ 2 + 16
    * log (1 - b) * b * ksDT 1 d ^ 2 + 16 * log (ksDT 1 d) * ksDT 1 d ^ 2 * b ^ 3 - 32
    * log (ksDT 1 d) * ksDT 1 d ^ 2 * b ^ 2 + 16 * log (ksDT 1 d) * b * ksDT 1 d ^ 2 + 24
    * ksDT 1 d ^ 2 * b ^ 3 - 48 * ksDT 1 d ^ 2 * b ^ 2 + 40 * b * ksDT 1 d ^ 2 - 16 * ksDT 1 d ^ 2
    - 16 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b + 8 * ksDT 1 d + 48) / (ksDT 1 d ^ 2 * (b
    - 1) ^ 2)), 0),
  ((16 * log (1 - b) * ksDT 1 d * b ^ 2 - 16 * log (1 - b) * ksDT 1 d * b + 16 * log (ksDT 1 d)
    * ksDT 1 d * b ^ 2 - 16 * log (ksDT 1 d) * ksDT 1 d * b + 24 * ksDT 1 d * b ^ 2 - 24
    * ksDT 1 d * b + 16 * ksDT 1 d - 40) / (ksDT 1 d * (b - 1)), 1)]

/-- The simple-pole coefficient of the `w`-integrand `ksWW4B` at `1 - 1 / (ksDT 1 d * (1 - b))`. -/
noncomputable def ksWW4Bc (b d : ℝ) : ℝ :=
  (8 * ksDT 1 d * b ^ 2 - 40 * ksDT 1 d * b + 32 * ksDT 1 d - 56) / (ksDT 1 d ^ 3 * (b - 1) ^ 3)

/-- The double-pole coefficient of the `w`-integrand `ksWW4B` at `1 - 1 / (ksDT 1 d * (1 - b))`. -/
noncomputable def ksWW4Be (b d : ℝ) : ℝ :=
  -((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4 * (b - 1) ^ 4))

variable {b d w : ℝ}

/-- **The `ρ`-integral on `0 < w < σ₋` for `β ∈ (σ₋, σ₊)`** (`A_β < 0 < A_w`, `Y = w/β`). -/
theorem ksWW_rho_4A (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2))
    (hw : w ∈ Ioo 0 ((1 - d) / 2)) :
    ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d) = ksWPe (ksWW4AL b d) (ksWW4AP b d) w +
      ksWPq (1 / (b * ksDT 1 d)) (ksWW4Ac b d) (ksWW4Ae b d) w := by
  obtain ⟨hd0, hd1⟩ := hd
  have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hw0 : 0 < w := hw.1
  have hbw : w - b < 0 := by linarith [hw.2, hb.1]
  have hT := ksWW_T_pos ⟨hd0, hd1⟩
  have hA := ksWW_ksDA_pos ⟨hd0, hd1⟩ (Or.inl hw.2)
  have hB := ksWW_ksDA_neg ⟨hd0, hd1⟩ hb.1 hb.2
  have eY := ksWW_ksDYmax_left hb' (by linarith : w ≤ b)
  have hm : w - (1 - d) / 2 ≠ 0 := by linarith [hw.2]
  have hp : w - (1 + d) / 2 ≠ 0 := by linarith [hw.2, hd0]
  have hfac := ksWW_fac_left (w := w) hT.ne' hb'.1.ne'
  have hX : ksDT 1 d * ((w - b) * (w - 1 / (b * ksDT 1 d))) ≠ 0 := by
    rw [← hfac]
    nlinarith [mul_pos (div_pos hw0 hb'.1) (neg_pos.2 hB)]
  have hw1 : w - 1 / (b * ksDT 1 d) ≠ 0 := fun h => hX (by rw [h]; ring)
  rw [ksWV_integral_pos_neg hT hA hB (eY ▸ div_pos hw0 hb'.1)]
  have ers : ksWVrs (ksDA 1 (-ksDT 1 d) w) (ksDA 1 (-ksDT 1 d) b) (ksDYmax b w) =
      ksDA 1 (-ksDT 1 d) w / (ksDT 1 d * ((w - b) * (w - 1 / (b * ksDT 1 d)))) := by
    unfold ksWVrs
    rw [eY, hfac]
  have e1rs : 1 - ksDA 1 (-ksDT 1 d) w / (ksDT 1 d * ((w - b) * (w - 1 / (b * ksDT 1 d)))) =
      -w * ksDA 1 (-ksDT 1 d) b / (b * (ksDT 1 d * ((w - b) * (w - 1 / (b * ksDT 1 d))))) := by
    rw [one_sub_div hX, ← hfac, ← div_div]
    congr 1
    field_simp
    ring
  have lrs : log (ksDA 1 (-ksDT 1 d) w / (ksDT 1 d * ((w - b) * (w - 1 / (b * ksDT 1 d))))) =
      log (w - (1 - d) / 2) + log (w - (1 + d) / 2) - log (w - b) -
        log (w - 1 / (b * ksDT 1 d)) := by
    rw [log_div hA.ne' hX, ← log_neg_eq_log (ksDA _ _ w),
      ksWW_log_ksDA ⟨hd0, hd1⟩ (sub_ne_zero.1 hm) (sub_ne_zero.1 hp), log_mul hT.ne'
      (mul_ne_zero hbw.ne hw1), log_mul hbw.ne hw1]
    ring
  have l1rs : log (-w * ksDA 1 (-ksDT 1 d) b /
        (b * (ksDT 1 d * ((w - b) * (w - 1 / (b * ksDT 1 d)))))) =
      log w + log (ksDA 1 (-ksDT 1 d) b) - log b - log (ksDT 1 d) - log (w - b) -
        log (w - 1 / (b * ksDT 1 d)) := by
    rw [log_div (mul_ne_zero (neg_ne_zero.2 hw0.ne') hB.ne) (mul_ne_zero hb'.1.ne' hX),
      log_mul (neg_ne_zero.2 hw0.ne') hB.ne, log_neg_eq_log, log_mul hb'.1.ne' hX,
      log_mul hT.ne' (mul_ne_zero hbw.ne hw1), log_mul hbw.ne hw1]
    ring
  have lK : log (w / b * ksDA 1 (-ksDT 1 d) b / -ksDA 1 (-ksDT 1 d) w) =
      log w - log b + log (ksDA 1 (-ksDT 1 d) b) -
        (log (ksDT 1 d) + log (w - (1 - d) / 2) + log (w - (1 + d) / 2)) := by
    rw [log_div (mul_ne_zero (div_ne_zero hw0.ne' hb'.1.ne') hB.ne) (neg_ne_zero.2 hA.ne'),
      log_mul (div_ne_zero hw0.ne' hb'.1.ne') hB.ne, log_div hw0.ne' hb'.1.ne',
      ksWW_log_ksDA ⟨hd0, hd1⟩ (sub_ne_zero.1 hm) (sub_ne_zero.1 hp)]
  have lB : log (-ksDA 1 (-ksDT 1 d) b) = log (ksDA 1 (-ksDT 1 d) b) := log_neg_eq_log _
  rw [ers]
  simp only [ksWVF]
  rw [e1rs, lrs, l1rs, eY, lK]
  simp only [ksUf0, ksUcB, eY, lB, sub_self, log_zero, mul_zero, zero_mul, log_one, ksWPe, ksWPq,
    ksWW4AL, ksWW4AP, ksWW4Ac, ksWW4Ae, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sub_zero, add_zero]
  generalize log (w - (1 - d) / 2) = L1
  generalize log (w - (1 + d) / 2) = L2
  generalize log (w - b) = L3
  generalize log (w - 1 / (b * ksDT 1 d)) = L4
  generalize log w = L5
  generalize log (ksDA 1 (-ksDT 1 d) b) = L6
  generalize log (ksDT 1 d) = L7
  generalize log b = L8
  have hB' := hB.ne
  simp only [ksWW_ksDA_poly] at hB' ⊢
  have hD1 : b * ksDT 1 d * w - 1 ≠ 0 := by
    intro h
    apply hw1
    rw [ksWW_sub_w1 hT.ne' hb'.1.ne', h, zero_div]
  rw [ksWW_sub_w1 hT.ne' hb'.1.ne']
  generalize ksDT 1 d = T at *
  have : b ≠ 0 := hb'.1.ne'
  have : w - b ≠ 0 := hbw.ne
  have hT0 : T ≠ 0 := hT.ne'
  have hB2 : b * T * (b - 1) + 1 ≠ 0 := by intro h; apply hB'; linear_combination h
  have : b * w * T - 1 ≠ 0 := by intro h; apply hD1; linear_combination h
  field_simp
  ring

/-- **The `ρ`-integral on `σ₊ < w < 1` for `β ∈ (σ₋, σ₊)`** (`A_β < 0 < A_w`,
`Y = (1-w)/(1-β)`). -/
theorem ksWW_rho_4B (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2))
    (hw : w ∈ Ioo ((1 + d) / 2) 1) :
    ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d) = ksWPe (ksWW4BL b d) (ksWW4BP b d) w +
      ksWPq (1 - 1 / ((1 - b) * ksDT 1 d)) (ksWW4Bc b d) (ksWW4Be b d) w := by
  obtain ⟨hd0, hd1⟩ := hd
  have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have h1b : 0 < 1 - b := by linarith [hb'.2]
  have hw1 : 0 < 1 - w := by linarith [hw.2]
  have hbw : 0 < w - b := by linarith [hw.1, hb.2]
  have hT := ksWW_T_pos ⟨hd0, hd1⟩
  have hA := ksWW_ksDA_pos ⟨hd0, hd1⟩ (Or.inr hw.1)
  have hB := ksWW_ksDA_neg ⟨hd0, hd1⟩ hb.1 hb.2
  have eY := ksWW_ksDYmax_right hb' (by linarith : b ≤ w)
  have hm : w - (1 - d) / 2 ≠ 0 := by linarith [hw.1]
  have hp : w - (1 + d) / 2 ≠ 0 := by linarith [hw.1]
  have hfac := ksWW_fac_right (w := w) hT.ne' h1b.ne'
  have hX : ksDT 1 d * ((w - b) * (w - (1 - 1 / ((1 - b) * ksDT 1 d)))) ≠ 0 := by
    rw [← hfac]
    nlinarith [mul_pos (div_pos hw1 h1b) (neg_pos.2 hB)]
  have hw0 : w - (1 - 1 / ((1 - b) * ksDT 1 d)) ≠ 0 := fun h => hX (by rw [h]; ring)
  rw [ksWV_integral_pos_neg hT hA hB (eY ▸ div_pos hw1 h1b)]
  have ers : ksWVrs (ksDA 1 (-ksDT 1 d) w) (ksDA 1 (-ksDT 1 d) b) (ksDYmax b w) =
      ksDA 1 (-ksDT 1 d) w / (ksDT 1 d * ((w - b) * (w - (1 - 1 / ((1 - b) * ksDT 1 d))))) := by
    unfold ksWVrs
    rw [eY, hfac]
  have e1rs : 1 - ksDA 1 (-ksDT 1 d) w /
        (ksDT 1 d * ((w - b) * (w - (1 - 1 / ((1 - b) * ksDT 1 d))))) =
      (w - 1) * ksDA 1 (-ksDT 1 d) b /
        ((1 - b) * (ksDT 1 d * ((w - b) * (w - (1 - 1 / ((1 - b) * ksDT 1 d)))))) := by
    rw [one_sub_div hX, ← hfac, ← div_div]
    congr 1
    field_simp
    ring
  have lrs : log (ksDA 1 (-ksDT 1 d) w /
        (ksDT 1 d * ((w - b) * (w - (1 - 1 / ((1 - b) * ksDT 1 d)))))) =
      log (w - (1 - d) / 2) + log (w - (1 + d) / 2) - log (w - b) -
        log (w - (1 - 1 / ((1 - b) * ksDT 1 d))) := by
    rw [log_div hA.ne' hX, ← log_neg_eq_log (ksDA _ _ w),
      ksWW_log_ksDA ⟨hd0, hd1⟩ (sub_ne_zero.1 hm) (sub_ne_zero.1 hp), log_mul hT.ne'
      (mul_ne_zero hbw.ne' hw0), log_mul hbw.ne' hw0]
    ring
  have l1rs : log ((w - 1) * ksDA 1 (-ksDT 1 d) b /
        ((1 - b) * (ksDT 1 d * ((w - b) * (w - (1 - 1 / ((1 - b) * ksDT 1 d))))))) =
      log (w - 1) + log (ksDA 1 (-ksDT 1 d) b) - log (1 - b) - log (ksDT 1 d) - log (w - b) -
        log (w - (1 - 1 / ((1 - b) * ksDT 1 d))) := by
    rw [log_div (mul_ne_zero (by linarith) hB.ne) (mul_ne_zero h1b.ne' hX),
      log_mul (by linarith) hB.ne, log_mul h1b.ne' hX, log_mul hT.ne'
      (mul_ne_zero hbw.ne' hw0), log_mul hbw.ne' hw0]
    ring
  have lK : log ((1 - w) / (1 - b) * ksDA 1 (-ksDT 1 d) b / -ksDA 1 (-ksDT 1 d) w) =
      log (w - 1) - log (1 - b) + log (ksDA 1 (-ksDT 1 d) b) -
        (log (ksDT 1 d) + log (w - (1 - d) / 2) + log (w - (1 + d) / 2)) := by
    rw [log_div (mul_ne_zero (div_ne_zero hw1.ne' h1b.ne') hB.ne) (neg_ne_zero.2 hA.ne'),
      log_mul (div_ne_zero hw1.ne' h1b.ne') hB.ne, log_div hw1.ne' h1b.ne',
      ksWW_log_ksDA ⟨hd0, hd1⟩ (sub_ne_zero.1 hm) (sub_ne_zero.1 hp),
      ← log_neg_eq_log (w - 1), neg_sub]
  have lB : log (-ksDA 1 (-ksDT 1 d) b) = log (ksDA 1 (-ksDT 1 d) b) := log_neg_eq_log _
  rw [ers]
  simp only [ksWVF]
  rw [e1rs, lrs, l1rs, eY, lK]
  simp only [ksUf0, ksUcB, eY, lB, sub_self, log_zero, mul_zero, zero_mul, log_one, ksWPe, ksWPq,
    ksWW4BL, ksWW4BP, ksWW4Bc, ksWW4Be, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sub_zero, add_zero]
  generalize log (w - (1 - d) / 2) = L1
  generalize log (w - (1 + d) / 2) = L2
  generalize log (w - b) = L3
  generalize log (w - (1 - 1 / ((1 - b) * ksDT 1 d))) = L4
  generalize log (w - 1) = L5
  generalize log (ksDA 1 (-ksDT 1 d) b) = L6
  generalize log (ksDT 1 d) = L7
  generalize log (1 - b) = L8
  have hB' := hB.ne
  simp only [ksWW_ksDA_poly] at hB' ⊢
  have hD0 : (1 - b) * ksDT 1 d * (w - 1) + 1 ≠ 0 := by
    intro h
    apply hw0
    rw [ksWW_sub_w0 hT.ne' h1b.ne', h, zero_div]
  rw [ksWW_sub_w0 hT.ne' h1b.ne']
  generalize ksDT 1 d = T at *
  have : (1 - b) ≠ 0 := h1b.ne'
  have : (b - 1) ≠ 0 := by linarith
  have : w - b ≠ 0 := hbw.ne'
  have hT0 : T ≠ 0 := hT.ne'
  have hB2 : b * T * (b - 1) + 1 ≠ 0 := by intro h; apply hB'; linear_combination h
  field_simp
  ring

end QED.ChainProof.SetAKS

end
