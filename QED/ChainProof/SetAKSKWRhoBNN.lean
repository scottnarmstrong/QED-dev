/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBR
public import QED.ChainProof.SetAKSKWRhoBP

/-!
# Set (a), stage D: the `VB` density after the `ρ`-integral, both denominators negative

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. For
`β ∈ (σ₋, σ₊)` and `w ∈ (σ₋, σ₊)` (`σ± = (1 ± δ)/2`, `T = 4/(1-δ²)`) both node denominators
`A_w`, `A_β` are negative, and the `ρ`-integral of `ksWnB` (`ksWV_integral_neg_neg`) is a
polynomial in `w` plus polynomials times `log w` (or `log (1 - w)`), `log (w - σ₋)` and
`log (w - σ₊)`, in the form `ksWPe` (`Real.log` is even, so `log |x| = log x`). The split at
`w = β` is where `ksDYmax β w` changes branch.

Main results:

* **`ksWW_rho_2A`**: `∫₀¹ ksWnB dρ = ksWPe (ksWW2AL β δ) (ksWW2AP β δ) w` on `σ₋ < w < β`;
* **`ksWW_rho_2B`**: the same with `ksWW2BL`, `ksWW2BP` on `β < w < σ₊`;
* `ksWW_ksDA_eq`: `A_w = T (w - σ₋)(w - σ₊)`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

/-- The log part of the `w`-integrand `ksWW2A`. -/
noncomputable def ksWW2AL (_b d : ℝ) : List (ℝ × ℕ × ℝ) := [
  (8, 1, 0),
  (-8, 2, 0),
  (-8, 1, ((1 - d) / 2)),
  (8, 2, ((1 - d) / 2)),
  (-8, 1, ((1 + d) / 2)),
  (8, 2, ((1 + d) / 2))]

/-- The polynomial part of the `w`-integrand `ksWW2A`. -/
noncomputable def ksWW2AP (b d : ℝ) : List (ℝ × ℕ) := [
  ((16 * log (ksDA 1 (-ksDT 1 d) b) * b ^ 2 - 16 * log (ksDA 1 (-ksDT 1 d) b) * b - 8
    * log (ksDT 1 d) * b - 8 * log b * b + 24 * b ^ 2 - 20 * b + 16) / b, 1),
  ((8 * log (ksDT 1 d) + 8 * log b - 4), 2)]

/-- The log part of the `w`-integrand `ksWW2B`. -/
noncomputable def ksWW2BL (_b d : ℝ) : List (ℝ × ℕ × ℝ) := [
  (8, 1, 1),
  (-8, 2, 1),
  (-8, 1, ((1 - d) / 2)),
  (8, 2, ((1 - d) / 2)),
  (-8, 1, ((1 + d) / 2)),
  (8, 2, ((1 + d) / 2))]

/-- The polynomial part of the `w`-integrand `ksWW2B`. -/
noncomputable def ksWW2BP (b d : ℝ) : List (ℝ × ℕ) := [
  (-((16 * log (ksDA 1 (-ksDT 1 d) b) * b ^ 2 - 16 * log (ksDA 1 (-ksDT 1 d) b) * b + 24 * b ^ 2
    - 24 * b + 16) / (b - 1)), 0),
  ((-(8 * log (1 - b) * b) + 8 * log (1 - b) + 16 * log (ksDA 1 (-ksDT 1 d) b) * b ^ 2 - 16
    * log (ksDA 1 (-ksDT 1 d) b) * b - 8 * log (ksDT 1 d) * b + 8 * log (ksDT 1 d) + 24 * b ^ 2
    - 20 * b + 12) / (b - 1), 1),
  ((8 * log (1 - b) + 8 * log (ksDT 1 d) - 4), 2)]

variable {b d w : ℝ}

theorem ksWW_T_pos (hd : d ∈ Ioo (0 : ℝ) 1) : 0 < ksDT 1 d := by
  unfold ksDT
  have : 0 < 1 - d ^ 2 := by nlinarith [hd.1, hd.2]
  positivity

/-- `A_w = T (w - σ₋)(w - σ₊)`. -/
theorem ksWW_ksDA_eq (hd : d ∈ Ioo (0 : ℝ) 1) (w : ℝ) :
    ksDA 1 (-ksDT 1 d) w = ksDT 1 d * ((w - (1 - d) / 2) * (w - (1 + d) / 2)) := by
  have : 1 - d ^ 2 ≠ 0 := by nlinarith [hd.1, hd.2]
  unfold ksDA ksDT
  field_simp
  ring

/-- `log |A_w| = log T + log (w - σ₋) + log (w - σ₊)` (`Real.log` is even). -/
theorem ksWW_log_ksDA (hd : d ∈ Ioo (0 : ℝ) 1) (hm : w ≠ (1 - d) / 2) (hp : w ≠ (1 + d) / 2) :
    log (-ksDA 1 (-ksDT 1 d) w) =
      log (ksDT 1 d) + log (w - (1 - d) / 2) + log (w - (1 + d) / 2) := by
  rw [log_neg_eq_log, ksWW_ksDA_eq hd, log_mul (ksWW_T_pos hd).ne'
    (mul_ne_zero (sub_ne_zero.2 hm) (sub_ne_zero.2 hp)),
    log_mul (sub_ne_zero.2 hm) (sub_ne_zero.2 hp), add_assoc]

theorem ksWW_ksDA_neg (hd : d ∈ Ioo (0 : ℝ) 1) (h1 : (1 - d) / 2 < w) (h2 : w < (1 + d) / 2) :
    ksDA 1 (-ksDT 1 d) w < 0 := by
  rw [ksWW_ksDA_eq hd]
  exact mul_neg_of_pos_of_neg (ksWW_T_pos hd)
    (mul_neg_of_pos_of_neg (by linarith) (by linarith))

theorem ksWW_ksDA_pos (hd : d ∈ Ioo (0 : ℝ) 1) (h : w < (1 - d) / 2 ∨ (1 + d) / 2 < w) :
    0 < ksDA 1 (-ksDT 1 d) w := by
  rw [ksWW_ksDA_eq hd]
  refine mul_pos (ksWW_T_pos hd) ?_
  rcases h with h | h
  · exact mul_pos_of_neg_of_neg (by linarith) (by linarith [hd.1])
  · exact mul_pos (by linarith [hd.1]) (by linarith)

theorem ksWW_ksDYmax_left (hb : b ∈ Ioo (0 : ℝ) 1) (hw : w ≤ b) : ksDYmax b w = w / b := by
  unfold ksDYmax
  refine min_eq_left ?_
  have h1 : 0 < 1 - b := by linarith [hb.2]
  rw [div_le_div_iff₀ hb.1 h1]
  nlinarith

theorem ksWW_ksDYmax_right (hb : b ∈ Ioo (0 : ℝ) 1) (hw : b ≤ w) :
    ksDYmax b w = (1 - w) / (1 - b) := by
  unfold ksDYmax
  refine min_eq_right ?_
  have h1 : 0 < 1 - b := by linarith [hb.2]
  rw [div_le_div_iff₀ h1 hb.1]
  nlinarith

/-- **The `ρ`-integral on `σ₋ < w < β`, `β ∈ (σ₋, σ₊)`.** -/
theorem ksWW_rho_2A (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2))
    (hw : w ∈ Ioo ((1 - d) / 2) b) :
    ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d) = ksWPe (ksWW2AL b d) (ksWW2AP b d) w := by
  have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1, hd.2], by linarith [hb.2, hd.2]⟩
  have hw0 : 0 < w := by linarith [hw.1, hd.2]
  have hA := ksWW_ksDA_neg hd hw.1 (by linarith [hw.2, hb.2])
  have hB := ksWW_ksDA_neg hd hb.1 hb.2
  have eY := ksWW_ksDYmax_left hb' hw.2.le
  rw [ksWV_integral_neg_neg hA hB (eY ▸ div_pos hw0 hb'.1)]
  rw [ksWW_log_ksDA (w := w) hd (by linarith [hw.1]) (by linarith [hw.2, hb.2]), log_neg_eq_log]
  simp only [ksWVF, ksUf0, ksUcB, eY, log_div hw0.ne' hb'.1.ne', sub_self, log_zero,
    mul_zero, log_one, ksWPe, ksWW2AL, ksWW2AP, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, sub_zero]
  have := hb'.1.ne'
  field_simp
  ring

/-- **The `ρ`-integral on `β < w < σ₊`, `β ∈ (σ₋, σ₊)`.** -/
theorem ksWW_rho_2B (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2))
    (hw : w ∈ Ioo b ((1 + d) / 2)) :
    ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d) = ksWPe (ksWW2BL b d) (ksWW2BP b d) w := by
  have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1, hd.2], by linarith [hb.2, hd.2]⟩
  have hw1 : 0 < 1 - w := by linarith [hw.2, hd.2]
  have h1b : 0 < 1 - b := by linarith [hb'.2]
  have hA := ksWW_ksDA_neg hd (by linarith [hw.1, hb.1]) hw.2
  have hB := ksWW_ksDA_neg hd hb.1 hb.2
  have eY := ksWW_ksDYmax_right hb' hw.1.le
  rw [ksWV_integral_neg_neg hA hB (eY ▸ div_pos hw1 h1b)]
  rw [ksWW_log_ksDA (w := w) hd (by linarith [hw.1, hb.1]) (by linarith [hw.2]), log_neg_eq_log]
  have l1 : log (1 - w) = log (w - 1) := by rw [← log_neg_eq_log, neg_sub]
  simp only [ksWVF, ksUf0, ksUcB, eY, log_div hw1.ne' h1b.ne', l1, sub_self, log_zero,
    mul_zero, log_one, ksWPe, ksWW2BL, ksWW2BP, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, sub_zero]
  have : b - 1 ≠ 0 := by linarith
  have := h1b.ne'
  field_simp
  ring

end QED.ChainProof.SetAKS

end
