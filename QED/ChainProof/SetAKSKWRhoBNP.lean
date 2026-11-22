/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBNN

/-!
# Set (a), stage D: the `VB` density after the `ρ`-integral for `β ∉ [σ₋, σ₊]`

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. For
`β ∈ (0, σ₋)` and `w ∈ (σ₋, σ₊)` (`σ± = (1 ± δ)/2`, `T = 4/(1-δ²)`) the node denominators have
`A_w < 0 < A_β`, `ksDYmax β w = (1-w)/(1-β)`, and `A_w - Y A_β = T (w - β)(w - w₀)`,
`w₀ = 1 - 1/((1-β)T) > σ₊`, so the cut of the `ρ`-interval is `r⋆ = A_w/(T (w - β)(w - w₀))`. The
`ρ`-integral of `ksWnB` (`ksWV_integral_neg_pos`) is a polynomial-logarithmic combination `ksWPe`
plus a simple and a double pole at `w₀`.

The mirror case `β > σ₊` has `Y = w/β`, `A_w - Y A_β = T (w - β)(w - w₁)`, `w₁ = 1/(βT) < σ₋`.

Main results:

* **`ksWW_rho_3`**: `∫₀¹ ksWnB dρ = ksWPe (ksWW3L β δ) (ksWW3P β δ) w + ksWPq w₀ c₁ c₂ w`;
* **`ksWW_rho_5`**: for `β > σ₊`, the same with `ksWW5L`, `ksWW5P` and the pole `w₁`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

/-- The log part of the `w`-integrand `ksWW3`. -/
noncomputable def ksWW3L (b d : ℝ) : List (ℝ × ℕ × ℝ) := [
  (-(16 * b), 0, 1),
  ((16 * b + 8), 1, 1),
  (-8, 2, 1),
  (-((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)), 1, ((1 - d) / 2)),
  ((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1), 2, ((1 - d) / 2)),
  (-((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)), 1, ((1 + d) / 2)),
  ((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1), 2, ((1 + d) / 2)),
  (16 * b, 0, b),
  (-((16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b
    + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)), 1, b),
  ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1), 2, b),
  (16 * b, 0, (1 - 1 / ((1 - b) * ksDT 1 d))),
  (-((16 * ksDT 1 d * b ^ 3 - 8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b
    + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)), 1, (1 - 1 / ((1 - b) * ksDT 1 d))),
  ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1), 2, (1 - 1 / ((1 - b) * ksDT 1 d)))]

/-- The polynomial part of the `w`-integrand `ksWW3`. -/
noncomputable def ksWW3P (b d : ℝ) : List (ℝ × ℕ) := [
  ((16 * log (1 - b) * ksDT 1 d ^ 2 * b ^ 3 - 32 * log (1 - b) * ksDT 1 d ^ 2 * b ^ 2 + 16
    * log (1 - b) * b * ksDT 1 d ^ 2 - 16 * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d ^ 2 * b ^ 3 + 32
    * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d ^ 2 * b ^ 2 - 16 * log (ksDA 1 (-ksDT 1 d) b) * b
    * ksDT 1 d ^ 2 + 16 * log (ksDT 1 d) * ksDT 1 d ^ 2 * b ^ 3 - 32 * log (ksDT 1 d)
    * ksDT 1 d ^ 2 * b ^ 2 + 16 * log (ksDT 1 d) * b * ksDT 1 d ^ 2 - 16 * ksDT 1 d * b ^ 2 + 8
    * ksDT 1 d * b + 8 * ksDT 1 d + 48) / (ksDT 1 d ^ 2 * (b - 1) ^ 2), 0),
  (-((16 * log (1 - b) * ksDT 1 d * b ^ 2 - 8 * log (1 - b) * ksDT 1 d * b - 8 * log (1 - b)
    * ksDT 1 d - 16 * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d * b ^ 2 + 16
    * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d * b + 16 * log (ksDT 1 d) * ksDT 1 d * b ^ 2 - 8
    * log (ksDT 1 d) * ksDT 1 d * b - 8 * log (ksDT 1 d) * ksDT 1 d - 4 * ksDT 1 d * b + 4
    * ksDT 1 d - 40) / (ksDT 1 d * (b - 1))), 1),
  ((8 * log (1 - b) + 8 * log (ksDT 1 d) - 4), 2)]

/-- The simple-pole coefficient of the `w`-integrand `ksWW3` at `1 - 1 / (ksDT 1 d * (1 - b))`. -/
noncomputable def ksWW3c (b d : ℝ) : ℝ :=
  -((8 * ksDT 1 d * b ^ 2 - 40 * ksDT 1 d * b + 32 * ksDT 1 d - 56) / (ksDT 1 d ^ 3 * (b - 1) ^ 3))

/-- The double-pole coefficient of the `w`-integrand `ksWW3` at `1 - 1 / (ksDT 1 d * (1 - b))`. -/
noncomputable def ksWW3e (b d : ℝ) : ℝ :=
  (8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4 * (b - 1) ^ 4)

/-- The log part of the `w`-integrand `ksWW5`. -/
noncomputable def ksWW5L (b d : ℝ) : List (ℝ × ℕ × ℝ) := [
  ((16 * b - 8), 1, 0),
  (-8, 2, 0),
  (-((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)), 1, ((1 - d) / 2)),
  ((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1), 2, ((1 - d) / 2)),
  (-((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)), 1, ((1 + d) / 2)),
  ((16 * ksDT 1 d - 32) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1), 2, ((1 + d) / 2)),
  (-((16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b
    + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)), 1, b),
  ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1), 2, b),
  (-((16 * ksDT 1 d * b ^ 3 - 24 * ksDT 1 d * b ^ 2 + 8 * ksDT 1 d * b - 16 * ksDT 1 d + 16 * b
    + 24) / (ksDT 1 d * b ^ 2 - ksDT 1 d * b + 1)), 1, (1 / (b * ksDT 1 d))),
  ((8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b - 16 * ksDT 1 d + 40) / (ksDT 1 d * b ^ 2 - ksDT 1 d
    * b + 1), 2, (1 / (b * ksDT 1 d)))]

/-- The polynomial part of the `w`-integrand `ksWW5`. -/
noncomputable def ksWW5P (b d : ℝ) : List (ℝ × ℕ) := [
  (-((16 * ksDT 1 d * b ^ 2 + 16 * ksDT 1 d * b - 48) / (ksDT 1 d ^ 2 * b ^ 2)), 0),
  ((16 * log (ksDA 1 (-ksDT 1 d) b) * ksDT 1 d * b ^ 2 - 16 * log (ksDA 1 (-ksDT 1 d) b)
    * ksDT 1 d * b - 16 * log (ksDT 1 d) * ksDT 1 d * b ^ 2 + 8 * log (ksDT 1 d) * ksDT 1 d * b
    - 16 * log b * ksDT 1 d * b ^ 2 + 8 * log b * ksDT 1 d * b + 4 * ksDT 1 d * b + 40)
    / (ksDT 1 d * b), 1),
  ((8 * log (ksDT 1 d) + 8 * log b - 4), 2)]

/-- The simple-pole coefficient of the `w`-integrand `ksWW5` at `1 / (ksDT 1 d * b)`. -/
noncomputable def ksWW5c (b d : ℝ) : ℝ :=
  -((8 * ksDT 1 d * b ^ 2 + 24 * ksDT 1 d * b - 56) / (ksDT 1 d ^ 3 * b ^ 3))

/-- The double-pole coefficient of the `w`-integrand `ksWW5` at `1 / (ksDT 1 d * b)`. -/
noncomputable def ksWW5e (b d : ℝ) : ℝ :=
  (8 * ksDT 1 d * b ^ 2 - 8 * ksDT 1 d * b + 8) / (ksDT 1 d ^ 4 * b ^ 4)

variable {b d w : ℝ}

theorem ksWW_ksDA_poly (T x : ℝ) : ksDA 1 (-T) x = T * x ^ 2 - T * x + 1 := by
  unfold ksDA
  ring

/-- `A_w - Y A_β = T (w - β)(w - w₀)` for `Y = (1-w)/(1-β)`, `w₀ = 1 - 1/((1-β)T)`. -/
theorem ksWW_fac_right {T : ℝ} (hT : T ≠ 0) (h1b : 1 - b ≠ 0) :
    ksDA 1 (-T) w - (1 - w) / (1 - b) * ksDA 1 (-T) b =
      T * ((w - b) * (w - (1 - 1 / ((1 - b) * T)))) := by
  simp only [ksWW_ksDA_poly]
  field_simp
  ring

/-- `w - w₀` as a quotient. -/
theorem ksWW_sub_w0 {T : ℝ} (hT : T ≠ 0) (h1b : 1 - b ≠ 0) :
    w - (1 - 1 / ((1 - b) * T)) = ((1 - b) * T * (w - 1) + 1) / ((1 - b) * T) := by
  field_simp
  ring

/-- `A_w - Y A_β = T (w - β)(w - w₁)` for `Y = w/β`, `w₁ = 1/(βT)`. -/
theorem ksWW_fac_left {T : ℝ} (hT : T ≠ 0) (hb : b ≠ 0) :
    ksDA 1 (-T) w - w / b * ksDA 1 (-T) b = T * ((w - b) * (w - 1 / (b * T))) := by
  simp only [ksWW_ksDA_poly]
  field_simp
  ring

/-- `w - w₁` as a quotient. -/
theorem ksWW_sub_w1 {T : ℝ} (hT : T ≠ 0) (hb : b ≠ 0) :
    w - 1 / (b * T) = (b * T * w - 1) / (b * T) := by
  field_simp

/-- **The `ρ`-integral on `σ₋ < w < σ₊` for `β < σ₋`** (`A_w < 0 < A_β`). -/
theorem ksWW_rho_3 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2))
    (hw : w ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d) = ksWPe (ksWW3L b d) (ksWW3P b d) w +
      ksWPq (1 - 1 / ((1 - b) * ksDT 1 d)) (ksWW3c b d) (ksWW3e b d) w := by
  obtain ⟨hd0, hd1⟩ := hd
  have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨hb.1, by linarith [hb.2]⟩
  have h1b : 0 < 1 - b := by linarith [hb'.2]
  have hw1 : 0 < 1 - w := by linarith [hw.2]
  have hbw : 0 < w - b := by linarith [hw.1, hb.2]
  have hT := ksWW_T_pos ⟨hd0, hd1⟩
  have hA := ksWW_ksDA_neg ⟨hd0, hd1⟩ hw.1 hw.2
  have hB := ksWW_ksDA_pos ⟨hd0, hd1⟩ (Or.inl hb.2)
  have eY := ksWW_ksDYmax_right hb' (by linarith : b ≤ w)
  have hm : w - (1 - d) / 2 ≠ 0 := by linarith [hw.1]
  have hp : w - (1 + d) / 2 ≠ 0 := by linarith [hw.2]
  have hfac := ksWW_fac_right (w := w) hT.ne' h1b.ne'
  have hX : ksDT 1 d * ((w - b) * (w - (1 - 1 / ((1 - b) * ksDT 1 d)))) ≠ 0 := by
    rw [← hfac]
    nlinarith [mul_pos (div_pos hw1 h1b) hB]
  have hw0 : w - (1 - 1 / ((1 - b) * ksDT 1 d)) ≠ 0 := fun h => hX (by rw [h]; ring)
  rw [ksWV_integral_neg_pos hT hA hB (eY ▸ div_pos hw1 h1b)]
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
    rw [log_div hA.ne hX, ← log_neg_eq_log (ksDA _ _ w),
      ksWW_log_ksDA ⟨hd0, hd1⟩ (sub_ne_zero.1 hm) (sub_ne_zero.1 hp), log_mul hT.ne'
      (mul_ne_zero hbw.ne' hw0), log_mul hbw.ne' hw0]
    ring
  have l1rs : log ((w - 1) * ksDA 1 (-ksDT 1 d) b /
        ((1 - b) * (ksDT 1 d * ((w - b) * (w - (1 - 1 / ((1 - b) * ksDT 1 d))))))) =
      log (w - 1) + log (ksDA 1 (-ksDT 1 d) b) - log (1 - b) - log (ksDT 1 d) - log (w - b) -
        log (w - (1 - 1 / ((1 - b) * ksDT 1 d))) := by
    rw [log_div (mul_ne_zero (by linarith) hB.ne') (mul_ne_zero h1b.ne' hX),
      log_mul (by linarith) hB.ne', log_mul h1b.ne' hX, log_mul hT.ne'
      (mul_ne_zero hbw.ne' hw0), log_mul hbw.ne' hw0]
    ring
  have lK : log ((1 - w) / (1 - b) * ksDA 1 (-ksDT 1 d) b / -ksDA 1 (-ksDT 1 d) w) =
      log (w - 1) - log (1 - b) + log (ksDA 1 (-ksDT 1 d) b) -
        (log (ksDT 1 d) + log (w - (1 - d) / 2) + log (w - (1 + d) / 2)) := by
    rw [log_div (mul_ne_zero (div_ne_zero hw1.ne' h1b.ne') hB.ne') (neg_ne_zero.2 hA.ne),
      log_mul (div_ne_zero hw1.ne' h1b.ne') hB.ne', log_div hw1.ne' h1b.ne',
      ksWW_log_ksDA ⟨hd0, hd1⟩ (sub_ne_zero.1 hm) (sub_ne_zero.1 hp),
      ← log_neg_eq_log (w - 1), neg_sub]
  have lY : log ((1 - w) / (1 - b)) = log (w - 1) - log (1 - b) := by
    rw [log_div hw1.ne' h1b.ne', ← log_neg_eq_log (w - 1), neg_sub]
  rw [ers]
  simp only [ksWVF]
  rw [e1rs, lrs, l1rs, eY, lK, lY, ksWW_log_ksDA ⟨hd0, hd1⟩ (sub_ne_zero.1 hm) (sub_ne_zero.1 hp)]
  simp only [ksUf0, ksUcB, eY, sub_self, log_zero, mul_zero, zero_mul, log_one, ksWPe, ksWPq,
    ksWW3L, ksWW3P, ksWW3c, ksWW3e, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sub_zero, add_zero]
  generalize log (w - (1 - d) / 2) = L1
  generalize log (w - (1 + d) / 2) = L2
  generalize log (w - b) = L3
  generalize log (w - (1 - 1 / ((1 - b) * ksDT 1 d))) = L4
  generalize log (w - 1) = L5
  generalize log (ksDA 1 (-ksDT 1 d) b) = L6
  generalize log (ksDT 1 d) = L7
  generalize log (1 - b) = L8
  have hB' := hB.ne'
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

/-- **The `ρ`-integral on `σ₋ < w < σ₊` for `β > σ₊`** (`A_w < 0 < A_β`, `Y = w/β`). -/
theorem ksWW_rho_5 (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1)
    (hw : w ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d) = ksWPe (ksWW5L b d) (ksWW5P b d) w +
      ksWPq (1 / (b * ksDT 1 d)) (ksWW5c b d) (ksWW5e b d) w := by
  obtain ⟨hd0, hd1⟩ := hd
  have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1], hb.2⟩
  have hw0 : 0 < w := by linarith [hw.1]
  have hbw : w - b < 0 := by linarith [hw.2, hb.1]
  have hT := ksWW_T_pos ⟨hd0, hd1⟩
  have hA := ksWW_ksDA_neg ⟨hd0, hd1⟩ hw.1 hw.2
  have hB := ksWW_ksDA_pos ⟨hd0, hd1⟩ (Or.inr hb.1)
  have eY := ksWW_ksDYmax_left hb' (by linarith : w ≤ b)
  have hm : w - (1 - d) / 2 ≠ 0 := by linarith [hw.1]
  have hp : w - (1 + d) / 2 ≠ 0 := by linarith [hw.2]
  have hfac := ksWW_fac_left (w := w) hT.ne' hb'.1.ne'
  have hX : ksDT 1 d * ((w - b) * (w - 1 / (b * ksDT 1 d))) ≠ 0 := by
    rw [← hfac]
    nlinarith [mul_pos (div_pos hw0 hb'.1) hB]
  have hw1 : w - 1 / (b * ksDT 1 d) ≠ 0 := fun h => hX (by rw [h]; ring)
  rw [ksWV_integral_neg_pos hT hA hB (eY ▸ div_pos hw0 hb'.1)]
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
    rw [log_div hA.ne hX, ← log_neg_eq_log (ksDA _ _ w),
      ksWW_log_ksDA ⟨hd0, hd1⟩ (sub_ne_zero.1 hm) (sub_ne_zero.1 hp), log_mul hT.ne'
      (mul_ne_zero hbw.ne hw1), log_mul hbw.ne hw1]
    ring
  have l1rs : log (-w * ksDA 1 (-ksDT 1 d) b /
        (b * (ksDT 1 d * ((w - b) * (w - 1 / (b * ksDT 1 d)))))) =
      log w + log (ksDA 1 (-ksDT 1 d) b) - log b - log (ksDT 1 d) - log (w - b) -
        log (w - 1 / (b * ksDT 1 d)) := by
    rw [log_div (mul_ne_zero (neg_ne_zero.2 hw0.ne') hB.ne') (mul_ne_zero hb'.1.ne' hX),
      log_mul (neg_ne_zero.2 hw0.ne') hB.ne', log_neg_eq_log, log_mul hb'.1.ne' hX,
      log_mul hT.ne' (mul_ne_zero hbw.ne hw1), log_mul hbw.ne hw1]
    ring
  have lK : log (w / b * ksDA 1 (-ksDT 1 d) b / -ksDA 1 (-ksDT 1 d) w) =
      log w - log b + log (ksDA 1 (-ksDT 1 d) b) -
        (log (ksDT 1 d) + log (w - (1 - d) / 2) + log (w - (1 + d) / 2)) := by
    rw [log_div (mul_ne_zero (div_ne_zero hw0.ne' hb'.1.ne') hB.ne') (neg_ne_zero.2 hA.ne),
      log_mul (div_ne_zero hw0.ne' hb'.1.ne') hB.ne', log_div hw0.ne' hb'.1.ne',
      ksWW_log_ksDA ⟨hd0, hd1⟩ (sub_ne_zero.1 hm) (sub_ne_zero.1 hp)]
  have lY : log (w / b) = log w - log b := log_div hw0.ne' hb'.1.ne'
  rw [ers]
  simp only [ksWVF]
  rw [e1rs, lrs, l1rs, eY, lK, lY, ksWW_log_ksDA ⟨hd0, hd1⟩ (sub_ne_zero.1 hm) (sub_ne_zero.1 hp)]
  simp only [ksUf0, ksUcB, eY, sub_self, log_zero, mul_zero, zero_mul, log_one, ksWPe, ksWPq,
    ksWW5L, ksWW5P, ksWW5c, ksWW5e, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    sub_zero, add_zero]
  generalize log (w - (1 - d) / 2) = L1
  generalize log (w - (1 + d) / 2) = L2
  generalize log (w - b) = L3
  generalize log (w - 1 / (b * ksDT 1 d)) = L4
  generalize log w = L5
  generalize log (ksDA 1 (-ksDT 1 d) b) = L6
  generalize log (ksDT 1 d) = L7
  generalize log b = L8
  have hB' := hB.ne'
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

end QED.ChainProof.SetAKS

end
