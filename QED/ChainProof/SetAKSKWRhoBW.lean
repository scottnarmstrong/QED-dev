/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWRhoBNN
public import QED.ChainProof.SetAKSKWRhoBPN

/-!
# Set (a), stage D: the `VB` density after the `ρ`- and `w`-integrals

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. For fixed
`β ∈ (0, 1)` and `δ ∈ (0, 1)` (`σ± = (1 ± δ)/2`, `T = 4/(1-δ²)`), the `ρ`-integral of `ksWnB` is,
on each piece of the `w`-interval, a polynomial-logarithmic combination `ksWPe` plus at most a
simple and a double pole off the piece (`ksWW_rho_2A`, `ksWW_rho_2B`, `ksWW_rho_3`, `ksWW_rho_4A`,
`ksWW_rho_4B`, `ksWW_rho_5`), and zero where both node denominators are positive. The
`w`-integral is therefore explicit (`ksWP_piece`, `ksWP_piece_q`):

* `β < σ₋`: only `w ∈ (σ₋, σ₊)` contributes (`A_w < 0 < A_β`);
* `σ₋ < β < σ₊`: four pieces, split at `σ₋`, `β` (where `ksDYmax β w` changes branch) and `σ₊`;
* `β > σ₊`: only `w ∈ (σ₋, σ₊)` contributes.

Main results:

* **`ksWW_w_I`**, **`ksWW_w_II`**, **`ksWW_w_III`**: the `w`-integral in the three ranges;
* **`ksWW_ksWRhoB_eq`**: `ρ_B(δ) = ∫₀¹ ksWWE β δ dβ`.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology intervalIntegral

namespace QED.ChainProof.SetAKS

variable {b d : ℝ}

theorem ksWW_Y_pos (hb : b ∈ Ioo (0 : ℝ) 1) {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 < ksDYmax b w :=
  lt_min (div_pos hw.1 hb.1) (div_pos (by linarith [hw.2]) (by linarith [hb.2]))

theorem ksWW_inv_K (hd : d ∈ Ioo (0 : ℝ) 1) {c : ℝ} (hc : c ≠ 0) :
    1 / (c * ksDT 1 d) = (1 - d) * (1 + d) / (4 * c) := by
  have : 1 - d ^ 2 ≠ 0 := by nlinarith [hd.1, hd.2]
  unfold ksDT
  field_simp
  ring

theorem ksWW_w0_gt (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    (1 + d) / 2 < 1 - 1 / ((1 - b) * ksDT 1 d) := by
  have h1b : 0 < 1 - b := by linarith [hb.2, hd.1]
  rw [ksWW_inv_K hd h1b.ne']
  have : (1 - d) * (1 + d) / (4 * (1 - b)) < (1 - d) / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hb.2, hd.1, hd.2]
  linarith

theorem ksWW_w0_lt (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) 1) :
    1 - 1 / ((1 - b) * ksDT 1 d) < (1 + d) / 2 := by
  have h1b : 0 < 1 - b := by linarith [hb.2]
  rw [ksWW_inv_K hd h1b.ne']
  have : (1 - d) / 2 < (1 - d) * (1 + d) / (4 * (1 - b)) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [hb.1, hd.1, hd.2]
  linarith

theorem ksWW_w1_gt (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 + d) / 2)) :
    (1 - d) / 2 < 1 / (b * ksDT 1 d) := by
  rw [ksWW_inv_K hd hb.1.ne', lt_div_iff₀ (by linarith [hb.1])]
  nlinarith [hb.2, hd.1, hd.2]

theorem ksWW_w1_lt (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    1 / (b * ksDT 1 d) < (1 - d) / 2 := by
  have hb0 : 0 < b := by linarith [hb.1, hd.1]
  rw [ksWW_inv_K hd hb0.ne', div_lt_iff₀ (by linarith)]
  nlinarith [hb.1, hd.1, hd.2]

theorem ksWW_not_mem_uIcc {p l u : ℝ} (hlu : l ≤ u) (h : p < l ∨ u < p) : p ∉ uIcc l u := by
  rw [uIcc_of_le hlu]
  rintro ⟨h1, h2⟩
  rcases h with h | h <;> linarith

/-- The `ρ`-integral vanishes where both node denominators are positive. -/
theorem ksWW_rho_zero (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hB : b < (1 - d) / 2 ∨ (1 + d) / 2 < b) {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1)
    (hA : w < (1 - d) / 2 ∨ (1 + d) / 2 < w) :
    ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d) = 0 :=
  ksWV_integral_pos_pos (ksWW_ksDA_pos hd hA) (ksWW_ksDA_pos hd hB) (ksWW_Y_pos hb hw)

/-- The value of the `w`-integral for `β < σ₋`. -/
noncomputable def ksWWEI (b d : ℝ) : ℝ :=
  ksWPv (ksWW3L b d) (ksWW3P b d) ((1 - d) / 2) ((1 + d) / 2) +
    (ksWPQ (1 - 1 / ((1 - b) * ksDT 1 d)) (ksWW3c b d) (ksWW3e b d) ((1 + d) / 2) -
      ksWPQ (1 - 1 / ((1 - b) * ksDT 1 d)) (ksWW3c b d) (ksWW3e b d) ((1 - d) / 2))

/-- The value of the `w`-integral for `β ∈ (σ₋, σ₊)`. -/
noncomputable def ksWWEII (b d : ℝ) : ℝ :=
  (ksWPv (ksWW4AL b d) (ksWW4AP b d) 0 ((1 - d) / 2) +
      (ksWPQ (1 / (b * ksDT 1 d)) (ksWW4Ac b d) (ksWW4Ae b d) ((1 - d) / 2) -
        ksWPQ (1 / (b * ksDT 1 d)) (ksWW4Ac b d) (ksWW4Ae b d) 0)) +
    ksWPv (ksWW2AL b d) (ksWW2AP b d) ((1 - d) / 2) b +
    ksWPv (ksWW2BL b d) (ksWW2BP b d) b ((1 + d) / 2) +
    (ksWPv (ksWW4BL b d) (ksWW4BP b d) ((1 + d) / 2) 1 +
      (ksWPQ (1 - 1 / ((1 - b) * ksDT 1 d)) (ksWW4Bc b d) (ksWW4Be b d) 1 -
        ksWPQ (1 - 1 / ((1 - b) * ksDT 1 d)) (ksWW4Bc b d) (ksWW4Be b d) ((1 + d) / 2)))

/-- The value of the `w`-integral for `β > σ₊`. -/
noncomputable def ksWWEIII (b d : ℝ) : ℝ :=
  ksWPv (ksWW5L b d) (ksWW5P b d) ((1 - d) / 2) ((1 + d) / 2) +
    (ksWPQ (1 / (b * ksDT 1 d)) (ksWW5c b d) (ksWW5e b d) ((1 + d) / 2) -
      ksWPQ (1 / (b * ksDT 1 d)) (ksWW5c b d) (ksWW5e b d) ((1 - d) / 2))

/-- **The `VB` density after the `ρ`- and `w`-integrals**, as a function of `β`. -/
noncomputable def ksWWE (b d : ℝ) : ℝ :=
  if b < (1 - d) / 2 then ksWWEI b d else if b < (1 + d) / 2 then ksWWEII b d else ksWWEIII b d

/-- **The `w`-integral for `β < σ₋`.** -/
theorem ksWW_w_I (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo 0 ((1 - d) / 2)) :
    ∫ w in Ioo (0 : ℝ) 1, ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d) = ksWWEI b d := by
  have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨hb.1, by linarith [hb.2, hd.1]⟩
  have hsm : (0 : ℝ) ≤ (1 - d) / 2 := by linarith [hd.2]
  have hms : (1 - d) / 2 ≤ (1 + d) / 2 := by linarith [hd.1]
  have hsp : (1 + d) / 2 ≤ 1 := by linarith [hd.2]
  obtain ⟨i1, v1⟩ := ksWP_piece_zero (f := fun w => ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d))
    hsm fun w hw => (ksWW_rho_zero hd hb' (Or.inl hb.2) ⟨hw.1, by linarith [hw.2]⟩
      (Or.inl hw.2)).symm
  obtain ⟨i2, v2⟩ := ksWP_piece_q (f := fun w => ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d))
    _ _ _ _ _ hms (ksWW_not_mem_uIcc hms (Or.inr (ksWW_w0_gt hd hb)))
    fun w hw => (ksWW_rho_3 hd hb hw).symm
  obtain ⟨i3, v3⟩ := ksWP_piece_zero (f := fun w => ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d))
    hsp fun w hw => (ksWW_rho_zero hd hb' (Or.inl hb.2) ⟨by linarith [hw.1, hd.1], hw.2⟩
      (Or.inr hw.1)).symm
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← integral_add_adjacent_intervals i1 (i2.trans i3), ← integral_add_adjacent_intervals i2 i3,
    v1, v2, v3, ksWWEI]
  ring

/-- **The `w`-integral for `β ∈ (σ₋, σ₊)`**, split at `σ₋`, `β` and `σ₊`. -/
theorem ksWW_w_II (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 - d) / 2) ((1 + d) / 2)) :
    ∫ w in Ioo (0 : ℝ) 1, ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d) = ksWWEII b d := by
  have hsm : (0 : ℝ) ≤ (1 - d) / 2 := by linarith [hd.2]
  have hsp : (1 + d) / 2 ≤ 1 := by linarith [hd.2]
  have hb0 : b ∈ Ioo 0 ((1 + d) / 2) := ⟨by linarith [hb.1, hd.2], hb.2⟩
  have hb1 : b ∈ Ioo ((1 - d) / 2) 1 := ⟨hb.1, by linarith [hb.2, hd.2]⟩
  obtain ⟨i1, v1⟩ := ksWP_piece_q (f := fun w => ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d))
    _ _ _ _ _ hsm (ksWW_not_mem_uIcc hsm (Or.inr (ksWW_w1_gt hd hb0)))
    fun w hw => (ksWW_rho_4A hd hb hw).symm
  obtain ⟨i2, v2⟩ := ksWP_piece (f := fun w => ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d))
    _ _ hb.1.le fun w hw => (ksWW_rho_2A hd hb hw).symm
  obtain ⟨i3, v3⟩ := ksWP_piece (f := fun w => ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d))
    _ _ hb.2.le fun w hw => (ksWW_rho_2B hd hb hw).symm
  obtain ⟨i4, v4⟩ := ksWP_piece_q (f := fun w => ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d))
    _ _ _ _ _ hsp (ksWW_not_mem_uIcc hsp (Or.inl (ksWW_w0_lt hd hb1)))
    fun w hw => (ksWW_rho_4B hd hb hw).symm
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← integral_add_adjacent_intervals i1 ((i2.trans i3).trans i4),
    ← integral_add_adjacent_intervals (i2.trans i3) i4, ← integral_add_adjacent_intervals i2 i3,
    v1, v2, v3, v4, ksWWEII]
  ring

/-- **The `w`-integral for `β > σ₊`.** -/
theorem ksWW_w_III (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo ((1 + d) / 2) 1) :
    ∫ w in Ioo (0 : ℝ) 1, ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d) = ksWWEIII b d := by
  have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hb.1, hd.1], hb.2⟩
  have hsm : (0 : ℝ) ≤ (1 - d) / 2 := by linarith [hd.2]
  have hms : (1 - d) / 2 ≤ (1 + d) / 2 := by linarith [hd.1]
  have hsp : (1 + d) / 2 ≤ 1 := by linarith [hd.2]
  obtain ⟨i1, v1⟩ := ksWP_piece_zero (f := fun w => ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d))
    hsm fun w hw => (ksWW_rho_zero hd hb' (Or.inr hb.1) ⟨hw.1, by linarith [hw.2]⟩
      (Or.inl hw.2)).symm
  obtain ⟨i2, v2⟩ := ksWP_piece_q (f := fun w => ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d))
    _ _ _ _ _ hms (ksWW_not_mem_uIcc hms (Or.inl (ksWW_w1_lt hd hb)))
    fun w hw => (ksWW_rho_5 hd hb hw).symm
  obtain ⟨i3, v3⟩ := ksWP_piece_zero (f := fun w => ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d))
    hsp fun w hw => (ksWW_rho_zero hd hb' (Or.inr hb.1) ⟨by linarith [hw.1, hd.1], hw.2⟩
      (Or.inr hw.1)).symm
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← integral_add_adjacent_intervals i1 (i2.trans i3), ← integral_add_adjacent_intervals i2 i3,
    v1, v2, v3, ksWWEIII]
  ring

/-- The `w`-integral equals `ksWWE β δ` off `β ∈ {σ₋, σ₊}`. -/
theorem ksWW_w_eq (hd : d ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hm : b ≠ (1 - d) / 2)
    (hp : b ≠ (1 + d) / 2) :
    ∫ w in Ioo (0 : ℝ) 1, ∫ ρ in Ioo (0 : ℝ) 1, ksWnB ρ b w (ksDT 1 d) = ksWWE b d := by
  unfold ksWWE
  rcases lt_or_gt_of_ne hm with h1 | h1
  · simp only [h1, ↓reduceIte]
    exact ksWW_w_I hd ⟨hb.1, h1⟩
  · simp only [not_lt.2 h1.le, ↓reduceIte]
    rcases lt_or_gt_of_ne hp with h2 | h2
    · simp only [h2, ↓reduceIte]
      exact ksWW_w_II hd ⟨h1, h2⟩
    · simp only [not_lt.2 h2.le, ↓reduceIte]
      exact ksWW_w_III hd ⟨h2, hb.2⟩

/-- **The `VB` spectral density as a single integral over `β`**:
`ρ_B(δ) = ∫₀¹ ksWWE β δ dβ`. -/
theorem ksWW_ksWRhoB_eq (hd : d ∈ Ioo (0 : ℝ) 1) :
    ksWRhoB d = ∫ b in Ioo (0 : ℝ) 1, ksWWE b d := by
  unfold ksWRhoB
  refine setIntegral_congr_ae measurableSet_Ioo ?_
  filter_upwards [Measure.ae_ne volume ((1 - d) / 2), Measure.ae_ne volume ((1 + d) / 2)]
    with b hm hp hb
  exact ksWW_w_eq hd hb hm hp

end QED.ChainProof.SetAKS

end
