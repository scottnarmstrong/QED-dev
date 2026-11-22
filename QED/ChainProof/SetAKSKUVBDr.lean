/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVBRem

/-!
# Set (a), stage D: the domination of the `VB` remainder

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral of the `VB` class). The
remainder `ksUDr` of the `VB` node integrand (`ksU_ksUDr_eq`) is bounded, uniformly in the
cutoff `Λ ≥ 1`, by `C · ksUg ρ · ksUg w` on the open cube, with `C` depending on `M`, `s`
only. The five pieces are bounded separately:

* `Q₁` by the moment weight `ksU_wt_moment`;
* the regular logarithm by `ksU_abs_log_sub_le` and the logarithms of the node;
* `Q₃` by the mediant bound and `-log ρ ≤ 4(1 - ρ) ksUg ρ`;
* the two dilogarithm pieces by the exact form `ksU_K_sub_eq`, the inversion
  `K(z) + K(z⁻¹) = (log z)²/2 + 2K(1)` and `η log Λ ≤ 4√t`.

Main result: **`ksU_abs_ksUDr_le`**.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace QED.ChainProof.SetAKS

/-- `Kb = M² + |s|`, the upper bound of `A` on `[0, 1]`. -/
noncomputable def ksUKb (M s : ℝ) : ℝ := M ^ 2 + |s|

/-- `LA = |log kA| + |log Kb|`, a bound of `|log A|` on `[0, 1]`. -/
noncomputable def ksULA (M s : ℝ) : ℝ := |Real.log (ksUkA M s)| + |Real.log (ksUKb M s)|

theorem ksU_abs_log_ksDA_le {M s σ : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s)
    (hσ : σ ∈ Icc (0 : ℝ) 1) : |Real.log (ksDA M s σ)| ≤ ksULA M s :=
  ksU_abs_log_le_of_le (ksU_ksUkA_pos hM hs) (ksU_kA_le_ksDA hσ) (ksU_ksDA_le hσ)

theorem ksU_ksULA_nonneg (M s : ℝ) : 0 ≤ ksULA M s := by unfold ksULA; positivity

theorem ksU_ksUKb_nonneg (M s : ℝ) : 0 ≤ ksUKb M s := by unfold ksUKb; positivity

theorem ksU_sq_sum5_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d),
    sq_nonneg (c - e), sq_nonneg (d - e)]

theorem ksU_abs_ksUq_le {ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) : |ksUq ρ β w| ≤ 256 := by
  obtain ⟨r0, r1⟩ := hρ
  obtain ⟨b0, b1⟩ := hβ
  obtain ⟨w0, w1⟩ := hw
  have a0 : 0 ≤ 1 - ρ := by linarith
  have a1 : 1 - ρ ≤ 1 := by linarith
  have hbw : |β - w| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hw2 : |2 * w - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have c1 : |(1 - β) + (1 - ρ) * (β - w)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg a0 b0.le, mul_nonneg a0 w0.le]
  have d1 : |2 * (1 - β) + (1 - ρ) * (β - w)| ≤ 3 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg a0 b0.le, mul_nonneg a0 w0.le]
  have t2 : |32 * (1 - ρ) * w * (w - 1)| ≤ 32 := by
    rw [abs_le]; constructor <;>
      nlinarith [mul_nonneg a0 w0.le, mul_nonneg (mul_nonneg a0 w0.le) (by linarith : 0 ≤ 1 - w)]
  have t3 : |32 * (2 * w - 1) * ((1 - β) + (1 - ρ) * (β - w))| ≤ 32 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 32)]
    have := mul_le_mul hw2 c1 (abs_nonneg _) zero_le_one
    linarith
  have t5 : |32 * (β - w) * (2 * (1 - β) + (1 - ρ) * (β - w))| ≤ 96 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 32)]
    have := mul_le_mul hbw d1 (abs_nonneg _) zero_le_one
    linarith
  have t1 : |-32 * w| ≤ 32 := by rw [abs_le]; constructor <;> linarith
  have t4 : |32 * (β - w)| ≤ 32 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 32)]; linarith
  unfold ksUq
  rw [abs_le]
  constructor <;> linarith [abs_le.1 t1, abs_le.1 t2, abs_le.1 t3, abs_le.1 t4, abs_le.1 t5]

theorem ksU_abs_ksUf0_le {β w : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    |ksUf0 β w| ≤ 4 * ksDYmax β w := by
  obtain ⟨b0, b1⟩ := hβ
  have hY := ksU_ksDYmax_pos ⟨b0, b1⟩ hw
  have hq : 0 ≤ β * (1 - β) := mul_nonneg b0.le (by linarith)
  have hq4 : β * (1 - β) ≤ 1 / 4 := by nlinarith [sq_nonneg (β - 1 / 2)]
  unfold ksUf0
  rw [show -16 * β * (1 - β) * ksDYmax β w = -(16 * (β * (1 - β)) * ksDYmax β w) by ring,
    abs_neg, abs_of_nonneg (by positivity)]
  nlinarith

theorem ksU_sqrt_le_rpow {t Kb ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hKb : 0 ≤ Kb)
    (ht : t ≤ Kb / (1 - ρ)) : Real.sqrt t ≤ Real.sqrt Kb * (1 - ρ) ^ (-(1 / 2 : ℝ)) := by
  have h1 : 0 < 1 - ρ := by linarith [hρ.2]
  have e : (1 - ρ) ^ (-(1 / 2 : ℝ)) = Real.sqrt ((1 - ρ)⁻¹) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg h1.le, Real.inv_rpow h1.le]
  rw [e, ← Real.sqrt_mul hKb]
  exact Real.sqrt_le_sqrt (by rwa [← div_eq_mul_inv])

/-- `log(1 + t/Λ) log Λ ≤ 4√t` for `t ≥ 0`, `Λ ≥ 1`. -/
theorem ksU_eta_log_le {t Λ : ℝ} (ht : 0 ≤ t) (hΛ : 1 ≤ Λ) :
    Real.log (1 + t / Λ) * Real.log Λ ≤ 4 * Real.sqrt t := by
  have hΛ0 : 0 < Λ := by linarith
  have hη := ksU_log_one_add_le (div_nonneg ht hΛ0.le)
  rw [Real.sqrt_div' t hΛ0.le] at hη
  have hL := ksU_log_le_two_sqrt hΛ0
  have hs : 0 < Real.sqrt Λ := Real.sqrt_pos.2 hΛ0
  calc Real.log (1 + t / Λ) * Real.log Λ ≤ 2 * (Real.sqrt t / Real.sqrt Λ) * (2 * Real.sqrt Λ) :=
        mul_le_mul hη hL (Real.log_nonneg hΛ) (by positivity)
    _ = 4 * Real.sqrt t := by field_simp; ring

theorem ksU_ksUK_le_log_sq {z : ℝ} (hz : 0 < z) : ksUK z ≤ Real.log z ^ 2 / 2 + 2 * ksUK 1 := by
  have := ksU_ksUK_inv hz
  have := ksU_ksUK_nonneg (inv_pos.2 hz).le
  linarith

theorem ksU_ksUK_one_mem : 0 ≤ ksUK 1 ∧ ksUK 1 ≤ 1 :=
  ⟨ksU_ksUK_nonneg zero_le_one, ksU_ksUK_le zero_le_one⟩

theorem ksU_abs_add5_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have := abs_add_le (a + b + c + d) e
  have := abs_add_le (a + b + c) d
  have := abs_add_le (a + b) c
  have := abs_add_le a b
  linarith

section Node

variable {M s ρ β w : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) (hρ : ρ ∈ Ioo (0 : ℝ) 1)
  (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1)
include hM hs hρ hβ hw

theorem ksU_abs_ksUG0_le : |ksUG0 M s ρ β w| ≤ 5600 * M ^ 2 + 4000 * ksUKb M s := by
  have hwI := Ioo_subset_Icc_self hw
  have hc := ksU_coef_le (M := M) hρ hβ hw 0
  have hA := ksD_ksDA_pos hM hs hwI
  have hAle := ksU_ksDA_le (M := M) (s := s) hwI
  have e1 := abs_le.1 hc.1
  have e2 := abs_le.1 hc.2
  simp only [ksUG0, ksUGc, Fin.val_zero, Nat.cast_zero, zero_add, mul_one]
  unfold ksUKb
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ ksDHc (ksUPtB ρ β) w 0 + 8000) hA.le,
    mul_nonneg (by linarith : 0 ≤ 8000 - ksDHc (ksUPtB ρ β) w 0) hA.le]

/-- The bound of `Q₁`. -/
theorem ksU_abs_ksUQ1_le {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    |ksUQ1 M s Λ ρ β w| ≤ (5600 * M ^ 2 + 4000 * ksUKb M s) * (4 * (ksUkA M s)⁻¹) * ksUg ρ := by
  have hG := ksU_abs_ksUG0_le hM hs hρ hβ hw
  obtain ⟨r0, r1⟩ := hρ
  have h1 : 0 < 1 - ρ := by linarith
  have hwI := Ioo_subset_Icc_self hw
  have hβI := Ioo_subset_Icc_self hβ
  have hkA := ksU_ksUkA_pos hM hs
  have hA := ksD_ksDA_pos hM hs hwI
  have hY := ksU_ksDYmax_pos hβ hw
  have hY1 := ksU_ksDYmax_le_one hβ (w := w)
  have hb₀ := ksU_ksDbB_zero_pos hM hs ⟨r0, r1⟩ hβ
  have hb₀lo : ρ * ksUkA M s / (1 - ρ) ≤ ksDbB M 0 (ksUPtB ρ β) s := by
    rw [ksU_ksDbB_zero_ptB ⟨r0, r1⟩]; gcongr; exact ksU_kA_le_ksDA hβI
  have hB := ksU_ksDbB_ptB (M := M) (u := Λ) (s := s) (β := β) ⟨r0, r1⟩
  have hBge : ksDbB M 0 (ksUPtB ρ β) s ≤ ksDbB M Λ (ksUPtB ρ β) s := by
    rw [hB]; have := div_nonneg hΛ r0.le; linarith
  have j0 := ksU_J1_nonneg hA (hb₀.trans_le hBge) hY.le 0
  have ja := ksU_J1_anti hA hb₀ hBge hY.le 0
  have hm := ksU_wt_moment ⟨r0, r1⟩ hkA (ksU_kA_le_ksDA hwI) hb₀lo hY.le hY1 0
  set J0 := ksDJ1 (ksDA M s w) (ksDbB M 0 (ksUPtB ρ β) s) (ksDYmax β w) 0
  set JB := ksDJ1 (ksDA M s w) (ksDbB M Λ (ksUPtB ρ β) s) (ksDYmax β w) 0
  have e : ksUQ1 M s Λ ρ β w = ksUG0 M s ρ β w * ((1 - ρ)⁻¹ * (J0 - JB)) := by
    simp only [ksUQ1]; ring
  rw [e, abs_mul]
  have hi : 0 ≤ (1 - ρ)⁻¹ := inv_nonneg.2 h1.le
  have h2 : |(1 - ρ)⁻¹ * (J0 - JB)| ≤ 4 * (ksUkA M s)⁻¹ * ksUg ρ := by
    rw [abs_of_nonneg (mul_nonneg hi (by linarith))]
    calc (1 - ρ)⁻¹ * (J0 - JB) ≤ (1 - ρ)⁻¹ * J0 := by gcongr; linarith
      _ ≤ _ := hm
  have hK := ksU_ksUKb_nonneg M s
  calc |ksUG0 M s ρ β w| * |(1 - ρ)⁻¹ * (J0 - JB)| ≤
        (5600 * M ^ 2 + 4000 * ksUKb M s) * (4 * (ksUkA M s)⁻¹ * ksUg ρ) :=
        mul_le_mul hG h2 (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- The logarithm of `x = (1 - ρ)R`. -/
theorem ksU_abs_log_ksUR_le :
    |Real.log ((1 - ρ) * ksUR M s ρ β w)| ≤ |Real.log (1 - ρ)| + |Real.log ρ| +
      2 * (|Real.log w| + |Real.log (1 - w)|) + ksULA M s := by
  obtain ⟨r0, r1⟩ := hρ
  have h1 : 0 < 1 - ρ := by linarith
  have hwI := Ioo_subset_Icc_self hw
  have hβI := Ioo_subset_Icc_self hβ
  have hkA := ksU_ksUkA_pos hM hs
  have hA := ksD_ksDA_pos hM hs hwI
  have hAb := ksD_ksDA_pos hM hs hβI
  have hkw := ksU_kA_le_ksDA (M := M) (s := s) hwI
  have hkb := ksU_kA_le_ksDA (M := M) (s := s) hβI
  have hAw := ksU_ksDA_le (M := M) (s := s) hwI
  have hAbl := ksU_ksDA_le (M := M) (s := s) hβI
  have hY := ksU_ksDYmax_pos hβ hw
  have hY1 := ksU_ksDYmax_le_one hβ (w := w)
  have hlY := ksU_abs_log_ksDYmax_le hβ hw
  set Y := ksDYmax β w
  set D := (1 - ρ) * ksDA M s w + ρ * ksDA M s β * Y with hD
  have hDlo : ksUkA M s * Y ≤ D := by
    have : ksUkA M s * Y ≤ ksDA M s w := by nlinarith
    have : ksUkA M s * Y ≤ ksDA M s β * Y := by nlinarith
    nlinarith
  have hDhi : D ≤ ksUKb M s := by
    unfold ksUKb
    have : ksDA M s β * Y ≤ M ^ 2 + |s| := by nlinarith
    nlinarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDlo
  have hlD := ksU_abs_log_le_of_le (by positivity) hDlo hDhi
  rw [Real.log_mul hkA.ne' hY.ne'] at hlD
  have e : Real.log ((1 - ρ) * ksUR M s ρ β w) =
      Real.log (1 - ρ) + Real.log Y - Real.log ρ - Real.log D := by
    rw [ksUR, ← hD, mul_div_assoc', Real.log_div (by positivity) (by positivity),
      Real.log_mul h1.ne' hY.ne', Real.log_mul r0.ne' hD0.ne']
    ring
  rw [e]
  have k1 := abs_sub (Real.log (1 - ρ) + Real.log Y - Real.log ρ) (Real.log D)
  have k2 := abs_sub (Real.log (1 - ρ) + Real.log Y) (Real.log ρ)
  have k3 := abs_add_le (Real.log (1 - ρ)) (Real.log Y)
  have k4 := abs_add_le (Real.log (ksUkA M s)) (Real.log Y)
  unfold ksULA
  linarith

/-- The bound of the regular logarithm piece. -/
theorem ksU_abs_P2_le {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    |ksUq ρ β w * ksDYmax β w / 2 *
        (Real.log (1 + Λ * ((1 - ρ) * ksUR M s ρ β w)) - Real.log Λ)| ≤
      128 * (1 + 2 * (|Real.log (1 - ρ)| + |Real.log ρ| +
        2 * (|Real.log w| + |Real.log (1 - w)|) + ksULA M s)) := by
  have hq := ksU_abs_ksUq_le hρ hβ hw
  have hY := ksU_ksDYmax_pos hβ hw
  have hY1 := ksU_ksDYmax_le_one hβ (w := w)
  have hx : 0 < (1 - ρ) * ksUR M s ρ β w :=
    mul_pos (by linarith [hρ.2]) (ksU_ksUR_pos hM hs hρ hβ hw)
  have hl := ksU_abs_log_sub_le hx hΛ
  have hl1 := ksU_log_one_add_le_abs hx
  have hlx := ksU_abs_log_ksUR_le hM hs hρ hβ hw
  rw [abs_mul, abs_div, abs_mul, abs_of_pos hY, abs_two]
  have h0 : |ksUq ρ β w| * ksDYmax β w / 2 ≤ 128 := by nlinarith [abs_nonneg (ksUq ρ β w)]
  have hn : 0 ≤ |ksUq ρ β w| * ksDYmax β w / 2 := by positivity
  calc |ksUq ρ β w| * ksDYmax β w / 2 *
        |Real.log (1 + Λ * ((1 - ρ) * ksUR M s ρ β w)) - Real.log Λ| ≤
        128 * (1 + 2 * |Real.log ((1 - ρ) * ksUR M s ρ β w)|) :=
        mul_le_mul h0 (by linarith) (abs_nonneg _) (by norm_num)
    _ ≤ _ := by gcongr

omit hM hs hβ hw in
/-- `-log ρ ≤ 4(1 - ρ) ksUg ρ`. -/
theorem ksU_neg_log_le_one_sub : -Real.log ρ ≤ 4 * (1 - ρ) * ksUg ρ := by
  have h := ksU_neg_log_one_sub_le (x := 1 - ρ) ⟨by linarith [hρ.2], by linarith [hρ.1]⟩
  rwa [sub_sub_cancel, ksU_ksUg_symm] at h

/-- The bound of `Q₃`. -/
theorem ksU_abs_ksUQ3_le {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    |ksUQ3 M s Λ ρ β w| ≤ 32 * ksUg ρ + 4 * ksUKb M s * (ksUkA M s)⁻¹ := by
  have hnl := ksU_neg_log_le_one_sub hρ
  have hf := ksU_abs_ksUf0_le hβ hw
  obtain ⟨r0, r1⟩ := hρ
  have h1 : 0 < 1 - ρ := by linarith
  have hwI := Ioo_subset_Icc_self hw
  have hβI := Ioo_subset_Icc_self hβ
  have hkA := ksU_ksUkA_pos hM hs
  have hA := ksD_ksDA_pos hM hs hwI
  have hAb := ksD_ksDA_pos hM hs hβI
  have hkb := ksU_kA_le_ksDA (M := M) (s := s) hβI
  have hAw := ksU_ksDA_le (M := M) (s := s) hwI
  have hY := ksU_ksDYmax_pos hβ hw
  have hR := ksU_ksUR_pos hM hs ⟨r0, r1⟩ hβ hw
  set Y := ksDYmax β w with hYd
  set A := ksDA M s w with hAd
  set Ab := ksDA M s β with hAbd
  -- the mediant bound
  have hmed := ksU_abs_log_ratio_le (mul_pos h1 hR) (div_pos h1 hAb) hΛ
  have e1 : (1 + Λ * (1 - ρ) * ksUR M s ρ β w) / (1 + Λ * (1 - ρ) / Ab) =
      (1 + Λ * ((1 - ρ) * ksUR M s ρ β w)) / (1 + Λ * ((1 - ρ) / Ab)) := by ring
  have hD0 : 0 < (1 - ρ) * A + ρ * Ab * Y := by positivity
  have hT0 : 0 < ρ + (1 - ρ) * (A / (Ab * Y)) := by positivity
  have e2 : (1 - ρ) * ksUR M s ρ β w / ((1 - ρ) / Ab) =
      (ρ * (ρ + (1 - ρ) * (A / (Ab * Y))))⁻¹ := by
    simp only [ksUR, ← hYd, ← hAd, ← hAbd]
    field_simp
    ring
  rw [e2] at hmed
  -- the logarithm of `R A(β) = (ρ t)⁻¹`
  set c := A / (Ab * Y) with hc
  have hc0 : 0 < c := by positivity
  set t := ρ + (1 - ρ) * c with ht
  have htρ : ρ ≤ t := by have := mul_pos h1 hc0; linarith
  have ht0 : 0 < t := r0.trans_le htρ
  have hlt1 : Real.log t ≤ (1 - ρ) * c := by
    have := Real.log_le_sub_one_of_pos ht0; nlinarith
  have hlt2 : Real.log ρ ≤ Real.log t := Real.log_le_log r0 htρ
  have hlρ : Real.log ρ ≤ 0 := Real.log_nonpos r0.le r1.le
  have hL : |Real.log (ρ * t)⁻¹| ≤ -2 * Real.log ρ + (1 - ρ) * c := by
    rw [Real.log_inv, Real.log_mul r0.ne' ht0.ne', abs_le]
    constructor <;> nlinarith [mul_pos h1 hc0]
  -- assemble
  have hfc : |ksUf0 β w| * c ≤ 4 * ksUKb M s * (ksUkA M s)⁻¹ := by
    have : |ksUf0 β w| * c ≤ 4 * Y * c := by gcongr
    have e3 : 4 * Y * c = 4 * A * Ab⁻¹ := by rw [hc]; field_simp
    have : A * Ab⁻¹ ≤ ksUKb M s * (ksUkA M s)⁻¹ :=
      mul_le_mul hAw (inv_anti₀ hkA hkb) (by positivity) (ksU_ksUKb_nonneg M s)
    unfold ksUKb at *
    nlinarith
  have hfl : |ksUf0 β w| * ((1 - ρ)⁻¹ * (-2 * Real.log ρ)) ≤ 32 * ksUg ρ := by
    have : (1 - ρ)⁻¹ * (-2 * Real.log ρ) ≤ 8 * ksUg ρ := by
      rw [inv_mul_le_iff₀ h1]; nlinarith
    have hY1 := ksU_ksDYmax_le_one hβ (w := w)
    have : |ksUf0 β w| ≤ 4 := by linarith
    have : 0 ≤ (1 - ρ)⁻¹ * (-2 * Real.log ρ) := mul_nonneg (inv_pos.2 h1).le (by linarith)
    nlinarith [abs_nonneg (ksUf0 β w)]
  unfold ksUQ3
  rw [e1, abs_mul, abs_mul, abs_of_pos (inv_pos.2 h1)]
  calc (1 - ρ)⁻¹ * |ksUf0 β w| *
        |Real.log ((1 + Λ * ((1 - ρ) * ksUR M s ρ β w)) / (1 + Λ * ((1 - ρ) / Ab)))| ≤
        (1 - ρ)⁻¹ * |ksUf0 β w| * (-2 * Real.log ρ + (1 - ρ) * c) := by
        gcongr; exact hmed.trans hL
    _ = |ksUf0 β w| * ((1 - ρ)⁻¹ * (-2 * Real.log ρ)) + |ksUf0 β w| * c := by
        field_simp
    _ ≤ _ := by linarith

/-- The bound of the first dilogarithm piece. -/
theorem ksU_abs_P4_le {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    |ρ * ksUcB w * ((ksUK ((ρ * ksDbB M 0 (ksUPtB ρ β) s + Λ) *
          (ksDYmax β w / (ρ * ksDA M s w))) - Real.log Λ ^ 2 / 2 -
          ksUl3 M s ρ β w * Real.log Λ) -
        ksUK (ksDbB M 0 (ksUPtB ρ β) s * ksDYmax β w / ksDA M s w))| ≤
      4 * (800 + 18 * ksULA M s ^ 2 + 2 * ksUKb M s ^ 2 + 4 * Real.sqrt (ksUKb M s)) *
        (ksUg ρ * ksUg w) := by
  have hcB := ksU_abs_ksUcB_le hw
  have hLB := ksU_logs_le_B hρ hw
  obtain ⟨r0, r1⟩ := hρ
  have h1 : 0 < 1 - ρ := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hwI := Ioo_subset_Icc_self hw
  have hβI := Ioo_subset_Icc_self hβ
  have hA := ksD_ksDA_pos hM hs hwI
  have hAb := ksD_ksDA_pos hM hs hβI
  have hAbl := ksU_ksDA_le (M := M) (s := s) hβI
  have hlA := ksU_abs_log_ksDA_le hM hs hwI
  have hlAb := ksU_abs_log_ksDA_le hM hs hβI
  have hY := ksU_ksDYmax_pos hβ hw
  have hlY := ksU_abs_log_ksDYmax_le hβ hw
  have hb₀ := ksU_ksDbB_zero_pos hM hs ⟨r0, r1⟩ hβ
  have hb₀e := ksU_ksDbB_zero_ptB (M := M) (s := s) (β := β) ⟨r0, r1⟩
  have hLA := ksU_ksULA_nonneg M s
  have hKb := ksU_ksUKb_nonneg M s
  have hK1 := ksU_ksUK_one_mem
  set G := ksUg ρ * ksUg w with hG
  set LA := ksULA M s
  set Kb := ksUKb M s
  set Y := ksDYmax β w
  set A := ksDA M s w
  set b₀ := ksDbB M 0 (ksUPtB ρ β) s
  set lr := |Real.log ρ|
  set lr' := |Real.log (1 - ρ)|
  set lw := |Real.log w|
  set lw' := |Real.log (1 - w)|
  have ha : 0 < Y / (ρ * A) := by positivity
  set a := Y / (ρ * A) with had
  set t := ρ * b₀ with htd
  have ht : 0 ≤ t := by positivity
  have htle : t ≤ Kb / (1 - ρ) := by
    rw [htd, hb₀e, le_div_iff₀ h1]
    have : ρ * (ρ * ksDA M s β / (1 - ρ)) * (1 - ρ) = ρ * ρ * ksDA M s β := by field_simp
    rw [this]
    have : ρ * ρ ≤ 1 := by nlinarith only [r0, r1]
    have : ρ * ρ * ksDA M s β ≤ ksDA M s β := mul_le_of_le_one_left hAb.le this
    unfold Kb ksUKb; linarith
  -- the exact form
  have hK := ksU_K_sub_eq ha ht hΛ0
  set η := Real.log (1 + t / Λ) with hηd
  set L := Real.log Λ
  have hL0 : 0 ≤ L := Real.log_nonneg hΛ
  have hη0 : 0 ≤ η := Real.log_nonneg (by have := div_nonneg ht hΛ0.le; linarith)
  have hηL : η * L ≤ 4 * Real.sqrt t := ksU_eta_log_le ht hΛ
  have hsq : Real.sqrt t ≤ Real.sqrt Kb * G :=
    (ksU_sqrt_le_rpow ⟨r0, r1⟩ hKb htle).trans
      (mul_le_mul_of_nonneg_left hLB.2.2.2.2.2.2.2.2.2.2.2 (Real.sqrt_nonneg _))
  have hηle : η ≤ Kb + lr' := by
    have hle : 1 + t / Λ ≤ (1 + Kb) / (1 - ρ) := by
      have : t / Λ ≤ t := div_le_self ht hΛ
      rw [le_div_iff₀ h1]
      have h3 := (le_div_iff₀ h1).1 htle
      have h4 := mul_le_mul_of_nonneg_right this h1.le
      linarith
    have := Real.log_le_log (by positivity) hle
    rw [Real.log_div (by positivity) h1.ne'] at this
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + Kb)
    have := neg_abs_le (Real.log (1 - ρ))
    linarith
  -- the logarithms
  have hla : |Real.log a| ≤ lw + lw' + lr + LA := by
    rw [had, Real.log_div hY.ne' (by positivity), Real.log_mul r0.ne' hA.ne']
    have := abs_sub (Real.log Y) (Real.log ρ + Real.log A)
    have := abs_add_le (Real.log ρ) (Real.log A)
    linarith
  have hlz : |Real.log (b₀ * Y / A)| ≤ lr + lr' + lw + lw' + 2 * LA := by
    rw [hb₀e, Real.log_div (by positivity) hA.ne', Real.log_mul (by positivity) hY.ne',
      Real.log_div (by positivity) h1.ne', Real.log_mul r0.ne' hAb.ne']
    have := abs_sub (Real.log ρ + Real.log (ksDA M s β) - Real.log (1 - ρ) + Real.log Y)
      (Real.log A)
    have := abs_add_le (Real.log ρ + Real.log (ksDA M s β) - Real.log (1 - ρ)) (Real.log Y)
    have := abs_sub (Real.log ρ + Real.log (ksDA M s β)) (Real.log (1 - ρ))
    have := abs_add_le (Real.log ρ) (Real.log (ksDA M s β))
    linarith
  have hS : lr ^ 2 + lr' ^ 2 + lw ^ 2 + lw' ^ 2 ≤ 64 * G := by
    simp only [lr, lr', lw, lw', sq_abs]; linarith [hLB.2.2.2.2.2.2.2.1, hLB.2.2.2.2.2.2.2.2.1,
      hLB.2.2.2.2.2.2.2.2.2.1, hLB.2.2.2.2.2.2.2.2.2.2.1]
  have hla2 : Real.log a ^ 2 ≤ 5 * (lr ^ 2 + lr' ^ 2 + lw ^ 2 + lw' ^ 2 + LA ^ 2) := by
    have h0 : 0 ≤ |Real.log a| := abs_nonneg _
    have h5 := ksU_sq_sum5_le lw lw' lr LA 0
    have h2 : |Real.log a| ^ 2 ≤ (lw + lw' + lr + LA + 0) ^ 2 := by
      rw [add_zero]; exact pow_le_pow_left₀ h0 hla 2
    rw [← sq_abs]
    linarith [sq_nonneg lr']
  have hlz2 : Real.log (b₀ * Y / A) ^ 2 ≤
      5 * (lr ^ 2 + lr' ^ 2 + lw ^ 2 + lw' ^ 2 + 4 * LA ^ 2) := by
    have h0 : 0 ≤ |Real.log (b₀ * Y / A)| := abs_nonneg _
    have h5 := ksU_sq_sum5_le lr lr' lw lw' (2 * LA)
    have h2 := pow_le_pow_left₀ h0 hlz 2
    rw [← sq_abs]
    linarith
  have hη2 : η ^ 2 ≤ 2 * Kb ^ 2 + 2 * lr' ^ 2 := by
    have h2 := pow_le_pow_left₀ hη0 hηle 2
    linarith [sq_nonneg (Kb - lr')]
  have hlη : |Real.log a * η| ≤ (Real.log a ^ 2 + η ^ 2) / 2 := by
    rw [abs_mul, abs_of_nonneg hη0]
    have := two_mul_le_add_sq (|Real.log a|) η
    rw [sq_abs] at this
    linarith
  -- the dilogarithms
  have hz : ((t + Λ) * a)⁻¹ ≤ a⁻¹ := by
    exact inv_anti₀ ha (le_mul_of_one_le_left ha.le (by linarith))
  have hKz0 := ksU_ksUK_nonneg (inv_pos.2 (by positivity : 0 < (t + Λ) * a)).le
  have hKz : ksUK ((t + Λ) * a)⁻¹ ≤ Real.log a ^ 2 / 2 + 2 * ksUK 1 := by
    have := ksU_ksUK_mono (inv_pos.2 (by positivity : 0 < (t + Λ) * a)).le hz
    have h2 := ksU_ksUK_le_log_sq (inv_pos.2 ha)
    rw [Real.log_inv, neg_sq] at h2
    linarith
  have hb0YA : 0 < b₀ * Y / A := by positivity
  have hKb0 := ksU_ksUK_nonneg hb0YA.le
  have hKb1 := ksU_ksUK_le_log_sq hb0YA
  have hX : |ksUK ((t + Λ) * a) - L ^ 2 / 2 - ksUl3 M s ρ β w * L - ksUK (b₀ * Y / A)| ≤
      800 * G + 18 * LA ^ 2 + 2 * Kb ^ 2 + 4 * (Real.sqrt Kb * G) := by
    rw [show ksUl3 M s ρ β w = Real.log a from rfl, hK]
    have hlη' := abs_le.1 hlη
    have hsq0 : 0 ≤ Real.log a ^ 2 := sq_nonneg _
    have hη20 : 0 ≤ η ^ 2 := sq_nonneg _
    have hlz0 : 0 ≤ Real.log (b₀ * Y / A) ^ 2 := sq_nonneg _
    have hlr' : lr' ^ 2 ≤ 16 * G := by
      simp only [lr', sq_abs]; exact hLB.2.2.2.2.2.2.2.2.1
    have A1 : Real.log a ^ 2 ≤ 320 * G + 5 * LA ^ 2 := by linarith
    have A2 : Real.log (b₀ * Y / A) ^ 2 ≤ 320 * G + 20 * LA ^ 2 := by linarith
    have A3 : η ^ 2 ≤ 2 * Kb ^ 2 + 32 * G := by linarith
    have hG1 := hLB.1
    have hLA2 : 0 ≤ LA ^ 2 := sq_nonneg _
    have hηL0 := mul_nonneg hη0 hL0
    have hsG : 0 ≤ Real.sqrt Kb * G := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
    have hKb2 : 0 ≤ Kb ^ 2 := sq_nonneg _
    have k1 := hK1.1
    have k2 := hK1.2
    rw [abs_le]
    constructor <;> linarith
  have hG1 := hLB.1
  have hX' : |ksUK ((t + Λ) * a) - L ^ 2 / 2 - ksUl3 M s ρ β w * L - ksUK (b₀ * Y / A)| ≤
      (800 + 18 * LA ^ 2 + 2 * Kb ^ 2 + 4 * Real.sqrt Kb) * G := by
    have : 18 * LA ^ 2 ≤ 18 * LA ^ 2 * G := le_mul_of_one_le_right (by positivity) hG1
    have : 2 * Kb ^ 2 ≤ 2 * Kb ^ 2 * G := le_mul_of_one_le_right (by positivity) hG1
    linarith
  have hρc : |ρ * ksUcB w| ≤ 4 := by
    rw [abs_mul, abs_of_pos r0]
    calc ρ * |ksUcB w| ≤ 1 * 4 := mul_le_mul r1.le hcB (abs_nonneg _) zero_le_one
      _ = 4 := one_mul 4
  rw [show (ρ * b₀ + Λ) = t + Λ from rfl, abs_mul, mul_assoc]
  exact mul_le_mul hρc hX' (abs_nonneg _) (by norm_num)

omit hρ in
/-- The bound of the second dilogarithm piece. -/
theorem ksU_abs_P5_le {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    |ksUf0 β w * (ksUK ((0 + Λ) * (ksDA M s β)⁻¹) - Real.log Λ ^ 2 / 2 -
        Real.log (ksDA M s β)⁻¹ * Real.log Λ)| ≤
      4 * (ksULA M s ^ 2 / 2 + 2 + ksUKb M s) := by
  have hf := ksU_abs_ksUf0_le hβ hw
  have hY1 := ksU_ksDYmax_le_one hβ (w := w)
  have hΛ0 : 0 < Λ := by linarith
  have hβI := Ioo_subset_Icc_self hβ
  have hAb := ksD_ksDA_pos hM hs hβI
  have hAbl := ksU_ksDA_le (M := M) (s := s) hβI
  have hlAb := ksU_abs_log_ksDA_le hM hs hβI
  have hK1 := ksU_ksUK_one_mem
  have hK := ksU_K_sub_eq (inv_pos.2 hAb) le_rfl hΛ0
  simp only [zero_div, add_zero, zero_add, Real.log_one, zero_mul, mul_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hK
  rw [zero_add, hK]
  have hz : 0 < (Λ * (ksDA M s β)⁻¹)⁻¹ := by positivity
  have hKz0 := ksU_ksUK_nonneg hz.le
  have hKz := ksU_ksUK_le hz.le
  have hz' : (Λ * (ksDA M s β)⁻¹)⁻¹ ≤ ksUKb M s := by
    rw [mul_inv, inv_inv]
    have : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ
    unfold ksUKb; nlinarith [inv_pos.2 hΛ0]
  have hl2 : Real.log (ksDA M s β)⁻¹ ^ 2 ≤ ksULA M s ^ 2 := by
    rw [Real.log_inv, neg_sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hlAb 2
  have hin : |Real.log (ksDA M s β)⁻¹ ^ 2 / 2 + 2 * ksUK 1 - ksUK (Λ * (ksDA M s β)⁻¹)⁻¹| ≤
      ksULA M s ^ 2 / 2 + 2 + ksUKb M s := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Real.log (ksDA M s β)⁻¹)]
  rw [abs_mul]
  exact mul_le_mul (by linarith) hin (abs_nonneg _) (by norm_num)

/-- `|log(Y/(ρA))| ≤ |log w| + |log(1 - w)| + |log ρ| + LA`. -/
theorem ksU_abs_ksUl3_le : |ksUl3 M s ρ β w| ≤
    |Real.log w| + |Real.log (1 - w)| + |Real.log ρ| + ksULA M s := by
  have hwI := Ioo_subset_Icc_self hw
  have hA := ksD_ksDA_pos hM hs hwI
  have hlA := ksU_abs_log_ksDA_le hM hs hwI
  have hY := ksU_ksDYmax_pos hβ hw
  have hlY := ksU_abs_log_ksDYmax_le hβ hw
  rw [ksUl3, Real.log_div hY.ne' (by have := hρ.1; positivity),
    Real.log_mul hρ.1.ne' hA.ne']
  have := abs_sub (Real.log (ksDYmax β w)) (Real.log ρ + Real.log (ksDA M s w))
  have := abs_add_le (Real.log ρ) (Real.log (ksDA M s w))
  linarith

omit hM hs in
theorem ksU_abs_ksUb2_le : |ksUb2 ρ β w| ≤ 4 := by
  have hcB := ksU_abs_ksUcB_le hw
  have hf := ksU_abs_ksUf0_le hβ hw
  have hY1 := ksU_ksDYmax_le_one hβ (w := w)
  have hρc : |ρ * ksUcB w| ≤ 4 := by
    rw [abs_mul, abs_of_pos hρ.1]
    calc ρ * |ksUcB w| ≤ 1 * 4 := mul_le_mul hρ.2.le hcB (abs_nonneg _) zero_le_one
      _ = 4 := one_mul 4
  unfold ksUb2
  have := abs_add_le (ρ * ksUcB w / 2) (ksUf0 β w / 2)
  rw [abs_div, abs_div, abs_two] at this
  linarith

theorem ksU_abs_ksUb1_le : |ksUb1 M s ρ β w| ≤ (152 + 8 * ksULA M s) * (ksUg ρ * ksUg w) := by
  have hcB := ksU_abs_ksUcB_le hw
  have hf := ksU_abs_ksUf0_le hβ hw
  have hY := ksU_ksDYmax_pos hβ hw
  have hY1 := ksU_ksDYmax_le_one hβ (w := w)
  have hq := ksU_abs_ksUq_le hρ hβ hw
  have hl3 := ksU_abs_ksUl3_le hM hs hρ hβ hw
  have hβI := Ioo_subset_Icc_self hβ
  have hlAb := ksU_abs_log_ksDA_le hM hs hβI
  have hLB := ksU_logs_le_B hρ hw
  have hLA := ksU_ksULA_nonneg M s
  have hρc : |ρ * ksUcB w| ≤ 4 := by
    rw [abs_mul, abs_of_pos hρ.1]
    calc ρ * |ksUcB w| ≤ 1 * 4 := mul_le_mul hρ.2.le hcB (abs_nonneg _) zero_le_one
      _ = 4 := one_mul 4
  have e1 : |ksUq ρ β w * ksDYmax β w / 2| ≤ 128 := by
    rw [abs_div, abs_mul, abs_of_pos hY, abs_two]
    have := mul_le_mul hq hY1 hY.le (by norm_num)
    linarith
  have e2 : |ρ * ksUcB w * ksUl3 M s ρ β w| ≤
      4 * (|Real.log w| + |Real.log (1 - w)| + |Real.log ρ| + ksULA M s) := by
    rw [abs_mul]; exact mul_le_mul hρc hl3 (abs_nonneg _) (by norm_num)
  have e3 : |ksUf0 β w * Real.log (ksDA M s β)⁻¹| ≤ 4 * ksULA M s := by
    rw [abs_mul, Real.log_inv, abs_neg]
    exact mul_le_mul (by linarith) hlAb (abs_nonneg _) (by norm_num)
  have hLAG : ksULA M s ≤ ksULA M s * (ksUg ρ * ksUg w) := le_mul_of_one_le_right hLA hLB.1
  unfold ksUb1
  have := abs_add_le (ksUq ρ β w * ksDYmax β w / 2 + ρ * ksUcB w * ksUl3 M s ρ β w)
    (ksUf0 β w * Real.log (ksDA M s β)⁻¹)
  have := abs_add_le (ksUq ρ β w * ksDYmax β w / 2) (ρ * ksUcB w * ksUl3 M s ρ β w)
  linarith [hLB.1, hLB.2.2.2.1, hLB.2.2.2.2.2.1, hLB.2.2.2.2.2.2.1]

theorem ksU_abs_ksUMd_le {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    |ksUMd M s Λ ρ β w| ≤ 4 * Λ * (ksUkA M s)⁻¹ := by
  have hf := ksU_abs_ksUf0_le hβ hw
  have hY1 := ksU_ksDYmax_le_one hβ (w := w)
  have h1 : 0 < 1 - ρ := by linarith [hρ.2]
  have hβI := Ioo_subset_Icc_self hβ
  have hkA := ksU_ksUkA_pos hM hs
  have hAb := ksD_ksDA_pos hM hs hβI
  have hkb := ksU_kA_le_ksDA (M := M) (s := s) hβI
  have hx : 0 ≤ Λ * (1 - ρ) / ksDA M s β := by positivity
  have hl0 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + Λ * (1 - ρ) / ksDA M s β)
  have hl1 := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + Λ * (1 - ρ) / ksDA M s β)
  unfold ksUMd
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 h1), abs_of_nonneg hl0]
  have hf4 : |ksUf0 β w| ≤ 4 := by linarith
  calc (1 - ρ)⁻¹ * |ksUf0 β w| * Real.log (1 + Λ * (1 - ρ) / ksDA M s β) ≤
        (1 - ρ)⁻¹ * 4 * (Λ * (1 - ρ) / ksDA M s β) := by gcongr; linarith
    _ = 4 * Λ * (ksDA M s β)⁻¹ := by field_simp
    _ ≤ 4 * Λ * (ksUkA M s)⁻¹ := by gcongr

omit hρ in
theorem ksU_abs_f0K_le {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    |ksUf0 β w * ksUK (Λ / ksDA M s β)| ≤ 4 * Λ * (ksUkA M s)⁻¹ := by
  have hf := ksU_abs_ksUf0_le hβ hw
  have hY1 := ksU_ksDYmax_le_one hβ (w := w)
  have hβI := Ioo_subset_Icc_self hβ
  have hkA := ksU_ksUkA_pos hM hs
  have hAb := ksD_ksDA_pos hM hs hβI
  have hkb := ksU_kA_le_ksDA (M := M) (s := s) hβI
  have hx : 0 ≤ Λ / ksDA M s β := by positivity
  rw [abs_mul, abs_of_nonneg (ksU_ksUK_nonneg hx)]
  calc |ksUf0 β w| * ksUK (Λ / ksDA M s β) ≤ 4 * (Λ / ksDA M s β) :=
        mul_le_mul (by linarith) (ksU_ksUK_le hx) (ksU_ksUK_nonneg hx) (by norm_num)
    _ ≤ 4 * Λ * (ksUkA M s)⁻¹ := by
        rw [div_eq_mul_inv, ← mul_assoc]; gcongr

end Node

/-- **The domination of the `VB` remainder**: for `M > 0` and `s > -4M²` there is `C` with
`|ksUDr M s Λ ρ β w| ≤ C ksUg ρ ksUg w` for all `Λ ≥ 1` on the open cube. -/
theorem ksU_abs_ksUDr_le {M s : ℝ} (hM : 0 < M) (hs : -(4 * M ^ 2) < s) :
    ∃ C, ∀ Λ : ℝ, 1 ≤ Λ → ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ β ∈ Ioo (0 : ℝ) 1, ∀ w ∈ Ioo (0 : ℝ) 1,
      |ksUDr M s Λ ρ β w| ≤ C * (ksUg ρ * ksUg w) := by
  set LA := ksULA M s with hLAd
  set Kb := ksUKb M s with hKbd
  set kA := ksUkA M s with hkAd
  have hLA := ksU_ksULA_nonneg M s
  have hKb := ksU_ksUKb_nonneg M s
  have hkA := ksU_ksUkA_pos hM hs
  refine ⟨(5600 * M ^ 2 + 4000 * Kb) * (4 * kA⁻¹) + 128 * (25 + 2 * LA) +
    (32 + 4 * Kb * kA⁻¹) + 4 * (800 + 18 * LA ^ 2 + 2 * Kb ^ 2 + 4 * Real.sqrt Kb) +
    4 * (LA ^ 2 / 2 + 2 + Kb), fun Λ hΛ ρ hρ β hβ w hw => ?_⟩
  have h1 := ksU_abs_ksUQ1_le hM hs hρ hβ hw (by linarith : (0 : ℝ) ≤ Λ)
  have h2 := ksU_abs_P2_le hM hs hρ hβ hw hΛ
  have h3 := ksU_abs_ksUQ3_le hM hs hρ hβ hw (by linarith : (0 : ℝ) ≤ Λ)
  have h4 := ksU_abs_P4_le hM hs hρ hβ hw hΛ
  have h5 := ksU_abs_P5_le hM hs hβ hw hΛ
  have hLB := ksU_logs_le_B hρ hw
  simp only [← hLAd, ← hKbd, ← hkAd] at h1 h2 h3 h4 h5
  set G := ksUg ρ * ksUg w
  have hG1 := hLB.1
  have hC1 : 0 ≤ (5600 * M ^ 2 + 4000 * Kb) * (4 * kA⁻¹) := by positivity
  have e1 : (5600 * M ^ 2 + 4000 * Kb) * (4 * kA⁻¹) * ksUg ρ ≤
      (5600 * M ^ 2 + 4000 * Kb) * (4 * kA⁻¹) * G := mul_le_mul_of_nonneg_left hLB.2.1 hC1
  have e2 : 128 * (1 + 2 * (|Real.log (1 - ρ)| + |Real.log ρ| +
      2 * (|Real.log w| + |Real.log (1 - w)|) + LA)) ≤ 128 * (25 + 2 * LA) * G := by
    have : LA ≤ LA * G := le_mul_of_one_le_right hLA hG1
    linarith [hLB.2.2.2.1, hLB.2.2.2.2.1, hLB.2.2.2.2.2.1, hLB.2.2.2.2.2.2.1]
  have e3 : 32 * ksUg ρ + 4 * Kb * kA⁻¹ ≤ (32 + 4 * Kb * kA⁻¹) * G := by
    have : 4 * Kb * kA⁻¹ ≤ 4 * Kb * kA⁻¹ * G := le_mul_of_one_le_right (by positivity) hG1
    linarith [hLB.2.1]
  have e5 : 4 * (LA ^ 2 / 2 + 2 + Kb) ≤ 4 * (LA ^ 2 / 2 + 2 + Kb) * G :=
    le_mul_of_one_le_right (by positivity) hG1
  rw [ksU_ksUDr_eq hM hs hρ hw Λ]
  refine (ksU_abs_add5_le _ _ _ _ _).trans ?_
  linarith

end QED.ChainProof.SetAKS

end
