/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKUVBLim

/-!
# Set (a), stage D: elementary bounds for the `VB` expansion

Helper level for `SetAKSFix e` (Set (a) of the three-loop coefficient), stage D (the
Källén–Sabry identification), step D3 (the photon-mass integral of the `VB` class). Elementary
inequalities used to dominate the pieces of the split `ksU_ksUDB_split` uniformly in the cutoff
`Λ ≥ 1` by a multiple of `ksUg ρ · ksUg w`.

Main results:

* `ksU_abs_log_le_of_le`, `ksU_abs_log_sub_le`, `ksU_abs_log_ratio_le` (mediant);
* `ksU_K_sub_eq`: the exact form of `K((t + Λ)a) - (log Λ)²/2 - log a log Λ`;
* `ksU_logs_le_B`: the logarithms at a node `(ρ, w)`;
* `ksU_abs_log_ksDYmax_le`: `|log Y| ≤ |log w| + |log(1 - w)|`.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace QED.ChainProof.SetAKS

theorem ksU_abs_log_le_of_le {a z b : ℝ} (ha : 0 < a) (haz : a ≤ z) (hzb : z ≤ b) :
    |Real.log z| ≤ |Real.log a| + |Real.log b| := by
  have h1 := Real.log_le_log ha haz
  have h2 := Real.log_le_log (ha.trans_le haz) hzb
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b),
    abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem ksU_abs_log_sub_le {a Λ : ℝ} (ha : 0 < a) (hΛ : 1 ≤ Λ) :
    |Real.log (1 + Λ * a) - Real.log Λ| ≤ |Real.log a| + Real.log (1 + a) := by
  have hΛ0 : 0 < Λ := by linarith
  have e : Real.log (1 + Λ * a) - Real.log Λ = Real.log (Λ⁻¹ + a) := by
    rw [← Real.log_div (by positivity) hΛ0.ne']
    congr 1
    field_simp
  rw [e]
  have hi : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ
  have hi0 : 0 < Λ⁻¹ := inv_pos.2 hΛ0
  have h := ksU_abs_log_le_of_le ha (by linarith : a ≤ Λ⁻¹ + a) (by linarith : Λ⁻¹ + a ≤ 1 + a)
  rwa [abs_of_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + a))] at h

/-- **The mediant bound**: `|log((1 + Λa)/(1 + Λb))| ≤ |log(a/b)|` for `Λ ≥ 0`. -/
theorem ksU_abs_log_ratio_le {a b Λ : ℝ} (ha : 0 < a) (hb : 0 < b) (hΛ : 0 ≤ Λ) :
    |Real.log ((1 + Λ * a) / (1 + Λ * b))| ≤ |Real.log (a / b)| := by
  have h1 : 0 < 1 + Λ * a := by positivity
  have h2 : 0 < 1 + Λ * b := by positivity
  rcases le_total b a with h | h
  · have l1 : 1 ≤ (1 + Λ * a) / (1 + Λ * b) := by
      rw [le_div_iff₀ h2]; nlinarith
    have l2 : (1 + Λ * a) / (1 + Λ * b) ≤ a / b := by
      rw [div_le_div_iff₀ h2 hb]; nlinarith
    have := Real.log_le_log (by linarith) l2
    rw [abs_of_nonneg (Real.log_nonneg l1), abs_of_nonneg (Real.log_nonneg ((one_le_div hb).2 h))]
    exact this
  · have l1 : (1 + Λ * a) / (1 + Λ * b) ≤ 1 := by
      rw [div_le_iff₀ h2]; nlinarith
    have l2 : a / b ≤ (1 + Λ * a) / (1 + Λ * b) := by
      rw [div_le_div_iff₀ hb h2]; nlinarith
    have := Real.log_le_log (div_pos ha hb) l2
    rw [abs_of_nonpos (Real.log_nonpos (by positivity) l1),
      abs_of_nonpos (Real.log_nonpos (by positivity) ((div_le_one hb).2 h))]
    linarith

theorem ksU_log_one_add_le_abs {x : ℝ} (hx : 0 < x) : Real.log (1 + x) ≤ 1 + |Real.log x| := by
  rcases le_total x 1 with h | h
  · have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)
    linarith [abs_nonneg (Real.log x)]
  · have h2 : Real.log (1 + x) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul two_ne_zero hx.ne'] at h2
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    linarith [le_abs_self (Real.log x)]

theorem ksU_ksUg_symm (x : ℝ) : ksUg (1 - x) = ksUg x := by
  unfold ksUg; rw [sub_sub_cancel]; ring

theorem ksU_neg_log_one_sub_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    -Real.log (1 - x) ≤ 4 * x * ksUg x := by
  obtain ⟨r0, r1⟩ := hx
  have h1 : 0 < 1 - x := by linarith
  have hg := ksU_one_le_ksUg ⟨r0, r1⟩
  have hgr := (ksU_rpow_le_ksUg ⟨r0, r1⟩).2
  rcases le_or_gt x (1 / 2) with h | h
  · have hl := Real.one_sub_inv_le_log_of_pos h1
    have : (1 - x)⁻¹ ≤ 2 := by rw [inv_le_comm₀ h1 two_pos]; linarith
    have e : 1 - (1 - x)⁻¹ = -(x * (1 - x)⁻¹) := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left this r0.le]
  · have hl := ksU_abs_log_le h1 (by linarith)
    rw [abs_of_nonpos (Real.log_nonpos h1.le (by linarith))] at hl
    nlinarith

/-- The exact form of the dilogarithm at large argument (`a > 0`, `t ≥ 0`, `Λ > 0`). -/
theorem ksU_K_sub_eq {a t Λ : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hΛ : 0 < Λ) :
    ksUK ((t + Λ) * a) - Real.log Λ ^ 2 / 2 - Real.log a * Real.log Λ =
      Real.log a ^ 2 / 2 + Real.log (1 + t / Λ) * Real.log Λ +
        Real.log a * Real.log (1 + t / Λ) + Real.log (1 + t / Λ) ^ 2 / 2 + 2 * ksUK 1 -
        ksUK ((t + Λ) * a)⁻¹ := by
  have hz0 : 0 < (t + Λ) * a := by positivity
  have hinv := ksU_ksUK_inv hz0
  have hlog : Real.log ((t + Λ) * a) = Real.log Λ + Real.log a + Real.log (1 + t / Λ) := by
    rw [show (t + Λ) * a = Λ * a * (1 + t / Λ) by field_simp; ring,
      Real.log_mul (by positivity) (by positivity), Real.log_mul hΛ.ne' ha.ne']
  rw [hlog] at hinv
  linarith [hinv]

theorem ksU_abs_log_ksDYmax_le {β w : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    |Real.log (ksDYmax β w)| ≤ |Real.log w| + |Real.log (1 - w)| := by
  obtain ⟨b0, b1⟩ := hβ
  obtain ⟨w0, w1⟩ := hw
  have hY := ksU_ksDYmax_pos ⟨b0, b1⟩ ⟨w0, w1⟩
  have hY1 := ksU_ksDYmax_le_one ⟨b0, b1⟩ (w := w)
  have hlo : w * (1 - w) ≤ ksDYmax β w := by
    refine le_min ?_ ?_
    · rw [le_div_iff₀ b0]; nlinarith [mul_pos w0 (sub_pos.2 w1)]
    · rw [le_div_iff₀ (by linarith)]; nlinarith [mul_pos w0 (sub_pos.2 w1)]
  have h := Real.log_le_log (by nlinarith) hlo
  rw [Real.log_mul w0.ne' (by linarith)] at h
  rw [abs_of_nonpos (Real.log_nonpos hY.le hY1), abs_of_nonpos (Real.log_nonpos w0.le w1.le),
    abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
  linarith

/-- The logarithms at a node `(ρ, w)`, dominated by `G = ksUg ρ · ksUg w`. -/
theorem ksU_logs_le_B {ρ w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    1 ≤ ksUg ρ * ksUg w ∧ ksUg ρ ≤ ksUg ρ * ksUg w ∧ ksUg w ≤ ksUg ρ * ksUg w ∧
      |Real.log ρ| ≤ 2 * (ksUg ρ * ksUg w) ∧ |Real.log (1 - ρ)| ≤ 2 * (ksUg ρ * ksUg w) ∧
      |Real.log w| ≤ 2 * (ksUg ρ * ksUg w) ∧ |Real.log (1 - w)| ≤ 2 * (ksUg ρ * ksUg w) ∧
      Real.log ρ ^ 2 ≤ 16 * (ksUg ρ * ksUg w) ∧ Real.log (1 - ρ) ^ 2 ≤ 16 * (ksUg ρ * ksUg w) ∧
      Real.log w ^ 2 ≤ 16 * (ksUg ρ * ksUg w) ∧ Real.log (1 - w) ^ 2 ≤ 16 * (ksUg ρ * ksUg w) ∧
      (1 - ρ) ^ (-(1 / 2 : ℝ)) ≤ ksUg ρ * ksUg w := by
  have gx := ksU_one_le_ksUg hρ
  have gs := ksU_one_le_ksUg hw
  have rx := ksU_rpow_le_ksUg hρ
  have rs := ksU_rpow_le_ksUg hw
  have hgx : ksUg ρ ≤ ksUg ρ * ksUg w := le_mul_of_one_le_right (by linarith) gs
  have hgs : ksUg w ≤ ksUg ρ * ksUg w := le_mul_of_one_le_left (by linarith) gx
  have p1 : 0 < 1 - ρ := by linarith [hρ.2]
  have p2 : 0 < 1 - w := by linarith [hw.2]
  have l1 := ksU_abs_log_le hρ.1 hρ.2.le
  have l2 := ksU_abs_log_le p1 (by linarith [hρ.1])
  have l3 := ksU_abs_log_le hw.1 hw.2.le
  have l4 := ksU_abs_log_le p2 (by linarith [hw.1])
  have q1 := ksU_log_sq_le hρ.1 hρ.2.le
  have q2 := ksU_log_sq_le p1 (by linarith [hρ.1])
  have q3 := ksU_log_sq_le hw.1 hw.2.le
  have q4 := ksU_log_sq_le p2 (by linarith [hw.1])
  refine ⟨by nlinarith, hgx, hgs, by linarith [rx.1], by linarith [rx.2], by linarith [rs.1],
    by linarith [rs.2], by linarith [rx.1], by linarith [rx.2], by linarith [rs.1],
    by linarith [rs.2], by linarith [rx.2]⟩

theorem ksU_integrable_ksUg_cube :
    Integrable (fun z : (ℝ × ℝ) × ℝ => ksUg z.1.1 * ksUg z.2)
      (((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))).prod
        (volume.restrict (Ioo (0 : ℝ) 1))) := by
  have h1 : Integrable (fun p : ℝ × ℝ => ksUg p.1)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    have h := ksU_integrableOn_ksUg.mul_prod (integrableOn_const (μ := volume)
      (s := Ioo (0 : ℝ) 1) (C := (1 : ℝ)) (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
    simpa using h
  exact h1.mul_prod ksU_integrableOn_ksUg

end QED.ChainProof.SetAKS

end
