/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import QED.ChainProof.SetAKSKWAsmBVal
public import QED.ChainProof.SetAKSKUVBExp

/-!
# Set (a), stage D: the joint integrability of the `VB` node density

Helper level for `KsCoreOne` (Set (a) of the three-loop coefficient), dispersive route. The
weight `ksWBw ρ β w` of the node norm bound `ksWB_integral_norm_le` is dominated by
`ksUg ρ · ksUg w`, which is integrable on the unit cube: the coefficients `g₀, g₁, q, f₀, c` are
bounded, `log(1 + ρY/(1-ρ))/ρ ≤ -log(1-ρ)/ρ ≤ 4 ksUg ρ`, the `K` difference is bounded by
`log(1 + max)` times a bounded logarithm, and `(1-ρ)⁻¹ f₀ (1/r - 1/p) = -16bY(b-a)/D₀` with
`Y ≤ D₀`. The nodes with `w(1-w) = β(1-β)` form a null set of the cube. Hence the joint
integrand `n_B k_s` is integrable on `(0,1)³ × (4, ∞)`.

Main results:

* `ksWB_ksWBw_le`: `ksWBw ρ β w ≤ 2000 ksUg ρ ksUg w`;
* `ksWB_measurable_ksWnB`, `ksWB_ae_ne_cube`;
* **`ksWB_integrable_VB_joint`**.
-/

@[expose] public section

open Real MeasureTheory Set

namespace QED.ChainProof.SetAKS

theorem ksWB_abs_g_le {ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) : |ksWBg0 ρ β w| ≤ 200 ∧ |ksWBg1 ρ β w| ≤ 200 := by
  obtain ⟨r0, r1⟩ := hρ
  obtain ⟨b0, b1⟩ := hβ
  obtain ⟨w0, w1⟩ := hw
  set c := (1 - ρ * β) * (1 - w) + ρ * (1 - β) * w with hc
  have c0 : 0 ≤ c := by
    have : 0 ≤ 1 - ρ * β := by nlinarith
    have : 0 ≤ ρ * (1 - β) := by nlinarith
    positivity
  have c1 : c ≤ 1 := by nlinarith [mul_pos r0 b0, mul_pos r0 (sub_pos.2 b1)]
  have eg0 : ksWBg0 ρ β w = 16 * (w ^ 2 - 3 * w + 1) + 16 * (4 * w - 3) * c + 16 * c ^ 2 -
      ((-32 * (1 - ρ) * w + 32 * (1 - ρ) ^ 2 * w * (w - 1)) +
        (-32 + 32 * (1 - ρ) * (2 * w - 1)) * c + 32 * c ^ 2) / 2 := by
    simp [ksWBg0, ksDEc, ksDHc, ksDcv, ksDc0, ksUPtB, hc]
  have eg1 : ksWBg1 ρ β w = -(((-32 * (1 - ρ) * w + 32 * (1 - ρ) ^ 2 * w * (w - 1)) +
        (-32 + 32 * (1 - ρ) * (2 * w - 1)) * c + 32 * c ^ 2) * (w * (1 - w)) / 2) := by
    simp [ksWBg1, ksDHc, ksDcv, ksDc0, ksUPtB, hc]
  have h1 : 0 < 1 - ρ := by linarith
  have hw' : 0 < 1 - w := by linarith
  have hH : |(-32 * (1 - ρ) * w + 32 * (1 - ρ) ^ 2 * w * (w - 1)) +
        (-32 + 32 * (1 - ρ) * (2 * w - 1)) * c + 32 * c ^ 2| ≤ 200 := by
    rw [abs_le]; constructor <;>
      nlinarith [mul_pos h1 w0, mul_pos (mul_pos h1 h1) (mul_pos w0 hw'), mul_nonneg c0 c0,
        mul_nonneg (mul_nonneg h1.le c0) w0.le, mul_nonneg h1.le c0, mul_nonneg c0 w0.le]
  refine ⟨?_, ?_⟩
  · rw [eg0, abs_le]; rw [abs_le] at hH; constructor <;>
      nlinarith [mul_nonneg c0 w0.le, mul_nonneg c0 c0]
  · rw [eg1, abs_neg, abs_div, abs_mul, abs_of_pos (mul_pos w0 hw')]
    have : w * (1 - w) ≤ 1 := by nlinarith
    have h0 := abs_nonneg ((-32 * (1 - ρ) * w + 32 * (1 - ρ) ^ 2 * w * (w - 1)) +
        (-32 + 32 * (1 - ρ) * (2 * w - 1)) * c + 32 * c ^ 2)
    rw [abs_of_pos (two_pos : (0 : ℝ) < 2), div_le_iff₀ two_pos]
    nlinarith [mul_pos w0 hw']


theorem ksWB_abs_log_one_add_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |log (1 + x) - log (1 + y)| ≤ |x - y| := by
  have k : ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → log (1 + u) - log (1 + v) ≤ |u - v| := by
    intro u v hu hv
    rw [← log_div (by linarith) (by linarith)]
    refine (log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
    nlinarith [le_abs_self (u - v), abs_nonneg (u - v)]
  rw [abs_le]
  refine ⟨?_, k x y hx hy⟩
  have := k y x hy hx
  rw [abs_sub_comm] at this
  linarith

theorem ksWB_abs_ksUq_le {ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) : |ksUq ρ β w| ≤ 256 := by
  obtain ⟨r0, r1⟩ := hρ
  obtain ⟨b0, b1⟩ := hβ
  obtain ⟨w0, w1⟩ := hw
  have h1 : 0 < 1 - ρ := by linarith
  unfold ksUq
  rw [abs_le]; constructor <;>
    nlinarith [mul_pos h1 w0, mul_pos (mul_pos h1 w0) (sub_pos.2 w1), mul_pos h1 b0,
      mul_pos h1 (sub_pos.2 b1), mul_pos (mul_pos h1 h1) b0, mul_pos (mul_pos h1 h1) w0,
      mul_pos (mul_pos h1 h1) (mul_pos b0 w0), mul_pos (mul_pos h1 w0) b0,
      mul_pos (mul_pos h1 w0) w0, mul_pos (mul_pos h1 b0) b0, mul_pos b0 w0,
      mul_pos (mul_pos h1 h1) (mul_pos w0 w0), mul_pos (mul_pos h1 h1) (mul_pos b0 b0)]

theorem ksWB_w12_le {ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) :
    (|ksWBg0 ρ β w| + |ksWBg1 ρ β w|) / ρ * log (1 + ksWBl ρ β w * ksWBr β / ksWBq w) +
      ρ * |ksUcB w| * |ksUK (ksWBl ρ β w * (ksWBr β + 1) / (ksWBq w + 1)) -
        ksUK (ksWBl ρ β w * ksWBr β / ksWBq w)| ≤ 1600 * ksUg ρ + 4 * (1 + 4 * ρ * ksUg ρ) := by
  obtain ⟨hq0, hq4, hr0, hr4, hl0, hY, hY1, hD0⟩ := ksWB_basic hρ hβ hw
  obtain ⟨hG1, hgρ, hgw, hlρ, -, hlw, hlw1, -⟩ := ksU_logs_le_B hρ hw
  obtain ⟨hg0, hg1⟩ := ksWB_abs_g_le hρ hβ hw
  have hqb := ksWB_abs_ksUq_le hρ hβ hw
  have hc := ksU_abs_ksUcB_le hw
  have hlY := ksU_abs_log_ksDYmax_le hβ hw
  have hL := ksU_neg_log_one_sub_le hρ
  obtain ⟨r0, r1⟩ := hρ
  have h1 : 0 < 1 - ρ := by linarith
  have ha : 0 < w * (1 - w) := mul_pos hw.1 (by linarith [hw.2])
  have hb : 0 < β * (1 - β) := mul_pos hβ.1 (by linarith [hβ.2])
  have ha4 : w * (1 - w) ≤ 1 / 4 := by nlinarith [sq_nonneg (w - 1 / 2)]
  have hb4 : β * (1 - β) ≤ 1 / 4 := by nlinarith [sq_nonneg (β - 1 / 2)]
  set Y := ksDYmax β w with hYd
  set z0 := ksWBl ρ β w * ksWBr β / ksWBq w with hz0
  set z1 := ksWBl ρ β w * (ksWBr β + 1) / (ksWBq w + 1) with hz1
  have ez0 : z0 = ρ * Y / (1 - ρ) := by
    simp only [hz0, ksWBl, ksWBr, ksWBq, ← hYd]
    field_simp
    exact div_self (by rw [mul_assoc (β * (1 - β))]; exact (mul_pos hb ha).ne')
  have hz0p : 0 < z0 := by rw [ez0]; positivity
  have hlog0 : log (1 + z0) ≤ -log (1 - ρ) := by
    rw [← log_inv]
    refine log_le_log (by linarith) ?_
    rw [ez0, ← one_div, le_div_iff₀ h1, add_mul, div_mul_cancel₀ _ h1.ne']
    nlinarith
  have hlog0' : 0 ≤ log (1 + z0) := log_nonneg (by linarith)
  -- `z₁ = z₀ (1 + 1/r)/(1 + 1/q)`
  have ez1 : z1 = z0 * (1 + 1 / ksWBr β) / (1 + 1 / ksWBq w) := by
    simp only [hz0, hz1]
    field_simp
  have hir : 1 / ksWBr β ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hr4
  have hiq : 1 / ksWBq w ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hq4
  have hir0 : 0 < 1 / ksWBr β := by positivity
  have hiq0 : 0 < 1 / ksWBq w := by positivity
  have hz1p : 0 < z1 := by rw [ez1]; positivity
  have hz1le : z1 ≤ 5 / 4 * z0 := by
    rw [ez1, div_le_iff₀ (by linarith)]
    nlinarith
  have hmax : log (1 + max z1 z0) ≤ 1 + log (1 + z0) := by
    have : 1 + max z1 z0 ≤ 2 * (1 + z0) := by
      rcases le_total z1 z0 with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    refine (log_le_log (by positivity) this).trans ?_
    rw [log_mul (by norm_num) (by positivity)]
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogd : |log z1 - log z0| ≤ 1 := by
    rw [ez1, log_div (by positivity) (by positivity), log_mul hz0p.ne' (by positivity)]
    have e : log z0 + log (1 + 1 / ksWBr β) - log (1 + 1 / ksWBq w) - log z0 =
        log (1 + 1 / ksWBr β) - log (1 + 1 / ksWBq w) := by ring
    rw [e]
    refine (ksWB_abs_log_one_add_sub_le hir0.le hiq0.le).trans ?_
    rw [abs_le]; constructor <;> linarith
  have T2 : ρ * |ksUcB w| * |ksUK z1 - ksUK z0| ≤ 4 * (1 + 4 * ρ * ksUg ρ) := by
    have hK := ksWB_abs_ksUK_sub_le hz1p hz0p
    have hK' : |ksUK z1 - ksUK z0| ≤ 1 + 4 * ρ * ksUg ρ := by
      refine hK.trans ?_
      have h0 : 0 ≤ log (1 + max z1 z0) := log_nonneg (by
        have := le_max_right z1 z0; linarith)
      calc log (1 + max z1 z0) * |log z1 - log z0| ≤ log (1 + max z1 z0) * 1 :=
            mul_le_mul_of_nonneg_left hlogd h0
        _ ≤ 1 + 4 * ρ * ksUg ρ := by linarith
    have : ρ * |ksUcB w| ≤ 4 := by nlinarith [abs_nonneg (ksUcB w)]
    calc ρ * |ksUcB w| * |ksUK z1 - ksUK z0| ≤ 4 * |ksUK z1 - ksUK z0| :=
          mul_le_mul_of_nonneg_right this (abs_nonneg _)
      _ ≤ 4 * (1 + 4 * ρ * ksUg ρ) := by linarith
  have T1 : (|ksWBg0 ρ β w| + |ksWBg1 ρ β w|) / ρ * log (1 + z0) ≤ 1600 * ksUg ρ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ r0]
    have : (|ksWBg0 ρ β w| + |ksWBg1 ρ β w|) * log (1 + z0) ≤ 400 * (4 * ρ * ksUg ρ) :=
      mul_le_mul (by linarith) (hlog0.trans hL) hlog0' (by norm_num)
    linarith
  linarith

theorem ksWB_w4_le {ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) :
    |(1 - ρ)⁻¹ * ksUf0 β w| *
      |log (1 + 1 / ksWBr β) - log (1 + 1 / ksWBp ρ β w)| ≤ 1 := by
  obtain ⟨hq0, hq4, hr0, hr4, hl0, hY, hY1, hD0⟩ := ksWB_basic hρ hβ hw
  obtain ⟨r0, r1⟩ := hρ
  have h1 : 0 < 1 - ρ := by linarith
  have ha : 0 < w * (1 - w) := mul_pos hw.1 (by linarith [hw.2])
  have hb : 0 < β * (1 - β) := mul_pos hβ.1 (by linarith [hβ.2])
  have ha4 : w * (1 - w) ≤ 1 / 4 := by nlinarith [sq_nonneg (w - 1 / 2)]
  have hb4 : β * (1 - β) ≤ 1 / 4 := by nlinarith [sq_nonneg (β - 1 / 2)]
  have hpdef : ksWBp ρ β w = (ksWBl ρ β w * ksWBr β + ksWBq w) / (1 + ksWBl ρ β w) := rfl
  have hp4 : 4 ≤ ksWBp ρ β w := by
    rw [hpdef, le_div_iff₀ (by linarith)]
    linarith [mul_le_mul_of_nonneg_left hr4 hl0.le]
  have hip0 : 0 < 1 / ksWBp ρ β w := by positivity
  have hir0 : 0 < 1 / ksWBr β := by positivity
  have hD : ksWBD0 ρ β w = 1 - ρ + ρ * ksDYmax β w := rfl
  have hf : ksUf0 β w = -16 * (β * (1 - β)) * ksDYmax β w := by unfold ksUf0; ring
  have e : (1 - ρ)⁻¹ * ksUf0 β w * (1 / ksWBr β - 1 / ksWBp ρ β w) =
      -(16 * (β * (1 - β)) * ksDYmax β w * (β * (1 - β) - w * (1 - w)) / ksWBD0 ρ β w) := by
    have hD' : 1 - ρ + ρ * ksDYmax β w ≠ 0 := by rw [← hD]; exact hD0.ne'
    have hl1 : 1 + ksWBl ρ β w ≠ 0 := by linarith
    have hn : ksWBl ρ β w * ksWBr β + ksWBq w ≠ 0 := by positivity
    rw [hpdef, hD, hf]
    simp only [ksWBl, ksWBr, ksWBq] at hl1 hn ⊢
    generalize ksDYmax β w = Y at *
    generalize w * (1 - w) = a at *
    generalize β * (1 - β) = b at *
    field_simp
    ring
  rw [mul_comm]
  refine (mul_le_mul_of_nonneg_right
    (ksWB_abs_log_one_add_sub_le hir0.le hip0.le) (abs_nonneg _)).trans ?_
  rw [← abs_mul, show (1 / ksWBr β - 1 / ksWBp ρ β w) * ((1 - ρ)⁻¹ * ksUf0 β w) = _ from
    (mul_comm _ _).trans e, abs_neg, abs_div, abs_of_pos hD0, div_le_one hD0, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 16 * (β * (1 - β)) * ksDYmax β w)]
  have hDY : ksDYmax β w ≤ ksWBD0 ρ β w := by
    rw [hD]
    nlinarith
  have hab : |β * (1 - β) - w * (1 - w)| ≤ 1 / 4 := by
    rw [abs_le]; constructor <;> linarith
  calc 16 * (β * (1 - β)) * ksDYmax β w * |β * (1 - β) - w * (1 - w)| ≤
        16 * (1 / 4) * ksDYmax β w * (1 / 4) := by gcongr
    _ ≤ ksWBD0 ρ β w := by linarith

/-- **The weight of the `VB` node is dominated** by `ksUg ρ · ksUg w`. -/
theorem ksWB_ksWBw_le {ρ β w : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hw : w ∈ Ioo (0 : ℝ) 1) : ksWBw ρ β w ≤ 2000 * (ksUg ρ * ksUg w) := by
  have T12 := ksWB_w12_le hρ hβ hw
  have T4 := ksWB_w4_le hρ hβ hw
  obtain ⟨hq0, hq4, hr0, hr4, hl0, hY, hY1, hD0⟩ := ksWB_basic hρ hβ hw
  obtain ⟨hG1, hgρ, hgw, hlρ, -, hlw, hlw1, -⟩ := ksU_logs_le_B hρ hw
  have hqb := ksWB_abs_ksUq_le hρ hβ hw
  have hc := ksU_abs_ksUcB_le hw
  have hlY := ksU_abs_log_ksDYmax_le hβ hw
  obtain ⟨r0, r1⟩ := hρ
  have hb : 0 < β * (1 - β) := mul_pos hβ.1 (by linarith [hβ.2])
  have hb4 : β * (1 - β) ≤ 1 / 4 := by nlinarith [sq_nonneg (β - 1 / 2)]
  have hpdef : ksWBp ρ β w = (ksWBl ρ β w * ksWBr β + ksWBq w) / (1 + ksWBl ρ β w) := rfl
  have hp4 : 4 ≤ ksWBp ρ β w := by
    rw [hpdef, le_div_iff₀ (by linarith)]
    linarith [mul_le_mul_of_nonneg_left hr4 hl0.le]
  have hip : 1 / ksWBp ρ β w ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hp4
  have hip0 : 0 < 1 / ksWBp ρ β w := by positivity
  have hiq : 1 / ksWBq w ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hq4
  have hiq0 : 0 < 1 / ksWBq w := by positivity
  have hlogp : log (1 + 1 / ksWBp ρ β w) ≤ 1 / 4 := by
    linarith [log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + 1 / ksWBp ρ β w)]
  have hlogq : log (1 + 1 / ksWBq w) ≤ 1 / 4 := by
    linarith [log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + 1 / ksWBq w)]
  have hlogq0 : 0 ≤ log (1 + 1 / ksWBq w) := log_nonneg (by linarith)
  have hf0 : |ksUf0 β w| ≤ 4 := by
    have e : ksUf0 β w = -(16 * (β * (1 - β)) * ksDYmax β w) := by unfold ksUf0; ring
    rw [e, abs_neg, abs_of_pos (mul_pos (mul_pos (by norm_num) hb) hY)]
    nlinarith [mul_le_mul hb4 hY1 hY.le (by norm_num)]
  have T3 : |ksUq ρ β w * ksDYmax β w / 2| * log (1 + 1 / ksWBp ρ β w) ≤ 128 := by
    have : |ksUq ρ β w * ksDYmax β w / 2| ≤ 128 := by
      rw [abs_div, abs_mul, abs_of_pos hY, abs_two]
      nlinarith [abs_nonneg (ksUq ρ β w)]
    have h0 : 0 ≤ log (1 + 1 / ksWBp ρ β w) := log_nonneg (by linarith)
    have := mul_le_mul this hlogp h0 (by norm_num)
    linarith
  have T5 : |ρ * ksUcB w * log (ksDYmax β w / ρ)| * log (1 + 1 / ksWBq w) ≤
      24 * (ksUg ρ * ksUg w) := by
    have : |ρ * ksUcB w * log (ksDYmax β w / ρ)| ≤ 4 * (6 * (ksUg ρ * ksUg w)) := by
      rw [abs_mul, abs_mul, abs_of_pos r0, log_div hY.ne' r0.ne']
      have hl : |log (ksDYmax β w) - log ρ| ≤ 6 * (ksUg ρ * ksUg w) := by
        refine (abs_sub _ _).trans ?_
        linarith
      have : ρ * |ksUcB w| ≤ 4 := by nlinarith [abs_nonneg (ksUcB w)]
      exact mul_le_mul this hl (abs_nonneg _) (by norm_num)
    have := mul_le_mul this hlogq hlogq0 (by linarith)
    linarith
  have T6 : |ρ * ksUcB w / 2| * 5 ≤ 10 := by
    rw [abs_div, abs_mul, abs_of_pos r0, abs_two]
    nlinarith [abs_nonneg (ksUcB w)]
  have T7 : |ksUf0 β w / 2| * 5 ≤ 10 := by
    rw [abs_div, abs_two]
    linarith
  unfold ksWBw
  have : ρ * ksUg ρ ≤ ksUg ρ := by
    have := mul_le_mul_of_nonneg_right r1.le (by linarith [ksU_one_le_ksUg ⟨r0, r1⟩] :
      (0 : ℝ) ≤ ksUg ρ)
    linarith
  linarith

theorem ksWB_measurable_ite {α : Type*} [MeasurableSpace α] {f g a b : α → ℝ}
    (hf : Measurable f) (hg : Measurable g) (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x => if f x < g x then a x else b x :=
  Measurable.ite (measurableSet_lt hf hg) ha hb

theorem ksWB_measurable_ksWnB :
    Measurable fun p : ((ℝ × ℝ) × ℝ) × ℝ => ksWnB p.1.1.1 p.1.1.2 p.1.2 p.2 := by
  have hY : Measurable fun p : ((ℝ × ℝ) × ℝ) × ℝ => ksDYmax p.1.1.2 p.1.2 := by
    unfold ksDYmax; fun_prop
  have hG : Measurable fun p : ((ℝ × ℝ) × ℝ) × ℝ => ksUG0 1 (-p.2) p.1.1.1 p.1.1.2 p.1.2 := by
    unfold ksUG0 ksUGc ksDEc ksDHc ksDcv ksDc0 ksDc1 ksUPtB ksDA
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail]
    fun_prop
  unfold ksWnB ksDA ksUq ksUf0 ksUcB
  repeat' (first | apply ksWB_measurable_ite | fun_prop | apply Measurable.add |
    apply Measurable.mul | apply Measurable.neg)

/-- Off a null set of the cube, the thresholds of `A_w` and `A_β` differ. -/
theorem ksWB_ae_ne_cube :
    ∀ᵐ z ∂(((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))).prod
      (volume.restrict (Ioo (0 : ℝ) 1))), z.2 * (1 - z.2) ≠ z.1.2 * (1 - z.1.2) := by
  have hm : MeasurableSet {z : (ℝ × ℝ) × ℝ | z.2 * (1 - z.2) ≠ z.1.2 * (1 - z.1.2)} :=
    (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
  refine (Measure.ae_prod_iff_ae_ae hm).2 (Filter.Eventually.of_forall fun x => ?_)
  have h1 : ∀ᵐ y ∂(volume.restrict (Ioo (0 : ℝ) 1)), y ≠ x.2 :=
    ae_restrict_of_ae (by rw [ae_iff]; simp)
  have h2 : ∀ᵐ y ∂(volume.restrict (Ioo (0 : ℝ) 1)), y ≠ 1 - x.2 :=
    ae_restrict_of_ae (by rw [ae_iff]; simp)
  filter_upwards [h1, h2] with y hy1 hy2
  intro h
  have : (y - x.2) * (1 - y - x.2) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h' | h'
  · exact hy1 (by linarith)
  · exact hy2 (by linarith)

/-- The joint integrand of the `VB` dispersive exchange. -/
noncomputable def ksWjB (s : ℝ) (p : ((ℝ × ℝ) × ℝ) × ℝ) : ℝ :=
  ksWnB p.1.1.1 p.1.1.2 p.1.2 p.2 * (s / (p.2 * (s + p.2)))

theorem ksWB_measurable_ksWjB (s : ℝ) : Measurable (ksWjB s) :=
  ksWB_measurable_ksWnB.mul (by fun_prop)

/-- **The joint integrability of the `VB` dispersive exchange**: `n_B k_s` is integrable on
`(0,1)³ × (4, ∞)`. -/
theorem ksWB_integrable_VB_joint {s : ℝ} (hs : -4 < s) :
    Integrable (ksWjB s) ((((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioo (0 : ℝ) 1))).prod (volume.restrict (Ioo (0 : ℝ) 1))).prod
        (volume.restrict (Ioi 4))) := by
  have hmeas := ksWB_measurable_ksWjB s
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  have hae := Filter.Eventually.and ksU_ae_mem_cube ksWB_ae_ne_cube
  constructor
  · filter_upwards [hae] with z hz
    exact (ksWB_node_disp hz.1.1 hz.1.2.1 hz.1.2.2 hz.2 hs).1
  · refine Integrable.mono' (ksU_integrable_ksUg_cube.const_mul (ksWcs s * 2000))
      (hmeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) ?_
    filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    refine (ksWB_integral_norm_le hz.1.1 hz.1.2.1 hz.1.2.2 hz.2 hs).trans ?_
    have := mul_le_mul_of_nonneg_left (ksWB_ksWBw_le hz.1.1 hz.1.2.1 hz.1.2.2)
      (ksW_ksWcs_nonneg hs)
    linarith

end QED.ChainProof.SetAKS

end
